--[[
	WARNING: Heads up! This script has not been verified by ScriptBlox. Use at your own risk!
]]
--[[
    ╔══════════════════════════════════════════════════════════════╗
    ║              DARKWIRED - MINERS WORLD PREDICTOR              ║
    ║         Particle ESP + Pattern Analysis + Prediction         ║
    ║                  + Seed Hunter + Mesh Detection              ║
    ║                       + Full UI + Persistence                ║
    ║                      + Tracer System (Debug)                 ║
    ╚══════════════════════════════════════════════════════════════╝
]]

local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local UserInputService = game:GetService("UserInputService")
local HttpService = game:GetService("HttpService")
local Camera = workspace.CurrentCamera

local player = Players.LocalPlayer
local guiParent = player:WaitForChild("PlayerGui")

-------------------------------------------------
-- CONFIGURATION
-------------------------------------------------
local GRID_SIZE = 4
local PREDICTION_RADIUS = 50
local UPDATE_INTERVAL = 0.5
local MIN_SAMPLES_FOR_PREDICTION = 5
local ENABLE_SEED_HUNT = true
local ENABLE_MESH_DETECTION = true
local ENABLE_PREDICTION = true
local ENABLE_FOCUS_MODE = true
local ENABLE_PATTERN = true
local ENABLE_ADVANCED = true
local ENABLE_TRACERS = true               -- master tracer toggle

-- Check if Drawing is supported
local DRAWING_SUPPORTED = pcall(Drawing.new, "Line")
if not DRAWING_SUPPORTED then
    warn("[Darkwired] Drawing library not supported – tracers will not appear.")
end

-------------------------------------------------
-- RARITY DATA
-------------------------------------------------
local rarities = {
    {name="Zenith",    color=Color3.fromRGB(120,0,120)},
    {name="Divine",    color=Color3.fromRGB(255,255,255)},
    {name="Celestial", color=Color3.fromRGB(0,255,255)},
    {name="Ethereal",  color=Color3.fromRGB(255,20,147)},
    {name="Mythic",    color=Color3.fromRGB(255,0,0)},
    {name="Legendary", color=Color3.fromRGB(255,200,0)},
    {name="Epic",      color=Color3.fromRGB(170,0,255)},
    {name="Rare",      color=Color3.fromRGB(0,120,255)},
    {name="Uncommon",  color=Color3.fromRGB(0,255,0)}
}
local rarityByName = {}
for _, r in ipairs(rarities) do rarityByName[r.name] = r end

-- Enabled rarities (ESP)
local espEnabled = {}
for _, r in ipairs(rarities) do espEnabled[r.name] = true end

-- Tracer enabled per rarity
local tracerEnabled = {}
for _, r in ipairs(rarities) do tracerEnabled[r.name] = false end

-- MeshId mapping
local targets = {
    ["rbxassetid://103949883753847"] = "TNT UN",
    ["rbxassetid://14365388307"]     = "Dynamite",
    ["rbxassetid://88911303348714"]  = "TNT CO",
    ["rbxassetid://12796568017"]     = "Emerald",
    ["rbxassetid://132422790581482"] = "Drill TNT",
    ["rbxassetid://130746239003755"] = "TNT RA",
    ["rbxassetid://136756472360049"] = "ore tnt",
    ["rbxassetid://97885003736109"]  = "TNT EP"
}
local targetNames = {}
for id, name in pairs(targets) do targetNames[id] = name end

-------------------------------------------------
-- ÖZEL BLOKLAR (kahverengi ESP + ışınlanma)
-- * ore tnt  : rbxassetid://136756472360049
-- * Emerald  : rbxassetid://12796568017
-------------------------------------------------
local SPECIAL_ORE_IDS = {
    ["rbxassetid://136756472360049"] = "ore tnt",
    ["rbxassetid://12796568017"]     = "Emerald",
}
local SPECIAL_ORE_COLOR   = Color3.fromRGB(139, 90, 43)
local SPECIAL_ORE_OUTLINE = Color3.fromRGB(210, 140, 60)
local specialOreEnabled   = true
local specialOreParts     = {}   -- part -> {highlight, billboard}
local specialOreList      = {}   -- { {part=.., pos=..} } ışınlanma için

-------------------------------------------------
-- DATA STORAGE
-------------------------------------------------
local scannedBlocks = {}               -- grid position -> block data
local scannedParts = {}                 -- set to avoid reprocessing
local rarityCounts = {}
for _, r in ipairs(rarities) do rarityCounts[r.name] = 0 end

local depthHist = {}                    -- per rarity: Y index -> count
for _, r in ipairs(rarities) do depthHist[r.name] = {} end

local positionsByRarity = {}            -- per rarity: list of grid positions
for _, r in ipairs(rarities) do positionsByRarity[r.name] = {} end

local spatialHash = {}                  -- key string -> block data
local predictionMarkers = {}             -- key -> part

-- For easy removal when disabling rarities
local espByRarity = {}                   -- rarity name -> list of {highlight, billboard}
for _, r in ipairs(rarities) do espByRarity[r.name] = {} end

-- For tracers
local tracerLines = {}                   -- key -> Drawing line object
local tracerUpdateConn = nil

-------------------------------------------------
-- UTILITY FUNCTIONS
-------------------------------------------------
local function roundToGrid(pos)
    local x = math.floor((pos.X + GRID_SIZE/2) / GRID_SIZE) * GRID_SIZE
    local y = math.floor((pos.Y + GRID_SIZE/2) / GRID_SIZE) * GRID_SIZE
    local z = math.floor((pos.Z + GRID_SIZE/2) / GRID_SIZE) * GRID_SIZE
    return Vector3.new(x, y, z)
end

local function posKey(pos)
    return string.format("%.0f,%.0f,%.0f", pos.X, pos.Y, pos.Z)
end

local function colorDistance(c1, c2)
    return (c1.R-c2.R)^2 + (c1.G-c2.G)^2 + (c1.B-c2.B)^2
end

local function avgColorFromEmitter(emitter)
    local seq = emitter.Color
    local r, g, b, count = 0, 0, 0, 0
    for _, kp in ipairs(seq.Keypoints) do
        r = r + kp.Value.R
        g = g + kp.Value.G
        b = b + kp.Value.B
        count = count + 1
    end
    if count == 0 then return nil end
    return Color3.new(r/count, g/count, b/count)
end

local function closestRarity(avgColor)
    if not avgColor then return nil end
    local bestRarity, bestDist = nil, math.huge
    for _, r in ipairs(rarities) do
        local d = colorDistance(avgColor, r.color)
        if d < bestDist then
            bestDist = d
            bestRarity = r
        end
    end
    return bestDist < 3 and bestRarity or nil
end

local function findPart(obj)
    while obj do
        if obj:IsA("BasePart") then return obj end
        obj = obj.Parent
    end
    return nil
end


-------------------------------------------------
-- ÖZEL BLOK ESP OLUŞTUR / KALDIR
-------------------------------------------------
local function createSpecialOreESP(part, oreName)
    -- Highlight: kahverengi dolgu
    local hl = Instance.new("Highlight")
    hl.Parent = part
    hl.FillColor = SPECIAL_ORE_COLOR
    hl.FillTransparency = 0.35
    hl.OutlineColor = SPECIAL_ORE_OUTLINE
    hl.OutlineTransparency = 0
    hl.DepthMode = Enum.HighlightDepthMode.AlwaysOnTop

    -- BillboardGui: isim + "tıkla ışınlan" yazısı
    local bb = Instance.new("BillboardGui")
    bb.Parent = part
    bb.Size = UDim2.new(0, 110, 0, 36)
    bb.StudsOffset = Vector3.new(0, 4, 0)
    bb.AlwaysOnTop = true
    bb.LightInfluence = 0

    local bg = Instance.new("Frame", bb)
    bg.Size = UDim2.fromScale(1, 1)
    bg.BackgroundColor3 = Color3.fromRGB(60, 35, 10)
    bg.BackgroundTransparency = 0.25
    bg.BorderSizePixel = 0
    Instance.new("UICorner", bg).CornerRadius = UDim.new(0, 6)
    local bgStroke = Instance.new("UIStroke", bg)
    bgStroke.Color = SPECIAL_ORE_OUTLINE
    bgStroke.Thickness = 1.5

    local nameL = Instance.new("TextLabel", bg)
    nameL.Size = UDim2.new(1, 0, 0.55, 0)
    nameL.BackgroundTransparency = 1
    nameL.Text = "⬛ " .. oreName
    nameL.Font = Enum.Font.GothamBlack
    nameL.TextScaled = true
    nameL.TextColor3 = SPECIAL_ORE_OUTLINE
    nameL.TextStrokeTransparency = 0
    nameL.TextStrokeColor3 = Color3.new(0,0,0)

    local hintL = Instance.new("TextLabel", bg)
    hintL.Size = UDim2.new(1, 0, 0.42, 0)
    hintL.Position = UDim2.new(0, 0, 0.55, 0)
    hintL.BackgroundTransparency = 1
    hintL.Text = "[ tıkla → ışınlan ]"
    hintL.Font = Enum.Font.Gotham
    hintL.TextScaled = true
    hintL.TextColor3 = Color3.fromRGB(220, 180, 100)
    hintL.TextStrokeTransparency = 0
    hintL.TextStrokeColor3 = Color3.new(0,0,0)

    return hl, bb
end

local function removeAllSpecialOreESP()
    for part, esp in pairs(specialOreParts) do
        pcall(function() esp.hl:Destroy() end)
        pcall(function() esp.bb:Destroy() end)
    end
    specialOreParts = {}
end

-------------------------------------------------
-- EN YAKIN NADİRLİK BLOĞUNU BUL
-------------------------------------------------
local function findNearestRarityBlock(rarityName, fromPos)
    local bestPart, bestDist = nil, math.huge
    for _, data in pairs(scannedBlocks) do
        if data.rarity == rarityName and data.part and data.part.Parent then
            local d = (data.part.Position - fromPos).Magnitude
            if d < bestDist then
                bestDist = d
                bestPart = data.part
            end
        end
    end
    return bestPart
end

-------------------------------------------------
-- IŞINLANMA FONKSİYONU
-------------------------------------------------
local function teleportTo(pos)
    local char = player.Character
    local hrp = char and char:FindFirstChild("HumanoidRootPart")
    if not hrp then return end
    hrp.CFrame = CFrame.new(pos + Vector3.new(0, 4, 0))
end

local function identifyRarity(part)
    -- Particles first
    local emitter = part:FindFirstChildOfClass("ParticleEmitter")
    if emitter and emitter.Color then
        local avg = avgColorFromEmitter(emitter)
        local rarity = closestRarity(avg)
        if rarity then return rarity end
    end

    -- MeshId fallback
    if ENABLE_MESH_DETECTION and part:IsA("MeshPart") and part.MeshId ~= "" then
        local name = targetNames[part.MeshId]
        if name then
            -- Could map to rarity if known
        end
    end
    return nil
end

-------------------------------------------------
-- BLOCK PROCESSING (with ESP storage)
-------------------------------------------------
local function processBlock(part)
    if scannedParts[part] then return end
    scannedParts[part] = true

    local rarity = identifyRarity(part)
    if not rarity then return end
    print("[DEBUG] Block processed:", part.Name, rarity.name) -- Debug

    local gridPos = roundToGrid(part.Position)
    local key = posKey(gridPos)
    if spatialHash[key] then return end

    local blockData = {
        part = part,
        rarity = rarity.name,
        pos = gridPos,
        color = rarity.color,
        mesh = part:IsA("MeshPart") and part.MeshId or nil
    }
    scannedBlocks[gridPos] = blockData
    spatialHash[key] = blockData
    rarityCounts[rarity.name] = rarityCounts[rarity.name] + 1

    local yIndex = math.floor(gridPos.Y / GRID_SIZE)
    depthHist[rarity.name][yIndex] = (depthHist[rarity.name][yIndex] or 0) + 1
    table.insert(positionsByRarity[rarity.name], gridPos)

    -- Create ESP only if rarity is enabled
    if espEnabled[rarity.name] then
        local highlight = Instance.new("Highlight")
        highlight.Parent = part
        highlight.FillColor = rarity.color
        highlight.DepthMode = Enum.HighlightDepthMode.AlwaysOnTop

        local billboard = Instance.new("BillboardGui")
        billboard.Parent = part
        billboard.Size = UDim2.new(0, 120, 0, 40)
        billboard.StudsOffset = Vector3.new(0, 3, 0)
        billboard.AlwaysOnTop = true
        local label = Instance.new("TextLabel", billboard)
        label.Size = UDim2.fromScale(1, 1)
        label.BackgroundTransparency = 1
        label.Text = rarity.name:upper()
        label.Font = Enum.Font.GothamBlack
        label.TextScaled = true
        label.TextColor3 = rarity.color
        label.TextStrokeTransparency = 0

        blockData.highlight = highlight
        blockData.billboard = billboard
        table.insert(espByRarity[rarity.name], {highlight = highlight, billboard = billboard})
    end
end

-------------------------------------------------
-- ÖZEL BLOK TARAMA (MeshPart ID kontrolü)
-------------------------------------------------
local function processSpecialOre(part)
    if specialOreParts[part] then return end  -- zaten işlendi
    if not part:IsA("MeshPart") then return end
    local oreName = SPECIAL_ORE_IDS[part.MeshId]
    if not oreName then return end

    -- Listeye ekle
    table.insert(specialOreList, {part = part, pos = part.Position})

    if specialOreEnabled then
        local hl, bb = createSpecialOreESP(part, oreName)
        specialOreParts[part] = {hl = hl, bb = bb}

        -- Billboard'daki tıklama butonu (TextButton)
        -- Kullanıcı bill board'a tıklayamaz ama Billboard'a ClickDetector koyabiliriz.
        -- Alternatif: part'a ClickDetector ekle
        local cd = part:FindFirstChildOfClass("ClickDetector")
        if not cd then
            cd = Instance.new("ClickDetector", part)
            cd.MaxActivationDistance = 300
        end
        cd.MouseClick:Connect(function()
            teleportTo(part.Position)  -- ClickDetector: callback gerekmez
        end)
    end
end

-------------------------------------------------
-- EVENT HANDLERS
-------------------------------------------------
workspace.DescendantAdded:Connect(function(inst)
    if inst:IsA("ParticleEmitter") then
        local part = findPart(inst)
        if part then processBlock(part) end
    elseif ENABLE_MESH_DETECTION and inst:IsA("MeshPart") and inst.MeshId ~= "" then
        processBlock(inst)
    end
end)

for _, inst in ipairs(workspace:GetDescendants()) do
    if inst:IsA("ParticleEmitter") then
        local part = findPart(inst)
        if part then processBlock(part) end
    elseif ENABLE_MESH_DETECTION and inst:IsA("MeshPart") and inst.MeshId ~= "" then
        processBlock(inst)
    end
end

-------------------------------------------------
-- ENHANCED PATTERN ANALYSIS & PREDICTION

-- Özel blok tarama: mevcut + yeni gelenler
for _, inst in ipairs(workspace:GetDescendants()) do
    if inst:IsA("MeshPart") and SPECIAL_ORE_IDS[inst.MeshId] then
        processSpecialOre(inst)
    end
end
workspace.DescendantAdded:Connect(function(inst)
    if inst:IsA("MeshPart") and SPECIAL_ORE_IDS[inst.MeshId] then
        processSpecialOre(inst)
    end
end)

-------------------------------------------------
-- ENHANCED PATTERN ANALYSIS & PREDICTION
-------------------------------------------------
local function updatePredictions()
    if not ENABLE_PREDICTION then return end

    local playerChar = player.Character
    local hrp = playerChar and playerChar:FindFirstChild("HumanoidRootPart")
    if not hrp then return end
    local playerGrid = roundToGrid(hrp.Position)

    local probMap = {}  -- key -> table rarityName -> score

    local function addProbability(gridPos, rarityName, score)
        local key = posKey(gridPos)
        probMap[key] = probMap[key] or {}
        probMap[key][rarityName] = (probMap[key][rarityName] or 0) + score
    end

    -- 1. Inverse distance weighting from observed blocks
    for rarityName, positions in pairs(positionsByRarity) do
        if espEnabled[rarityName] and #positions >= MIN_SAMPLES_FOR_PREDICTION then
            for _, obsPos in ipairs(positions) do
                local dx = obsPos.X - playerGrid.X
                local dy = obsPos.Y - playerGrid.Y
                local dz = obsPos.Z - playerGrid.Z
                if math.abs(dx) <= PREDICTION_RADIUS * GRID_SIZE and
                   math.abs(dy) <= PREDICTION_RADIUS * GRID_SIZE and
                   math.abs(dz) <= PREDICTION_RADIUS * GRID_SIZE then
                    local range = 2
                    for x = -range, range do
                        for y = -range, range do
                            for z = -range, range do
                                local candidate = obsPos + Vector3.new(x*GRID_SIZE, y*GRID_SIZE, z*GRID_SIZE)
                                local cKey = posKey(candidate)
                                if not spatialHash[cKey] then
                                    local distSq = x*x + y*y + z*z
                                    if distSq > 0 then
                                        local weight = 1 / (distSq + 0.5)
                                        addProbability(candidate, rarityName, weight)
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end

    -- 2. Depth likelihood boost
    for rarityName, hist in pairs(depthHist) do
        if espEnabled[rarityName] then
            local total = 0
            for _, cnt in pairs(hist) do total = total + cnt end
            if total > MIN_SAMPLES_FOR_PREDICTION then
                for key, scores in pairs(probMap) do
                    local pos = Vector3.new(
                        tonumber(key:match("([^,]+),([^,]+),([^,]+)"))
                    )
                    local yIndex = math.floor(pos.Y / GRID_SIZE)
                    local depthProb = (hist[yIndex] or 0) / total
                    if depthProb > 0 then
                        for rname, sc in pairs(scores) do
                            scores[rname] = sc * (1 + depthProb)
                        end
                    end
                end
            end
        end
    end

    -- 3. Advanced pattern detection (if enabled)
    if ENABLE_ADVANCED then
        for rarityName, positions in pairs(positionsByRarity) do
            if espEnabled[rarityName] and #positions >= 3 then
                local function checkAxis(axis, positions)
                    local groups = {}
                    for _, pos in ipairs(positions) do
                        local key
                        if axis == "X" then
                            key = string.format("%.0f,%.0f", pos.Y, pos.Z)
                        elseif axis == "Y" then
                            key = string.format("%.0f,%.0f", pos.X, pos.Z)
                        else -- Z
                            key = string.format("%.0f,%.0f", pos.X, pos.Y)
                        end
                        groups[key] = groups[key] or {}
                        table.insert(groups[key], pos)
                    end
                    for _, linePositions in pairs(groups) do
                        if #linePositions >= 3 then
                            table.sort(linePositions, function(a,b)
                                if axis == "X" then return a.X < b.X
                                elseif axis == "Y" then return a.Y < b.Y
                                else return a.Z < b.Z end
                            end)
                            for i = 1, #linePositions-1 do
                                local a = linePositions[i]
                                local b = linePositions[i+1]
                                local diff
                                if axis == "X" then diff = (b.X - a.X) / GRID_SIZE
                                elseif axis == "Y" then diff = (b.Y - a.Y) / GRID_SIZE
                                else diff = (b.Z - a.Z) / GRID_SIZE end
                                if diff == 2 then
                                    local mid
                                    if axis == "X" then
                                        mid = Vector3.new(a.X + GRID_SIZE, a.Y, a.Z)
                                    elseif axis == "Y" then
                                        mid = Vector3.new(a.X, a.Y + GRID_SIZE, a.Z)
                                    else
                                        mid = Vector3.new(a.X, a.Y, a.Z + GRID_SIZE)
                                    end
                                    if not spatialHash[posKey(mid)] then
                                        addProbability(mid, rarityName, 5.0)
                                    end
                                end
                            end
                            if #linePositions >= 2 then
                                local first = linePositions[1]
                                local second = linePositions[2]
                                local dir
                                if axis == "X" then
                                    if second.X - first.X == GRID_SIZE then
                                        dir = Vector3.new(GRID_SIZE, 0, 0)
                                    end
                                elseif axis == "Y" then
                                    if second.Y - first.Y == GRID_SIZE then
                                        dir = Vector3.new(0, GRID_SIZE, 0)
                                    end
                                else
                                    if second.Z - first.Z == GRID_SIZE then
                                        dir = Vector3.new(0, 0, GRID_SIZE)
                                    end
                                end
                                if dir then
                                    local before = first - dir
                                    local after = linePositions[#linePositions] + dir
                                    if not spatialHash[posKey(before)] then
                                        addProbability(before, rarityName, 4.0)
                                    end
                                    if not spatialHash[posKey(after)] then
                                        addProbability(after, rarityName, 4.0)
                                    end
                                end
                            end
                        end
                    end
                end
                checkAxis("X", positions)
                checkAxis("Y", positions)
                checkAxis("Z", positions)
            end
        end

        -- 3b. Cluster filling (3x3x3 neighborhood)
        for key, scores in pairs(probMap) do
            local pos = Vector3.new(
                tonumber(key:match("([^,]+),([^,]+),([^,]+)"))
            )
            for rarityName, _ in pairs(scores) do
                local count = 0
                for x = -1, 1 do
                    for y = -1, 1 do
                        for z = -1, 1 do
                            if not (x==0 and y==0 and z==0) then
                                local neighborPos = pos + Vector3.new(x*GRID_SIZE, y*GRID_SIZE, z*GRID_SIZE)
                                local neighborKey = posKey(neighborPos)
                                if spatialHash[neighborKey] and spatialHash[neighborKey].rarity == rarityName then
                                    count = count + 1
                                end
                            end
                        end
                    end
                end
                if count >= 3 then
                    scores[rarityName] = scores[rarityName] * (1 + count*0.3)
                end
            end
        end
    end

    -- Create/update markers
    local MARKER_THRESHOLD = 0.1
    for key, scores in pairs(probMap) do
        local bestRarity, bestScore = nil, 0
        for rname, score in pairs(scores) do
            if score > bestScore then
                bestScore = score
                bestRarity = rname
            end
        end
        if bestRarity and bestScore >= MARKER_THRESHOLD then
            if not predictionMarkers[key] then
                local pos = Vector3.new(
                    tonumber(key:match("([^,]+),([^,]+),([^,]+)"))
                )
                local marker = Instance.new("Part")
                marker.Size = Vector3.new(GRID_SIZE-0.2, GRID_SIZE-0.2, GRID_SIZE-0.2)
                marker.Position = pos
                marker.Anchored = true
                marker.CanCollide = false
                marker.Transparency = 0.5
                marker.BrickColor = BrickColor.new(rarityByName[bestRarity].color)
                marker.Material = Enum.Material.Neon
                marker.Parent = workspace
                predictionMarkers[key] = marker
            else
                predictionMarkers[key].BrickColor = BrickColor.new(rarityByName[bestRarity].color)
            end
        else
            if predictionMarkers[key] then
                predictionMarkers[key]:Destroy()
                predictionMarkers[key] = nil
            end
        end
    end

    -- Clean up markers for cells no longer in probMap
    for key, marker in pairs(predictionMarkers) do
        if not probMap[key] then
            marker:Destroy()
            predictionMarkers[key] = nil
        end
    end
end

-------------------------------------------------
-- FOCUS MODE
-------------------------------------------------
local function updateFocusMode()
    if not ENABLE_FOCUS_MODE then return end
    local playerChar = player.Character
    local hrp = playerChar and playerChar:FindFirstChild("HumanoidRootPart")
    if not hrp then return end
    for key, marker in pairs(predictionMarkers) do
        if (marker.Position - hrp.Position).Magnitude > PREDICTION_RADIUS * GRID_SIZE * 1.5 then
            marker:Destroy()
            predictionMarkers[key] = nil
        end
    end
end

-------------------------------------------------
-- SEED HUNTER
-------------------------------------------------
local function huntSeed()
    print("[SEED HUNTER] Starting scan...")
    local gc = getgc(true)
    for _, obj in ipairs(gc) do
        if type(obj) == "table" then
            for k, v in pairs(obj) do
                if type(k) == "string" and (k:lower():find("seed") or k:lower():find("noise") or k:lower():find("generat")) then
                    warn("[SEED] Possible seed in table:", k, v)
                end
            end
        elseif type(obj) == "function" then
            local info = debug.getinfo(obj)
            if info then
                local i = 1
                while true do
                    local name, value = debug.getupvalue(obj, i)
                    if not name then break end
                    if type(name) == "string" and (name:lower():find("seed") or name:lower():find("noise")) then
                        warn("[SEED] Upvalue in function", info.name or "?", name, "=", value)
                    end
                    i = i + 1
                end
            end
        end
    end

    local oldNew = Instance.new
    Instance.new = function(className, parent)
        local inst = oldNew(className, parent)
        if className == "Part" or className == "MeshPart" then
            task.defer(function()
                wait()
                if inst and inst.Parent then
                    processBlock(inst)
                end
            end)
        end
        return inst
    end
    print("[SEED HUNTER] Scan complete. Check output for seeds.")
end

if ENABLE_SEED_HUNT then
    task.defer(huntSeed)
end

-------------------------------------------------
-- PERSISTENCE
-------------------------------------------------
local SAVE_FILE = "miners_world_data.json"
local SAVE_INTERVAL = 100
local blocksSinceSave = 0

local function saveData()
    local data = {
        positionsByRarity = positionsByRarity,
        depthHist = depthHist,
        rarityCounts = rarityCounts,
        timestamp = os.time()
    }
    local success, encoded = pcall(HttpService.JSONEncode, HttpService, data)
    if success then
        pcall(writefile, SAVE_FILE, encoded)
        print("[Persistence] Data saved.")
    end
end

local function loadData()
    local success, content = pcall(readfile, SAVE_FILE)
    if not success or not content then return end
    local decoded = pcall(HttpService.JSONDecode, HttpService, content)
    if not decoded then return end
    local data = decoded
    if data.positionsByRarity then positionsByRarity = data.positionsByRarity end
    if data.depthHist then depthHist = data.depthHist end
    if data.rarityCounts then rarityCounts = data.rarityCounts end
    print("[Persistence] Data loaded.")
end

-- Hook processBlock to auto-save
local originalProcessBlock = processBlock
processBlock = function(part)
    originalProcessBlock(part)
    blocksSinceSave = blocksSinceSave + 1
    if blocksSinceSave >= SAVE_INTERVAL then
        blocksSinceSave = 0
        saveData()
    end
end

task.spawn(loadData)

getgenv().SaveData = saveData
getgenv().LoadData = loadData

-------------------------------------------------
-- MANUAL BLOCK LABELING
-------------------------------------------------
local labelingMode = false
local labelTarget = nil

getgenv().LabelBlock = function()
    labelingMode = true
    print("[Label] Click a block to label...")
    local conn
    conn = player:GetMouse().Button1Down:Connect(function()
        if not labelingMode then conn:Disconnect() return end
        labelTarget = player:GetMouse().Target
        if labelTarget and labelTarget:IsA("BasePart") then
            print("[Label] Selected:", labelTarget.Name)
            print("[Label] Use LabelAs('RarityName') to assign")
        else
            print("[Label] Not a valid part")
        end
        labelingMode = false
        conn:Disconnect()
    end)
end

getgenv().LabelAs = function(rarityName)
    if not labelTarget then
        warn("[Label] No block selected. Run LabelBlock() first.")
        return
    end
    local rarity = rarityByName[rarityName]
    if not rarity then
        warn("[Label] Unknown rarity:", rarityName)
        return
    end
    local gridPos = roundToGrid(labelTarget.Position)
    local key = posKey(gridPos)
    if spatialHash[key] then
        print("[Label] Block already recorded, updating...")
    end
    local blockData = {
        part = labelTarget,
        rarity = rarity.name,
        pos = gridPos,
        color = rarity.color,
        mesh = labelTarget:IsA("MeshPart") and labelTarget.MeshId or nil,
        manuallyLabeled = true
    }
    scannedBlocks[gridPos] = blockData
    spatialHash[key] = blockData
    rarityCounts[rarity.name] = (rarityCounts[rarity.name] or 0) + 1
    local yIndex = math.floor(gridPos.Y / GRID_SIZE)
    depthHist[rarity.name][yIndex] = (depthHist[rarity.name][yIndex] or 0) + 1
    table.insert(positionsByRarity[rarity.name], gridPos)

    if espEnabled[rarity.name] then
        local highlight = Instance.new("Highlight")
        highlight.Parent = labelTarget
        highlight.FillColor = rarity.color
        highlight.DepthMode = Enum.HighlightDepthMode.AlwaysOnTop

        local billboard = Instance.new("BillboardGui")
        billboard.Parent = labelTarget
        billboard.Size = UDim2.new(0, 120, 0, 40)
        billboard.StudsOffset = Vector3.new(0, 3, 0)
        billboard.AlwaysOnTop = true
        local label = Instance.new("TextLabel", billboard)
        label.Size = UDim2.fromScale(1, 1)
        label.BackgroundTransparency = 1
        label.Text = rarity.name:upper() .. " (MANUAL)"
        label.Font = Enum.Font.GothamBlack
        label.TextScaled = true
        label.TextColor3 = rarity.color
        label.TextStrokeTransparency = 0

        blockData.highlight = highlight
        blockData.billboard = billboard
        table.insert(espByRarity[rarity.name], {highlight = highlight, billboard = billboard})
    end

    print("[Label] Block labeled as", rarityName)
    labelTarget = nil
end

-------------------------------------------------
-- TRACER SYSTEM (with debug)
-------------------------------------------------
local function updateTracers()
    if not ENABLE_TRACERS or not DRAWING_SUPPORTED then
        for _, line in pairs(tracerLines) do
            line:Remove()
        end
        tracerLines = {}
        return
    end

    local screenCenter = Camera.ViewportSize / 2
    if screenCenter.X == 0 or screenCenter.Y == 0 then
        return
    end

    local newLines = {}
    local tracerCount = 0

    for key, data in pairs(scannedBlocks) do
        local rarity = data.rarity
        if tracerEnabled[rarity] and data.part and data.part.Parent then
            tracerCount = tracerCount + 1
            local blockPos = data.part.Position
            if not tracerLines[key] then
                local line = Drawing.new("Line")
                line.Thickness = 3
                line.Color = Color3.new(data.color.R, data.color.G, data.color.B) * 255
                line.Transparency = 1
                line.ZIndex = 10
                line.Visible = false
                tracerLines[key] = line
                print("[Tracer] Created for", key)
            end
            local toVec, onScreen = Camera:WorldToViewportPoint(blockPos)
            if onScreen then
                tracerLines[key].From = Vector2.new(screenCenter.X, screenCenter.Y)
                tracerLines[key].To = Vector2.new(toVec.X, toVec.Y)
                tracerLines[key].Visible = true
            else
                tracerLines[key].Visible = false
            end
            newLines[key] = tracerLines[key]
        end
    end

    if tracerCount > 0 then
        print("[Tracer] Drawing", tracerCount, "lines")
    end

    for key, line in pairs(tracerLines) do
        if not newLines[key] then
            line:Remove()
            tracerLines[key] = nil
        end
    end
end

tracerUpdateConn = RunService.RenderStepped:Connect(updateTracers)

-------------------------------------------------
-- TEST TRACER FUNCTION
-------------------------------------------------
local function createTestTracer()
    local char = player.Character
    if not char then return end
    local hrp = char:FindFirstChild("HumanoidRootPart")
    if not hrp then return end

    local testPart = Instance.new("Part")
    testPart.Size = Vector3.new(4,4,4)
    testPart.Position = hrp.Position + Vector3.new(0, 10, 20)
    testPart.Anchored = true
    testPart.CanCollide = false
    testPart.BrickColor = BrickColor.new("Bright red")
    testPart.Material = Enum.Material.Neon
    testPart.Parent = workspace

    local dummyRarity = rarities[1]
    local gridPos = roundToGrid(testPart.Position)
    local key = posKey(gridPos)
    if not spatialHash[key] then
        local blockData = {
            part = testPart,
            rarity = dummyRarity.name,
            pos = gridPos,
            color = dummyRarity.color,
            mesh = nil,
            isTest = true
        }
        scannedBlocks[gridPos] = blockData
        spatialHash[key] = blockData
        tracerEnabled[dummyRarity.name] = true
        print("[Test] Added test block at", gridPos)
    end

    task.delay(10, function()
        if testPart and testPart.Parent then
            testPart:Destroy()
            local key = posKey(gridPos)
            scannedBlocks[gridPos] = nil
            spatialHash[key] = nil
            print("[Test] Test block removed")
        end
    end)
end

-------------------------------------------------
-- MAIN LOOP
-------------------------------------------------
task.spawn(function()
    while true do
        task.wait(UPDATE_INTERVAL)
        updatePredictions()
        if ENABLE_FOCUS_MODE then
            updateFocusMode()
        end
    end
end)

-------------------------------------------------
-- UI CREATION (Küçültülmüş & Düzeltilmiş)
-------------------------------------------------
local function InitScannerUI()
    local gui = Instance.new("ScreenGui")
    gui.Name = "DarkwiredPredictor"
    gui.Parent = guiParent
    gui.ResetOnSpawn = false
    gui.ZIndexBehavior = Enum.ZIndexBehavior.Sibling

    -- Renk sabitleri
    local COL_ON_BG    = Color3.fromRGB(30, 160, 60)   -- Açık: koyu yeşil arka plan
    local COL_OFF_BG   = Color3.fromRGB(160, 30, 30)   -- Kapalı: koyu kırmızı arka plan
    local COL_ON_TEXT  = Color3.fromRGB(180, 255, 180)  -- Açık: açık yeşil yazı
    local COL_OFF_TEXT = Color3.fromRGB(255, 160, 160)  -- Kapalı: açık kırmızı yazı

    -- Toggle görünümünü uygulayan yardımcı
    local function applyToggle(btn, isOn, label)
        if isOn then
            btn.BackgroundColor3 = COL_ON_BG
            btn.TextColor3      = COL_ON_TEXT
            btn.Text            = "✔ " .. label
        else
            btn.BackgroundColor3 = COL_OFF_BG
            btn.TextColor3      = COL_OFF_TEXT
            btn.Text            = "✖ " .. label
        end
    end

    -- ── Ana çerçeve ──
    local mainFrame = Instance.new("Frame", gui)
    mainFrame.Size = UDim2.new(0, 320, 0, 600)
    mainFrame.Position = UDim2.new(0.03, 0, 0.15, 0)
    mainFrame.BackgroundColor3 = Color3.fromRGB(18, 18, 26)
    mainFrame.Active = true
    mainFrame.Draggable = true
    Instance.new("UICorner", mainFrame).CornerRadius = UDim.new(0, 12)

    -- Ekran dışına çıkmayı engelle
    mainFrame:GetPropertyChangedSignal("Position"):Connect(function()
        local vp = Camera.ViewportSize
        local abs = mainFrame.AbsolutePosition
        local sz  = mainFrame.AbsoluteSize
        local x = math.clamp(abs.X, 0, vp.X - sz.X)
        local y = math.clamp(abs.Y, 0, vp.Y - sz.Y)
        if abs.X ~= x or abs.Y ~= y then
            mainFrame.Position = UDim2.new(0, x, 0, y)
        end
    end)

    -- Kapat butonu
    local closeBtn = Instance.new("TextButton", mainFrame)
    closeBtn.Size = UDim2.new(0, 22, 0, 22)
    closeBtn.Position = UDim2.new(1, -26, 0, 4)
    closeBtn.BackgroundColor3 = Color3.fromRGB(220, 50, 50)
    closeBtn.Text = "✕"
    closeBtn.TextColor3 = Color3.new(1,1,1)
    closeBtn.Font = Enum.Font.GothamBold
    closeBtn.TextSize = 13
    closeBtn.BorderSizePixel = 0
    Instance.new("UICorner", closeBtn).CornerRadius = UDim.new(0, 6)
    closeBtn.MouseButton1Click:Connect(function() gui:Destroy() end)

    -- Başlık
    local title = Instance.new("TextLabel", mainFrame)
    title.Size = UDim2.new(1, -36, 0, 28)
    title.Position = UDim2.new(0, 8, 0, 4)
    title.BackgroundTransparency = 1
    title.Text = "⬡ DARKWIRED PREDICTOR"
    title.Font = Enum.Font.GothamBlack
    title.TextSize = 14
    title.TextColor3 = Color3.new(1,1,1)
    title.TextXAlignment = Enum.TextXAlignment.Left

    -- İstatistik kutusu
    local stats = Instance.new("TextLabel", mainFrame)
    stats.Name = "Stats"
    stats.Size = UDim2.new(0.94, 0, 0, 70)
    stats.Position = UDim2.new(0.03, 0, 0, 36)
    stats.BackgroundColor3 = Color3.fromRGB(25, 25, 35)
    stats.TextColor3 = Color3.new(1,1,1)
    stats.Font = Enum.Font.Gotham
    stats.TextSize = 10
    stats.TextXAlignment = Enum.TextXAlignment.Left
    stats.TextYAlignment = Enum.TextYAlignment.Top
    stats.Text = "Başlatılıyor..."
    stats.BorderSizePixel = 0
    Instance.new("UICorner", stats).CornerRadius = UDim.new(0, 8)

    -- Tooltip
    local tooltip = Instance.new("TextLabel", mainFrame)
    tooltip.Name = "Tooltip"
    tooltip.Size = UDim2.new(0.94, 0, 0, 20)
    tooltip.Position = UDim2.new(0.03, 0, 0, 111)
    tooltip.BackgroundColor3 = Color3.fromRGB(35, 35, 45)
    tooltip.TextColor3 = Color3.fromRGB(200,200,200)
    tooltip.Font = Enum.Font.Gotham
    tooltip.TextSize = 10
    tooltip.Text = "Butonların üzerine gel"
    tooltip.BorderSizePixel = 0
    Instance.new("UICorner", tooltip).CornerRadius = UDim.new(0, 6)

    -- =============================================
    -- ÖZELLİK TOGGLE BUTONLARI
    -- getfenv() yerine doğrudan upvalue kullanılıyor
    -- =============================================
    local featureFrame = Instance.new("Frame", mainFrame)
    featureFrame.Size = UDim2.new(0.94, 0, 0, 130)
    featureFrame.Position = UDim2.new(0.03, 0, 0, 136)
    featureFrame.BackgroundTransparency = 1

    local featureGrid = Instance.new("UIGridLayout", featureFrame)
    featureGrid.CellSize = UDim2.new(0.31, -2, 0, 26)
    featureGrid.CellPadding = UDim2.new(0.02, 0, 0, 4)

    -- Her özellik: getter + setter + label + açıklama
    local features = {
        {
            label = "Tahmin",
            desc  = "Nadir blokları tahmin et (neon işaretçi)",
            get   = function() return ENABLE_PREDICTION end,
            set   = function(v)
                ENABLE_PREDICTION = v
                if not v then
                    for _, m in pairs(predictionMarkers) do m:Destroy() end
                    predictionMarkers = {}
                end
            end,
        },
        {
            label = "Mesh Algıla",
            desc  = "MeshId ile blokları tanımla",
            get   = function() return ENABLE_MESH_DETECTION end,
            set   = function(v) ENABLE_MESH_DETECTION = v end,
        },
        {
            label = "Odak Modu",
            desc  = "Sadece yakındaki tahminleri göster",
            get   = function() return ENABLE_FOCUS_MODE end,
            set   = function(v) ENABLE_FOCUS_MODE = v end,
        },
        {
            label = "Seed Avı",
            desc  = "Dünya seed'ini hafızada tara",
            get   = function() return ENABLE_SEED_HUNT end,
            set   = function(v) ENABLE_SEED_HUNT = v end,
        },
        {
            label = "Desen",
            desc  = "Derinlik ve küme analizi",
            get   = function() return ENABLE_PATTERN end,
            set   = function(v) ENABLE_PATTERN = v end,
        },
        {
            label = "Gelişmiş",
            desc  = "Damar ve küme dolumu",
            get   = function() return ENABLE_ADVANCED end,
            set   = function(v) ENABLE_ADVANCED = v end,
        },
        {
            label = "Tracer",
            desc  = "Tracer çizgilerini aç/kapat",
            get   = function() return ENABLE_TRACERS end,
            set   = function(v) ENABLE_TRACERS = v end,
        },
    }

    for _, f in ipairs(features) do
        local btn = Instance.new("TextButton", featureFrame)
        btn.Font = Enum.Font.GothamBold
        btn.TextSize = 9
        btn.BorderSizePixel = 0
        Instance.new("UICorner", btn).CornerRadius = UDim.new(0, 6)

        -- İlk durum
        applyToggle(btn, f.get(), f.label)

        btn.MouseEnter:Connect(function() tooltip.Text = f.desc end)
        btn.MouseLeave:Connect(function() tooltip.Text = "Butonların üzerine gel" end)

        local fCapture = f
        btn.MouseButton1Click:Connect(function()
            local newVal = not fCapture.get()
            fCapture.set(newVal)
            applyToggle(btn, newVal, fCapture.label)
        end)
    end

    -- Aksiyon butonları (toggle değil, tek seferlik)
    local actionDefs = {
        {
            label = "Test Tracer",
            desc  = "Test bloğu oluştur (tracer kontrolü)",
            color = Color3.fromRGB(200, 200, 0),
            action = function(btn)
                createTestTracer()
                local orig = btn.Text; btn.Text = "Oluşturuldu!"
                task.wait(1); btn.Text = orig
            end,
        },
        {
            label = "Tahm.Temizle",
            desc  = "Tüm tahmin işaretçilerini sil",
            color = Color3.fromRGB(200, 60, 60),
            action = function(btn)
                for _, m in pairs(predictionMarkers) do m:Destroy() end
                predictionMarkers = {}
                local orig = btn.Text; btn.Text = "Temizlendi!"
                task.wait(0.6); btn.Text = orig
            end,
        },
    }

    for _, a in ipairs(actionDefs) do
        local btn = Instance.new("TextButton", featureFrame)
        btn.Text = a.label
        btn.Font = Enum.Font.GothamBold
        btn.TextSize = 9
        btn.BackgroundColor3 = a.color
        btn.TextColor3 = Color3.new(0,0,0)
        btn.BorderSizePixel = 0
        Instance.new("UICorner", btn).CornerRadius = UDim.new(0, 6)
        btn.MouseEnter:Connect(function() tooltip.Text = a.desc end)
        btn.MouseLeave:Connect(function() tooltip.Text = "Butonların üzerine gel" end)
        local aCapture = a
        btn.MouseButton1Click:Connect(function() aCapture.action(btn) end)
    end

    -- =============================================
    -- =============================================
    -- ÖZEL BLOK BÖLÜMÜ (ore tnt + Emerald)
    -- =============================================
    local oreSection = Instance.new("Frame", mainFrame)
    oreSection.Size = UDim2.new(0.94, 0, 0, 82)
    oreSection.Position = UDim2.new(0.03, 0, 0, 268)
    oreSection.BackgroundColor3 = Color3.fromRGB(50, 28, 8)
    oreSection.BorderSizePixel = 0
    Instance.new("UICorner", oreSection).CornerRadius = UDim.new(0, 8)
    local oreStroke = Instance.new("UIStroke", oreSection)
    oreStroke.Color = SPECIAL_ORE_OUTLINE
    oreStroke.Thickness = 1.5

    local oreTitle = Instance.new("TextLabel", oreSection)
    oreTitle.Size = UDim2.new(0.5, 0, 0.48, 0)
    oreTitle.Position = UDim2.new(0, 8, 0, 3)
    oreTitle.BackgroundTransparency = 1
    oreTitle.Text = "⬛ ore tnt  |  💎 Emerald"
    oreTitle.Font = Enum.Font.GothamBlack
    oreTitle.TextSize = 10
    oreTitle.TextColor3 = SPECIAL_ORE_OUTLINE
    oreTitle.TextXAlignment = Enum.TextXAlignment.Left

    local oreCountL = Instance.new("TextLabel", oreSection)
    oreCountL.Name = "OreCount"
    oreCountL.Size = UDim2.new(0.55, 0, 0, 16)
    oreCountL.Position = UDim2.new(0, 8, 0, 22)
    oreCountL.BackgroundTransparency = 1
    oreCountL.Text = "Bulunan: 0"
    oreCountL.Font = Enum.Font.Gotham
    oreCountL.TextSize = 9
    oreCountL.TextColor3 = Color3.fromRGB(180, 140, 80)
    oreCountL.TextXAlignment = Enum.TextXAlignment.Left

    -- Aç/Kapa toggle butonu
    local oreToggle = Instance.new("TextButton", oreSection)
    oreToggle.Size = UDim2.new(0, 72, 0, 20)
    oreToggle.Position = UDim2.new(1, -78, 0, 4)
    oreToggle.Font = Enum.Font.GothamBold
    oreToggle.TextSize = 10
    oreToggle.BorderSizePixel = 0
    Instance.new("UICorner", oreToggle).CornerRadius = UDim.new(0, 6)

    local function refreshOreToggle()
        if specialOreEnabled then
            oreToggle.BackgroundColor3 = Color3.fromRGB(30, 160, 60)
            oreToggle.TextColor3 = Color3.fromRGB(180, 255, 180)
            oreToggle.Text = "✔ AÇIK"
        else
            oreToggle.BackgroundColor3 = Color3.fromRGB(160, 30, 30)
            oreToggle.TextColor3 = Color3.fromRGB(255, 160, 160)
            oreToggle.Text = "✖ KAPALI"
        end
    end
    refreshOreToggle()

    oreToggle.MouseButton1Click:Connect(function()
        specialOreEnabled = not specialOreEnabled
        refreshOreToggle()
        if specialOreEnabled then
            for _, entry in ipairs(specialOreList) do
                local part = entry.part
                if part and part.Parent and not specialOreParts[part] then
                    local oreName = SPECIAL_ORE_IDS[part.MeshId] or "?"
                    local hl, bb = createSpecialOreESP(part, oreName)
                    specialOreParts[part] = {hl = hl, bb = bb}
                end
            end
        else
            removeAllSpecialOreESP()
        end
    end)

    -- Alt buton satırı: [⚡ Işınlan] [🔍 Tara] [🗑 Temizle]
    local oreBtnY = 44
    local oreBtnH = 22

    -- ⚡ Işınlan: en yakın ore tnt VEYA Emerald'a ışınlan
    local oreTpBtn = Instance.new("TextButton", oreSection)
    oreTpBtn.Size = UDim2.new(0, 82, 0, oreBtnH)
    oreTpBtn.Position = UDim2.new(0, 6, 0, oreBtnY)
    oreTpBtn.Text = "⚡ Işınlan"
    oreTpBtn.Font = Enum.Font.GothamBold
    oreTpBtn.TextSize = 10
    oreTpBtn.BackgroundColor3 = Color3.fromRGB(60, 40, 120)
    oreTpBtn.TextColor3 = Color3.fromRGB(200, 180, 255)
    oreTpBtn.BorderSizePixel = 0
    Instance.new("UICorner", oreTpBtn).CornerRadius = UDim.new(0, 5)

    oreTpBtn.MouseButton1Click:Connect(function()
        local hrp = player.Character and player.Character:FindFirstChild("HumanoidRootPart")
        if not hrp then return end
        -- En yakın özel bloğu bul
        local bestPart, bestDist = nil, math.huge
        for _, entry in ipairs(specialOreList) do
            local part = entry.part
            if part and part.Parent then
                local d = (part.Position - hrp.Position).Magnitude
                if d < bestDist then bestDist = d; bestPart = part end
            end
        end
        if bestPart then
            teleportTo(bestPart.Position)
            oreTpBtn.Text = "✓ Ulaşıldı"
            oreTpBtn.BackgroundColor3 = Color3.fromRGB(30, 140, 50)
            task.wait(1.2)
            oreTpBtn.Text = "⚡ Işınlan"
            oreTpBtn.BackgroundColor3 = Color3.fromRGB(60, 40, 120)
        else
            oreTpBtn.Text = "✗ Bulunamadı"
            oreTpBtn.BackgroundColor3 = Color3.fromRGB(140, 30, 30)
            task.wait(1.2)
            oreTpBtn.Text = "⚡ Işınlan"
            oreTpBtn.BackgroundColor3 = Color3.fromRGB(60, 40, 120)
        end
    end)

    -- 🔍 Tekrar Tara: specialOreList'i temizleyip workspace'i yeniden tara
    local oreScanBtn = Instance.new("TextButton", oreSection)
    oreScanBtn.Size = UDim2.new(0, 82, 0, oreBtnH)
    oreScanBtn.Position = UDim2.new(0, 94, 0, oreBtnY)
    oreScanBtn.Text = "🔍 Tara"
    oreScanBtn.Font = Enum.Font.GothamBold
    oreScanBtn.TextSize = 10
    oreScanBtn.BackgroundColor3 = Color3.fromRGB(20, 60, 120)
    oreScanBtn.TextColor3 = Color3.fromRGB(150, 200, 255)
    oreScanBtn.BorderSizePixel = 0
    Instance.new("UICorner", oreScanBtn).CornerRadius = UDim.new(0, 5)

    oreScanBtn.MouseButton1Click:Connect(function()
        oreScanBtn.Text = "⏳ Taranıyor"
        task.spawn(function()
            -- Mevcut scanned listesini sıfırla ama ESP koru
            specialOreList = {}
            for _, inst in ipairs(workspace:GetDescendants()) do
                if inst:IsA("MeshPart") and SPECIAL_ORE_IDS[inst.MeshId] then
                    table.insert(specialOreList, {part = inst, pos = inst.Position})
                    if specialOreEnabled and not specialOreParts[inst] then
                        local oreName = SPECIAL_ORE_IDS[inst.MeshId] or "?"
                        local hl, bb = createSpecialOreESP(inst, oreName)
                        specialOreParts[inst] = {hl = hl, bb = bb}
                    end
                end
            end
            task.wait(0.5)
            oreScanBtn.Text = "✓ " .. #specialOreList .. " bulundu"
            task.wait(1.5)
            oreScanBtn.Text = "🔍 Tara"
        end)
    end)

    -- 🗑 Temizle: bulunan özel blok listesini ve ESP'leri sil
    local oreClearBtn = Instance.new("TextButton", oreSection)
    oreClearBtn.Size = UDim2.new(0, 82, 0, oreBtnH)
    oreClearBtn.Position = UDim2.new(0, 182, 0, oreBtnY)
    oreClearBtn.Text = "🗑 Temizle"
    oreClearBtn.Font = Enum.Font.GothamBold
    oreClearBtn.TextSize = 10
    oreClearBtn.BackgroundColor3 = Color3.fromRGB(100, 30, 10)
    oreClearBtn.TextColor3 = Color3.fromRGB(255, 160, 130)
    oreClearBtn.BorderSizePixel = 0
    Instance.new("UICorner", oreClearBtn).CornerRadius = UDim.new(0, 5)

    oreClearBtn.MouseButton1Click:Connect(function()
        removeAllSpecialOreESP()
        specialOreList = {}
        oreClearBtn.Text = "✓ Temizlendi"
        oreClearBtn.BackgroundColor3 = Color3.fromRGB(30, 140, 50)
        task.wait(1.2)
        oreClearBtn.Text = "🗑 Temizle"
        oreClearBtn.BackgroundColor3 = Color3.fromRGB(100, 30, 10)
    end)

    -- =============================================
    -- NADİRLİK BUTONLARI + TRACER + IŞINLAN
    -- Her satır: [✔ Adı] [●] [⚡]
    -- =============================================
    local rarityFrame = Instance.new("Frame", mainFrame)
    rarityFrame.Size = UDim2.new(0.94, 0, 0, 261)
    rarityFrame.Position = UDim2.new(0.03, 0, 0, 326)
    rarityFrame.BackgroundTransparency = 1

    local rarityList = Instance.new("UIListLayout", rarityFrame)
    rarityList.FillDirection = Enum.FillDirection.Vertical
    rarityList.Padding = UDim.new(0, 3)
    rarityList.SortOrder = Enum.SortOrder.LayoutOrder

    local function safeTextColor(bgColor)
        local brightness = bgColor.R * 0.299 + bgColor.G * 0.587 + bgColor.B * 0.114
        return brightness > 0.6 and Color3.new(0,0,0) or Color3.new(1,1,1)
    end

    for _, r in ipairs(rarities) do
        local container = Instance.new("Frame", rarityFrame)
        container.Size = UDim2.new(1, 0, 0, 26)
        container.BackgroundTransparency = 1

        -- ESP buton: sol %58
        local espBtn = Instance.new("TextButton", container)
        espBtn.Size = UDim2.new(0.58, -2, 1, 0)
        espBtn.Position = UDim2.new(0, 0, 0, 0)
        espBtn.Font = Enum.Font.GothamBold
        espBtn.TextSize = 9
        espBtn.BorderSizePixel = 0
        Instance.new("UICorner", espBtn).CornerRadius = UDim.new(0, 6)

        -- Tracer buton: orta %20 (daire)
        local tracerBtn = Instance.new("TextButton", container)
        tracerBtn.Size = UDim2.new(0.20, -2, 0.9, 0)
        tracerBtn.Position = UDim2.new(0.59, 2, 0.05, 0)
        tracerBtn.Font = Enum.Font.GothamBold
        tracerBtn.TextSize = 12
        tracerBtn.BorderSizePixel = 0
        Instance.new("UICorner", tracerBtn).CornerRadius = UDim.new(1, 0)

        -- Işınlan butonu: sağ %20
        local tpBtn = Instance.new("TextButton", container)
        tpBtn.Size = UDim2.new(0.20, -2, 0.9, 0)
        tpBtn.Position = UDim2.new(0.80, 2, 0.05, 0)
        tpBtn.Text = "⚡"
        tpBtn.Font = Enum.Font.GothamBold
        tpBtn.TextSize = 11
        tpBtn.BackgroundColor3 = Color3.fromRGB(40, 40, 60)
        tpBtn.TextColor3 = Color3.fromRGB(200, 200, 255)
        tpBtn.BorderSizePixel = 0
        Instance.new("UICorner", tpBtn).CornerRadius = UDim.new(0, 5)

        local function refreshEspBtn()
            if espEnabled[r.name] then
                espBtn.BackgroundColor3 = r.color
                espBtn.TextColor3 = safeTextColor(r.color)
                espBtn.Text = "✔ " .. r.name
            else
                espBtn.BackgroundColor3 = Color3.fromRGB(160, 30, 30)
                espBtn.TextColor3 = Color3.fromRGB(255, 160, 160)
                espBtn.Text = "✖ " .. r.name
            end
        end

        local function refreshTracerBtn()
            if tracerEnabled[r.name] then
                tracerBtn.BackgroundColor3 = r.color
                tracerBtn.TextColor3 = safeTextColor(r.color)
                tracerBtn.Text = "●"
            else
                tracerBtn.BackgroundColor3 = Color3.fromRGB(45, 45, 55)
                tracerBtn.TextColor3 = Color3.fromRGB(120, 120, 140)
                tracerBtn.Text = "○"
            end
        end

        refreshEspBtn()
        refreshTracerBtn()

        espBtn.MouseEnter:Connect(function() tooltip.Text = r.name .. " ESP aç/kapat" end)
        tracerBtn.MouseEnter:Connect(function() tooltip.Text = r.name .. " Tracer aç/kapat" end)
        tpBtn.MouseEnter:Connect(function() tooltip.Text = r.name .. " → en yakın bloğa ışınlan" end)
        espBtn.MouseLeave:Connect(function() tooltip.Text = "Butonların üzerine gel" end)
        tracerBtn.MouseLeave:Connect(function() tooltip.Text = "Butonların üzerine gel" end)
        tpBtn.MouseLeave:Connect(function() tooltip.Text = "Butonların üzerine gel" end)

        local rCapture = r
        -- ESP tıklama
        espBtn.MouseButton1Click:Connect(function()
            espEnabled[rCapture.name] = not espEnabled[rCapture.name]
            refreshEspBtn()
            if espEnabled[rCapture.name] then
                for _, data in pairs(scannedBlocks) do
                    if data.rarity == rCapture.name and data.part and data.part.Parent and not data.highlight then
                        local highlight = Instance.new("Highlight")
                        highlight.Parent = data.part
                        highlight.FillColor = rCapture.color
                        highlight.DepthMode = Enum.HighlightDepthMode.AlwaysOnTop
                        local billboard = Instance.new("BillboardGui")
                        billboard.Parent = data.part
                        billboard.Size = UDim2.new(0, 120, 0, 40)
                        billboard.StudsOffset = Vector3.new(0, 3, 0)
                        billboard.AlwaysOnTop = true
                        local label = Instance.new("TextLabel", billboard)
                        label.Size = UDim2.fromScale(1, 1)
                        label.BackgroundTransparency = 1
                        label.Text = rCapture.name:upper()
                        label.Font = Enum.Font.GothamBlack
                        label.TextScaled = true
                        label.TextColor3 = rCapture.color
                        label.TextStrokeTransparency = 0
                        data.highlight = highlight
                        data.billboard = billboard
                        table.insert(espByRarity[rCapture.name], {highlight=highlight, billboard=billboard})
                    end
                end
            else
                for _, esp in ipairs(espByRarity[rCapture.name]) do
                    if esp.highlight then esp.highlight:Destroy() end
                    if esp.billboard then esp.billboard:Destroy() end
                end
                espByRarity[rCapture.name] = {}
                for _, data in pairs(scannedBlocks) do
                    if data.rarity == rCapture.name then
                        data.highlight = nil
                        data.billboard = nil
                    end
                end
            end
        end)

        -- Tracer tıklama
        tracerBtn.MouseButton1Click:Connect(function()
            tracerEnabled[rCapture.name] = not tracerEnabled[rCapture.name]
            refreshTracerBtn()
        end)

        -- ⚡ Işınlan: en yakın nadirlik bloğuna ışınlan
        tpBtn.MouseButton1Click:Connect(function()
            local hrp = player.Character and player.Character:FindFirstChild("HumanoidRootPart")
            if not hrp then return end
            local nearest = findNearestRarityBlock(rCapture.name, hrp.Position)
            if nearest then
                teleportTo(nearest.Position)
                tpBtn.Text = "✓"
                tpBtn.BackgroundColor3 = Color3.fromRGB(30, 140, 50)
                task.wait(1)
                tpBtn.Text = "⚡"
                tpBtn.BackgroundColor3 = Color3.fromRGB(40, 40, 60)
            else
                tpBtn.Text = "✗"
                tpBtn.BackgroundColor3 = Color3.fromRGB(140, 30, 30)
                task.wait(1)
                tpBtn.Text = "⚡"
                tpBtn.BackgroundColor3 = Color3.fromRGB(40, 40, 60)
            end
        end)
    end

    -- İstatistik güncelleme
    task.spawn(function()
        while gui and gui.Parent do
            local txt = ""
            for i, r in ipairs(rarities) do
                txt = txt .. r.name .. ": " .. (rarityCounts[r.name] or 0) .. "  "
                if i % 3 == 0 then txt = txt .. "\n" end
            end
            txt = txt .. "\nBloklar: " .. #scannedBlocks
            txt = txt .. "  |  Tahminler: " .. #predictionMarkers
            stats.Text = txt
            -- Özel blok sayısını güncelle
            local oreCount = 0
            for _ in pairs(specialOreParts) do oreCount = oreCount + 1 end
            oreCountL.Text = "Bulunan: " .. oreCount
            task.wait(1)
        end
    end)
end

task.wait(1)
InitScannerUI()

-------------------------------------------------
-- KEYBINDS
-------------------------------------------------
UserInputService.InputBegan:Connect(function(input, gameProcessed)
    if gameProcessed then return end
    if input.KeyCode == Enum.KeyCode.F9 then
        ENABLE_PREDICTION = not ENABLE_PREDICTION
        if not ENABLE_PREDICTION then
            for _, m in pairs(predictionMarkers) do m:Destroy() end
            predictionMarkers = {}
        end
        print("Tahmin:", ENABLE_PREDICTION and "AÇIK" or "KAPALI")
    elseif input.KeyCode == Enum.KeyCode.F8 then
        ENABLE_FOCUS_MODE = not ENABLE_FOCUS_MODE
        print("Odak Modu:", ENABLE_FOCUS_MODE and "AÇIK" or "KAPALI")
    elseif input.KeyCode == Enum.KeyCode.F7 then
        updatePredictions()
        print("Tahmin güncellendi")
    elseif input.KeyCode == Enum.KeyCode.F6 then
        for _, m in pairs(predictionMarkers) do m:Destroy() end
        predictionMarkers = {}
        scannedBlocks = {}
        scannedParts = {}
        spatialHash = {}
        for _, r in ipairs(rarities) do
            rarityCounts[r.name] = 0
            positionsByRarity[r.name] = {}
            depthHist[r.name] = {}
        end
        print("Tüm veriler temizlendi")
    elseif input.KeyCode == Enum.KeyCode.F5 then
        -- F5 = Özel blokları aç/kapat
        specialOreEnabled = not specialOreEnabled
        if specialOreEnabled then
            for _, entry in ipairs(specialOreList) do
                local part = entry.part
                if part and part.Parent and not specialOreParts[part] then
                    local oreName = SPECIAL_ORE_IDS[part.MeshId] or "?"
                    local hl, bb = createSpecialOreESP(part, oreName)
                    specialOreParts[part] = {hl = hl, bb = bb}
                end
            end
        else
            removeAllSpecialOreESP()
        end
        print("Özel Bloklar:", specialOreEnabled and "AÇIK" or "KAPALI")
    end
end)

print("[Darkwired Predictor] Yüklendi. F9=Tahmin  F8=Odak  F7=Güncelle  F6=Temizle  F5=ÖzelBlok")
if not DRAWING_SUPPORTED then
    print("[Darkwired] Not: Drawing kütüphanesi desteklenmiyor – tracer görünmeyecek.")
else
    print("[Darkwired] Drawing kütüphanesi destekleniyor – tracer çalışmalı.")
end
