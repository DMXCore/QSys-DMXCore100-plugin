local masterDimmer = -1
local fadeDuration = -1
local loopCount = -1

local SendFadeDuration = false

local LogReceived = false
local LogPing = false

local SendUpdates = false
local Connected = false
local blinkTimer = 0
local updateTimer = 0
local lastReceived = 0
local currentPreset = ""
local currentCue = ""
IP = ""
port = 8000
rxPort = 9000

local function lpak(_, ...) return string.pack(...) end

local oLvpk = {pack = lpak, unpack = string.unpack}
local mtab = {0, 3, 2, 1}

-- ++++++++++++++++++++++++++++++++++++++++++++++++++++
-- osc private functions
local endpad = string.char(0, 0, 0, 0)
function oscString(Str)
    local newS = Str .. string.char(0x0)
    local mod = string.len(newS) % 4
    return (newS .. string.sub(endpad, 1, mtab[mod + 1]))
end

function oscType(Str) return (oscString(',' .. Str)) end

function oscSymbol(Str)
    local s1, _ = string.find(Str, " ")
    return (oscString(string.sub(Str, 1, s1)))
end

function align4(n) return (math.floor((n - 1) / 4) + 1) * 4 end

function padBin(binD)
    local nwD = binD
    for i = 1, align4(#binD) - #binD do nwD = nwD .. string.char(0) end
    return nwD
end
-- +++++++++++++++++++++++++++++++++++++++++++++++++++
-- Creates an OSC packet
-- currently accepts the following types:
-- s  string
-- S  alt string
-- c  a char (32 bit int)
-- i  int (32-bit)
-- m  MIDI data, four bytes: channel, status, d1, d2
-- t  TIME data, two 32 ints: seconds, fraction of seconds
-- f  float (32-bit)
-- b  BLOB data, binary bytes
-- h  signed int (64-bit)
-- d  double float (64-bit)
--        The following have NO data block (but are DEcoded to a string: 'NIL', 'TRUE', etc...
-- N  NIL
-- T  TRUE
-- F  FALSE
-- I  Infinitum
-- [  Array begin
-- ]  Array end
function oscPacket(addrS, typeS, msgTab)
    local strl, types -- , tBlb

    if typeS == nil then
        strl = oscString(addrS) .. oscType('') -- no type & no data...EMPTY type block included in msg (comma and three zeros)
    else
        strl = oscString(addrS) .. oscType(typeS)

        if msgTab ~= nil then -- add data if type has arguments...some do not
            for argC = 1, #msgTab do
                types = string.sub(typeS, argC, argC)
                if types == 's' or types == 'S' then
                    strl = strl .. oscString(msgTab[argC])
                elseif types == 'f' then
                    strl = strl .. oLvpk.pack('string', '>f', msgTab[argC])
                elseif types == 'i' then
                    strl = strl .. oLvpk.pack('string', '>i4', msgTab[argC])
                elseif types == 'b' then
                    local tBlb = padBin(msgTab[argC])
                    strl = strl .. oLvpk.pack('string', '>i4', #msgTab[argC]) ..
                               tBlb
                elseif types == 'h' then
                    strl = strl .. oLvpk.pack('string', '>i8', msgTab[argC])
                elseif types == 'd' then
                    strl = strl .. oLvpk.pack('string', '>d', msgTab[argC])
                elseif types == 'c' then
                    strl = strl ..
                               oLvpk.pack('string', '>I', tostring(
                                              utf8.codepoint(msgTab[argC])))
                elseif types == 'm' then
                    strl = strl .. oLvpk.pack('string', 'c4', msgTab[argC])
                elseif types == 't' then
                    strl = strl .. oLvpk.pack('string', 'c8', msgTab[argC])
                elseif types == 'N' or types == 'T' or types == 'F' or types ==
                    'I' or types == string.char(91) or types == string.char(93) then
                    -- no data
                else
                    return (nil) -- unknown type
                end
            end
        end
    end
    return (strl)
end
-- unpack UDP OSC msg packet into:
--	oscAddr = oA
--	oscType = oT
--	oscData = oD
function oscUnpack(udpM)
    local oA, oT, oD

    oA = udpM:match("^[%p%w]+%z+")
    oT = udpM:match(',[%a%[+%]+]+')
    if oA ~= nil then
        local aBlk = #oA
        oA = oA:gsub('%z', '')
        if oT ~= nil then
            local dataBlk = aBlk + (math.floor((#oT) / 4) + 1) * 4
            oD = string.sub(udpM, dataBlk + 1)
            oT = oT:match('[^,]+')
        end
    end
    return oA, oT, oD
end
-- unpack OSC data block
-- currently unpacks the following types:
-- s  string
-- S  alt string
-- c  a char (but 32 bit int)
-- i  int (32-bit)
-- m  MIDI data, four bytes: channel, status, d1, d2
-- t  TIME data, two 32 ints: seconds, fraction of seconds
-- f  float (32-bit)
-- b  BLOB data, binary bytes
-- h  signed int (64-bit)
-- d  double float (64-bit)
--        These have no data block; a string ID is inserted in unpack table:
-- N  'NIL'
-- T  'TRUE'
-- F  'FALSE'
-- I  'INFINITUM'
-- [  'ARRAY_BEGIN'
-- ]  'ARRAY_END'
function oscDataUnpack(oT, oD)
    local tc, iv, nx, zloc
    local dTbl = {}
    if oT ~= nil then
        for i = 1, #oT do
            tc = oT:sub(i, i)
            if tc == 'f' then
                iv, nx = oLvpk.unpack(">f", oD)
                oD = string.sub(oD, 5)
                table.insert(dTbl, tonumber(iv))
            elseif tc == 's' or tc == 'S' then
                zloc, nx = string.find(oD, '\0')
                local tmpS = string.sub(oD, 1, zloc - 1)
                iv = string.format("%s", tmpS)
                nx = zloc + mtab[zloc % 4 + 1]
                oD = string.sub(oD, nx + 1)
                table.insert(dTbl, tostring(iv))
            elseif tc == 'b' then
                iv, nx = oLvpk.unpack(">i", oD)
                local blb = string.sub(oD, 1, iv + nx)
                oD = string.sub(oD, align4(iv - 1) + nx)
                table.insert(dTbl, blb)
            elseif tc == 'i' or tc == 'r' then
                iv, nx = oLvpk.unpack(">i", oD)
                oD = string.sub(oD, 5)
                table.insert(dTbl, tonumber(iv))
            elseif tc == 'c' then
                iv, nx = oLvpk.unpack(">i", oD)
                oD = string.sub(oD, 5)
                table.insert(dTbl, utf8.char(iv))
            elseif tc == 'm' then
                iv, nx = oLvpk.unpack("c4", oD)
                oD = string.sub(oD, 5)
                table.insert(dTbl, iv)
            elseif tc == 't' then
                iv, nx = oLvpk.unpack("c8", oD)
                oD = string.sub(oD, 9)
                table.insert(dTbl, iv)
            elseif tc == 'h' then
                iv, nx = oLvpk.unpack(">i8", oD)
                oD = string.sub(oD, 9)
                table.insert(dTbl, tonumber(iv))
            elseif tc == 'd' then
                iv, nx = oLvpk.unpack(">d", oD)
                oD = string.sub(oD, 9)
                table.insert(dTbl, tonumber(iv))
            elseif tc == 'I' then
                table.insert(dTbl, 'IMPULSE')
            elseif tc == 'T' then
                table.insert(dTbl, 'TRUE')
            elseif tc == 'F' then
                table.insert(dTbl, 'FALSE')
            elseif tc == 'N' then
                table.insert(dTbl, 'NIL')
            elseif tc == string.char(91) then
                table.insert(dTbl, 'ARRAY_BEGIN')
            elseif tc == string.char(93) then
                table.insert(dTbl, 'ARRAY_END')
            end
        end
    end
    return dTbl
end

function SetActive(ledControl, codeControl, currentValue)
    local ledValue

    if currentValue == codeControl.String and codeControl.String ~= "" then
        ledValue = 1
    else
        ledValue = 0
    end

    ledControl.Position = ledValue
end

function HandleData(socket, packet)
    local oscADDR, oscTYPE, oscDATA = oscUnpack(packet.Data)
    local dataT = oscDataUnpack(oscTYPE, oscDATA)

    lastReceived = updateTimer

    if dataT[1] ~= nil then
        if oscADDR == "/dmxcore/dimmer/master" then
            print("Master dimmer = " .. dataT[1])
            Controls.MasterDimmer.Position = dataT[1]
        elseif oscADDR == "/dmxcore/status/preset" then
            print("Preset = " .. dataT[1])
            currentPreset = dataT[1]
            if currentPreset ~= "" then currentCue = "" end
        elseif oscADDR == "/dmxcore/status/cue" then
            print("Cue = " .. dataT[1])
            currentCue = dataT[1]
            if currentCue ~= "" then currentPreset = "" end
        elseif oscADDR == "/dmxcore/status/text" then
            print("Status = " .. dataT[1])
            Controls.StatusDisplay.String = dataT[1]
        end
    end

    SetActive(Controls.PresetActive[1], Controls.PresetCode[1], currentPreset)
    SetActive(Controls.PresetActive[2], Controls.PresetCode[2], currentPreset)
    SetActive(Controls.PresetActive[3], Controls.PresetCode[3], currentPreset)
    SetActive(Controls.PresetActive[4], Controls.PresetCode[4], currentPreset)
    SetActive(Controls.PresetActive[5], Controls.PresetCode[5], currentPreset)
    SetActive(Controls.PresetActive[6], Controls.PresetCode[6], currentPreset)

    SetActive(Controls.CueActive[1], Controls.CueCode[1], currentCue)
    SetActive(Controls.CueActive[2], Controls.CueCode[2], currentCue)
    SetActive(Controls.CueActive[3], Controls.CueCode[3], currentCue)
    SetActive(Controls.CueActive[4], Controls.CueCode[4], currentCue)
    SetActive(Controls.CueActive[5], Controls.CueCode[5], currentCue)
    SetActive(Controls.CueActive[6], Controls.CueCode[6], currentCue)

    if LogReceived then
        -- output to console
        print(oscADDR, oscTYPE)
        if dataT ~= nil then
            for i, v in ipairs(dataT) do print(i .. ')', v) end
        end
    end
end

local tokenize = function(input, sep)
    local t = {}
    for str in string.gmatch(input, "([^" .. sep .. "]+)") do
        table.insert(t, str)
    end
    return t
end

local getIpAddress = function()
    local ipAddress = Controls.DMXCoreIP.String
    print("IP address is set to: ", ipAddress)
    if ipAddress == "" then
        print("IP address can not be empty, setting to default: ",
              defaultIpAddress)
        ipAddress = defaultIpAddress
        Controls.DMXCoreIP.String = defaultIpAddress
    end
    local ipTable = tokenize(ipAddress, ".")
    if #ipTable ~= 4 then
        ipAddress = "INVALID"
    else
        for _, v in ipairs(ipTable) do
            if tonumber(v) == nil or tonumber(v) < 0 or tonumber(v) > 255 then
                ipAddress = "INVALID"
                break
            end
        end
    end
    if ipAddress == "INVALID" then
        print("Invalid IP address, setting to default: ", defaultIpAddress)
        ipAddress = defaultIpAddress
        Controls.DMXCoreIP.String = defaultIpAddress
    end
    return ipAddress
end

local getPort = function()
    local port = Controls.DMXCorePort.String
    print("Port is set to: ", port)
    if string.match(port, "%D") then
        print("Invalid port, setting to default: ", defaultPort)
        port = defaultPort
        Controls.DMXCorePort.String = defaultPort
    end
    port = tonumber(port)
    if port == nil then
        print("Port can not be empty, setting to default: ", defaultPort)
        port = defaultPort
        Controls.DMXCorePort.String = defaultPort
    end
    return port
end

Controls.StatusDisplay.String = ""
fadeDuration = Controls.FadeDuration.Value
loopCount = Controls.LoopCount.Value
Controls.FadeDurationDisplay.String = string.format("%.1f", fadeDuration) .. " s"
if loopCount == 0 then
    Controls.LoopCountDisplay.String = "Infinite"
else
    Controls.LoopCountDisplay.String = string.format("%.0f", loopCount)
end

OscSocket = UdpSocket.New()

-- Open socket
OscSocket:Open(nil, rxPort)

-- When data is received, handle it. Here I'm translating using the helper function above, then if the address matches a particular one, sending the values into a function built to handle that.
OscSocket.Data = HandleData

IP = getIpAddress()
port = getPort()

function timer1_func()
    blinkTimer = blinkTimer + 1

    Controls.ScriptActive.Position = blinkTimer % 2

    if blinkTimer == 5 then
        -- 5 seconds
        if LogPing then print("Sending Ping Message") end
        OscSocket:Send(IP, port, oscPacket('/ping', nil, {}))
        blinkTimer = 0
    end
end

OscSocket:Send(IP, port, oscPacket('/dmxcore/status', nil, {}))

-- Add the timer
Timer1 = Timer.New()
Timer1.EventHandler = timer1_func

-- and start it with a delay of 1000 ms
Timer1:Start(1)

-- Wire up event handlers
Controls.DMXCoreIP.EventHandler = function() ipAddress = getIpAddress() end
Controls.DMXCorePort.EventHandler = function() port = getPort() end
Controls.Blink.EventHandler = function(control)
    OscSocket:Send(IP, port, oscPacket('/dmxcore/blink', 'i', {control.Value}))
end
Controls.MasterDimmer.EventHandler = function(control)
    OscSocket:Send(IP, port,
                   oscPacket('/dmxcore/dimmer/master', 'f', {control.Position}))
end
Controls.GoToPreset[1].EventHandler = function()
    OscSocket:Send(IP, port,
                   oscPacket(
                       '/dmxcore/preset/' .. Controls.PresetCode[1].String, 'i',
                       {math.floor(fadeDuration * 1000)}))
end
Controls.GoToPreset[2].EventHandler = function()
    OscSocket:Send(IP, port,
                   oscPacket(
                       '/dmxcore/preset/' .. Controls.PresetCode[2].String, 'i',
                       {math.floor(fadeDuration * 1000)}))
end
Controls.GoToPreset[3].EventHandler = function()
    OscSocket:Send(IP, port,
                   oscPacket(
                       '/dmxcore/preset/' .. Controls.PresetCode[3].String, 'i',
                       {math.floor(fadeDuration * 1000)}))
end
Controls.GoToPreset[4].EventHandler = function()
    OscSocket:Send(IP, port,
                   oscPacket(
                       '/dmxcore/preset/' .. Controls.PresetCode[4].String, 'i',
                       {math.floor(fadeDuration * 1000)}))
end
Controls.GoToPreset[5].EventHandler = function()
    OscSocket:Send(IP, port,
                   oscPacket(
                       '/dmxcore/preset/' .. Controls.PresetCode[5].String, 'i',
                       {math.floor(fadeDuration * 1000)}))
end
Controls.GoToPreset[6].EventHandler = function()
    OscSocket:Send(IP, port,
                   oscPacket(
                       '/dmxcore/preset/' .. Controls.PresetCode[6].String, 'i',
                       {math.floor(fadeDuration * 1000)}))
end

Controls.PlayCue[1].EventHandler = function()
    OscSocket:Send(IP, port, oscPacket(
                       '/dmxcore/cue/' .. Controls.CueCode[1].String, 'i',
                       {loopCount}))
end
Controls.PlayCue[2].EventHandler = function()
    OscSocket:Send(IP, port, oscPacket(
                       '/dmxcore/cue/' .. Controls.CueCode[2].String, 'i',
                       {loopCount}))
end
Controls.PlayCue[3].EventHandler = function()
    OscSocket:Send(IP, port, oscPacket(
                       '/dmxcore/cue/' .. Controls.CueCode[3].String, 'i',
                       {loopCount}))
end
Controls.PlayCue[4].EventHandler = function()
    OscSocket:Send(IP, port, oscPacket(
                       '/dmxcore/cue/' .. Controls.CueCode[4].String, 'i',
                       {loopCount}))
end
Controls.PlayCue[5].EventHandler = function()
    OscSocket:Send(IP, port, oscPacket(
                       '/dmxcore/cue/' .. Controls.CueCode[5].String, 'i',
                       {loopCount}))
end
Controls.PlayCue[6].EventHandler = function()
    OscSocket:Send(IP, port, oscPacket(
                       '/dmxcore/cue/' .. Controls.CueCode[6].String, 'i',
                       {loopCount}))
end

Controls.StopCue.EventHandler = function()
    OscSocket:Send(IP, port, oscPacket('/dmxcore/cuecontrol/stop', nil, {}))
end

Controls.FadeDuration.EventHandler = function(control)
    fadeDuration = control.Value
    Controls.FadeDurationDisplay.String = string.format("%.1f", fadeDuration) .. " s"
end

Controls.LoopCount.EventHandler = function(control)
    loopCount = control.Value
    if loopCount == 0 then
        Controls.LoopCountDisplay.String = "Infinite"
    else
        Controls.LoopCountDisplay.String = string.format("%.0f", loopCount)
    end
end

Controls.FadeToBlack.EventHandler = function()
    OscSocket:Send(IP, port, oscPacket('/dmxcore/dimmer/master/fadeto', 'fi', { 0, math.floor(fadeDuration * 1000) } ))
end
Controls.FadeTo100.EventHandler = function()
    OscSocket:Send(IP, port, oscPacket('/dmxcore/dimmer/master/fadeto', 'fi', { 1, math.floor(fadeDuration * 1000) } ))
end
