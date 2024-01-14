local errors = require("teal.errors")
local type Error = errors.Error

--------------------------------------------------------------------------------
-- Lexer
--------------------------------------------------------------------------------

local record lexer
   enum TokenKind
      "hashbang"
      "keyword"
      "op"
      "string"
      "[" "]" "(" ")" "{" "}" "," ":" "#" "." ";" "?"
      "::"
      "..."
      "identifier"
      "number"
      "integer"
      "$ERR unfinished_comment$"
      "$ERR invalid_string$"
      "$ERR invalid_number$"
      "$ERR invalid$"
      "$EOF$"
   end

   record Token
      x: integer
      y: integer
      tk: string
      kind: TokenKind
   end
end

local type Token = lexer.Token
local type TokenKind = lexer.TokenKind

local enum LexState
   "start"
   "any"
   "identifier"
   "got -"
   "got --"
   "got ."
   "got .."
   "got ="
   "got ~"
   "got ["
   "got 0"
   "got <"
   "got >"
   "got /"
   "got :"
   "got --["
   "string single"
   "string single got \\"
   "string double"
   "string double got \\"
   "string long"
   "string long got ]"
   "comment short"
   "comment long"
   "comment long got ]"
   "number dec"
   "number decfloat"
   "number hex"
   "number hexfloat"
   "number power"
   "number powersign"
end

local last_token_kind <total>: {LexState:TokenKind} = {
   ["start"] = nil, -- never in a token
   ["any"] = nil, -- never in a token
   ["identifier"] = "identifier",
   ["got -"] = "op",
   ["got --"] = nil, -- drop comment
   ["got ."] = ".",
   ["got .."] = "op",
   ["got ="] = "op",
   ["got ~"] = "op",
   ["got ["] = "[",
   ["got 0"] = "number",
   ["got <"] = "op",
   ["got >"] = "op",
   ["got /"] = "op",
   ["got :"] = "op",
   ["got --["] = nil, -- drop comment
   ["string single"] = "$ERR invalid_string$",
   ["string single got \\"] = "$ERR invalid_string$",
   ["string double"] = "$ERR invalid_string$",
   ["string double got \\"] = "$ERR invalid_string$",
   ["string long"] = "$ERR invalid_string$",
   ["string long got ]"] = "$ERR invalid_string$",
   ["comment short"] = nil, -- drop comment
   ["comment long"] = "$ERR unfinished_comment$",
   ["comment long got ]"] = "$ERR unfinished_comment$",
   ["number dec"] = "integer",
   ["number decfloat"] = "number",
   ["number hex"] = "integer",
   ["number hexfloat"] = "number",
   ["number power"] = "number",
   ["number powersign"] = "$ERR invalid_number$",
}

local keywords: {string:boolean} = {
   ["and"] = true,
   ["break"] = true,
   ["do"] = true,
   ["else"] = true,
   ["elseif"] = true,
   ["end"] = true,
   ["false"] = true,
   ["for"] = true,
   ["function"] = true,
   ["goto"] = true,
   ["if"] = true,
   ["in"] = true,
   ["local"] = true,
   ["nil"] = true,
   ["not"] = true,
   ["or"] = true,
   ["repeat"] = true,
   ["return"] = true,
   ["then"] = true,
   ["true"] = true,
   ["until"] = true,
   ["while"] = true,
}

local lex_any_char_states: {string:LexState} = {
   ["\""] = "string double",
   ["'"] = "string single",
   ["-"] = "got -",
   ["."] = "got .",
   ["0"] = "got 0",
   ["<"] = "got <",
   [">"] = "got >",
   ["/"] = "got /",
   [":"] = "got :",
   ["="] = "got =",
   ["~"] = "got ~",
   ["["] = "got [",
}

for c = string.byte("a"), string.byte("z") do
   lex_any_char_states[string.char(c)] = "identifier"
end
for c = string.byte("A"), string.byte("Z") do
   lex_any_char_states[string.char(c)] = "identifier"
end
lex_any_char_states["_"] = "identifier"

for c = string.byte("1"), string.byte("9") do
   lex_any_char_states[string.char(c)] = "number dec"
end

local lex_word: {string:boolean} = {}
for c = string.byte("a"), string.byte("z") do
   lex_word[string.char(c)] = true
end
for c = string.byte("A"), string.byte("Z") do
   lex_word[string.char(c)] = true
end
for c = string.byte("0"), string.byte("9") do
   lex_word[string.char(c)] = true
end
lex_word["_"] = true

local lex_decimals: {string:boolean} = {}
for c = string.byte("0"), string.byte("9") do
   lex_decimals[string.char(c)] = true
end

local lex_hexadecimals: {string:boolean} = {}
for c = string.byte("0"), string.byte("9") do
   lex_hexadecimals[string.char(c)] = true
end
for c = string.byte("a"), string.byte("f") do
   lex_hexadecimals[string.char(c)] = true
end
for c = string.byte("A"), string.byte("F") do
   lex_hexadecimals[string.char(c)] = true
end

local lex_any_char_kinds: {string:TokenKind} = {}
local single_char_kinds: {TokenKind} = {"[", "]", "(", ")", "{", "}", ",", "#", ";", "?"}
for _, c in ipairs(single_char_kinds) do
   lex_any_char_kinds[c] = c
end
for _, c in ipairs({"+", "*", "|", "&", "%", "^"}) do
   lex_any_char_kinds[c] = "op"
end

local lex_space: {string:boolean} = {}
for _, c in ipairs({" ", "\t", "\v", "\n", "\r"}) do
   lex_space[c] = true
end

local escapable_characters: {string:boolean} = {
   a = true,
   b = true,
   f = true,
   n = true,
   r = true,
   t = true,
   v = true,
   z = true,
   ["\\"] = true,
   ["\'"] = true,
   ["\""] = true,
   ["\r"] = true,
   ["\n"] = true,
}

local function lex_string_escape(input: string, i: integer, c: string): integer, boolean
   if escapable_characters[c] then
      return 0, true
   elseif c == "x" then
      return 2, (
         lex_hexadecimals[input:sub(i+1, i+1)] and
         lex_hexadecimals[input:sub(i+2, i+2)]
      )
   elseif c == "u" then
      if input:sub(i+1, i+1) == "{" then
         local p = i + 2
         if not lex_hexadecimals[input:sub(p, p)] then
            return 2, false
         end
         while true do
            p = p + 1
            c = input:sub(p, p)
            if not lex_hexadecimals[c] then
               return p - i, c == "}"
            end
         end
      end
   elseif lex_decimals[c] then
      local len = lex_decimals[input:sub(i+1, i+1)]
                  and (lex_decimals[input:sub(i+2, i+2)] and 2 or 1)
                  or  0
      return len, tonumber(input:sub(i, i + len)) < 256
   else
      return 0, false
   end
end

function lexer.lex(input: string, filename: string): {Token}, {Error}
   local tokens: {Token} = {}

   local state: LexState = "any"
   local fwd = true
   local y = 1
   local x = 0
   local i = 0
   local lc_open_lvl = 0
   local lc_close_lvl = 0
   local ls_open_lvl = 0
   local ls_close_lvl = 0
   local errs: {Error} = {}
   local nt = 0

   local tx: integer
   local ty: integer
   local ti: integer
   local in_token = false

   local function begin_token()
      tx = x
      ty = y
      ti = i
      in_token = true
   end

   local function end_token(kind: TokenKind, tk: string)
      nt = nt + 1
      tokens[nt] = {
         x = tx,
         y = ty,
         tk = tk,
         kind = kind,
      }
      in_token = false
   end

   local function end_token_identifier()
      local tk = input:sub(ti, i - 1)
      nt = nt + 1
      tokens[nt] = {
         x = tx,
         y = ty,
         tk = tk,
         kind = keywords[tk] and "keyword" or "identifier"
      }
      in_token = false
   end

   local function end_token_prev(kind: TokenKind)
      local tk = input:sub(ti, i - 1)
      nt = nt + 1
      tokens[nt] = {
         x = tx,
         y = ty,
         tk = tk,
         kind = kind
      }
      in_token = false
   end

   local function end_token_here(kind: TokenKind)
      local tk = input:sub(ti, i)
      nt = nt + 1
      tokens[nt] = {
         x = tx,
         y = ty,
         tk = tk,
         kind = kind
      }
      in_token = false
   end

   local function drop_token()
      in_token = false
   end

   local function add_syntax_error()
      local t = tokens[nt]
      local msg: string
      if t.kind == "$ERR invalid_string$" then
         msg = "malformed string"
      elseif t.kind == "$ERR invalid_number$" then
         msg = "malformed number"
      elseif t.kind == "$ERR unfinished_comment$" then
         msg = "unfinished long comment"
      else
         msg = "invalid token '" .. t.tk .. "'"
      end
      table.insert(errs, {
         filename = filename,
         y = t.y,
         x = t.x,
         msg = msg,
      })
   end

   local len = #input
   if input:sub(1,2) == "#!" then
      begin_token()
      i = input:find("\n")
      if not i then
         i = len + 1
      end
      end_token_prev("hashbang")
      y = 2
      x = 0
   end
   state = "any"

   while i <= len do
      if fwd then
         i = i + 1
         if i > len then
            break
         end
      end

      local c: string = input:sub(i, i)

      if fwd then
         if c == "\n" then
            y = y + 1
            x = 0
         else
            x = x + 1
         end
      else
         fwd = true
      end

      if state == "any" then
         local st = lex_any_char_states[c]
         if st then
            state = st
            begin_token()
         else
            local k = lex_any_char_kinds[c]
            if k then
               begin_token()
               end_token(k, c)
            elseif not lex_space[c] then
               begin_token()
               end_token_here("$ERR invalid$")
               add_syntax_error()
            end
         end
      elseif state == "identifier" then
         if not lex_word[c] then
            end_token_identifier()
            fwd = false
            state = "any"
         end
      elseif state == "string double" then
         if c == "\\" then
            state = "string double got \\"
         elseif c == "\"" then
            end_token_here("string")
            state = "any"
         end
      elseif state == "comment short" then
         if c == "\n" then
            state = "any"
         end
      elseif state == "got =" then
         local t: string
         if c == "=" then
            t = "=="
         else
            t = "="
            fwd = false
         end
         end_token("op", t)
         state = "any"
      elseif state == "got ." then
         if c == "." then
            state = "got .."
         elseif lex_decimals[c] then
            state = "number decfloat"
         else
            end_token(".", ".")
            fwd = false
            state = "any"
         end
      elseif state == "got :" then
         local t: TokenKind
         if c == ":" then
            t = "::"
         else
            t = ":"
            fwd = false
         end
         end_token(t, t)
         state = "any"
      elseif state == "got [" then
         if c == "[" then
            state = "string long"
         elseif c == "=" then
            ls_open_lvl = ls_open_lvl + 1
         else
            end_token("[", "[")
            fwd = false
            state = "any"
            ls_open_lvl = 0
         end
      elseif state == "number dec" then
         if lex_decimals[c] then
            -- proceed
         elseif c == "." then
            state = "number decfloat"
         elseif c == "e" or c == "E" then
            state = "number powersign"
         else
            end_token_prev("integer")
            fwd = false
            state = "any"
         end
      elseif state == "got -" then
         if c == "-" then
            state = "got --"
         else
            end_token("op", "-")
            fwd = false
            state = "any"
         end
      elseif state == "got .." then
         if c == "." then
            end_token("...", "...")
         else
            end_token("op", "..")
            fwd = false
         end
         state = "any"
      elseif state == "number hex" then
         if lex_hexadecimals[c] then
            -- proceed
         elseif c == "." then
            state = "number hexfloat"
         elseif c == "p" or c == "P" then
            state = "number powersign"
         else
            end_token_prev("integer")
            fwd = false
            state = "any"
         end
      elseif state == "got --" then
         if c == "[" then
            state = "got --["
         else
            fwd = false
            state = "comment short"
            drop_token()
         end
      elseif state == "got 0" then
         if c == "x" or c == "X" then
            state = "number hex"
         elseif c == "e" or c == "E" then
            state = "number powersign"
         elseif lex_decimals[c] then
            state = "number dec"
         elseif c == "." then
            state = "number decfloat"
         else
            end_token_prev("integer")
            fwd = false
            state = "any"
         end
      elseif state == "got --[" then
         if c == "[" then
            state = "comment long"
         elseif c == "=" then
            lc_open_lvl = lc_open_lvl + 1
         else
            fwd = false
            state = "comment short"
            drop_token()
            lc_open_lvl = 0
         end
      elseif state == "comment long" then
         if c == "]" then
            state = "comment long got ]"
         end
      elseif state == "comment long got ]" then
         if c == "]" and lc_close_lvl == lc_open_lvl then
            drop_token()
            state = "any"
            lc_open_lvl = 0
            lc_close_lvl = 0
         elseif c == "=" then
            lc_close_lvl = lc_close_lvl + 1
         else
            state = "comment long"
            lc_close_lvl = 0
         end
      elseif state == "string double got \\" then
         local skip, valid = lex_string_escape(input, i, c)
         i = i + skip
         if not valid then
            end_token_here("$ERR invalid_string$")
            add_syntax_error()
         end
         x = x + skip
         state = "string double"
      elseif state == "string single" then
         if c == "\\" then
            state = "string single got \\"
         elseif c == "'" then
            end_token_here("string")
            state = "any"
         end
      elseif state == "string single got \\" then
         local skip, valid = lex_string_escape(input, i, c)
         i = i + skip
         if not valid then
            end_token_here("$ERR invalid_string$")
            add_syntax_error()
         end
         x = x + skip
         state = "string single"
      elseif state == "got ~" then
         local t: string
         if c == "=" then
            t = "~="
         else
            t = "~"
            fwd = false
         end
         end_token("op", t)
         state = "any"
      elseif state == "got <" then
         local t: string
         if c == "=" then
            t = "<="
         elseif c == "<" then
            t = "<<"
         else
            t = "<"
            fwd = false
         end
         end_token("op", t)
         state = "any"
      elseif state == "got >" then
         local t: string
         if c == "=" then
            t = ">="
         elseif c == ">" then
            t = ">>"
         else
            t = ">"
            fwd = false
         end
         end_token("op", t)
         state = "any"
      elseif state == "got /" then
         local t: string
         if c == "/" then
            t = "//"
         else
            t = "/"
            fwd = false
         end
         end_token("op", t)
         state = "any"
      elseif state == "string long" then
         if c == "]" then
            state = "string long got ]"
         end
      elseif state == "string long got ]" then
         if c == "]" then
            if ls_close_lvl == ls_open_lvl then
               end_token_here("string")
               state = "any"
               ls_open_lvl = 0
               ls_close_lvl = 0
            end
         elseif c == "=" then
            ls_close_lvl = ls_close_lvl + 1
         else
            state = "string long"
            ls_close_lvl = 0
         end
      elseif state == "number hexfloat" then
         if c == "p" or c == "P" then
            state = "number powersign"
         elseif not lex_hexadecimals[c] then
            end_token_prev("number")
            fwd = false
            state = "any"
         end
      elseif state == "number decfloat" then
         if c == "e" or c == "E" then
            state = "number powersign"
         elseif not lex_decimals[c] then
            end_token_prev("number")
            fwd = false
            state = "any"
         end
      elseif state == "number powersign" then
         if c == "-" or c == "+" then
            state = "number power"
         elseif lex_decimals[c] then
            state = "number power"
         else
            end_token_here("$ERR invalid_number$")
            add_syntax_error()
            state = "any"
         end
      elseif state == "number power" then
         if not lex_decimals[c] then
            end_token_prev("number")
            fwd = false
            state = "any"
         end
      end
   end

   if in_token then
      if last_token_kind[state] then
         end_token_prev(last_token_kind[state])
         if last_token_kind[state]:sub(1, 4) == "$ERR" then
            add_syntax_error()
         elseif keywords[tokens[nt].tk] then
            tokens[nt].kind = "keyword"
         end
      else
         drop_token()
      end
   end

   table.insert(tokens, { x = x + 1, y = y, i = i, tk = "$EOF$", kind = "$EOF$" })

   return tokens, errs
end

local function binary_search<T, U>(list: {T}, item: U, cmp: function(T, U): boolean): integer, T
   local len <const> = #list
   local mid: integer
   local s, e = 1, len
   while s <= e do
      mid = math.floor((s + e) / 2)
      local val <const> = list[mid]
      local res <const> = cmp(val, item)
      if res then
         if mid == len then
            return mid, val
         else
            if not cmp(list[mid + 1], item) then
               return mid, val
            end
         end
         s = mid + 1
      else
         e = mid - 1
      end
   end
end

function lexer.get_token_at(tks: {Token}, y: integer, x: integer): string
   local _, found <const> = binary_search(
      tks, nil,
      function(tk: Token): boolean
         return tk.y < y
            or (tk.y == y and tk.x <= x)
      end
   )

   if found
      and found.y == y
      and found.x <= x and x < found.x + #found.tk
   then
      return found.tk
   end
end

return lexer
