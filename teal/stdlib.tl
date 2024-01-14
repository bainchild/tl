return [=====[

do
   global type any
   global type thread
   global type userdata

   local enum FileStringMode
      "a" "l" "L" "*a" "*l" "*L"
   end

   local enum FileNumberMode
      "n" "*n"
   end

   local enum FileMode
      "a" "l" "L" "*a" "*l" "*L" "n" "*n"
   end

   global record FILE
      userdata

      enum SeekWhence
         "set" "cur" "end"
      end

      enum SetVBufMode
         "no" "full" "line"
      end

      close: function(FILE): boolean, string, number
      flush: function(FILE)

      lines: function(FILE): (function(): (string))
      lines: function(FILE, FileNumberMode...): (function(): (number...))
      lines: function(FILE, (number | FileStringMode)...): (function(): (string...))
      lines: function(FILE, (number | FileMode)...): (function(): ((string | number)...))
      lines: function(FILE, (number | string)...): (function(): (string...))

      read: function(FILE): string
      read: function(FILE, FileNumberMode...): number...
      read: function(FILE, (number | FileStringMode)...): string...
      read: function(FILE, (number | FileMode)...): ((string | number)...)
      read: function(FILE, (number | string)...): (string...)

      seek: function(FILE, ? SeekWhence, ? number): integer, string
      setvbuf: function(FILE, SetVBufMode, ? number)

      write: function(FILE, (string | number)...): FILE, string

      metamethod __close: function(FILE)
   end

   global record coroutine
      type Function = function(any...): any...

      create: function(Function): thread
      close: function(thread): boolean, string
      isyieldable: function(): boolean
      resume: function(thread, any...): boolean, any...
      running: function(): thread, boolean
      status: function(thread): string
      wrap: function<F>(F): F
      yield: function(any...): any...
   end

   global record debug
      record GetInfoTable
         name: string
         namewhat: string
         source: string
         short_src: string
         linedefined: integer
         lastlinedefined: integer
         what: string
         currentline: integer
         istailcall: boolean
         nups: integer
         nparams: integer
         isvararg: boolean
         func: any
         activelines: {integer:boolean}
      end

      enum HookEvent
         "call" "tail call" "return" "line" "count"
      end

      type HookFunction = function(HookEvent, integer)

      getinfo: function(any): GetInfoTable
      getinfo: function(any, string): GetInfoTable
      getinfo: function(thread, any, string): GetInfoTable

      sethook: function(thread, HookFunction, string, number)
      sethook: function(HookFunction, string, number)
   end

   global record io
      enum OpenMode
         "r" "w" "a" "r+" "w+" "a+"
         "rb" "wb" "ab" "r+b" "w+b" "a+b"
         "*r" "*w" "*a" "*r+" "*w+" "*a+"
         "*rb" "*wb" "*ab" "*r+b" "*w+b" "*a+b"
      end

      close: function(? FILE)
      input: function(? FILE): FILE
      flush: function()

      lines: function(? string): (function(): (string))
      lines: function(? string, FileNumberMode...): (function(): (number...))
      lines: function(? string, (number | FileStringMode)...): (function(): (string...))
      lines: function(? string, (number | FileMode)...): (function(): ((string | number)...))
      lines: function(? string, (number | string)...): (function(): (string...))

      open: function(string, ? OpenMode): FILE, string
      output: function(? FILE): FILE
      popen: function(string, ? OpenMode): FILE, string

      read: function(): string
      read: function(FileNumberMode...): number...
      read: function((number | FileStringMode)...): string...
      read: function((number | FileMode)...): ((string | number)...)
      read: function((number | string)...): (string...)

      stderr: FILE
      stdin: FILE
      stdout: FILE
      tmpfile: function(): FILE
      type: function(any): string
      write: function((string | number)...): FILE, string
   end

   global record math
      abs: function(integer): integer
      abs: function(number): number

      acos: function(number): number
      asin: function(number): number
      atan: function(number, ? number): number
      atan2: function(number, number): number
      ceil: function(number): integer
      cos: function(number): number
      cosh: function(number): number
      deg: function(number): number
      exp: function(number): number
      floor: function(number): integer

      fmod: function(integer, integer): integer
      fmod: function(number, number): number

      frexp: function(number): number, number
      huge: number
      ldexp: function(number, number): number
      log: function(number, ? number): number
      log10: function(number): number

      max: function(integer...): integer
      max: function((number | integer)...): number
      max: function<T>(T...): T
      max: function(any...): any

      maxinteger: integer --[[needs_compat]]

      min: function(integer...): integer
      min: function((number | integer)...): number
      min: function<T>(T...): T
      min: function(any...): any

      mininteger: integer --[[needs_compat]]

      modf: function(number): integer, number
      pi: number
      pow: function(number, number): number
      rad: function(number): number

      random: function(number, ? number): integer
      random: function(): number

      randomseed: function(number, number): integer, integer
      sin: function(number): number
      sinh: function(number): number
      sqrt: function(number): number
      tan: function(number): number
      tanh: function(number): number
      tointeger: function(any): integer
      type: function(any): string
      ult: function(number, number): boolean
   end

   global record metatable<T>
      enum Mode
         "k" "v" "kv"
      end

      __call: function(T, any...): any...
      __mode: Mode
      __name: string
      __tostring: function(T): string
      __pairs: function<K, V>(T): (function(): (K, V))

      __index: any --[[FIXME: function | table | anything with an __index metamethod]]
      __newindex: any --[[FIXME: function | table | anything with an __index metamethod]]

      __gc: function(T)
      __close: function(T)

      __add: function(any, any): any
      __sub: function(any, any): any
      __mul: function(any, any): any
      __div: function(any, any): any
      __idiv: function(any, any): any
      __mod: function(any, any): any
      __pow: function(any, any): any
      __band: function(any, any): any
      __bor: function(any, any): any
      __bxor: function(any, any): any
      __shl: function(any, any): any
      __shr: function(any, any): any
      __concat: function(any, any): any

      __len: function(T): any
      __unm: function(T): any
      __bnot: function(T): any

      __eq: function(any, any): boolean
      __lt: function(any, any): boolean
      __le: function(any, any): boolean
   end

   global record os
      record DateTable
         year: integer
         month: integer
         day: integer
         hour: integer
         min: integer
         sec: integer
         wday: integer
         yday: integer
         isdst: boolean
      end

      enum DateMode
         "!*t" "*t"
      end

      clock: function(): number

      date: function(DateMode, ? number): DateTable
      date: function(? string, ? number): string

      difftime: function(number, number): number
      execute: function(string): boolean, string, integer
      exit: function(? (number | boolean), ? boolean)
      getenv: function(string): string
      remove: function(string): boolean, string
      rename: function(string, string): boolean, string
      setlocale: function(string, ? string): string
      time: function(? DateTable): integer
      tmpname: function(): string
   end

   global record package
      config: string
      cpath: string
      loaded: {string:any}
      loaders: { function(string): any, any }
      path: string
      preload: {any:any}
      searchers: { function(string): any }
   end

   global record string
      char: function(number...): string

      byte: function(string, ? number): integer
      byte: function(string, number, number): integer...

      dump: function(function(any...): (any), ? boolean): string
      find: function(string, string, ? number, ? boolean): integer, integer, string
      format: function(string, any...): string
      gmatch: function(string, string): (function(): string...)

      gsub: function(string, string, string, ? number): string, integer
      gsub: function(string, string, {string:string}, ? number): string, integer
      gsub: function(string, string, function(string...): (string | number | boolean), ? number): string, integer

      len: function(string): integer
      lower: function(string): string
      match: function(string, string, ? number): string...
      pack: function(string, any...): string
      packsize: function(string): integer
      rep: function(string, number, ? string): string
      reverse: function(string): string
      sub: function(string, number, ? number): string
      unpack: function(string, string, ? number): any...
      upper: function(string): string
   end

   global record table
      type SortFunction = function<A>(A, A): boolean

      record PackTable<A>
         is {A}

         n: integer
      end

      concat: function({(string | number)}, ? string, ? number, ? number): string

      insert: function<A>({A}, number, A)
      insert: function<A>({A}, A)

      pack: function<T>(T...): PackTable<T>
      pack: function(any...): {any:any}

      remove: function<A>({A}, ? number): A
      sort: function<A>({A}, ? SortFunction<A>)

      unpack: function<A>({A}, ? number, ? number): A... --[[needs_compat]]
   end

   local record StandardLibrary
      enum CollectGarbageCommand
         "collect"
         "count"
         "stop"
         "restart"
      end

      enum CollectGarbageSetValue
         "step"
         "setpause"
         "setstepmul"
      end

      enum CollectGarbageIsRunning
         "isrunning"
      end

      type LoadFunction = function(): string

      enum LoadMode
         "b" "t" "bt"
      end

      type XpcallMsghFunction = function(...: any): ()

      arg: {string}
      assert: function<A, B>(A, ? B): A

      collectgarbage: function(CollectGarbageCommand): number
      collectgarbage: function(CollectGarbageSetValue, number): number
      collectgarbage: function(CollectGarbageIsRunning): boolean
      collectgarbage: function(string, ? number): (boolean | number)

      error: function(? any, ? number)
      ipairs: function<A>({A}): (function():(integer, A))

      load: function((string | LoadFunction), ? string, ? LoadMode, ? table): (function, string)
      load: function((string | LoadFunction), ? string, ? string, ? table): (function, string)

      next: function<K, V>({K:V}, ? K): (K, V)
      next: function<A>({A}, ? integer): (integer, A)

      pairs: function<K, V>({K:V}): (function():(K, V))
      pcall: function(function(any...):(any...), any...): boolean, any...
      print: function(any...)
      require: function(string): any

      select: function<T>(number, T...): T
      select: function(number, any...): any
      select: function(string, any...): integer

      setmetatable: function<T>(T, metatable<T>): T

      tonumber: function(any): number
      tonumber: function(any, number): integer

      tostring: function(any): string
      type: function(any): string
      xpcall: function(function(any...):(any...), XpcallMsghFunction, any...): boolean, any...
      _VERSION: string
   end

   global arg <const> = StandardLibrary.arg
   global assert <const> = StandardLibrary.assert
   global collectgarbage <const> = StandardLibrary.collectgarbage
   global error <const> = StandardLibrary.error
   global load <const> = StandardLibrary.load
   global next <const> = StandardLibrary.next
   global pairs <const> = StandardLibrary.pairs
   global pcall <const> = StandardLibrary.pcall
   global print <const> = StandardLibrary.print
   global require <const> = StandardLibrary.require
   global select <const> = StandardLibrary.select
   global setmetatable <const> = StandardLibrary.setmetatable
   global tostring <const> = StandardLibrary.tostring
   global tonumber <const> = StandardLibrary.tonumber
   global ipairs <const> = StandardLibrary.ipairs
   global type <const> = StandardLibrary.type
   global xpcall <const> = StandardLibrary.xpcall
   global _VERSION <const> = StandardLibrary._VERSION
end

]=====]
