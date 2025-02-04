type Token = {data: string, delim: string}
exception SytnaxError
signature TOKENIZER =
sig
  val stream: string ref
  val nextTok: unit -> Token
end

structure Tokenizer:>TOKENIZER =
struct
  val stream = ref ""
  val delimiter = [" ", ",", "+", "++", "-", "--", "=", "==", "(", ")", "'","-=", "*=", "+="]
  val twodelimiter = ["+", "-", "=","*"]
  local
    fun find (_: string, []) = false
      | find (str, s :: l) =
          str = s orelse find (str, l)
    fun auxNext (prev, str) =
      case str of
        s :: l =>
          let
            val del_s = find (Char.toString s, delimiter)
            val del2_s = find (Char.toString s, twodelimiter)
            val del2_prev = find (prev, twodelimiter)
          in
            if del2_s andalso del2_prev then
              if find (prev ^ Char.toString s, delimiter) then
                ("", Char.toString s, implode l)
              else
                raise SytnaxError
            else if del2_s then
              let val (_, del2, rest) = auxNext (Char.toString s, l)
              in ("", Char.toString s ^ del2, rest)
              end
            else if del2_prev then
              ("", "", implode l)
            else if del_s then
              ("", Char.toString s, implode l)
            else
              let val (r, del, rest) = auxNext (Char.toString s, l)
              in (Char.toString s ^ r, del, rest)
              end
          end
      | [] => ("", "", "")
  in
    fun nextTok () =
      let val (tok, del, rest) = auxNext ("", explode (!stream))
      in (stream := rest; {data = tok, delim = del})
      end
  end
end (*AST ... *)

