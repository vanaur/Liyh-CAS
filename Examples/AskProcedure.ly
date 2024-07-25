use Liyh.Files

enumeration Maybe<t>
   Nothing
   Just[just: t]

procedure Ask[prompt: String or '>>> ', type: Type]
   mutable userInput := Nothing

   do
      do Write[prompt]
      userInput <- ReadData[url: stdin, format: TypeFormat<type>]

      if userInput = Nothing then
         perform writeln['Not the good input format, expected a {type}.']

   while userInput = Nothing

   select userInput
      Just[result] -> return result
      Nothing[] -> return Ask[prompt, type] # This might not occur

