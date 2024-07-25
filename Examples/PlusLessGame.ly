use Liyh.Random

procedure Play[toGuess: Natural, mutable maxCount: Integer or -1]
   mutable count := 0

   if maxCount != -1 then
      do Write['The game starts, you have {maxCount} tries!']
   else
      do Write['The game starts!']

   while maxCount != 0
      maxCount <- maxCount - 1
      count <- count + 1

      input := UserInput[text: 'Guess the number: ', expect: Natural]

      select input
         x when (x > toGuess) -> do Write['Lesser!']
         x when (x < toGuess) -> do Write['Greater!']
         _ -> breakloop
      
      do Write['You found the number in {count} moves!']

rnd := RandInt[0, 100]
do Play[rnd]

