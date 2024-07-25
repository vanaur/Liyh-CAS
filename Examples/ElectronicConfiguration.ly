use Liyh.String

procedure ElectronConfig[z: Natural]
   subshells := { "1s", "2s", "2p", "3s", "3p", "4s", "3d", "4p", "5s", "4d", "5p", "6s", "4f", "5d", "6p", "7s", "5f", "6d", "7p" }
   subshellMaxElectrons := { 2, 2, 6, 2, 6, 2, 10, 6, 2, 10, 6, 2, 14, 10, 6, 2, 14, 10, 6  }
   
   mutable remainingElectrons := z
   mutable electronConfig := ''
   mutable index := 0
   
   while remainingElectrons > 0
      electronsInSubshell = Min[remainingElectrons, subshellMaxElectrons.[index]]
      electronConfig <- electronConfig + subshells.[index] + (electronsInSubshell :: String) + ' '
      remainingElectrons <- remainingElectrons - electronsInSubshell
      index <- index + 1

   return electronConfig

