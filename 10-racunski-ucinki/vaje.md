## Naloga 1

Lambda račun razširite z učinkoma za branje in pisanje (IO). Pri tem se osredotočimo zgolj na branje in pisanje celih števil.

Da lahko beležimo v katerem koraku program nekaj prebere oz. izpiše, naj nova operacijska semantika uporablja označene puščice.

- Če se v koraku ni zgodilo nič, potem uporabimo navadno puščico.   
- Če smo v koraku izpisali število `n`, potem puščico označimo z `!n`.
- Če smo v koraku prebrali število `n`, potem puščico označimo z `?n`.

Sedaj je potrebno tudi stara pravila dopolniti z označenimi puščicami. Da se število pravil ne potroji, lahko uporabljate spremenljivke za tip oznake na puščici.

## Naloga 2

Napišite program, ki prebere dve števili in izpiše njuno vsoto. Narišite drevo vseh možnih izvajanj programa.

## Naloga 3

Sedaj, ko imamo na voljo razširitev Lambda računa s pomnilnikom, lahko v Lambda računu modeliramo IMP. Napišite prevajalnik, ki sprejme program v IMPu in vrne program v Lambda računu.

## Naloga 4

Lambda račun s pomnilnikom razširite še s hkratnim izvajanjem. Izračun `c1 || c2`, za `c1 : unit` in `c2 : unit`, lahko naredi korak v prvi ali drugi komponenti. Ko izračuna obe komponenti, vrne `unit` (torej je izvajanje zanimivo le v kombinaciji z drugimi učinki).

Je naš programski jezik še determinističen? Če ni, napišite program, ki bo imel več možnih rezultatov.
