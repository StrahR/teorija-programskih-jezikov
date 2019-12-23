# Naloga 1

1. Napišite prestreznik `mute`, ki prestreže vgrajeni `Print` in prepreči izpis. Program naj nadaljuje nemoteno. 

2. Napišite prestreznik `shift_text_right n`, ki vse izpisano besedilo zamakne v desno za `n` mest.

3. Prestreznik `underline` vsako izpisano vrstico podčrta (tako da v novi vrstici izpiše primerno število znakov `-`).

4. Prestreznik `custom_separator sep` naj poskrbi, da se ločeno izpisani tekst ne loči z `\n` temveč separatorjem `sep`.

# Naloga 2

Želimo narediti prestreznik za memoizacijo. Že izračunane vrednosti bomo (neučinkovito) hranili v seznamu parov.

1. Napišite funkciji za delo s seznami parov `find : 'a -> ('a * 'b) list -> 'b option` in `save : 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list`.

2. Da si poenostavimo življenje, se osredotočimo zgolj na funkcije `int -> int`. V nadaljevanju uporabljamo preimenovanji `type arg = int` in `type result = int`.
  Naša memoizacija bo potrebovala pomnilnik, zato bomo zanj definirali poseben prestreznik. Definirajte učinka `Lookup : arg -> result option` in `Remember : arg * result -> unit`. Nato zanju napišite prestreznik `memory`, ki upravlja s pomnilnikom tipa `(arg * result) list`.

3. Sedaj lahko funkcije že uporabljajo pomnilnik za memoizacijo, vendar bi želeli, da je memoizacija funkcije zgolj eno od možnih izvajanj. Zato definirajte učinek `Evaluate : ((int -> int) * int) -> int`, ki sprejme funkcijo in argument, ter nam vrne rezultat. 
  Funkcij sedaj ne kličemo več kot `f x` temveč kot `perform (Evaluate (f, x))` (priporočam, da si ustvarite pomožno funkcijo `eval f x = ...` za lepšo sintakso). Napišite prestreznik `no_memo`, ki funkcijo izvede, kot bi se izvedla sicer. Nato napišite še prestreznik `memo`, ki funkcijo memoizira.

**Namig:** Če želite rekurzivne prestreznike, jih definirajte kot `let rec h () = handler ...` kjer jih lahko sedaj v telesu definicije uporabite z `with h () handle ...`.

# Naloga 3

Generatorji so funkcije, ki zaporedoma uporabljajo učinek `Yield : int -> unit`. 

1. Napišite funkcijo, ki generira vsa naravna števila.

2. Napišite funkcijo `collect n gen`, ki iz generatorja `gen` pobere prvih `n` vrednosti.

3. Napišite prestreznik `generator gen`, ki na zahtevo `Generate : unit -> int` generira novo vrednost iz generatorja `gen`.

**Namig:** Eden od možnih načinov je, da z dodatnim prestreznikom generatorje iz tipa `unit -> unit!{Yield}` pretvorite v tip `unit -> gen`. Tu je `gen` novo definiran tip, ki označuje, da je generator bodisi končal, bodisi pa je proizvedel element in svoje posodobljeno stanje (ponovno tipa `unit -> gen`). Če potrebujete, ima Eff vgrajeno funkcijo `failwith msg`.
