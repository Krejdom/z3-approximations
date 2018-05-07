# 05/10/2017
- Zažádáno o instalaci Z3, python-z3 a python3-venv.
- Prozření, že pysmt vůbec asi potřebovat nebudu.

# 06/10/2017
- Fanda instaluje Z3 na všechny pc ve Formele.
- Když změním v ~/.bashrc řádek s PATH na následující a vytvořím si v homu složku bin, tak potom můžu veškeré binárky, co jsou v této složce, spouštět odkudkoli jen tak, že napíšu jejich jméno.
	PATH=/usr/sbin:/sbin:/usr/etc:~/bin:$PATH

# 09/10/2017
- Prošla jsem si tutoriál na Z3: https://rise4fun.com/Z3/tutorial/guide

# 15/10/2017
- Přečetla jsem si článek Solving Quantified Bit-Vector Formulas Using Binary Decision Diagrams

# 17/10/2017
- Prošla jsem si návod na Python API do Z3.
- Funkce v Z3 jsou totální a nemají žádné vedlejší efekty (na rozdíl od jiných programovacích jazyků).
- Z3 je založena na prvořádové logice.
- Neinterpretovaná celočíselná kontanta = proměnná.
- Bit-Vector definuji jako:
	x = BitVec('x', 16)

- Operace a jejich znaménkové a bezznaménkové verze
    signed ... unsigned
    -------------------
	<  ... ULT
	<= ... ULE
	>  ... UGT
	>= ... UGE
	/  ... UDiv
	%  ... URem
	>> ... LShR

# 20/10/2017
- Stáhla jsem si LaTeXovou šablonu ClassicThesis na text práce.
- Inicializovala jsem si gitové repo na text práce.

# 23/10/2017
- Zeptala jsem se Martina, které benchmarky mám použít a dostala jsem přesně toto:
	https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/BV
ze stránky:
	http://smtlib.cs.uiowa.edu/benchmarks.shtml
- Když chci nahrát vstupní soubor v SMTlib formátu pomocí Pythonu a vyhodnotit ho, stačí použít toto:
	z3.solve(z3.parse_smt2_file("<FILE-PATH>"))

# 16/11/2017
- Martin doporučuje tuto stránku na citace. (Najdu tam článek a zobrazí mi to k němu bibtexovou citaci a budu mít aspoň sjednocený styl u všech.) :)
    http://dblp.uni-trier.de
- Dva dny do odevzdání přehledové kapitoly, to bude ještě sranda. :D
- V přehledové kapitole (po konzultaci s Martinem) bych měla přejít od představení různých solverů a různých postupů zpracování Bit-Vektorů po to, jak to dělá Z3 a Q3B teď, jak jsou na tom, jaké techniky používají a jaké druhy aproximací máme.

# 07/11/2017
- Heňo je čarovný. Tímhle se bude buildit všechno a bude se to samo aktualizovat, když něco změním!
    latexmk -pdf -pvc ClassicThesis.tex
    
# 22/01/2018
- SMTweek #1: https://www.fi.muni.cz/~xjonas/SMTweek/
- man page pro Z3 Python: https://z3prover.github.io/api/html/namespacez3py.html
- implementace užitečných z3 funkcí: https://github.com/Z3Prover/z3/blob/f5bba636740e0e77e03ed70166ef92c62bfebb7f/src/api/python/z3/z3.py
- Z3 Python tutorial: https://ericpony.github.io/z3py-tutorial/guide-examples.htm
- Z3 Python tutorial (advanced): http://ericpony.github.io/z3py-tutorial/advanced-examples.htm

- Načtení a procházení formule, identifikace velikosti, typu formule a typu kvantifikace.

# 23/01/2018
- Pro vytvoření nové formule použiji kontrukci `formula.decl().__call__(*...)`
- Program dokáže změnit šířku bit-vektorových proměnných a konstant.
- U některých formulí se mohou ještě objevit problémy s aritou operátorů (násobení) a Distinct, zatím jsem na to ale nenarazila, tak nevím, jakou to má aritu a jak to případně ošetřit.

# 24/01/2018
- Ověřování splnitelnosti formule a pokus o postupné zpřesňování aproximací.
- Uhlazení kódu, rozdělení do více funkcí, okomentování.

# 25/01/2018
- Zkusit jak se budou chovat aproximace, pokud jich udělám x různých, bez ohledu na šířku bit-vektoru a míru aproximace rovnoměrně rozložím v intervalu (0, maximální 
- Opravena chyba, když jsem zaměnila + a &. O:)

# 26/01/2018
- K paralelismu Q/E a timeoutu využívám krásnou pythonní knihovnu multiprocessing: https://docs.python.org/3/library/multiprocessing.html
- Pro spuštění na všech benchmarcích spustit příkaz se vložce s BV..
    python3 ../develop/01.py **/*.smt2
- Při spuštění háže chybu RecursionError.
- Nefunguje třeba na /wintersteiger/fmsd13/fixpoint/small-bug1-fixpoint-1.smt2

# 01/03/2018
- Opravila jsem zapomenutý problém se znovuvytvořením Exists() formule. Vytvářela jsem tam vždycky jen ForAll().

# 12/03/2018
- Odstranila jsem problém se špatným výběrem aproximovaných proměnných. Chyba byla v tom, že jsem předávala vždy původní seznam `var_list`, nikoli jeho kopii (záludnost v Pythonu). Teď je všude, kde se předává proměnná `var_list` jako argument, nejdřív zkopírovaná. Asi to není nutné všude, takže jako vylepšení kódu je možné to asi někde smazat.
- Další chyba nastává u formule `/BV_benchmarky/20170501-Heizmann-UltimateAutomizer/gcd_2_true-unreach-call_true-no-overflow.i_914.smt2`, nevím, jak se vypořádat s `SignExt()` (to na to prý vliv nemá).

# 19/03/2018
- Chyba je v polaritě Not(ForAll...) se nepřepne na "Exists", ale vyhodnocuje se pořád pomoví overaproximace.
- Mám nástřel osnovy textu:

0 Úvod
1 SMT v teorii bit vektorů
    1.0 Solvery
2 Aproximace
    2.0 Over
    2.1 Under
3 Implementace v Z3
    3.0 Nástroj Z3 (popis)
    3.1 Python API (příklad užití)
        3.1.0 De Bruijn indexování
    3.2 Pseudokód aproximací
        3.2.0 Paralelní souběh procesů
        3.2.1 Polarita
4 Experimentální vyhodnocení
5 Závěr

- TODO: vylepšení: neopakovat část s přepínáním polarity
- SOLVED: Násleudující benchmark vrací unknown-unknown, když ho pustím samotnej, když ho pustím mezi více, tak vrací unknown-result:
    ../BV_benchmarky/20170501-Heizmann-UltimateAutomizer/jain_1_true-unreach-call_true-no-overflow.i_56.smt2
- TODO: Měla bych zjistit, jestli někdy projde aproximace, když timeoutne originální formule.

# 20/3/2018
- Něco spadlo:
    z3.z3types.Z3Exception: b'out of memory'
- TODO: Vyčistit kód od debugů a starých poznámek.
- Snažím se teď řešit situaci kdy je aproximace undef a originál je sat/unsat, nastává to třeba u formule: ../BV_benchmarky/20170501-Heizmann-UltimateAutomizer/jain_1_true-unreach-call_true-no-overflow.i_408.smt2 --> budu to prostě dál aproximovat, když aproximace vyjde unknown, stejně, jako by to vyšlo nějak určitě
- Problém v nedeterminičnosti bude pravděpodobně v tom, že na výsledek používám stejnou frontu!!

# 21/03/2018
- SOLVED: Zvlčily mi procesy. Nějak se množí a nevím co s tím. Začne se to kazit na tomto benchmarku (Po jeho doběhnutí mi tam zůstanou viset dva procesy.):
    ../BV_benchmarky/20170501-Heizmann-UltimateAutomizer/jain_2_true-unreach-call_true-no-overflow.i_198.smt2 
- Tak jsem předchozí problém vyřešila (asi). Zakonalý pes byl v tom, že se timeout měřil na procesu `p`, který spouštěl parelelně proces under-aproximace a over-aproximace (`p1` a `p2`), ale při přešvihnutí jedné minuty se zabil právě jen proces `p` a ty dva potomci tam zůstali viset.
- To mohlo možná způsobit i nekonzistenci výsledků, když jsem spustila jen jeden benchmark a když jsem je spustila všechny. Výsledek se totiž ukládá do fronty a ty přeživší potomci mohli kdykoli později doběhnout a vrazit do té fronty svůj výsledek.
- Dál by možná bylo fajn, aby když se dopočítá aproximace, tak zabila ten originál a napsalo to `OK!`, abych věděla, v kolika případech to pomůže. A nebo tam rovnou vrazit časový údaj, ať už se to dá porovnávat.
- Pořád se některé formule nechtějí v aproximaci dopočítat: ../BV_benchmarky/20170501-Heizmann-UltimateAutomizer/jain_1_true-unreach-call_true-no-overflow.i_408.smt2

# 22/03/2018
- z3.z3types.Z3Exception: b'bit-vector size must be greater than zero' po ../BV_benchmarky/wintersteiger/fmsd13/ranking/filesys_smbmrx_midatlas.c.smt2

# 26/03/2018
- TODO na tento týden:
    1. DONE Měřit, jak dlouho trvá rozhodnutí formule (originál vs. aproximace)
    2. DONE Zjistit, za jak dlouho timeoutují aproximace (nesčítá se to náhodou? to by vysvětlovalo to, že tam teď nejsou vykřičníky, jak jsem to předělala)
    3. Sepsat část k polaritě.
    4. DONE Udělat prezentaci na 4minutovou obhajobu.
    5. Udělat nějaký pěkný graf.

- Měřím čas podle: https://stackoverflow.com/questions/7370801/measure-time-elapsed-in-python
- Návod na grafy (tento vypadá fajn): http://pythonic.eu/fjfi/posts/matplotlib.html
- Výsledky z prvního pokusu (id, original, approximated) jsou v souboru:
    result_20170501-Heizmann-UltimateAutomizer.txt

# 27/03/2018
- Opravila jsem problém, který nastával u různě velkých proměnných, protože se rozšiřovaly na `max_bit_width` i ty, co byly kratší. Přidala jsem podmínku do funkce, která dělá aproximace a teď by se měla v takovém případě vrátit originální formule.
- Další chyba, která nastává je:
    ctypes.ArgumentError: argument 1: <class 'RecursionError'>: maximum recursion depth exceeded
- A to např. na benchmarku:
    ../BV_benchmarky/wintersteiger/fmsd13/fixpoint/cache-coherence-2-fixpoint-2.smt2
- Rekurze je zrádná. Limit lze v Pythonu zvýšit pomocí:
    `sys.setrecursionlimit(1500)`
- Další možnost je optimalozovat kvantifikované formule následujícím způsobem: Pokud je ve formule tvaru ForAll x (ForAll y (...)), není nutné ji komplet rekurzivně procházet, ale pomocí cyklu se podívat na `body` vnější formule a případně kvantifikovanou proměnnou přidat do seznamu rovnou.

# 28/03/2018
- Při spuštění testů 20170501-Heizmann-UltimateAutomizer s timeoutem 100 s:
    - apro_faster:  4
    - orig_faster:  62
    - same_time:  65
- Dělám slajdy na 4 minutovou obhajobu do prezentačních dovedností.
- Někde chci mít ukázku toho, jak vypadají formule:
    - smt2 formát ->
    - příkaz, kterým se to převede ->
    - formát po konverzi (prefixový) ->
    - ukázka ve stromu
    - + vytvětlení rekurzního zpracování a sekvenčních vylepšení kvantifikátorů viz výše.
    
# 29/03/2018
- Prezentovala jsem čtyřminutovou obhajobu. 4 minuty jsou strašně málo. Aspoň mám předpřipravenou prezentaci na obhajobu.

# 30/03/2018
- Překopírovala jsem tabulku a schéma z obhajoby do textu bakalářky, v tabulce budou snad potom hezčí výsledky. :D

# 31/03/2018
- Píšu sekci o polaritě.
- Už jednou jsem řešila problém, že se mi nečíslují sekce a podsekce. Byl to tento problém: https://tex.stackexchange.com/questions/299969/titlesec-loss-of-section-numbering-with-the-new-update-2016-03-15 pro jeho vyřešení stačí nahrát do složky se zdrojákama soubor titlesec.sty, který jsem stáhla už nevím odkud.
- Mám udávat všechny tři De Morganovy zákony?
- Kam dát odkaz na citaci u definice?

# 04/04/2018
- Překopala jsem fci `qform_process` a implementovala "sekvenční zkratku". Odstranila jsem i zvýšení limitu rekurze a běží to jak na drátkách (aspoň na tom jednom benchmarku, kde to předtím padalo, jdu to zkusit i na další.
- TODO: `qform_process` rozložit fci na víc menších. Logicky pojmenovat. To by chtělo asi u všech fcí. O:)
- Tak na té rekurzi to padá pořád, ale sice to vyhodí chybu, ale výsledek to normálně vrátí.

# 05/04/2018
- Noční můra se vrací. b'bit-vector size must be greater than zero', padá to u banchmarků ../BV_benchmarky/wintersteiger/fmsd13/fixpoint/fixpoint/sdlx-fixpoint-4.smt2

# 10/04/2018
- TOOD: Ověřit, že rekurze vrátí správný výsledek do result.
- done: Není náhodou De Morgan Tvrzení?
- Na tabulky je dobré používat balíček booktabs. (Martin)
- done: Citace nejen číslem.
- TODO: Dopsat Strejdu do poděkování za to, že mi pověděl chytrou věc. (wall time vs. CPU time, nástroje: Cgroups, Banchexec?)

# 17/04/2018
- Píšu a píšu.
- TODO: V Bibliografii mám anglické "in", to by chtělo odstranit.

# 19/04/2018
- Udělala jsem vizualiazci různých typů redukcí do textu.

# 23/04/2018
- Asi jsem objevila podstatnou chybu. Měla jsem přehozené menšítko v podmínce o aproximacích. Všechny dosavadní výsledky jsou tedy pravděpodobně nerelevantní.
- Kreslím si schéma funkcí a rozkládám ty velké na menší.

# 07/05/2018
- Vytvářím soubor s pracovním názvem 02.py, který má být hotovým prográmkem, který přiložím k bakalářce. Tz. že bude rozhodovat vždy jen jeden soubor s formulí a bude poustět paralelně jak aproximace, tak i originál. Nad tím potom musím postavit skript, který pustí 02 a jen výpočet originálu.
- Předělala jsem tam i drobně paralelismus, kterej byl nějakej čudnej. Podle tohoto: https://stackoverflow.com/questions/48677978/python-run-multiple-get-requests-in-parallel-and-stop-on-first-response

