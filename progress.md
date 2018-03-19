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
4 Experimentální vyhodnocení
5 Závěr

- TODO: vylepšení: neopakovat část s přepínáním polarity
- TODO: Násleudující benchmark vrací unknown-unknown, když ho pustím samotnej, když ho pustím mezi více, tak vrací unknown-result: /20170501-Heizmann-UltimateAutomizer/jain_1_true-unreach-call_true-no-overflow.i_56.smt2
- TODO: Měla bych zjistit, jestli někdy projde aproximace, když timeoutne originální formule.

