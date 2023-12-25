#import "template.typ": *
#show: ieee.with(
  title: [Aerodinamica ],
  abstract: [
    Appunti del corso di aerodinamica 22/23
  ],
  authors: (
    (
      name: "Lorenzo Cucchi",
    ),
  
  ),

  bibliography-file: "refs.bib",
)

= Corpi Tozzi
Dobbiamo definire la *vorticità*:
$ underline(omega)=underline(nabla)times underline(u) $ <vort>
Il rotore di un campo vettoriale possiede la seguente proprietà 
$ underline(nabla)dot (underline(nabla)times underline(A)))=0 $
Il flusso di vorticità non può sparire, è esattamente incomprimibile. Peril teroema di _Stokes_
$ integral.cont_gamma underline(u)dot underline(tau)d l=integral_s (underline(nabla)times underline(u))dot hat(n)d s=integral_s underline(omega)dot hat(n)d s $
Ricordando l'equazione @vort della vorticità:
$ (diff underline(omega))/(diff t) + underline(u)dot underline(nabla)underline(omega)=underline(omega)dot underline(nabla)underline(u)+1/(R e) nabla^2underline(omega) $
$ (D underline(omega))/(D t) = underline(omega)dot underline(nabla)underline(u) + 1/(R e) nabla^2underline(omega) $

Il primo termine è la rapidità con cui la vorticità di una particella varia nel tempo. Il secondo è il termine di *stretching* e *tilting*, stiramento o rotazione delle linee di corrente. Il terzo termine è la diffusione della vorticità ($italic(I)$ problema di Stokes).

=== Esempi

Consideriamo il fenomeno dello scarico del lavandino. Mano a mano che ci si avvicina allo scarico le linee di corrente tendono a diventare verticali e la vorticità aumenta. Tale fenomeno può essere giustificato anche dal fatto che il momento angolare si conserva e il volume di controllo si stringe mano a mano che si avvicina allo scarico. Pertanto diminuisce il momento di inerzia a favore della velocità angolare, cioè della *vorticità*.

Nelle gallerie del vento, prima della camera di prova, vengono poste reti e strutture a nido d'ape al fine di rompere le strutture vorticoseed evitare che la vorticità sia incrementata a seguito dell'accelerazione nel convergente.

== Teorema di Lagrange
Sotto le ipotesi di : _incomprimibilità_, _fluido newtoniano_, _forze di volume conservative_.

Se $ underline(omega)(underline(r),0)=0 " ," " " " "underline(omega)(underline(r),t)bar.v_(diff omega)=0&& " " forall t, " allora" $
$ underline(omega)(underline(r),t)=0 " in" " " Omega $

Questo teorema diventa molto importante quando possiamo separare il campo di moto in una zona interna ed una zona esterna.

=== Dimostrazione
$ underline(omega)(underline(r), t=0)=0 $
L'equazione della vorticità diviene:
$ lr((D underline(omega))/(D t)|)_(t=0) =0 $
Siccome per _hp._ $underline(omega)(underline(r),t)|_(diff Omega) =0$ allora $underline(omega)$ rimarrà nullo per ogni valore di _t_ su tutto il dominio.


== I th. di Helmholtz
Sotto hp. $" " underline(nabla)dot underline(u)=0" "$ , _effetti viscosi trascurabili_, $" " underline(f)=underline(nabla)E$.

Se una particella di fluido ha vorticità nulla nell'istante iniziale manterrà vorticità nulla anche negli istanti successivi.

Le ipotesi del _th. di Helmholtz_ sono #underline[deboli] rispetto a $" "underline(omega)(underline(r),t)|_(diff Omega)=0$ di _Lagrange_.


== Def. Linea Vorticosa
Una linea vorticosa è una linea tangente in ogni punto al vettore vorticità.

== II th. di Helmholtz
Sotto hp. $" "\uunderline(nabla)dot underline(u)=0" "$ , _effetti viscosi trascurabili_, $" " underline(f)=underline(nabla)E$.

Allora le linee vorticose sono *linee materiali*, ovvero linee i cui punti si muovono con velocità locale del fluido.

Se una linea materiale, in qualunque istante, è anche linea vorticola, allora resta tale in tutti gli istanti.

=== Dimostrazione

Sia $underline(x)=underline(x)(s,t)$ una linea vorticosa. Allora
$ (diff underline(x)(s,0))/(diff s) times underline(omega)(underline(x)(s,0),0)=0 $
Dobbiamo dimostrare che tale tesi vale $forall t$.

Supponiamo di fissare _s_
$ d/(d t)lr(((diff underline(x)(s,t))/(diff s)times underline(omega)(underline(x)(s,t),t)))=0 $
$ (diff^2 underline(x)(s,t))/(diff t diff s)times underline(omega)(underline(x)(s,t),t)+(diff underline(x)(s,t))/(diff s)times d/(d t)underline(omega)(underline(x)(s,t),t)=0 $
$ diff/(diff s)underline(u)(underline(x)(s,t),t)times underline(omega)(underline(x)(s,t),t) +\ +(diff underline(x)(s,t))/(diff s)times ((diff underline(omega))/(diff t)+underline(u)dot underline(nabla)underline(omega))=0 $
$ (hat(tau)dot underline(nabla))underline(u)times underline(omega)+hat(tau)times (underline(omega)dot underline(nabla))underline(u) $

Valutando in $t=0$.

$ (hat(tau)(s,0)dot underline(nabla))underline(u)times underline(omega)(underline(x)(s,0),0) +\ + hat(tau)(s,0)times (underline(omega)(underline(x)(s,0),0)dot underline(nabla))underline(u) $

Definisco $ underline(omega)(underline(x)(s,0),0)=C(s)hat(tau)(s,0) $
Allora 
$ (hat(tau)(s,0)dot underline(nabla))underline(u)times C(s)hat(tau)(s,0) +\ + hat(tau)(s,0)times (C(s)hat(tau)(s,0)dot underline(nabla))underline(u) $
$ C(s)lr([(hat(tau)dot underline(nabla))underline(u)times hat(tau)- (hat(tau)dot underline(nabla))underline(u)times hat(tau)]) =0 $
L'equazione è verificata all'istante iniziale. In definitiva:
$ d/(d t)lr(((diff underline(x))/(diff s) (s,t)times underline(omega)(underline(x)(s,t),t))|)_(t=0)=0 $

Dato che la funzione è nulla per $t=0$ e anche la sua derivata è nulla in $t=0$, allora rimarrà nulla $forall t$ date le _hp._ del problema.

== Th. di Kelvin
Sotto hp. $" "\uunderline(nabla)dot underline(u)=0" "$ , _effetti viscosi trascurabili_, $" " underline(f)=underline(nabla)E$.

Allora la circolazione associata ad una linea materiale non cambia nel tempo.
$ d/(d t)integral_gamma underline(u)dot hat(tau)d l = (d Gamma)/(d t)=0 $

Ricordando il teorema di derivazione sotto il segno di integrale:
$ d/(d t)integral_l underline(F)dot hat(tau) d l = integral_l (diff underline(F))/(diff t) + underline(nabla)times underline(F)times underline(v_c) +\ + underline(F)(underline(x)_c (1,t),t)dot underline(v)_c (1,t) - underline(F)(underline(x)_c (0,t),t)dot underline(v)_c (0,t) $

Dove i termini $underline(v)_c$ indicano la velocità del contorno. Poichè la linea di interesse è chiusa, i termini valutati in $s=0$ e in $s=1$ sono uguali e opposti.

Applicando tale teorema si ottiene:
$ d/(d t)integral.cont_l underline(u)dot hat(tau)d l=integral.cont_l (diff underline(u))/(diff t) + underline(nabla)times underline(u)times underline(u)= \ =-integral.cont_l underline(nabla)(1/2 underline(u)+p/rho) = 0 $
Risulta dimostrato essendo che l'integrale di un gradiente su linea chiusa è uguale a 0.

== Def. Tubo Vorticoso

Il tubo vorticoso è formato da linee vorticose. Se prendiamo una porzione chiusa come volume di controllo di tale tubo possiamo scrivere:

$ integral_Omega underline(nabla)dot underline(omega)=0 arrow.r.long^(D i v)integral.cont_(diff Omega)underline(omega)dot hat(n)= \ = integral_A underline(omega)dot hat(n)_A + integral_B underline(omega)dot hat(n)_B + integral_(S_l) underline(omega)dot hat(n)_(s_l) =0 $

Pertanto 
$ integral_A underline(omega)dot hat(n)_A = - integral_B underline(omega)dot hat(n)_B " "arrow.r.double.long " " Gamma_A = Gamma_B $

La circolazione si conserva lungo un tubo vorticoso. Se il tubo vorticoso c'è, non si elide mai, a meno che esso non si richiuda su se stesso.

Tale proprietà discende dal fatto che la vorticità è per definizione un _campo perfettamente solenoidale_.

== III Th. di Helmholtz
Sotto hp. $" "\uunderline(nabla)dot underline(u)=0" "$ , _effetti viscosi trascurabili_, $" " underline(f)=underline(nabla)E$.

Allora la circolazione, che per _Kelvin_ è costante lungo il tubo vorticoso, è costante anche nel tempo.

= Correnti incomprimibili attorno a \ corpi aerodinamci

Il _I th. di Helmholtz_ ci dice che una particella di fluido con $underline(omega)=0$ a monte, si mantiene a vorticità nulla finchè gli effetti viscosi sono trascurabili.

Il modello matematico nella zona irrotazionale sarà dato da:
$ cases(
  underline(nabla)times underline(u)=0,
  underline(nabla)dot   underline(u)=0
) " "+" " underline(u)dot underline(n)|_(diff Omega)=b $

Tali equazioni sono già sufficieti per trovare $underline(u)$, tali equazioni solo _lineari_.
$ underline(nabla)dot underline(u)=(diff u)/(diff x)+(diff v)/(diff y)+(diff w)/(diff z)=0 $

$ underline(nabla)times underline(u) = mat(hat(x),hat(y),hat(z); diff/(diff x),diff/(diff y),diff/(diff z); u,v,w) $
Nel caso bidimensionale:
$ cases(
  (diff u)/(diff x) + (diff v)/(diff y) = 0,
  (diff v)/(diff x) - (diff u)/(diff y) = 0
)
arrow.r.long
cases(
   (diff)/(diff x)lr(((diff u)/(diff x) + (diff v)/(diff y)))=0,
   (diff)/(diff y)lr(((diff v)/(diff x) - (diff u)/(diff y)))=0
) $

Da cui si ottiene

$ (diff^2 u)/(diff x^2) + (diff^2 v)/(diff y^2) arrow.double.r.long nabla^2u=0 $

Se deriviamo in maniera opposta e sommiamo le equazioni tra loro troviamo $nabla^2 v=0$. Entrambe le componenti $u$ e $v$ soddisfano l'equazione di _Laplace_ e sono pertanto dette *funzioni armoniche*.

Se il campo di velocità è irrotazionale e aggiungiamo l' _hp._ di *dominio semplicemenete connesso*, allora possiamo riscrivere il campo vettoriale $underline(u)$ come potenziale cinetico:
$ underline(u)=underline(nabla)phi $

Ma tale campo vettoriale è anche solenoidale, pertanto
$ underline(nabla)dot underline(u) = underline(nabla)dot (underline(nabla)phi)=nabla^2 phi=0 $
Pertanto anche il potenziale cinetico $phi$ è una funzione armonica. Per quanto riguarda la _BC_ 
$ underline(u)dot underline(n)=b arrow.double.r.long underline(nabla)phi dot underline(n) = (diff phi)/(diff n) = b $

Pertanto otteniamo un problema di _Neumann_ con condizione sulla derivata prima
$ cases(
  nabla^2 phi=0,
  lr((diff phi)/(diff n)) = b
) $

Sapendo che esiste anche la funzione di corrente nel caso 2D.
$ u = (diff psi)/(diff y) " ; "" " v= -(diff psi)/(diff x) $
Notando che
$ underline(nabla)times underline(u) = (diff v)/(diff x)-(diff u)/(diff y)=(diff^2 psi)/(diff x^2)+(diff^2 psi)/(diff y^2)=nabla^2psi $

Anche $psi$ è una funzione armonica.

Si considerei ora _Navier-Stokes_ per la quantità di moto:
$ (diff underline(u))/(diff t)+(underline(u)dot underline(nabla))underline(u)+1/rho underline(nabla)p=-underline(nabla)E $
Sviluppando $(underline(u)dot underline(nabla))underline(u)$
$ (diff underline(u))/(diff t)+cancel(underline(nabla)times underline(u)times underline(u))+1/2underline(nabla)abs(underline(u))^2+1/rho underline(nabla)p=-underline(nabla)E $
Considerando il potenziale cinetico $underline(nabla)phi=underline(u)$
$ underline(nabla)underbrace(lr(((diff phi)/(diff t)+abs(underline(nabla)phi)^2/(2)+p/rho +E)),"Quadrinomio di Bernoulli")=0 $
== I th. di Bernoulli
Sotto hp. di $" "\uunderline(nabla)dot underline(u)=0" "$ , _effetti viscosi trascurabili_, $" " underline(f)=underline(nabla)E$, _corrente irrotazionale_.

Il quadrinomio di _Bernoulli_ si conserva nello spazio.
\ \
Nel nostro caso le forze di volume sono spesso trascurabili e si ottiene dunque 
$ (diff phi)/(diff t)+abs(underline(nabla)phi)^2/(2)+p/rho = "cost" $

== Il paradosso instazionario
$ cases(
  nabla^2phi=0,
  lr((diff phi)/(diff n)) = b(underline(r),t)
) $
Siccome nel modello non ci sono derivate temporali, il potenziale si adatta _istantaneamente_ alle condizioni al contorno e non è influenzato dalla storia. Tale scenario non è fisicamente plausibile.

Il modello matematico è sempre dato da $ "Potenziale"+"Strato limite"+"Scia" $
In realtà, la storia di una corrente di questo tipo è nella zona rotazionale quindi nella scia.

== Avviamento di un profilo
Nella fase di avviamento 
$ underline(v) =U_infinity "sca"(t) $
Il th. di Kelvin dice che
$ (d Gamma_(l m)(t))/(d t) =0 $
Dove _lm_ è la linea materiale, tale scenario è riconducibile ad un aereo fermo sulla pista che parte da fermo. Dobbiamo tenere conto dei seguenti fatti fisici
$ cases(
  (diff underline(u))/(diff t) = -(underline(u)dot underline(nabla))underline(u)-underline(nabla)p+1/(R e)nabla^2 underline(u),
  underline(nabla)dot underline(u)=0
) 
$
I tempi caratteristici di tali termini
- $T_t=L/U_infinity$ , tempo caratteristico del trasporto
- $T_m=L/c$ , tempo caratteristico della massa, onde di pressione
- $T_v=L^2/nu$ , tempo caratteristico della diffusione

Vediamone i rapporti
$ T_t/T_nu = (L/U_infinity)/(L^2/nu)=nu/(L U_infinity)= 1/(R e) $
Nelle nostre applicazioni $R e>>1$ quindi $T_t<<T_nu$, il trasporto è molto più rapido della diffusione
$ T_t/T_m = (L/U_infinity)/(L/c)=c/U_infinity= 1/(M_a) $
In campo incomprimibile $M_a<<1$ quindi $T_t>>T_m$, la conservazione della massa è molto più rapida del trasporto.
In ordine:
+ Conservazione della massa,
+ Trasporto,
+ Diffusione

= Analisi complessa
Una breve introduzione ad alcuni teoremi di analisi complessa.
== Serie di Laurent
Come visto la serie di _Taylor_ è valida solo se le funzioni espanse sono analitiche. Tuttavia, tipicamente le funzioni di maggiore interesse non sono analitiche in tutto il dominio.

Supponiamo che $f(z)$ sia NON analitica in un disco, ma che lo sia in una regione anulare A, delimitata da due circonferenze concentriche, centrate in $z_0$  ed aventi raggio rispettivamente $r$ e $R$, con $r<R$.
Assumiamo che $f(z)$ sia analitica all'interno di questi cerchi concentrici e nella regione anulare A.
#set align(center)
#circle(radius: 50pt,
        fill: red,
        stroke: black,
        inset:  10pt,
      )[#set align(center + horizon) 
      #circle(radius: 15pt,
      stroke: black,
      fill: white)
      ]
#line(start: (14pt,-60pt),
length: 15pt)
#line(start: (34pt,-71pt),
length: 50pt,
angle: -45deg)
#path(fill: none,
stroke: black,
closed: true,
(0pt,-50pt),
(0pt, -90pt),
(20pt, -120pt),
(50pt,-100pt),
(45pt, -70pt),
)
#set align(left)

Allora esiste un'unica rappresentazione di $f(z)$ in serie di _Laurent_:
$ f(z)=sum_(n=0)^infinity a_n(z-z_0)^n + sum_(n=1)^infinity (b_n)/(z-z_0)^n $
dove, se chiamiamo $c_1:|z-z_0|<r$ e $c_2:|z-z_0|<R$
$ a_n = 1/(2 pi i)integral_(c_2)(f(xi)d xi)/((xi-z_0)^(n+1)) $
$ b_n = 1/(2 pi i)integral_(c_1)(f(xi)d xi)/((xi-z_0)^(1-n)) $
Il termine della serie $sum_(n=1)^infinity (b_n)/((z-z_0)^n)$ è detta *parte principale* in quanto in sua assenza la serie di _Laurent_ sarebbe una semplice serie di potenze.
\
\
=== Definizione

$f(z)$ è analitica a infinito se $f(1slash tau)$ è analitica per $tau=0$
\
\
=== Definizione Residuo
Sia $f(z)$ una funzione analitica in un dominio a meno di una singolarità in $z_0$.Il coefficiente $b_1$ della sua serie di _Laurent_ è detto *residuo di f(z) in $z_0$*

Per un polo di ordine $m$
$ "Res"(z_0) =b_1=1/(m-1)!lim_(z arrow.r z_0)(d^(m-1))/(d z^(m-1))[(z-z_0)^m f(z)] $

\
===Teorema del Residuo di Cauchy

Sia $f(z)$ analitica su un dominio semplice e chiuso C, eccetto per un numero *finito* di singolarità poste all'interno di C. Allora:
$ integral_C f(z)d z= 2pi i sum_(i=1)^n "Res"(z_i) $
dove $z_i$ sono le singolarità isolate e C è percorso in senso positivo.

= Aerodinamica del profilo alare
Consideriamo il problema esterno dove la corrente è irrotazionale.
$ cases(
  underline(nabla)dot underline(u)=0,
  underline(nabla)times underline(u)=0
) arrow.double.r.long nabla^2phi=nabla^2psi=0 $
Dobbiamo poi ipotizzare che il campo sia _bidimensionale_ per poter definire $psi$. Inoltre, il campo deve essere _stazionario_.

Definiamo un _potenziale complesso_ funzione della posizione $z$ nel piano complesso, tale che:
$ f(z) = f(x+i y)=phi(x,y)+i psi(x,y)$
Essendo f(z) analitica, possiamo derivarla

$ (d f)/(d z)=(diff phi)/(diff x)+ i  (diff psi)/(diff x) = lr(((diff phi)/(diff y)
+i(diff psi)/(diff y)))(-i) $

pertanto 
$ (d f)/(d z)=u-i v=u-i v = w(z) " , Velocità complessa" $
Effettivamente torna e si ha
$ w(z)=overline(u)(z) $
Tra le ipotesi fatte per definire il potenzial c'era quella di *dominio monoconnesso* nel caso reale. Passando all'analisi complessa è sufficiente l'ipotesi di *irrotazionalità* per definire $phi$. Poi useremo anche l'incomprimibilità per ottenere funzioni armoniche.

Dobbiamo capire come rappresentare la corrente attorno al profilo.
Per le ipotesi sull'esistenza ed unicità della *serie di Laurent* possiamo vedere il profilo come una regione dove la velocità complessa è non analitica, mentre lo è in un anello grande a piacere, in quanto sotto ipotesi di _corrente stazionaria_ il campo di velocità non presenta singolarità nelle zone indisturbate. Inoltre, a meno del contorno del dominio ad anello, la serie di Laurent *converge uniformemente*.

Possiamo rappresentare la velocità complessa come 
$ w(z)=sum_(-infinity)^(infinity) a_n z^n=sum_(-infinity)^0 c_n z^n = c_0 + sum_(n=1)^infinity c_n/z^n  $

La forma più generale ed interessante è 
$ w(z)=sum_(n=-infinity)^0 c_n z^n $
Che è stata ottenuta sfruttando il teorema che ci dice che se tale funzione
è  uniformemente convergente a infinito, allora $a_n=0 "," n>=1 $.
Tale teorema si applica considerando come dominio un generico contorno contenente
il profilo. Siccome la corrente all'infinito ha velocità costante, la funzione è 
limitata.

Tale velocità complessa vale per ogni profilo e può essere vista come lasomma 
di infinite correnti semplici della forma
$ w(z) = c_0 + c_1/z + c_2/z^2 + ... $
Si noti che il termine $c_o$ sarà legato alla corrente uniforme. Al crescere 
di n in modulo i termini della serie decadono sempre più rapidamente. Questo
significia che la cosa più evidente è la corrente uniforme, le altre sono 
sfumature sempre meno evidenti che però condizionano la corrente.
\
\
\

== Soluzioni dell'equazione di Laplace

$ f(z)=c_0z+k+c_1log(z)-c_2/z-1/2 c_3/z^2 - ... $
Passiamo in rassegna i vari coefficienti

=== $c_0z$
$ psi(x,y) = "Im"{c_0z} = c_0^r y+ c_0^i x $
Le linee di corrente di tale potenziale sono un fascio di rette improprio.
Prendendo le linee di corrente 
$ y=-c_0^i/c_0^r x+k/c_0^r $ 
Pertanto il coefficiente angolare delle linee di corrente vale 
$ m=-c_0^i/c_0^r $
il meno è legato al fatto che la velocità complessa è il complesso coniugato 
della velocità. Tale velocità è dunque in realtà specchiata rispetto all'asse 
reale. 
Per dare incidenza al profilo possiamo ruotare $w(z)$ di $-alpha$ e  porre il 
profilo ad "incidenza nulla" 
$ tilde(w)(z) = e^(-i alpha)w(z) $
Si noti che la velocità reale viene ruotata di $alpha$ in qunato è il complesso
coiugato del vettore velocità reale.

=== $c_1/z$
$ f(z)=c_(-1)log(z)=c_(-1)(log(rho)-i theta) $ 
$ psi="Im"{f(z)} $
Se $c_(-1) in RR$, è una sorgente o pozzo
$ psi_1 = c_(-1)theta $
Se $c_(-1) in CC$, è un vortice irrotazionale
$ psi_2=c log(rho) $

Per definizione della circolazione e della portanza
$ cases(Gamma=integral.cont underline(u)dot hat(tau),
Q = integral.cont underline(u)dot hat(n)) $
Se vogliamo calcolarli in analisi complessa
$ integral.cont w d z=integral (u-i v)(d x+d y)= \
=integral(u d x+v d y)+i integral(-v d x+u d y)=Gamma + i Q $

L'integrale $integral.cont w(z)d z$ non è pari al potenziale complesso in 
quanto in queste funzioni vi è sempre almeno una singolarità e se noi prendiamo
un percorso chiuso che la contiene, *non* possiamo usare il teorema di *Morero*
e la funzione non è detto che ammetta una primitiva.

Se vogliamo calcolare circolazone e portata associati ad un profilo alare possiamo
prendere un circuito che racchiuda il profilo, ad una distanza almeno pari
alla corda dal suo centro, al fine di garantire la convergenza uniforme della
serie di Laurent.

$ Gamma+ i Q= integral.cont w d z= integral.cont(c_0+c_(-1)/z+c_(-2)/z^2+...)d z=\ 
Gamma +i Q=2 pi i c_(-1) $

=== $c_(-2)/z^2$

$ psi = "Im"{-c_(-2)/z}="Im"{-c_(-2)(x-i y)/(x^2+y^2)} $
Se $c_(-2) in RR $ 
$ psi_1 = c_(-2)y/(x^2+y^2)=k $
se $ k=0 arrow.double.r.long y=0 $
\
se $ k != 0 arrow.double.r.long x^2+y^2-c_(-2)/k y=0 $

Che risula essere la soluzione della doppietta, corrispondente a due coppie di 
circonferenze centrate sull'asse immaginario.

Se uniamo queste soluzioni possiamo ottenere delle soluzioni di particolare 
interesse come l'ogiva di Rankine formata da una corrente uniforme e una sorgente.
Tale proprietà deriva dalla linearità del Laplaciano.
\
\

== Azioni su corpi solidi
Sfruttiamo un bilancio della quantità di moto con Eulero nella zona esterna
$ d/(d t)integral_Omega rho underline(u)=integral.cont_(diff Omega)-p hat(n)-
integral.cont_(diff Omega)rho underline(u)(underline(u)dot hat(n)) $

Se il problema è stazionario, la variazione della quantità di moto è nulla 
e pertanto siottiene un'equazione di bilancio

$ underline(F)_c = -integral.cont_(diff Omega)p hat(n)-integral.cont_(diff 
Omega)rho underline(u)(underline(u)dot underline(n))  $

Tale relazione vale sotto ipotesi di:
+ Corrente stazionaria 
+ Corrente incomprimibile
+ Viscosità trascurabile

Se aggiungiamo l'ipotesi di irrotazionalità, vale Bernoulli
$ p+1/2 rho abs(underline(u))^2 = c $
Sostituendo p nella conservazione della qdm e considerando che l'integrale 
di una costante su un circuito chiuso è nulla otteniamo:
$ integral.cont_(diff Omega)-p hat(n) = integral.cont_(diff Omega=l)1/2
rho(u^2+v^2)hat(n)d l $
$ underline(F)_c=rho/2integral.cont_l lr([hat(x)(-(u^2-v^2)d y+2u v d x)+\
+hat(y)(-(u^2-v^2)d x-2 u v d y)]) $

Noi vogliamo esprimere la forza $F_c$ con i numeri complessi. 
$ integral.cont_l w^2d z=integral.cont_l (u-i v)^2(d x+i d y)=\
=integral.cont lr([((u^2-v^2)d x+2 u v d y)+i((u^2-v^2)d y - 2u v d x)]) $

Pertanto 
$ integral.cont_l w^2d z = -2/rho F_(c y)-2/rho i F_(c x) $
Provando a moltiplicare per $i$

$ F_(c x)-i F_(c y)=i rho/2 integral.cont_l w^2d z $
Abbiamo ricavato la *I formula di Blasius*.

== Calcolo del momento aerodinamico
Sotto le seguenti ipotesi:
+ Corrente stazionaria 
+ Corrente incomprimibile
+ Viscosità trascurabile 
La II cardinale ci diche che
$ (d Gamma)/(d t)=underline(M) $
dove $underline(Gamma)$ per un fluido reale vale
$ underline(Gamma)=integral_Omega underline(r)times rho underline(u)d V $
Con l'ipotesi di corrente stazionaria e sapendo che dalla III legge della 
dinamica $underline(M)_f=-underline(M)_c$

$ underline(M)_c=-integral.cont_(diff Omega) p underline(r)times hat(n)d s-
 integral.cont_(diff Omega)rho (underline(r)times underline(u))(underline(u)
dot hat(n))d s $

Svolgendo il calcolo vettoriale otteniamo
$ M_c = integral.cont_l -p(-x d x-y d y)-integral.cont_l rho(x v-y u)(u d y-v d x) $
Introducendo l'ipotesi di irrotazionalità possiamo usare Bernoulli,
$ p=c-1/2 rho(u^2+v^2) $
I calcoli non sono riportari, si procede volendo ricondursi al calcolo complesso
calcolando quindi $integral.cont_l w^2z d z$

Pertanto 
$ M_c = -rho/2 "Re"{integral.cont_l w^2z d z} $
*II formula di Blasius*
\
\

== Teorema di Kutta-Joukowsky
Calcoliamo forza e momento agenti su un generico profilo alare

$ cases(F_x -i F_y=i rho/2 integral.cont w^2 d z,
M_c =-rho/2 "Re"{integral.cont w^2 z d z}) $
Scrivo $w(z)$ in serie di Laurent 
$ w(z)=c_0 +c_(-1)/z+c_(-2)/z^2+... $
Calcolo il primo integrale ed uso il metodo del residuo
$ i rho/2 integral.cont w^2 d z= i rho/2 2 c_0c_(-1)2pi i= -2pi rho c_0c_(-1)  $
Ma $c_0=U_infinity$, $c_(-1)=Gamma/(2pi i)$ da cui 
$ F_x +i F_y = i rho Gamma U_infinity $

Pertanto 
$ cases(F_y=-rho Gamma U_infinity, F_x=0) $

Calcoliamo il momento, svolgiamo l'integrale ed utilizziamo nuovamente il metodo
del residuo 
$ integral.cont w^2z d z=(c_(-1)^2+2 c_0 c_(-2))2pi i $
Da cui 
$ M_c = -rho/2 "Re"{(c_(-1)^2+2c_0c_(-2))2pi i} $

ma $c_0=U_infinity$ , $c_(-1)=Gamma/(2pi i)$ mentre $c_(-2)$ rimane incognito.
$ M_c=-rho/2"Re"{2pi i(-Gamma^2/(4pi^2) +2U_infinity c_(-2))} $

Si osservi che il  momento aerodinamico dipende da $c_(-2) in CC$. Ciò significa 
che $M_c$ non è indipendente dalla forma del profilo. Siccome il momento e le 
forze sono calcolate rispetto ad un _SR_ ed il momento $M_c$ è centrato nell' 
origine di tale sistema, allora la portanza non ha momento e si ottiene 
$ M_c=-rho/2 "Re"{4pi i U_infinity c_(-2)} $

Si noti che nel caso in cui si abba una corrente attorno ad un cilindro, 
$c_(-2) in RR$ ed il momento è nullo.
\
\
Vogliamo ora capire come impiegare la soluzionesemplice del cilindro per il 
nostro caso  di interesse. Prima di farlo però, si ricordi che 
$ a,b in  CC arrow.double.r a dot b = rho e^(i theta) dot r e^(i phi)=
rho r e^(i(theta+ phi)) $

Una *funzione analitica* può essere vista come una *trasformazione* 
da un piano complesso ad un altro. 

Se $z=f(xi)$ è analitica, allora la trasformazione è *conforme*, 
l'angolo tra due vettori si *conserva* tra i due piani.

Supponendo i vettori infinitesimi, la loro posizone può essere espressa come:

$ xi_i=xi_0+d xi_i $
sfruttando il fatto che $xi=rho e^(i theta)$ 
$ cases(xi_1=xi_0+ d rho e^(i theta_1),
xi_2=xi_0+d rho e^(i theta_2))
arrow.double.r.long 
cases(d xi_1=d rho e^(i theta_1),
d xi_2=d rho e^(i theta_2)) $
Applicando la funzione, si ha $z_0=F(xi_0)$. Sviluppando:
$ cases(z_1=F(xi_1)=F(xi_0)+(d F)/(d xi) d xi_1+...,
z_2=F(xi_2)=F(xi_0)+(d F)/(d xi) d xi_2+...) $
Ma siccome 
$ cases(d z_1=z_1-z_0=(d F)/(d xi)d xi_1+...,
d z_2=z_2 - z_0 = (d F)/(d xi)d xi_2+...) $

Se vogliamo esprimere l'angolo tra i due vettori in ogni piano, possiamo 
farne il rapporto. In questo modo 
$ (d xi_2)/(d xi_1)=e^(i(theta_2-theta_1))=(d z_2)/(d z_1) $
Che conferma il fatto che _F_ sia una trasformata conforme. 

Si noti che la semplificazione del termine $(d F)/(d xi)$ è possibile *solo se*
tale derivata è non nulla. Pertanto, le funzioni analitiche sono trasformazioni
conformi se la loro derivata è non nulla. 

Se la funzione è anlatica ovunque, noi non possiamo passare dal cilindro alla 
forma del profilo, in quanto quest'ultimo presenta un punto angoloso in 
corrispondenza del bordo d'uscita. Dobbiamo fare in modo che la funzione non sia 
analitica ovunque. 

Dobbiamo capire come costruire lafunzione analitica corretta, che sia anche 
non analitica in un punto. Conosciamo il potenziale attorno al cilindro, in 
questo caso nel piano $xi$ 
$ Phi(xi(z))=f(z) $
$ w(z)=(d F)/(d z)=(d Phi(xi(z)))/(d z)=(d Phi)/(d xi)(d xi)/(d z)=(W(xi))/(d z 
slash d xi)  $
Sapendo che 
$ z=F(xi) arrow.r.long (d z)/(d xi)=F^'(xi) $
da cui 
$ w(z)=lr((W(xi))/(F^' (xi))|)_(xi=xi(z))=w(z(xi)) $

Le proprietà che richiediamo alla funzione $z(xi)$ di trasformazione sono:
+ $z(xi)$ analitica fuori dalla circonferenza $abs(xi-xi_0)>a$ 
+ Affinchè le correnti siano asintoticamente uguali richiediamo che:
$ lim_(xi arrow.r infinity)W(xi)=lim_(z arrow.r infinity) w(z)=lim_(z arrow.r 
infinity)(W(xi))/(d z slash d xi) $
Ciò si tradue nel chiedere che $(d z)/(d xi)=1$

Queste due ipotesi ci permettono di sviluppare in serie di Laurent con 
$c_n=0$ per $n>1$. Pertanto
$ z(xi)=c_1 xi+c_0+(c_(-1))/xi+c_(-2)/xi^2+... $
ma $c_1=1$ poichè $lim_(z arrow.r infinity) (d z)/(d xi)=1$

Vogliamo capire se la trasformazione garantisce la validità delle condizioni 
al contorno di non compenetrabilità. Si prendano due punti $xi_1$ e $z_1$: 
vogliamo vedere come variano gli angoli da un piano all'altro.

$ z_1+d z=z_1(xi_1+d xi)=z(xi_1)+lr((d z)/(d xi)|)_(xi=xi_1) d xi+... $
quindi 
$ d z=z_1+d z-z_1=lr((d z)/(d xi)|)_(xi=xi_1)d xi=b e^(i alpha)d xi $
Dunque la superficie ruota di un angolo $alpha$ passando dal piano di studio 
a quello fisico. Per la velocità invece
$ w(z_1)=W(xi_1)/(d z slash d xi|_(xi=xi_1))=W(xi_1)/b e^(-i alpha) $

Pertanto la velocità complessa ruota di $-alpha$, ma dunque la velocità reale 
ruota di $+alpha$, in accordo con la superficie. La condizione di non 
compenetrazione rimane valida. 

Tale condizione è verificata per tutti i punti di analiticità del dominio fisico.
Tuttavia, i profili sono dotati di un bordo d'uscita aguzzo al fine di imporre 
uan circolazione *sempre nello stesso verso* e costante.

Vediamo cosa succede sul bordo d'uscita.
$ w(z_(b u))=W(xi_(b u))/((d z)/(d xi)|_(xi=xi_(b u))) $
Tuttavia, per avere il bordo d'uscita spigoloso, la derivata al denominatore 
è nulla. Tuttavia, la velocità $w(z_(b u))$ in questo modo tenderebbe all'infito.
Dobbiamo quindi bilanciare, imponendo che 

$ W(xi_(b u))=0 $
Dove $xi_(b u)$ è il punto di ristagno sul cilindro. Tale relazione prende il 
nome di *condizione di Kutta*.

Dunque la condizione di Kutta ci dice anche che il bordo d'uscita è  un 
*punto di ristagno* per il cilindro. 


Vogliamo capire cosa succede alla circolazione quando si passa al piano fisico.

$ integral.cont w d z=integral.cont W(xi)/(d z slash d xi) (d z)/(d xi) d xi=
integral.cont W(xi)d xi=Gamma+i Q $

Dunque per Kutta-Joukowsky la *portanza* è la stessa.

Calcoliamo ora il *momento aerodinamico* sfruttando la II relazione di Blasius. 
Dobbiamo prima trovare il campo di moto nel piano di riferimento.
$ W(xi)=U_infinity (1-a^2/xi^2)+Gamma/(2pi i xi) $
dobbiamo inserire un parametro per regolare l'incidenza del profilo. 
Per farlo, ruotiamo la velocità complessa e anche il SR.
$  W(xi)=U_infinity (e^(-i alpha)-(a^2 e^(i alpha))/xi^2)+Gamma/(2pi i xi) $
Inoltre, non sapendo se il centro è nell'origine dobbiamo traslaro con 
$(xi-xi_0)$ dove $xi_0$ è il centro della circonferenza.
$ W(xi)=U_infinity (e^(-i alpha)-(a^2 e^(i alpha))/(xi-xi_0)^2)+Gamma/(2pi i (xi-xi_0)) $

Ricordando Blasius
$ M_a=-rho/2 "Re"{integral.cont w^2z d z}=-rho/2"Re"{integral.cont W(xi)/(d z slash d xi) z(xi) d xi} $

Ma 
$ z(xi)=xi+c_0+c_(-1)/2+c_(-2)/z^2+... $

Tuttavia la derivata è al denominatore e dobbiamo calcolare l'inversa di $z^'$:
$ 1=z^'dot (z^')^(-1)=1+D_(-1)/xi-C_(-1)/xi^2+D_(-2)/xi^2+... $
Da cui si ottengono le condizioni 
$ cases(D_(-1)=0, -C_(-1)+D_(-2)=0 arrow.r.long D_(-2)=C_(-1)) $
Pertanto trascurando i termini di ordine superiore
$ z^'=1+C_(-1)/xi+... $

Se vogliamo usare il teorema del residuo, tutte le espansioni devono essere 
centrate nello stesso punto. Dobbiamo scrivere $W(xi)$ come espansione centrata 
in $xi=0$ anzichè in $xi=xi_0$- 

Per farlo sfruttiamo la definizione della serie geometrica per $abs(t)<1$:
$ 1/(1-t)=sum_(n=0)^infinity t^n " ; " " " 1/(1-t)^2=sum_(n=1)^infinity n t^(n-1) $

Nel nostro caso:
$ 1/(xi-xi_0)=1/xi + xi_0/xi^2 +... $
$ 1/(xi-xi_0)^2 = 1/xi^2 +(2 xi)/xi^3 + ... $

Tornando al momento e aggiungendo questi termini per la traslazione ed espansione 
otteniamo dopo una serie di calcoli il seguente risultato:
$ M_0=-rho/2"Re"{2 U_infinity Gamma e^(-i alpha)(xi_0+c_0)+4 pi i c_(-1)
U_infinity e^(-2 i alpha)}  $
\
\
\
\
\
== Trasformazione di Joukowsky

Abbiamo ora tutti gli strumenti per determinare una trasformata conforme che ci 
consenta di passare da un piano analitico a quello fisico 
$ z=xi+l^2/xi $
La quale presenta una singolarità in $xi=0$. Pertanto, il cilindro nel piano $xi$ 
*deve contenere* l'origine in quanto vogliamo che all'esterno del cilindro il 
campo sia analitico. Vediamo cosa succede alla derivata, 
$ (d z)/(d xi)=1-l^2/xi^2=0 arrow.double.r.long xi=plus.minus l $
Il parametro $l$ rappresenta la distanza dei punti critici dall'origine. Sapendo che 

$ w(z)=W(xi(z))/(d z slash d xi|_(xi(z))) $
dobbiamo capire come è fatta $xi(z)$. Invertiamo $z(xi)$ 
$ z= (xi^2+l^2)/xi $ 
$ xi_(1,2)=(z plus.minus sqrt(z^2-4 l^2))/2 $

Ma nel campo complesso la radice quadrata è una funzione polidroma. Dobbiamo 
cercare i branch point che, in questo caso, sono la soluzione dell'equazione
che annulla il radicando 
$ z^2-4 l^2=0 arrow.r z_(1,2)=plus.minus 2 l $
E' fondamental ora definire il *branch cut*, che deve necessariamente congiungere
i due branch point. Se ciò on viene fatto è probabile che si giunga a risultati 
assurdi, legati al fatto che magari la funzione ha preso la soluzione sbagliata, 
dato che è polidroma. 

Se il branch cut va fuori dal corpo, si hanno delle discontinuità nella velocità
complessa. Tipicamente si esegue un branch cut diretta tra i due branch point.

E' possibile centrare il cilindro in diversi punti nel piano $xi$, affinchè siano 
soddisfatti i seguenti requisiti:
+ Essa deve contenere le singolarità $xi=0$;
+ Essa deve contenere o al più essere tangente alle singolarità legate all'annullamento dell derivata.
Vi sono vari casi, di cui sono riportate le soluzioni:
+ Circonferenza con $x_0=0" , " a=l$ che risulta essere $ xi=2l cos(theta)$
+ Circonferenza con $x_0=0" , " a>l$ risulta un ellisse con fuochi in $plus.minus 2 l$ 
     l'ellisse tuttavia non presenta punti angolosi pertanto non è possibile imporre
        la condizione di Kutta e non è possibile definire $Gamma$
+ Circonferenza traslata passante per $plus.minus l" , " xi_0=i h" , "a>l$ risulta
    essere un arco di circonferenza che descrive la linea media del profilo. 
    L'arco di circonferenza ottenuto risulta essere un branch cut valido.

\
\
\
\
    == Calcolo della portanza di un profilo di Joukowsky 

Noi non cosnosciamo la circolazione sul cilindro in quanto non sappiamo dove si 
trovano i punti di ristagno. Dobbiamo fare in modo che tale punto critico sia imposto

$ W(xi)=U_infinity (e^(-i alpha)-a^2/(xi-xi_0)^2 e^(i alpha))+Gamma/(2pi(xi-xi_0)) $
Ma noi vogliamo che $W(xi=l)=0$

Il vettore $+l$ può essere scritto come somma di due vettori 
$ l=xi_0+a e^(i theta r) $
dunque 
$ Gamma=-2pi i(l-xi_0)U_infinity (e^(-i alpha)-(a^2e^(i alpha))/(l-xi_0)^2)= $
$ Gamma=-4pi U_infinity a sin(alpha-theta_r) $

Dunque imponendo la condizione di Kutta abbiamo determinato la circolazion.
$ L=-rho U_infinity Gamma= 4pi rho U_infinity^2a sin(alpha-theta_r) $
Possiamo poi ricavare il coefficiente di portanza 
$ C_L=2pi sin(alpha-theta_r) $
Per una lastra piana $theta_r=0$ quindi ad $alpha=0$ il $C_L=0$.

Nel caso di un profilo simmetrico la circonferenza ha centro sull'asse reale e 
comprende al suo interno il punto critico $-l$.
Definendo $m$ il centro della circonferenza 
$ A=-m-a=-2m-l $
$ z_(b a)=((-2m-l)^2+l^2)/(-2m-l)=-2 (2m^2+2m l+l^2)/(2m+l) $
Quindi 
$ c=-z_(b a)+2l=4 (m+l)^2/(2m+l) $
Possiamo quindi valutare il $C_L$ 
$ C_L=8pi (2m+l)/(4(m+l)^2) (m+l)sin(alpha-theta_r) $
$ C_L=2pi (2m+l)/(m+l) sin(alpha-theta_r)  $

Questa soluzione vale per angoli piccoli.
\
\

== Trasformazione di Karman-Trefftz 

L'utilità della trasformazione di Joukowsky termina con quanto fatto. 
Dobbiamo capire come trovare una trasformazione priva del bordo d'uscita aguzzo.
La trasformazione di Joukowsky può essere scritta come 
$ (z-2l)/(z+2l)=(xi-l)^2/(x+l)^2 arrow.r.long (z-n l)/(z+n l)=(xi-l)^n/(xi+l)^n $

dove 
$ n=(2pi-tau)/pi $
Pertanto si aggiunge un ulteriore parametro che ci consente di fare un passo avanti.

L'idea è quella di scomporre la trasformata in più trasformazioni intermedie.
La prima trasformata viene scritta mediante *serie di Fourier*, in quanto essa consente
facilmente di mappare la parte della circonferenza che non presenta criticità
e consente di rappresentare bene ogni tipo di profilo. La parte critica del 
bordo d'uscita viene effettuata, invece, da *Karman-Trefftz*.

Non possiamo mappare direttamente il profilo con K-T in quanto non si riuscirebbero
a cogliere tutti i dettagli del profilo. 

Si noti che la trasformata di _Karman-Trefftz_ presenta un'ostilità legata 
al fatto che se n è razionale, compare sempre una radice e quindi la funzione 
è polidroma. Inoltre, se $n in R$ ed in particolare se n è irrazionale si 
hanno infinite soluzioni .

Le trasformazioni conformi ci permettono di studiare precisamente la corrente esterna 
su qualsiasi profilo. Tuttavia, talvolta non è semplice ed immediato lo 
studio di un profilo.
Vogliamo cercare una teoria che ci consenta, in modo approssimato,
ci dia delle *indicazioni qualitative*. 

