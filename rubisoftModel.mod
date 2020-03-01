option solver cplex;

# N.B.: il codice di seguito usa nomi compatti al fine di ridurre la verbosità. Sono presenti dei commenti, ma per comprendere al meglio il codice consultare la relazione allegata.

#Insiemi
set V; # videogiochi
set I; # tipi di impiego
set R; # ruoli
set E; # motori grafici

#Variabili
var X{I, V} >= 0 integer; # num programmatori
var Y{I, V} >= 0 integer; # num artisti
var Z{I, V} >= 0 integer; # num level designer
var P{E, V} binary; # scelta motore grafico
var W{E, V} >= 0 integer; # quantita� licenze singole
var Q{E, V} binary; # licenza royalty
var S{V} binary; # problemi nel team
var T{V} binary; # dimensione critica
var U{V} binary; # presenza dipendenti
var O{V} binary; # microtransazioni

#Parametri
param hn{R,V} > 0 integer; # ore necessarie in una certa area
param dl{V} > 0; # scadenza in mesi
param qc{V} >= 0 integer; # copie vendute
param cc{V} >= 0; # prezzo per copia
param d{R} >= 0, integer; # dipendenti per ruolo
param st{R} > 0, integer; # stipendi professionisti
param hm > 0 integer; # ore di lavoro al mese
param mt > 0 integer; # membri per conflitti interni
param md >= 0 integer; # dipendenti per risolvere conflitti
param phw >= 0; # percentuale di ore lavoro sprecate da conflitti
param phs >= 0; # percentuale ore lavoro risparmiate con motore costoso
param pap >= 0; # percentuale ore lavoro programmazione per microtransazioni
param pag >= 0; # percentuale ore lavoro grafica per microtransazioni
param fl{E} >= 0; # costo licenza prezzo fisso
param rl{E} >= 0; # costo licenza royalty
param av > 0; # valore aggiunto microtransazioni
param N integer;

#Funzione obiettivo
maximize GuadagnoTot : sum{v in V}(qc[v] * (cc[v] + av * O[v]) - (X["Pro",v] * st["Pr"] + Y["Pro",v] * st["Ar"] + Z["Pro",v] * st["Ld"])) - sum{e in E,v in V}(fl[e] * W[e,v] + rl[e] * Q[e,v] * qc[v] * cc[v]);

#Vincoli
subject to programmatoriDipendenti:
sum{v in V} X["Dip",v] <= d["Pr"];
subject to artistiDipendenti :
sum{v in V} Y["Dip",v] <= d["Ar"];
subject to leveldesignerDipendenti :
sum{v in V} Z["Dip",v] <= d["Ld"];

subject to oreProgrammazione{v in V} : 
sum{i in I} X[i,v] * hm * dl[v] >= hn["Pr",v] * (1 + phw * S[v] - phs * P["Re",v] + pap * O[v]);
subject to oreGrafica{v in V}: 
sum{i in I} Y[i,v] * hm * dl[v] >= hn["Ar",v] * (1 + phw * S[v] + pag * O[v]);
subject to oreLevelDesign{v in V} : 
sum{i in I} Z[i,v] * hm * dl[v] >= hn["Ld",v] * (1 + phw * S[v] - phs * P["Re",v]);

# se ho abbastanza dipendenti forza U a 1
subject to dipendentiNelTeam1{v in V} : 
(X["Dip",v] + Y["Dip",v] + Z["Dip",v]) - md + 1 <= N * U[v];
# se non ho abbastanza dipendenti forza U a 0
subject to dipendentiNelTeam2{v in V} : 
U[v] * md <= (X["Dip",v] + Y["Dip",v] + Z["Dip",v]);

# se ho raggiunto la dimensione critica forza T a 1
subject to dimensioneCritica1{v in V} :
sum{i in I} (X[i,v] + Y[i,v] + Z[i,v]) - mt + 1<=  N * T[v];
# se non ho raggiunto la dimensione critica forza T a 0
subject to dimensioneCritica2{v in V} : 
T[v] * mt <= sum{i in I} (X[i,v] + Y[i,v] + Z[i,v]);

subject to presenzaConflitti1{v in V} :
S[v] <= T[v];
subject to presenzaConflitti2{v in V} :
S[v] >= T[v] - U[v];
subject to presenzaConflitti3{v in V} :
S[v] <= (1 - U[v]);


subject to esclusivitaMotoreGrafico{v in V}:
sum{e in E} P[e,v] = 1;
# forzo ad essere 0 se P è 0
subject to acquistoLicenza1{v in V,e in E}:
Q[e,v] + W[e,v] <= N * P[e,v];
# forzo ad essere almeno 1 se P è 1
subject to acquistoLicenza2{v in V,e in E}:
Q[e,v] + W[e,v] >= 1 - N * (1 - P[e,v]);

subject to sceltaTipoLicenza{v in V,e in E}:
W[e,v] <= N * (1 - Q[e,v]);

subject to numeroMinimoLicenze{v in V,e in E}:
W[e,v] >= sum{i in I}(X[i,v]+Z[i,v]) - N * (1 - P[e,v] + Q[e,v]);
