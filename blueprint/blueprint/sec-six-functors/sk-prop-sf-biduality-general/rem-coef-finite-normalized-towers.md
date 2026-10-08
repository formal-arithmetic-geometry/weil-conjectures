+++
id = "rem-coef-finite-normalized-towers"
kind = "remark"
title = "Normalized towers supplied to the integral argument"
order = 2144
uses = ["cor-coef-finite-verdier", "def-weil-derived-complete-integral-detailed", "def-weil-pbc-adic-coefficient-datum", "lem-coef-finite-dualizing", "lem-weil-verdier-preservation-strata"]
+++
The objects $\omega_{X,A_{E,n}}$, with transition maps

$$
\omega_{X,A_{E,n+1}}\longrightarrow
\omega_{X,A_{E,n+1}}\otimes^L_{A_{E,n+1}}A_{E,n}
\xrightarrow{u}\omega_{X,A_{E,n}},
$$

form a normalized system by [lem-coef-finite-dualizing].
The uniform Tor interval is $[-2\dim X,0]$, by
[lem-weil-verdier-preservation-strata].
For a normalized system $K_n$ with uniform Tor interval
$[a,b]$, the maps of [cor-coef-finite-verdier] similarly
make $D_{X,A_{E,n}}K_n$ a normalized system with interval
$[-b-2\dim X,-a]$. Evaluation and double-dual maps are maps
of these coefficient systems. The normalization cocycles here
are the ones required by [def-weil-pbc-adic-coefficient-datum].

To pass to the integral category of
[def-weil-derived-complete-integral-detailed], the next argument must
still establish that a normalized system reconstructs with its
given reductions. It must also verify the uniform finite-Tor
condition for the reductions of an object of that definition:
the definition literally requires uniformly bounded constructible
reductions, rather than explicitly asserting finite Tor amplitude.
These are derived-completion and residue-test steps; neither is
proved simply by writing $R\varprojlim$. No common lisse
stratification of all finite levels is assumed in the finite
comparisons proved above.
