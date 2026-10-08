+++
id = "lem-fin-compact-bounded-and-base-change"
kind = "lemma"
title = "Compact direct images needed by the generic argument"
order = 1631
uses = ["def-amb-etale-compact-support", "def-weil-pbc-constructible-complexes", "def-weil-pbc-scheme-conventions", "lem-fin-extension-by-zero", "lem-fin-proper-bounded-constructible", "sbc-def-base-change-map", "sbc-prop-extension-by-zero-and-arbitrary-base-change", "thm-nagata-compactification", "thm-weil-pbc-bounded-below"]
+++
Let $f:X\to S$ be a separated finite-type morphism between
finite-type schemes over a field of characteristic different from
$\ell$. For $K\in D^b_c(X,\mathbf F_\ell)$, its
compact direct image
$Rf_!K$ is bounded constructible. For every morphism $v:S'\to S$ with Noetherian $S'$,
the compact direct-image exchange
$v^*Rf_!K\to Rf'_!v_X^*K$ is an isomorphism.

## Proof

Choose the compactification $f=pj$ supplied by
[thm-nagata-compactification]. By
[def-amb-etale-compact-support], $Rf_!K=Rp_*j_!K$.
The extension by zero is bounded constructible by
[lem-fin-extension-by-zero]; the proper direct image is
bounded constructible by [lem-fin-proper-bounded-constructible].
In the base-changed compactification the exchange is the composite
of the extension-by-zero comparison in
[sbc-prop-extension-by-zero-and-arbitrary-base-change] and
the proper comparison in [thm-weil-pbc-bounded-below].
Both are isomorphisms. This proof uses no ordinary direct-image
finiteness for an open immersion and asserts no bound on the
dimensions of the fibers of the chosen compactification.
