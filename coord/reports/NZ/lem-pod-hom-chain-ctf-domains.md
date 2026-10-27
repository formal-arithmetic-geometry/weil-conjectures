## Worker report

The module [PodHomChainCtfDomains.lean](lean/Sheaf/Paper/PodHomChainCtfDomains.lean) states
`WeilConjectures.PodHomChainDomains.domains_and_bijections`. It uses the four recorded
coefficient stages and a chosen `PodCtfAdjunctionData` for a separated finite type morphism.
The abbreviations `localHom`, `directHom`, and `supportHom` render respectively
$L_N=R\mathcal Hom_X(M,Rf^!N)$, $A_N=Rf_*L_N$, and
$B_N=R\mathcal Hom_Y(Rf_!M,N)$. `tensorX` and `tensorY` are the chosen left-factor
monoidal tensors from the closed presentations.

The first seven conjuncts state finite-Tor membership of $Rf_!M$, $A_N$, $B_N`,
$Rf^!N$, $L_N$, $Lf^*T$, and $M\otimes^LLf^*T$, in that order. The eighth conjunct
states that the supplied projection at $A_N$ is an isomorphism. The final five
conjuncts state bijectivity of the inverse ordinary adjunction hom-equivalence,
inverse left-factor tensor-Hom hom-equivalence, inverse exceptional adjunction
hom-equivalence, precomposition with the forward projection, and the target
left-factor tensor-Hom hom-equivalence. These are exactly the five bijections in
the node, with their stated directions and full-subcategory objects.

The statement dependencies used are: `Sheaf.Paper.SixFunctorOperationDatum`,
`WeilConjectures.SixFunctorOperationDatum`; `Sheaf.Paper.PodCtfAdjunctions`,
`WeilConjectures.PodCtfAdjunctionData` and its `ordinaryAdjunction`,
`exceptionalAdjunction`, `tensorAdjunctionX`, `tensorAdjunctionY`; the landed
`Sheaf.Paper.CtfCoefficientStageSelectors` declarations
`PodCoefficientStage.domain`, `operations`, `homPairs`, `internalHom`, and `tensor`;
`Sheaf.Paper.PodCtfPairingMaps` declarations `PodCtfPairing.homX`, `homY`, and
`projection`; and the operation interfaces imported from
`WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` and the derived operation
modules. The theorem proof is `sorry` as required for stage 2.

Edge cases checked: all four coefficient selectors are included, so the completed
integral, rational, and common-stage conventions are not dropped; the finite-Tor
property is required only where the selected domain requires it; `M` is unrestricted
in the recorded tensor domain while `T` is in the selected finite-Tor full
subcategory; the projection and all Hom sets retain the exact source and target
objects. Empty or zero objects are allowed by the full-subcategory quantification.

Searches for an existing declaration: `msearch.py ... leanfinder` with the query
“Finite Tor constructible domains and five adjunction Hom bijections pullback direct
image tensor internal Hom exceptional compact support projection formula” returned
only generic condensed-module adjunctions and no match. `msearch.py ... loogle`
queried `CategoryTheory.Adjunction.homEquiv, CategoryTheory.Iso.homCongr` and found
no combined result. `msearch.py ... grep` queried `homEquiv|homCongr` in
`CategoryTheory/Adjunction`; it found only generic Mathlib adjunction lemmas.
Repository searches with `rg` found the downstream chain helpers but no declaration
of this domains-and-bijections statement. The existing helper definitions in
`def-pod-ctf-pairing-maps` are cited and reused rather than copied.

No `STATEMENT-DISPUTED` or node fault was found.

## Second reading by NZ

The item node and module were read together. The binder hypotheses match the node's
fixed finite-field datum, four coefficient stages, separated finite-type morphism,
and chosen exceptional adjunction data. The seven membership clauses correspond
one-to-one with the six named objects and the tensor input; the projection clause
uses `PodCtfPairing.projection` at `A_N`; and the five `Function.Bijective` clauses
render the five Hom bijections in the node's displayed order. No hypothesis or
conclusion was added beyond the stated finite-Tor domain bookkeeping.
