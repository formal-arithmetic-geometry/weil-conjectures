## Worker report

Existing declaration: `Algebra.IndZariski.bijectiveOnStalks_algebraMap`,
`WeilConjectures.RingTheory.ProEtale.IndZariski`, lines 581–588 in the
slopmaster2 source. No module is added. Only the item’s `lean` record is changed;
the earlier attachment already named this theorem but lacked the complete
stage-2 record. Its source attribute is `@[stacks 096T]`. The theorem has no
individual docstring; the module documents ind-Zariski algebras, and the
`Algebra.IndZariski` and `RingHom.BijectiveOnStalks` declarations have the defining
docstrings. I read those declarations and their full surrounding binders.

The signature copied into `lean.statement` is verbatim from the theorem. Its
ambient variables supply `(R S : Type u) [CommRing R] [CommRing S] [Algebra R S]`.
The theorem requires no Noetherian, nonzero, injectivity, surjectivity, or
faithful-flatness hypothesis.

Clause-by-clause statement match:

- Commutative rings `R`, `S` are the two type parameters and the two `CommRing`
  instances. The specified ring map `v : R →+* S` is represented by the algebra
  structure `v.toAlgebra`; its algebra map is `v`. Conversely every algebra
  structure supplies the ring map used by the statement, so no map is lost.
- “S is the colimit of a small filtered diagram of commutative R-algebras” is
  exactly the field `Algebra.IndZariski.exists_colimitPresentation`: it quantifies
  `ι : Type u`, a `SmallCategory ι`, an `IsFiltered ι`, and
  `P : CategoryTheory.Limits.ColimitPresentation ι (CommAlgCat.of R S)`.
  Here `P.diag` is the diagram, `P.ι` its compatible algebra maps to `S`, and
  `P.isColimit` is the universal property of that very cocone with apex `S`.
  Thus this is the node’s categorical colimit, rather than an unrelated
  ring-level colimit or a bare existence of an unconnected algebra isomorphism.
- “Each R → C_i is a local isomorphism” is the field’s final clause
  `∀ i, Algebra.IsLocalIso R (P.diag.obj i)`. In Mathlib.RingTheory.LocalIso,
  `Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion` says for every
  prime `q` there is `g ∉ q` with
  `Algebra.IsStandardOpenImmersion R (Localization.Away g)`.
  `Algebra.IsStandardOpenImmersion.exists_away` then supplies `f : R` and
  `IsLocalization.Away f (Localization.Away g)`. This is exactly
  `C_g ≃ₐ[R] Localization.Away f`, using the uniqueness of localization as an
  R-algebra. Both directions of the stated neighborhood definition hold.
- The conclusion `(algebraMap R S).BijectiveOnStalks` unfolds to
  `∀ (q : Ideal S) [q.IsPrime], Function.Bijective
  (Localization.localRingHom (q.comap (algebraMap R S)) q (algebraMap R S) rfl)`.
  Thus `q` ranges over every prime of `S`, `p` is precisely `v⁻¹(q)`, and the map
  is the canonical localization map `R_p →+* S_q`. Bijectivity of a ring
  homomorphism is equivalent to its being an isomorphism, with inverse provided
  by `RingEquiv.ofBijective`; the conclusion identifies the specified map,
  rather than merely asserting that its source and target are isomorphic.

The common universe `u` for the two rings and diagram is the usual ring-diagram
size convention. Any given small diagram and its rings can be placed in one
common universe (and represented there by lifts if necessary); no countability,
finite index set, or smaller independent universe is imposed.

Dependency declarations read and used through the upstream module:

- `def-weil-ring-localization-away`:
  `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`;
  also `Mathlib.RingTheory.Localization.Away.Basic`, `IsLocalization.Away`.
  These are the localization objects and their R-algebra characterization
  inside the local-isomorphism hypothesis.
- `def-weil-pbc-category-colimit`:
  `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit` and `CategoryTheory.Limits.IsColimit`;
  `Mathlib.CategoryTheory.Filtered.Basic`, `CategoryTheory.IsFiltered`.
  The upstream hypothesis uses their presentation interface
  `CategoryTheory.Limits.ColimitPresentation` from
  `Mathlib.CategoryTheory.Limits.Presentation`; its `isColimit` field is the
  same universal property, with the specified apex instead of a chosen apex.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime` and
  `Localization.localRingHom`. Its residue-field and fibre-ring clauses are
  not needed for this particular node.

I read the source places in `literature/stacks-project/proetale.tex`:
`definition-local-isomorphism` (096E), `definition-ind-zariski` (096N), and
`lemma-ind-zariski-implies` (096T). The last is precisely the claimed implication.
096E describes open immersions in the neighborhood condition; the node and
Mathlib use its equivalent refinement to principal opens on source and base.
No correction to the node is needed.

Proof available in the existing source: take the filtered colimit presentation.
Every local-isomorphism stage identifies local rings. The canonical prime
localizations of the stages map compatibly to the localization of the colimit.
Every fraction in the latter comes from some stage, and every equality of
fractions is witnessed at a later stage. Surjectivity and injectivity of the
stage localization maps therefore imply those of the colimit localization map.
This is implemented by `Algebra.BijectiveOnStalks.of_colimitPresentation` and
`RingHom.IsLocalIso.bijectiveOnStalks`, followed by
`RingHom.bijectiveOnStalks_algebraMap.mpr`. No theorem is written or proved in
this delivery.

Edge cases checked: `IsFiltered` includes nonemptiness, so an empty diagram
cannot accidentally satisfy the hypothesis. If `S` is the zero ring, it has no
prime ideals and the conclusion is correctly vacuous; no `Nontrivial` instance
is demanded. The identity map is included (constant one-object presentation,
localizations away from 1). Arbitrary localizations and noninjective local
isomorphisms are allowed: the theorem assumes neither injectivity of `v` nor
surjectivity of its map on spectra. No characteristic restriction is present.

Searches made with `msearch.py NC lem-weil-pbc-ind-zariski-bijective-on-stalks`
(the sandbox `searches.jsonl` stores the raw query records):

- LeanFinder: “A filtered colimit of local isomorphisms of commutative algebras
  induces isomorphisms on all prime localizations”. Eight hits, including
  `RingHom.OfLocalizationPrime`, `RingHom.HoldsForLocalization.localRingHom`,
  and `AlgebraicGeometry.Spec_map_localization_isIso`; none states the complete
  filtered-colimit theorem.
- Loogle: `Algebra.IsLocalIso`. Twelve hits: the existing local-isomorphism
  definition, its constructor and neighborhood field, and its stability
  lemmas. They confirm the neighborhood notion, not the whole theorem.
- Mathlib grep: `bijectiveOnStalks|IndZariski|isLocalIso.*localRing`.
  Zero hits for the complete ind-Zariski/stalk statement.
- LeanSearch: “An ind Zariski ring homomorphism induces isomorphisms on local
  rings at every prime”. Unavailable: Internal Server Error; no search verdict
  is claimed from that service.
- Source and side-library `rg`:
  `bijectiveOnStalks_algebraMap|lem-weil-pbc-ind-zariski-bijective-on-stalks`
  over `WeilConjectures/` and `lean/Sheaf/`. Found the exact upstream theorem
  at IndZariski.lean:582 and its applications; the side-library occurrence is
  a proof-docstring citation in ClosedComponentSpectrumRestriction.lean.
  I also read the explicit ring-hom variant
  `RingHom.IndZariski.bijectiveOnStalks` in the same upstream module.

Validation: the prescribed `scompile.py` wrapper compiled the scratch `#check`
and `#print axioms` cleanly, including server confirmation. The theorem uses
exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The final packaging check is
`deliver2.py NC lem-weil-pbc-ind-zariski-bijective-on-stalks --no-push`.
No new nodes, dependency repairs, or statement disputes.

## Second reading by NC

I reread the node statement, its three dependency records, the Stacks source, and the
attached upstream declaration independently.

- Objects: the node introduces commutative rings `R,S`, a ring map `v : R →+* S`,
  and a filtered diagram of commutative `R`-algebras `C_i`.  The attached theorem
  uses `R S : Type u`, `[CommRing R] [CommRing S] [Algebra R S]`; taking the
  algebra structure induced by `v` makes `algebraMap R S` definitionally the map
  `v`.
- Filtered-colimit hypothesis: the node's small filtered colimit with its canonical
  maps is rendered by `Algebra.IndZariski.exists_colimitPresentation`, namely
  `ι : Type u`, `[SmallCategory ι]`, `[IsFiltered ι]`, and
  `P : ColimitPresentation ι (CommAlgCat.of R S)` with apex `S` and `P.isColimit`.
  `IsFiltered` includes nonemptiness, so the empty index case is excluded exactly as
  in the source.
- Local-isomorphism hypothesis: the node's condition that each stage is locally
  a localization is rendered by `∀ i, Algebra.IsLocalIso R (P.diag.obj i)`.
  Its field gives an element outside every target prime and a standard-open
  localization; `IsStandardOpenImmersion.exists_away` expands this to an
  `R`-algebra localization away from one source element, while an algebra
  equivalence transports the condition in the reverse direction.  Thus it matches
  the source's local-isomorphism neighborhood condition, including the possibility
  of shrinking the chosen neighborhood.
- Conclusion: `Algebra.IndZariski.bijectiveOnStalks_algebraMap` concludes
  `(algebraMap R S).BijectiveOnStalks`.  Unfolding this gives, for every prime
  `q : Ideal S` with `[q.IsPrime]`, `Function.Bijective` of
  `Localization.localRingHom (q.comap (algebraMap R S)) q (algebraMap R S) rfl`,
  exactly the canonical map `R_p → S_q` with `p = v⁻¹(q)`.  No quantifier,
  isomorphism clause, or map is added or omitted.

The dependency declarations are the recorded Mathlib leaves: `Localization.Away`
(and `IsLocalization.Away`), `CategoryTheory.Limits.colimit`/`IsColimit` with
`CategoryTheory.IsFiltered`, and `Localization.AtPrime` (plus
`Ideal.ResidueField`/`Ideal.Fiber`).  Each is the notion used by the node; no private
replacement or stronger ring hypothesis occurs.

Edge cases checked: the filtered index cannot be empty; the zero ring has no prime
ideals, so the conclusion is vacuous without a `Nontrivial` assumption; the identity
map is represented by the one-object filtered presentation and localization away
from `1`; arbitrary localizations and noninjective maps are allowed; no characteristic
or finiteness assumption is present; and the common universe `u` is the source
convention for the rings and diagram.

Searches were repeated with `msearch.py`: LeanFinder returned only individual
localization/stalk and filtered-colimit APIs, Loogle found no `Algebra.IndZariski`
declaration in Mathlib, and Mathlib grep found no complete ind-Zariski stalk theorem.
A source and side-library search found the exact sorry-free declaration
`Algebra.IndZariski.bijectiveOnStalks_algebraMap` at
`WeilConjectures/RingTheory/ProEtale/IndZariski.lean:581-588`; its ring-hom variant
`RingHom.IndZariski.bijectiveOnStalks` was also checked.  No existing declaration
or dependency mismatch was found, so no Lean file, node correction, or dependency
repair was necessary.
