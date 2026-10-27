## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseOpenValuativeProper` states
`AlgebraicGeometry.AlgebraicSpace.mapIsProper_of_denseOpen_valuative`, with proof `sorry`.
There are no new definitions, auxiliary proof obligations, or mathematical statement changes.
The source read is `literature/stacks-project/spaces-morphisms.tex`, Tag 089G,
`lemma-refined-valuative-criterion-universally-closed`, statement and proof; Tag 03KU,
`lemma-separated-implies-valuative`, statement and closed-equalizer proof. This is the node's
separated finite-type specialization of 089G(1)--(4), with the explicitly assumed open h.

Clause-by-clause correspondence:

- Schemes and spaces over Spec Z: `H X V : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`.
  The universe `u` is explicit, and all valuation test rings and fields are `Type u`, the
  universe of the site schemes, rather than an unrelated smaller universe. The ULift is
  exactly the project's terminal Spec Z convention. No relative-base hypothesis is added.
- Morphisms p and h: `(p : H ⟶ X) (h : V ⟶ H)`, the full-subcategory sheaf maps.
- Separated p: `hpsep : MapIsSeparated p`, whose definition tests the relative diagonal
  by `IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left)` on every scheme.
- Finite-type p: `hpft : MapIsFiniteType p`, exactly affine-test `MapIsQuasiCompact`
  and `MapIsLocally (@LocallyOfFiniteType)` on all compatible etale charts.
- Open immersion h: `hh : IsRepresentableWith (fun _ _ f ↦ IsOpenImmersion f.left)
  h.hom.hom`, so representability and the property on scheme tests are retained.
- Quasi-compact h: `hqc : MapIsQuasiCompact h.hom.hom`; this is the current corrected
  definition in ProperCurveModuli: for every affine scheme T mapping to the target,
  `CompactSpace (Point (Limits.pullback f a))`. It is not merely quasi-compactness of
  the map between the original point spaces.
- Dense image: `hd : Dense (pointImage h.hom.hom)`, using the recorded field-point classes,
  their image, and the final topology of etale scheme charts.
- Every valuation ring and its arbitrary specified fraction field: the `hext` binders
  `R`, `[CommRing R] [IsDomain R] [ValuationRing R]`, `K`, `[Field K] [Algebra R K]
  [IsFractionRing R K]`. Fields, non-discrete rings and rings of arbitrary rank are allowed.
- The generic map into V is `v : yoneda.obj (Over.mk
  (specULiftZIsTerminal.from (Spec (.of K)))) ⟶ V.obj.obj`; the base map x has the
  analogous source over R. These are Mathlib spectra with their unique structure maps
  to Spec Z. These natural transformations retain the maps, not merely point classes.
- The commuting solid diagram has left side `v ≫ h.hom.hom ≫ p.hom.hom` and right
  side x precomposed with the Yoneda image of `Over.homMk (Spec.map
  (CommRingCat.ofHom (algebraMap R K)))`. The slice source and target are explicit,
  and `specULiftZIsTerminal.hom_ext _ _` supplies the structural commutativity proof.
- Extension ring and domination: the existential `R'` is again a commutative domain with
  `ValuationRing R'`, and `ι : R →+* R'` is `Function.Injective` and `IsLocalHom`.
  Valuation rings have their canonical local-ring structures; locality of this injection
  is exactly contraction of the maximal ideal to the maximal ideal of R. It does not mean
  an arbitrary, possibly non-dominating extension.
- The extension field is `FractionRing R'`. Taking this canonical fraction field is
  equivalent to existentially choosing any fraction field K' of R': the unique R'-field
  isomorphism transports the maps. The field embedding from the given arbitrary K is
  `IsFractionRing.lift` of `(algebraMap R' (FractionRing R')).comp ι`, with injectivity
  supplied by the composite of `IsFractionRing.injective` and `hι`. Its restriction is
  exactly the given ring homomorphism, so no extra independent field map or compatibility
  assumption is introduced. Both fields and their extension remain in the site universe.
- The lift is the existential Yoneda map z from Spec R' into H. The first conjunct
  identifies `z ≫ p.hom.hom` with x precomposed by the Yoneda image of the slice map
  whose underlying scheme morphism is `Spec.map (CommRingCat.ofHom ι)`.
  The second conjunct restricts z along R' → FractionRing R' and identifies it with
  the pullback of `v ≫ h.hom.hom` along the canonical field embedding above. Every
  restriction uses `Over.homMk`, with explicit source and target and the canonical
  terminal-object equality for structural commutativity.
- Conclusion `MapIsProper p` expands to separated, finite type, universally closed.
  The last component uses closedness of the point map on the sheaf pullback after every
  algebraic-space base change, exactly as in the node. The background definitions of
  quasi-separatedness and finite presentation are not additional hypotheses. No Noetherian,
  rank-one, discrete, quasi-separated-base, or finite-presentation assumption occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`,
  `Scheme.Spec` (scheme and spectrum signatures/docstrings read).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith` and
  the sheaf-valued presentation. Its own definition has real data; no private copy is made.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` and its universal-property signature. The theorem is
  imported publicly through the two public modules; pullbacks in the property predicates
  are the actual sheaf/presheaf categorical pullbacks.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`,
  `pointTopologicalSpace`, with `Point` from AlgebraicSpacePointClasses.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`. These are the original
  recorded scheme predicates used by the landed space-property definitions.
- `Mathlib.RingTheory.Valuation.ValuationRing`: `ValuationRing`, its domain/divisibility
  definition and TFAE with the fraction-field definition;
  `Mathlib.Algebra.Field.Defs`: `Field`;
  `Mathlib.RingTheory.Localization.FractionRing`: `FractionRing`, `IsFractionRing.lift`
  and its uniqueness/restriction signatures. No restricted valuation-ring predicate is used.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, `mapPoint`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`,
  `MapIsLocally`, `MapIsFiniteType`, `MapIsUniversallyClosed`, `MapIsProper`.
  Their already landed definition-owner nodes `def-sfb-proper-curve-moduli` and
  `def-sfb-space-morphism-properties` are added to stmt_deps as authorized by brief §5.
- `Mathlib.AlgebraicGeometry.Limits`: `specULiftZIsTerminal`, with its terminal
  structure map and `hom_ext` uniqueness. `Mathlib.CategoryTheory.Comma.Over.Basic`:
  `Over.mk`, `Over.homMk`. These are used directly in the signature; no spectrum helper
  is defined or borrowed from a theorem node.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseOpenStackedValuation`:
  `exists_denseOpen_stackedValuation` is a proof input only. Its recorded signature,
  proof docstring and four compatibility equations were read. Its plain import stays
  because `lem-sfb-space-dense-open-stacked-valuation` is a proof_dep; that theorem
  node is absent from stmt_deps, and `stackedValuationSpec` is absent from the signature.

Plain imports retain stated proof dependencies: `Mathlib.RingTheory.Flat.TorsionFree`
(`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
(`Module.faithfullyFlat_iff`, `PrimeSpectrum.comap_surjective_of_faithfullyFlat`), and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`
(`IsClosedImmersion.exists_lift_of_isFractionRing`). Their source signatures were read.
The remaining proof dependency `lem-sfb-space-qc-valuative-existence-closed` has no Lean
record or mathlib_match in the read checkout, so no import is invented for it. Its eventual
proof import can be added by the maintainer. It is not required to type this statement.
The seven proof steps in the docstring track the node's seven steps, including the local
faithfully-flat argument, equalizer scheme, quotient valuation and extended criterion.

Edge cases checked before and after writing: V empty forces H empty by density, and the
hypothesis is then vacuous without forcing any nonempty source; H empty over arbitrary X
is allowed. V=H recovers the ordinary extension criterion. A field is a valuation ring and
its maximal ideal is zero, so identity and field-extension cases are included. All ranks
and both characteristic zero and positive characteristic are included. The ring R cannot
be the zero ring because the source valuation-ring definition is a domain with a fraction
field; this is not an added restriction. Neither X nor H is assumed quasi-compact as an
absolute space, Noetherian, reduced, or a scheme. The old A¹ → A¹/Z non-quasi-separated
example is not incorrectly accepted as quasi-compact: its affine self-test has infinitely
many affine-line components, and `MapIsQuasiCompact` retains that affine-test condition.
No new statement fault or unresolved dispute was found in the current corrected node.

Searches actually run (msearch.py group Q33, this item):

- LeanFinder: `proper morphism algebraic spaces dense open valuative criterion valuation
  ring extension` returned eight scheme valuative-criterion hits, led by
  `AlgebraicGeometry.IsProper.of_valuativeCriterion`; no dense-open algebraic-space theorem.
- Loogle: `IsProper ValuativeCriterion` returned zero hits, unknown identifier `IsProper`.
- LeanSearch: `A separated finite type algebraic space morphism is proper if valuation
  diagrams through a quasi compact dense open lift after dominating valuation ring extension`
  returned eight scheme properness/valuative hits; no exact statement.
- Grep: `dense.*open.*valuative|valuative.*proper`, initially scoped to
  `Mathlib/AlgebraicGeometry`, returned zero hits. A second, correctly scoped query
  `ValuativeCriterion|dense.*open` in `AlgebraicGeometry` returned 25 hits: scheme
  ValuativeCriterion, Proj and birational dense-open material. The relevant Mathlib
  ValuativeCriterion signatures were opened; they quantify over all generic diagrams for
  schemes, not diagrams through a dense open of an arbitrary algebraic space.
- Direct rg searches of `lean/WeilConjectures`, `lean/Sheaf` and the upstream names index
  for dense-open/valuative/proper names and Tag 089G found the landed stacked-valuation
  helper and unrelated scheme/curve material, no theorem with this statement.
  Searching the exact item id found no existing declaration of this item. The exact proposed declaration name has no hit in
  Sheaf, WeilConjectures or Mathlib.
- `tools/blueprint_refs.py search 'dense open valuative proper'` returned zero blueprint
  matches. `ancestor` says a node created for this item has blueprint.from.node = None;
  no new node is created, so no fabricated ancestor is recorded.

Validation: `scompile.py Q33 lem-sfb-space-dense-open-valuative-proper <module>` compiled
the repaired sandbox and library names cleanly (4.1 s and 2.1 s), without errors or unexpected warnings.
`set_option autoImplicit false` enforces explicit binding. Maximum Lean line width is 91.

## Second reading by Q33

This is a separate self-reading, since the dispatcher explicitly forbids starting other
agents; independent mathematical review remains with the maintainer. I reopened the node
and the final theorem signature and checked the following possible mismatches.

The base is precisely Spec Z; `u` covers the test rings, their fields, and the space site.
The p assumptions are exactly separated and finite type. The h assumptions retain all
three clauses (representable open immersion, affine-test quasi-compactness, and density).
In particular the hqc predicate was opened at its current source definition, rather than
inferred from an old topological-quasi-compactness convention. The universal premise starts
in V, not in H, and its compatibility composes through h then p in the correct order.
The lift targets H, not V; the two conclusions preserve the exact base map x and exact
field-valued map hv, rather than only their point classes. `IsLocalHom` plus injectivity
means domination, and `IsFractionRing.lift` fixes the field extension uniquely on R.
Choosing the canonical fraction field of R' introduces no restriction: arbitrary fraction
fields are uniquely isomorphic over R'. None of these is a vacuous added hypothesis.
The conclusion is the existing properness predicate, whose universal closedness quantifies
over arbitrary space base changes, including the identity. The finite-presentation and
quasi-separated conventions are explanatory in the node, not missing assumptions.

No mismatch required changing the mathematical statement. This reading added the two landed
property-owner citations to stmt_deps, leaving the
original statement and seven-step proof unchanged. It also checked that every new declaration
belongs to this one node, the only proof is `sorry`, and no definition or theorem is duplicated.


## Repair of returned head 740d4fc9aea9

H2 repaired by the maintainer's second alternative (Mathlib Spec/Over.mk directly).
The returned signature mentioned the plain def `stackedValuationSpec`, whose owner was
incorrectly added as a theorem statement dependency. Every occurrence of that def has
been replaced by `Spec`, `Spec.map`, `Over.mk`, `Over.homMk`, and Mathlib's unique
structure map to terminal Spec Z. No new definition or definition node is needed.
The theorem `lem-sfb-space-dense-open-stacked-valuation` is removed from the added
stmt_deps and retained unchanged in proof_deps. Its import is now plain rather than
public. Public Mathlib imports supply Limits and ValuationRing directly.

The current-main node was read and used as the base of the repaired copy. Its original
statement, source, proof, proof_deps and all maintainer fields are retained; the only
added stmt_deps are the two already accepted landed definition owners. Comparing the
returned sandbox with current main found no other content change to reconcile.
The compiler required explicit U and V slice objects in Over.homMk; all four arrows
now specify them, so no metavariable or implicit slice structure is left unresolved.
The structural equality arguments are applications of the existing `hom_ext` theorem,
not new postponed lemmas. Recompilation passed in sandbox and library modes.

A fresh self-reading of the repaired signature checked the four spectrum arrows:
Spec K → Spec R, Spec R' → Spec R, Spec Frac R' → Spec R', and
Spec Frac R' → Spec K. Their rings are respectively algebraMap R K, ι,
algebraMap R' (FractionRing R'), and the unique IsFractionRing.lift of ι.
Their slice structures are the unique maps to Spec Z, the very objects used by the
previous functor; this is just expansion into Mathlib constructions. The compatibility
premise, both lift equalities, all hypotheses and properness conclusion remain exactly
those independently accepted by the maintainer. H2 is the only returned point.
