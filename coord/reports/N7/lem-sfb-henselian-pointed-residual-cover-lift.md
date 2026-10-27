## Worker report

The delivery states `lem-sfb-henselian-pointed-residual-cover-lift` in
`Sheaf.AlgebraicGeometry.FundamentalGroup.HenselianPointedResidualCover`.
The namespace is `AlgebraicGeometry.Scheme.HenselianPointedResidualCover`.
The only postponed theorem is `henselian_pointed_residual_cover_lift`; its proof is
exactly `sorry`, with all ten DAG proof steps in its docstring. All four canonical
helper definitions have real data. `LiftData` is a structure of the comparison data
and the claimed properties, whose nonemptiness the theorem asserts. It is not an
assumed replacement for the conclusion.

The live Q42 review completed **stage 1**, not stage 2. There was no `lean` record and
no repair note for this item when read. The previous worker's stage-1 live-wins
objection therefore does not prohibit this stage-2 statement. The statement, split,
dependencies, and Q42 review are preserved verbatim. Only `lean` changes.

Hypotheses and the henselization:

| Node text | Lean |
| --- | --- |
| B is a commutative ring | `(B : Type u) [CommRing B]` |
| B is Noetherian | `[IsNoetherianRing B]` |
| J is an ideal of B | `(J : Ideal B)` |
| Spec(B/J) is nonempty and connected | `[ConnectedSpace (Spec (.of (B ⧸ J)))]`; `ConnectedSpace` includes nonemptiness |
| A geometric point s with algebraically closed field Omega | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of (B ⧸ J)))` |
| E is the pair henselization, with its canonical map from B | `c : Cocone (ObjectProperty.ι ...)` and `hc : IsColimit c`, using exactly the category in `RingTheory.pair_henselization`; E is `c.pt.right`, and B to E is `c.pt.hom` |
| Its marked ideal is JE | `J.map c.pt.hom.hom` |

The theorem works for every colimit cocone of this category. It does not replace
henselization by an arbitrary henselian extension or assume its conclusions. Its
existential `hE` supplies connectedness for the existing universal-cover API, and
its existential `h` supplies the canonical residual isomorphism for the explicit
helper constructions. Neither is an additional hypothesis.

Conclusions, including every clause of the node:

| Node clause | Lean rendering |
| --- | --- |
| E is Noetherian | `IsNoetherianRing c.pt.right` |
| Spec E is nonempty connected | existential `hE : ConnectedSpace (Spec c.pt.right)` |
| (E,JE) is the henselian pair | `HenselianRing c.pt.right (J.map c.pt.hom.hom)` |
| E/JE = B/J canonically | `h : Function.Bijective (Ideal.quotientMap ...)`; `residualEquiv` is `RingEquiv.ofBijective` of this exact quotient map |
| Reduction between finite etale covers | `LiftData.reduction_equivalence` for the actual `FiniteEtale.pullback (residualInclusion J b h)` |
| Small cofinal pointed connected finite etale Galois systems correspond | `pointed_equivalence : UniversalCover.Index (s ≫ residualInclusion J b h) ≌ UniversalCover.Index s`; these are the existing small models of pointed Galois covers |
| Underlying covers are identified by reduction | natural `finite_iso` from the pulled-back lifted cover diagram to the residual diagram |
| Pointed morphisms correspond | naturality of `finite_iso` and `finite_point`, normalized by the canonical `FiniteEtale.pullbackFiberIso` |
| Group actions correspond | the full finite-cover reduction equivalence identifies morphisms and their composition; `automorphisms` explicitly asserts bijectivity of its `mapIso` on every automorphism group; the natural fibre isomorphism intertwines these actions |
| Write the lifted covers as Spec C_lambda | `stages : (UniversalCover.Index ...)ᵒᵖ ⥤ Under E`, with `stage_iso` identifying their spectra with the exact existing cover diagram and `stage_over` identifying their E-structures |
| Each C_lambda is Noetherian | `LiftData.noetherian` |
| Each (C_lambda,JC_lambda) is henselian | `LiftData.henselian` |
| Their marked ideals are in their Jacobson radicals | `LiftData.radical`, using `Ideal.jacobson ⊥` |
| Each Spec C_lambda is nonempty connected | `LiftData.connected` |
| B to E is ind-etale | `RingHom.IndEtaleAcrossUniverses c.pt.hom.hom` in the outer theorem |
| B to each C_lambda is ind-etale | `LiftData.indEtale` for the composite of the actual structural ring maps |
| H is the filtered colimit of the C_lambda | `colimit : Cocone stages`, `isColimit : IsColimit colimit`; the opposite of the existing cofiltered `UniversalCover.Index` is filtered |
| (H,JH) is henselian | `LiftData.henselian_colimit` |
| JH is in the Jacobson radical | `LiftData.radical_colimit` |
| B to H is ind-etale | `LiftData.indEtale_colimit` |
| Spec H is the pointed universal cover of Spec E | `universal`, `universal_over`, and `universal_stage` identify it with the existing `UniversalCover.cover`, its structure map, and every limit projection; its marked point is transported from `UniversalCover.pt` |
| The residual finite rings are the reductions C_lambda/JC_lambda | `quotientDiagramFunctor` has these literal quotient rings and the induced quotient maps as its objects and arrows |
| This reduced system is the residual pointed Galois system | `residual_stage_iso`, `residual_stage_over`, and `residual_stage_reduction`; the last equation identifies its maps with the canonical quotient maps and `finite_iso` |
| H/JH is colim C_lambda/JC_lambda | `quotient_colimit : IsColimit ((quotientDiagramFunctor E (J.map b.hom)).mapCocone colimit)`; its vertex is literally H/JH and its legs are the canonical quotient maps |
| Its spectrum is exactly the residual pointed universal finite-etale limit | `residual_universal`, `residual_universal_over`, and `residual_universal_stage`, normalized by all finite coprojections |
| The residual marked point is the reduction of the lifted one | `residual_point` |
| The residual spectrum is nonempty connected | `residual_connected` |
| Its map is a pro-etale covering | `residual_weaklyEtale` and `residual_covering : Presieve.singleton (...) ∈ proetalePrecoverage ...`, using the canonical residual structural map |
| For J=0 the canonical B to E is an isomorphism | `J = ⊥ → Function.Bijective c.pt.hom.hom`; a bijective unital ring map is precisely a ring isomorphism |

The stage and colimit ideals are written `(J.map b.hom).map A.hom.hom`.
`Ideal.map_map` identifies these with J extended along the composite B to A.
The underlying rings of `stages` are therefore the C_lambda of the node and its
cocone vertex is H. An isomorphism to an unrelated ring or cover would not suffice:
all scheme comparisons are constrained by structure maps, finite projections,
quotient maps, and the marked-point equation.

Four helpers belong to this node's canonical comparison construction:
`quotientDiagramFunctor` implements the actual quotient diagram,
`residualEquiv` inverts the uniquely determined bijective quotient map,
`residualInclusion` is its closed immersion, and `residualProjection` composes the
actual quotient structure maps. Their docstrings and the `LiftData` docstring all
cite this node. No independent missing notion or dependency repair is needed.
No object is obtained from an unproved, nondetermining existence theorem.

Dependency declarations read and used:

- `def-weil-geometric-point`: `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, and inline scheme morphism from Spec Omega;
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField` was read.
- `lem-weil-pbc-pair-henselization`: `RingTheory.pair_henselization` in
  `WeilConjectures.RingTheory.PairHenselization`; the theorem binder repeats exactly
  its colimit diagram, not a new definition of henselization.
- `lem-sfb-pointed-finite-etale-limit-cover`:
  `AlgebraicGeometry.Scheme.UniversalCover.nonempty_pointedLimitCechCoordinates`
  and its `PointedLimitCechCoordinates` interface in
  `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`. Its public dependency
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction`
  supplies `Index`, `obj`, `point`, `diagram`, `p`, `cover`, `proj`, `pt`, and
  the actual small pointed Galois construction used in the signature.
- `def-weil-pbc-henselian-terminology`: Mathlib `HenselianRing`, publicly exposed by
  `WeilConjectures.Mathlib.RingTheory.Henselian`. Its `jac` field is precisely the
  Jacobson-radical condition. The recorded strictly henselian local ring class is
  not substituted for the general henselian pair.
- `def-weil-pbc-ind-etale-algebra`: `RingHom.IndEtaleAcrossUniverses` in
  `Sheaf.RingTheory.IndEtaleUniverseTransport`, which canonically transports the
  existing ind-etale predicate without choosing a presentation.
- `def-weil-pbc-proetale-site`: `Scheme.ProEt`, `Scheme.ProEt.topology`, and
  `Scheme.proetalePrecoverage` in `Mathlib.AlgebraicGeometry.Sites.Proetale`.
  The covering clause uses the defining precoverage, exactly as the recorded
  pointed-limit-cover module does.
- `def-weil-pbc-category-colimit`: `Cocone`, `IsColimit`, `colimit`, and `colimit.desc`
  in `Mathlib.CategoryTheory.Limits.HasLimits`; a colimit cocone is used so all
  coprojections and algebra structures are explicit.

The modules of all stated proof dependencies are imported, privately where used
only for the future proof: the Noetherian henselization and integral-henselian-pair
modules, the connectedness/idempotent criterion, henselian finite-etale lifting,
ind-etale stability, and the Mathlib modules containing finite presentation,
properness, finite morphisms, integral finite algebras, finite Noetherian algebras,
Spec preservation of limits, affine qcqs, and filtered-colimit representatives.
`lem-sfb-pointed-galois-limit-geometry` has no recorded Lean declaration or Mathlib
match; it is a proof dependency only, so no invented import is added. The existing
`UniversalCover.Index` already supplies the cofiltered instance needed to state
this item. Its role remains in the theorem's proof docstring.

Edge cases checked before writing:

- J=B and the zero quotient are excluded by the required nonempty connected Spec(B/J).
- J=0 is retained explicitly. E is canonically B; all zero-ideal quotient maps and
  residual comparisons remain meaningful and give the same pointed cover.
- B/J need not be a local ring. No local-ring, domain, reducedness, or G-ring
  assumption is imposed anywhere.
- An algebraically closed residual field is permitted; the residual pointed
  Galois system has terminal/trivial covers and its universal cover is that field.
- H may be non-Noetherian. Only E and finite stages are asserted Noetherian.
- The system is nonempty and cofiltered by the existing small pointed Galois API;
  its opposite is a legitimate filtered ring diagram, not an empty colimit.
- All objects, indices and coefficient fields use the compatible universe u of
  the dependency's universal cover. No independent smaller test-ring universe,
  equality of site object and morphism universes, or cardinal restriction is added.
- Finite etale group actions are handled by the actual full category equivalence,
  not solely by a bijection of cover isomorphism classes.

Searches actually run (the msearch calls are logged by the prescribed wrapper):

- LeanFinder: `For a Noetherian henselian pair reduction identifies pointed connected
  finite etale Galois covers and their universal cover colimits`. Eight hits,
  including `PointedGaloisObject.isColimit`, generic Galois-object lemmas and
  standard-etale root lifting. None states this henselian residual-cover lift.
- LeanSearch: `henselian pair equivalence finite etale covers universal cover reduction`.
  Eight hits on `HenselianRing`, `HenselianLocalRing`, and their fields/TFAE; no match.
- Loogle: `HenselianRing, IsEquivalence` returned zero hits with unknown identifier
  `IsEquivalence`; this malformed query was not treated as evidence of absence.
  The corrected query `HenselianRing` returned six hits on that class, completeness,
  and its fields, without the desired cover theorem.
- Mathlib grep via msearch:
  `henselian.*[Cc]over|[Cc]over.*henselian|[Hh]ensel.*[Gg]alois`: zero hits.
- Mathlib grep via msearch in `Algebra/Category`:
  `quotient.*[Ff]unctor|[Ff]unctor.*quotient|quotientDiagram`: five unrelated hits
  on group colimits and module resolutions, no functor taking the actual
  quotient rings of algebras under E.
- `rg` in the project's `WeilConjectures` and `Sheaf` roots for the preceding
  henselian-cover expressions and the full node id found no existing statement.
  Searches for `quotientDiagramFunctor`, `residualInclusion`, the new namespace
  and theorem name in Mathlib, both project roots and `dag/lean_names_upstream.json`
  found no declaration clash.
- Additional source searches for quotient functors found
  `Algebra.quotientBaseChange` in
  `WeilConjectures.RingTheory.SurjectiveQuotientBaseChange`: this is pushout-based
  extension of scalars in `CommAlgCat`, not the literal quotient-ring diagram in
  `Under E`. It is not a second statement of this item. The helper here records
  the actual quotient construction so the colimit equation is normalized.

Validation: the file passed both the sandbox and real library-module checks through
`scompile.py`, with no errors and no warnings. All universes and variables are bound
explicitly (`set_option autoImplicit false`). There is no statement correction,
STATEMENT-DISPUTED flag, new node, dependency module, or live-source edit.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
