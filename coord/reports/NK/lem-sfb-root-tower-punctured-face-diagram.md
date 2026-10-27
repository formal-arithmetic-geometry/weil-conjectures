## Worker report

The module `Sheaf.Paper.RootTowerPuncturedFaceDiagram` states the normalized punctured
root-tower coordinate-face diagram. All theorem proofs are `sorry`; definitions contain
actual constructions. The main declaration is
`AlgebraicGeometry.ProEtale.PuncturedFaceDiagram.rootTower_punctured_face_diagram`.
It proves `Assertion` for E and Omega. The normalization, nested and naturality theorems
are additional clauses of the same node, recorded in `lean.declarations`.

Clause-by-clause reading:

* Distinct primes: `p`, `ℓ`, `[Fact p.Prime]`, `[Fact ℓ.Prime]`, `hpℓ : p ≠ ℓ`.
  The characteristic-p field is `k` with `[Field k] [CharP k p]`.
* The finite norm-topological extension is `E` with `[NormedField E]`,
  `[NormedAlgebra ℚ_[ℓ] E]`, `[FiniteDimensional ℚ_[ℓ] E]`. The algebraic closure with
  extended norm is `Ω` with `[NormedField Ω] [NormedAlgebra E Ω] [IsAlgClosure E Ω]`.
* Both coefficients use `Profinite.continuousCoefficientRingObj`, whose sections are
  `ULift C(P,F)` with pointwise operations and precomposition. It is the existing
  scheme-universe instance of the recorded continuous-map coefficient construction,
  retaining all continuous functions for the incomplete algebraic closure.
* The module category is `RootCoordinateFace.Modules`, exactly Mathlib `Mod` over
  `condensedRingObj Λ X` on `Sheaf (Scheme.ProEt.topology X) Ab.{u+1}`. Pullback is
  the exact `upperStar.mapDerivedCategory`; `lower` is the recorded ordinary unbounded
  `moduleObjectDerivedPushforward`, not a separate cohomology construction.
* The regular separated finite-type scheme is `Y`, its map `y` to `Spec k`,
  `[LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]` and
  `hY : IsRegularScheme Y`. The affine etale chart is `b : Spec A ⟶ Y`, `[Etale b]`.
* `H`, `hH`, `hproduct` and `hbranches` render the reduced SNC divisor, its product
  equation and its exact list of branch supports. `IsStrictNormalCrossingsBoundary`
  includes reducedness and the expected regular intersections. The affine pro-etale
  chart is the ring map `a : A →+* R` with weakly etale `Spec.map a`.
* The actual tower is `Spec (tameRootAlgebra p (fun i ↦ a (s i)))`. Its existing
  quotient presentation imposes every positive prime-to-p power equation and every
  divisibility transition. The existing stratum quotient and zero-root evaluation
  introduce S and i; these names are unused notation in this node's conclusions.
* `out : Finset (Fin r)` is I_o; `Finset.univ \ out` is I_i, whose `Nonempty` is
  required. `outer t out` is D(product over out). The full puncture is
  `rootCoordinateOpen p t Finset.univ`, the inverse image of W. `Assertion` also
  binds `Z`, the reduced closed immersion `h` and its exact complementary range.
  Neither Z nor S is silently used as an extra assumption on the comparisons.
* `N` and `IsLisseCoefficientModule` are precisely the supplied finite locally free
  lisse module. `testModuleComplex` is its actual pullback to T[P], put in degree zero.
  `rootDiagram` uses the recorded profinite functor `profiniteToProEtOf`.
  `puncturedProjection` is the canonical open lift to V, not an arbitrary map.
* `full` is H_P and `punctured` is K_P. Their two `IsGE 0` conclusions express exactly
  zero cohomology in every negative degree in the ordinary unbounded derived category.
  Exact pullback allows N_P[0] to be restricted after the degree-zero embedding.
* For `J.Nonempty` and `J ⊆ univ \ out`, `rootFace` has U_J = Spec(R/baseIdeal t J),
  and V_J the actual fibre product with V; g and d are the two closed maps.
  `faceTerm` is the closed direct image of its exact inverse image. Closed images
  are exact here (finite unions of principal opens give quasi-compact complements),
  so the total-derived presentation is the canonical interpretation of d_* and g_*.
* `Assertion` supplies lambda and every mu as isomorphisms of derived objects.
  `lam.inv = openUnit ...` specifies exactly the inverse of the pushed actual open
  unit, using `RootCoordinateFace.lowerComp`, the adjunction-normalized composition.
  `mu.inv = faceUnit ...` specifies its normalized face comparison: pull the open
  unit to U_J, use the canonical mate for the open/closed square, then compose.
  Residual-face puncture invariance and coordinate-face comparison prove this inverse
  is invertible, as explained by steps 3--4 of the theorem docstring.
* `normalization` states `(Ra_*).map u ≫ mu.hom = lam.hom ≫ v`, where both u and v
  are the actual `adjunction.unit.app`. This is the node's displayed equation with
  Lean's left-to-right composition convention.
* `successive` uses the actual smaller-face adjunction unit, with normalized pullback
  and pushforward composition. `nested` states that the two mu maps intertwine these
  successive maps. Taking the canonical quotient maps and their cartesian restrictions
  gives every J ⊆ J'. The generic equation is also valid for identity and empty faces.
* `DiagramMap` and `FaceMap` bind actual commuting structural squares. `fullMap`,
  `puncturedMap`, `ambientMap`, `fullFaceMap`, `puncturedFaceMap` are explicitly the
  counit exchange mates followed by the supplied module map. `forward_naturality`
  gives their squares for the canonical forward units; `inverse_naturality` gives
  the requested lambda and mu squares. No naturality equation is replaced by an
  unspecified isomorphism or by a predicate assumed on the desired conclusion.
* To specialize naturality to P' → P, use the recorded profinite functor maps in the
  diagram. For module maps use identity geometric maps. For pro-etale base change
  use the cartesian projections (exchange is the actual localization map). For
  face/open-preserving tower automorphisms use their actual commuting maps and the
  supplied equivariant module arrow. For a profinite family Q use the same equations
  on the whole Q-parametrized schemes, with its supplied family action arrow. These
  formulas quantify over arbitrary diagrams of entire schemes and modules, so assert
  equality there, without reducing to any points of Q. Root-tower/profinite base-change
  identifies these terms with P × Q. Nested and normalization identify all augmentation
  and face arrows as well.
* No boundary trivialization, internal Hom comparison, completeness of Ω, positive
  rank, nonempty affine chart or nonempty profinite test is required or concluded.

Dependency declarations read and used:

* `Sheaf.Topology.ContinuousMapCondensedRing`: the recorded
  `Profinite.continuousMapRingSheafOfUniverse` and ring-object structure; the existing
  same-universe concrete instance comes from `ContinuousCoefficientUniverse` and
  `ContinuousCoefficientCommRing`, with the same continuous section presentation.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj` and `profiniteToProEtOf`, with their full docstrings/signatures.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, its action field and regular module.
* `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPushforward` and
  its exact-pullback adjunction interface.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme` (locally Noetherian
  and stalkwise regular); `StrictNormalCrossingsBoundary`: its full boundary predicate.
* `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
* `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`: the recorded theorem's full
  localization/exact-closed-image signature and actual unit/counit interpretation.
* Existing `RootTowerCoordinateFace`: base ideal, test schemes/maps, projection,
  actual derived adjunction, pullback/direct-image composition, `exchange` and its
  cube and pasting equations. Existing `RootTowerPunctureInvariance`:
  `rootCoordinateOpen`, and actual-unit puncture invariance for the proof plan.
* Existing `StrictLocalKummerTameModule`: `tameRootAlgebra` and its power/transition
  relations. The statement dependency list uses definition-node owners, including two new
  existing:true records for the seven previously unowned helpers. The two geometric
  theorem nodes remain proof dependencies only.

Edge cases checked before writing and during reading: empty out gives D(1) and the
identity outer open; r=0 has no admissible nonempty inner set; an empty affine chart,
empty face, empty P and rank-zero N remain allowed. J need not be a singleton, and
J=J' uses its actual identity restriction. The full root-face quotient need not be
confused with a nonreduced cartesian tower fibre: only the BASE face U_J appears here.
Universes use Scheme.{u}, Profinite.{u}, and Ab.{u+1}; site object and morphism
universes have not been forced equal.

Searches made with msearch.py (2026-10-24):

* LeanFinder: "Normalized derived direct image of punctured root tower and coordinate
  face restriction diagram": eight normalization-scheme hits, no derived face diagram.
* Loogle: `"rootTower", "unit"`: zero hits.
* grep Mathlib: `(rootTower|Kummer).*(face|punctur)|(face|punctur).*rootTower`: zero hits.
* LeanSearch: "Derived closed coordinate face diagram of a punctured compatible root
  tower with normalized adjunction units": eight normalization, simplicial and chart
  hits; none states this result.
* rg in both project roots found the existing coordinate-face, puncture and inner-support
  interfaces, but no declaration for this normalized punctured-face diagram. A literal
  item-id search in WeilConjectures also found none. The existing helpers are reused;
  the inner-support theorem additionally requires a boundary trivialization and has
  another conclusion, so is not an existing match for this statement.

No statement correction or disputed mathematical claim is reported. The source's latest
paragraph (3) is the open/proper direct-image route; the node is explicitly an agent-extracted
obligation on that route, and is not the blueprint unit's own statement.

## Second reading by NK

No second worker was started, as the dispatch expressly forbids it. The maintainer's
independent review reads this delivery. A final worker self-check compared every node
hypothesis and clause with the mappings above. It caught the initially omitted unused
Z/reduced-complement context, which is now explicit, and ensured that inverse naturality
is stated on whole parametrized terms, not only unit naturality or fibrewise equality.


## Repair of returned head 5b487df3c989

H2 is repaired without any Lean edit. The item module has SHA256
`cbd39092c4e16f369ada3cd879c041fed90d3e5fdc5b4ff09050705bcef8130e`, identical to
the returned delivery. Compared with current main, the item retains its mathematical
statement, proof, proof dependencies and all other non-worker fields. Its Lean binding
and definition dependencies are delivered on current main by the prescribed wrapper.

Removed `lem-sfb-root-tower-coordinate-face` and
`lem-sfb-root-tower-puncture-invariance` from `stmt_deps`; both remain in `proof_deps`.
The public imports still supply those proof-plan theorems. The definitions used to
write the statement are not theorem-chosen objects. Added
`def-sfb-test-map-derived-composition`, whose existing:true record owns
`RootCoordinateFace.Modules`, `upper`, `lower`, `adjunction`, `upperComp`, `lowerComp`,
`test` and `testMap`. Added the two existing:true definition nodes described below,
which own the six remaining face helpers and `rootCoordinateOpen`. The two legitimate
previously added definition dependencies (compatible root algebra and continuous
commutative coefficients) are retained. There is no statement correction.

H11 was advisory. No independent second worker was started, as the dispatch forbids
it; the maintainer's independent reading remains the substantive review. That review
explicitly found the hypotheses, normalized arrows, compatibility clauses, edge cases,
universes and docstrings sound. This repair changes only dependency ownership metadata
and the report. The new definition records were checked against the full declaration
signatures and real bodies, including their imported recorded dependencies.

## New nodes

`def-sfb-coordinate-face-exchange-data` records six already landed definitions in
`Sheaf.Paper.RootTowerCoordinateFace`: `exchange`, `squareUpper`, `towerProjection`,
`baseIdeal`, `baseInclusion`, `testModuleComplex`. The first two are the actual
pullback-composition comparison for a commuting square and its derived adjunction
mate. The next three construct the actual test-tower projection, coordinate ideal
and quotient closed inclusion. The last pulls a module to X[P] and places it in
degree zero. The TeX introduces every parameter and defines all six objects; it
assumes no exchange invertibility or lisse property. It cites the already owned
compatible root algebra and test/derived-composition constructions. Its lean.statement
is verbatim the `exchange` signature; its declarations list includes exactly these six
plain definitions. Source: latest direct-images paragraph (3), extracted normalized
coordinate-face construction. No new Lean source, proof, definition data or choice is
introduced.

`def-sfb-root-coordinate-open` records the already landed
`AlgebraicGeometry.ProEtale.rootCoordinateOpen` in
`Sheaf.Paper.RootTowerPunctureInvariance`. Its statement defines precisely the principal
open D(image of the selected parameter product) of the compatible-root algebra. It
cites the existing algebra definition and includes the empty selected set. Its
lean.statement is verbatim the declaration's signature. Source: the same paragraph
(3), its selected outer and full punctures. This is a definition-only existing:true
binding, not an invocation of puncture invariance.

For each new node the three actual msearch.py queries are recorded in mathlib_searches
with the raw search-result digest from searches.jsonl. The face-data query was
"Canonical coordinate face base ideals and inclusions, profinite root tower projection,
degree zero test module and derived counit exchange mate" (LeanSearch and LeanFinder:
eight unrelated generic declarations each); its Mathlib grep query was
`squareUpper|towerProjection|baseInclusion|testModuleComplex|RootCoordinateFace.exchange`
(zero hits). The open query was "Principal open subset of compatible root algebra
inverting a selected product of original parameters" (LeanSearch and LeanFinder:
principally `PrimeSpectrum.basicOpen` and localization lemmas); its Mathlib grep was
`rootCoordinateOpen` (zero hits). Thus Mathlib provides the generic basicOpen, while
the exact specialization is reused from the existing project declaration. Exact-name
searches in WeilConjectures gave no matches. Searches of all DAG definition nodes
found no owner for any of the seven new names; the eight shared names already owned
by `def-sfb-test-map-derived-composition` are deliberately excluded. Searches and
source reads in lean/Sheaf locate exactly the two recorded modules; no copy is made.
`blueprint_refs.py search` found zero nodes for "coordinate face" and
"root-coordinate-open"; `ancestor` returns null, inherited in both new records.

The new definitions retain empty index sets, empty schemes and empty profinite tests.
No new definition has a theorem as a statement dependency, no proof is postponed in
either new node, and the item's reviewed Lean source remains byte-identical.
