## Worker report

`Sheaf.CategoryTheory.ProjectiveCochainSuspension` states
`HomotopicalAlgebra.projective_cochain_suspension`. Its conclusion is
`Nonempty (ProjectiveCochainSuspensionStatement.{u, t} R)`. This structure contains
all clauses of the node, including `ProjectiveCochainCoherentSuspension` for the
actual module-complex localization. The node statement, dependencies and proof
are unchanged; only its `lean` field changes. No new nodes or dependency repairs.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| A commutative ring R | `(R : Type u) [CommRing R]`. |
| All unbounded R-module cochains | `CochainComplex (ModuleCat.{u} R) ℤ`, without support restrictions. |
| Projective model and cofibrant Q | `ProjectiveCochainCofibration R (HasZeroObject.zeroIsInitial.to Q)`, the recorded cofibration predicate of `lem-coef-projective-cochain-monoidal-model`, applied to `0 → Q`. |
| Shift `Q[1]`, terms `Qⁿ⁺¹`, differential `-d` | Mathlib's `CochainComplex.shiftFunctor (ModuleCat.{u} R) 1`, whose definition reindexes by `n+1` and multiplies the differential by `(-1)^1`. |
| `C(Q)ⁿ=Qⁿ⊕Qⁿ⁺¹`, differential `(db+a,-da)` | `projectiveSuspensionCone Q := CochainComplex.mappingCone (𝟙 Q)`. Mathlib stores the shifted source before the target; its `snd` is b and `fst` is a. The helpers use those existing projections to retain the node's coordinate order. |
| Inclusion `b ↦ (b,0)` | `projectiveSuspensionConeInclusion := mappingCone.inr (𝟙 Q)`. |
| Inclusion is a cofibration; cone cofibrant and contractible | Fields `cone_inclusion_cofibration`, `cone_cofibrant`, `cone_contractible`, each under the stated cofibrancy hypothesis on Q. Contractibility is `Nonempty (Homotopy (𝟙 (projectiveSuspensionCone Q)) 0)`. |
| Ordinary pushout | `projectiveSuspensionPushout Q := pushout i i` for the two actual cone inclusions. |
| Pushout terms and displayed differential | `projectiveSuspensionExplicit Q`, constructed with `CochainComplex.of`. Its term is `(Q.X n ⊞ Q.X (n+1)) ⊞ Q.X (n+1)` and its differential is the explicit three-coordinate biproduct map `projectiveSuspensionDifferential`, giving `(db+a₁+a₂,-da₁,-da₂)`. |
| Identification as the stated ordinary pushout | `pushout_coordinates` asserts `IsIso (projectiveSuspensionCoordinates Q)`. This map is fixed by `pushout.desc` from the concrete legs `(b,a) ↦ (b,a,0)` and `(b,a) ↦ (b,0,a)`, so this is the actual coordinate identification. |
| Projection `(b,a₁,a₂) ↦ a₂` | `projectiveSuspensionProjection` has degree components `biprod.snd`. `projectiveSuspensionPushoutProjection` is its composite with the canonical coordinate comparison. No map is selected from a mere existence assertion. |
| Projection a quasi-isomorphism | Field `projection_quasi_iso` asserts `QuasiIso (projectiveSuspensionPushoutProjection Q)` for every cofibrant Q. Together with the coordinate isomorphism, this is also the displayed projection's quasi-isomorphism. |
| Natural in cofibrant cochain maps | `projection_natural` quantifies Q, Q', both cofibrancy hypotheses and every `f : Q ⟶ Q'`, and gives the naturality equation for these same canonical projections. The cone map is Mathlib's `mappingCone.map` on `(f,f)`; `projectiveSuspensionPushoutMap` is the actual induced pushout map. |
| Cone span represents `0 ← Q → 0` in coherent localization | `projectiveSuspensionSpanToZero` is the explicit natural transformation with components `𝟙 Q`, 0, 0. The coherent predicate says its localized transformation is an `IsEquivalenceEdge` in the coherent span functor category. |
| Ordinary pushout computes suspension | For every cofibrant Q the coherent predicate asserts `IsColimitEdge` for the localized cone span, at `object q (projectiveSuspensionPushout Q)`, with precisely the image of its ordinary colimit cocone. The span equivalence therefore identifies it with the defining zero-span suspension. |
| Suspension naturally isomorphic to `[1]` on the ordinary homotopy category | The coherent predicate supplies suspension/loop via recorded `HasSuspensionLoop`, and the canonical ordinary localization functor `L : CochainComplex ... ⥤ SSet.hoFunctor.obj C`. It requires `L.IsLocalization quasiIso` and its equality with q on every simplex after the nerve-adjunction unit. The `Nonempty (L ⋙ hΣ ≅ CochainComplex.shiftFunctor ... 1 ⋙ L)` clause is a natural isomorphism on all complexes, hence identifies `hΣ` with the functor descended from `[1]` by the localization universal property. |
| Stable coherent localization | The coherent predicate explicitly asserts initiality and terminality of localized zero, existence of limiting and colimiting cones for every finite simplicial K and diagram F, that `hΣ` is an equivalence, and unconditionally `∀ s, IsPushoutSquare s ↔ IsPullbackSquare s`. There is no additional invertibility hypothesis on suspension. |

`ProjectiveCochainCoherentSuspension` quantifies
`C : SSet.{max (u+1) t}` and
`q : largeNerve.{u+1,u,t} (CochainComplex (ModuleCat.{u} R) ℤ) ⟶ C`
with `FiniteReedy.IsLocalization quasiIso q`, exactly the supplied homotopy coherent
localization. Complex objects have universe u+1 and morphisms universe u; they are
not forced into one universe. The independent ambient universe t remains explicit.
The natural comparison holds for all complexes, so it covers the functorial
cofibrant replacement passage in the node, rather than just objectwise shifts.

Dependency declarations read and used:

* `lem-coef-projective-cochain-monoidal-model`:
  `Sheaf.CategoryTheory.ProjectiveCochainMonoidalModel`, theorem
  `HomotopicalAlgebra.projectiveCochainMonoidalModel`, its complete
  `ProjectiveCochainMonoidalModel` structure and the predicates
  `TermwiseSplitInjection`, `DgProjective`, `DgProjectiveCokernel`, and
  `ProjectiveCochainCofibration`. They fix cofibrancy and the model used in
  the proof plan; no extra model-structure hypothesis is added.
* `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`; its cochains, quasi-isomorphisms, mapping cone and
  cochain shifts are used directly. The ordinary homotopy category here is
  the coherent localization's `SSet.hoFunctor.obj C` with its explicitly
  specified ordinary localization functor L, so no second derived-category
  choice or hidden size restriction is introduced.
* `lem-coef-pointed-model-stability`:
  `Sheaf.CategoryTheory.PointedModelStability`, theorem
  `HomotopicalAlgebra.PointedModel.pointed_model_category_stability` and
  `HasSuspensionLoop`, `squareShape`, `IsPushoutSquare`, `IsPullbackSquare`.
  Its imported `FiniteReedy` interface supplies `largeNerve`, `IsLocalization`,
  `object`, `diagram`, `transformation`, and `IsColimitEdge`; the full signatures,
  source docstrings and canonical ordinary-comparison clause were read.

Every postponed theorem has a complete source/proof docstring and belongs to a
specific clause of this node: `projectiveSuspensionDifferential_sq` (d²=0 in
step 4), `projectiveSuspensionLeg_comm` (step 4 cone-leg chain identities),
`projectiveSuspensionLeg_agree` (step 4 pushout compatibility),
`projectiveSuspensionProjection_comm` (step 5 projection chain identity),
`projectiveSuspensionConeMap_inclusion` (step 6 functoriality), and
`projective_cochain_suspension` (the complete seven-step node proof). All six
proofs are `by sorry`. Each definition has concrete data; the named theorems
supply only the construction's proof fields. No theorem is proved here.

Edge cases checked mathematically before the final statement:

* Q=0 and the zero ring: cones, triple objects and projections reduce to zero;
  no `Nontrivial`, `Nonempty` module-carrier or characteristic hypothesis occurs.
* Q=R[0]: the double cone pushout has the expected degree -1 kernel of the sum
  map, and projection of that kernel to a₂ gives the degree -1 shifted copy of R.
* Characteristic two: the cancellation argument and the section `(0,-a,a)`
  still work; no division by 2 or difference projection is used.
* Arbitrary unbounded Q and every integer n, including n=0: the formulas
  require no boundedness, induction start, finite generation or projectivity
  hypothesis beyond the model's cofibrancy condition.
* Empty finite simplicial K: the two finite-(co)limit clauses include this
  case and assert zero is both initial and terminal.
* Identity, zero, and arbitrary maps of cofibrants: naturality uses the same
  canonical projections and induced maps, without existential replacement maps.

Searches made for an existing theorem (2026-10-17):

* `msearch.py ... leanfinder "suspension in the projective model category of unbounded module cochain complexes is the cochain shift"`: eight hits, including `CochainComplex.isKProjective_shift_iff` and `instHasShiftInt`; these provide shifts/K-projectivity, not the pushout calculation and coherent stability.
* `msearch.py ... leansearch "The homotopy pushout of zero from a cofibrant module cochain complex to zero is naturally its cochain shift"`: eight ordinary Hom-complex shift/homotopy hits; no exact theorem.
* `msearch.py ... loogle "CochainComplex.mappingCone, Homotopy"`: twelve hits including the existing identity-cone contraction `mappingCone.homotopyToZeroOfId` and cone map/homotopy constructors. Those existing cone constructions are used; none states this whole theorem.
* An earlier Loogle query using unqualified `shiftFunctor` yielded no hits and an unknown-identifier note; it was replaced by the successful query above.
* `msearch.py ... grep "suspension|homotopyPushout|stable" Algebra/Homology`: seventeen quasi-isomorphism/shift/injective-model hits, no exact theorem.
* Direct `rg` of `projectiveSuspension|projective_cochain_suspension|suspension.*cochain|cochain.*suspension` over `WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json`: no existing declaration. Search for this item id in upstream `WeilConjectures/`: none. The DAG's `lem-pur-system-section-suspension` concerns sheaf flat-model systems, not one ring's projective model, as its recorded review also confirms.

The local blueprint proof was opened. It supplies the parent compact-support
argument, while the node explicitly attributes the cone calculation to the
agent-extracted proof, not to a non-existent Stacks theorem. No change to the
source or the node statement is needed. No `STATEMENT-DISPUTED` flag.

Validation: `scompile.py Q115 lem-cbc-projective-cochain-suspension
lean/Sheaf/CategoryTheory/ProjectiveCochainSuspension.lean` compiled the final
module separately in sandbox and library position, with no errors or warnings.
No global build was run. Every line is at most 100 characters.

## Second reading by Q115

Author self-check under the direct-delivery brief; the maintainer supplies the
independent review. I reread the node, dependency records, source declarations
and final module, matching each hypothesis and clause against the table above.
The initial draft's arbitrary coordinate isomorphism, unrelated existential
naturality maps, objectwise-only comparison and conditional stability were
replaced before delivery: coordinates are now `pushout.desc` of the specified
legs; both naturality sides use the fixed projection; the ordinary comparison
is a natural isomorphism on all complexes with a canonically specified L; and
coherent stability is unconditional for localization of this same module
category. The projection's chain-map proof was extracted into the named
`projectiveSuspensionProjection_comm`, so its definition contains no `sorry`.
The complete seven-step proof and all five helper proof plans are in docstrings.
The displayed differential, its signs, the two legs, and the rightmost projection
were checked against the node, including characteristic two and Q=0. The final
compile is clean. The node record lists every declaration and records the
main signature verbatim up to (excluding) `:=`, as required by preflight.
