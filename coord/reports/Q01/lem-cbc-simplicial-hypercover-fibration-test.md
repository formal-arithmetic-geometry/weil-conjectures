## Worker report

The module `Sheaf.CategoryTheory.SimplicialHypercoverFibrationTest` states
`CategoryTheory.LocalSimplicialPresheaf.simplicial_hypercover_fibration_test`, with
`sorry` as its only theorem proof. The auxiliary `simplicialAugmentation` is the
actual given hypercover augmentation with the two functor variables flipped.
Its data is `Functor.flipping.functor.map U.hom`, with no choice or postponed
existence assertion.

The source was opened online: Dugger--Hollander--Isaksen,
https://arxiv.org/pdf/math/0205027v2, Lemma 6.4 (printed pp. 17--18) and the
projective paragraph in the proof of Theorem 6.2 (printed p. 18). The latter
specifically requires replacing the hypercover by a projectively cofibrant object
before taking mapping spaces. The proof docstring records all seven steps of the
DAG proof, including that replacement, the cotensor corner, and strict path lifting.
No node statement is corrected or disputed.

Clause-by-clause rendering:

- The small ordinary site is `{C : Type u} [SmallCategory C]` and
  `J : GrothendieckTopology C`. Mathlib's topology consists of covering sieves,
  with maximality, stability, and transitivity. There are no pullback,
  subcanonical, nonempty, or finite-site hypotheses.
- The size convention is an explicit common working universe `u`: site objects,
  arrows, presheaf values, and hypercover summand indices are small there;
  categories of these objects live one universe higher. This is the same small
  ordinary-category convention as the recorded projective-model and localization
  declarations. The arbitrary level `u` is not fixed to `0`.
- The representable is the existing `SSet.ProjectivePresheaf.representable T`.
  Its values are discrete simplicial sets on `Hom(-,T)`. Hypercover augmentations
  use the canonically lifted representable already fixed by `AugmentedOver`;
  this is canonically isomorphic to that discrete representable.
- `I : C → Type u` and `H : ∀ T, I T → AugmentedOver.{u,u} C T` give the small
  family, indexed globally by the small type `Σ T : C, I T`. Repetitions are
  harmless. `hH` asserts that each member is a hypercover. `IsHypercover` requires
  semirepresentable terms and all proper-face augmented presheaf matching maps
  to be epimorphisms after `presheafToSheaf`. In degree zero its matching object
  is the terminal object of the presheaf slice, namely the augmentation target.
  It does not compute matching objects in the site.
- `hDense` quantifies over every target `T` and every hypercover `U` over it, and
  supplies an index `i` and `Nonempty (H T i ⟶ U)`. A morphism in `AugmentedOver`
  is a morphism in the slice, so the refinement commutes with the augmentation
  and stays over exactly the same `T`. No chosen refinement is assumed.
- `m`, `hW`, and `hF` specify the projective model structure: its weak equivalences
  are objectwise Kan--Quillen weak homotopy equivalences and its fibrations are
  objectwise horn-right-lifting maps. The cofibrations are thereby determined by
  the model axioms, rather than being replaced by all monomorphisms.
- `E` and `hE` specify its usual simplicial enrichment via the recorded
  `IsUsualEnrichment`, including underlying arrows and composition. `Q`, `ε`,
  and `hQ` specify an original-model functorial cofibrant replacement with a
  natural trivial-fibration augmentation. They are presentation data for the
  node's projectively derived mapping spaces, available by the recorded
  projective-model and localization statements, not extra site hypotheses.
- `L`, `hLC`, and `hLW` specify the stipulated left Bousfield localization:
  unchanged projective cofibrations and the existing `localEquivalences` for
  the actual family of augmentation maps. The latter uses derived
  precomposition into every projectively fibrant local object. `hLF` records
  exactly the node's fibrant-object characterization through the existing
  `IsLocal`. Explicit `@... m E` keeps these tests in the original model and
  enrichment even though `L` is also in scope. This avoids the local-instance
  ambiguity described in `BousfieldLocalFibrations`.
- `{X Y}` and `p` are the given simplicial presheaves and morphism. `hp` is the
  localized fibration hypothesis; `hX` and `hY` are their localized fibrancy,
  expressed by their terminal arrows. `hw : IsLocalWeakEquivalence J p` is
  precisely the existing associated-components and positive homotopy-sheaf
  condition, on all restrictions/basepoints in every slice. Original Kan
  fibrancy of both objects follows from `hLF`; it is not an extra assumption.
- The first conclusion quantifies over every `T` and asserts both
  `SSet.modelCategoryQuillen.J.rlp (p.app (op T))` and
  `SSet.Enhanced.IsWeakHomotopyEquivalence (p.app (op T))`: exactly an
  objectwise trivial Kan fibration.
- The second conclusion quantifies over every `T` and `n : ℕ` and uses
  `HasLiftingProperty` for the actual tensor of the discrete representable
  with the boundary inclusion. This quantifies over every commutative square
  and asserts a strict diagonal with both triangle equations. The tensor is
  Cartesian and computed objectwise. Dimension zero is included.

Dependency declarations used, read in their recorded source modules:

- `def-weil-size-convention`: its recorded metatheoretic convention, no Lean
  declaration or module; rendered by explicit universe `u`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, and `sheafificationAdjunction`, used through `IsHypercover`
  and `IsLocalWeakEquivalence`.
- `Mathlib.AlgebraicTopology.SimplicialSet.Basic`, `Degenerate`, `Subcomplex`,
  and `Finite`: `SSet`, `SSet.degenerate`, `SSet.nonDegenerate`,
  `SSet.Subcomplex`, `SSet.Finite`; standard simplicial sets, subsets, and
  finite-boundary conventions. The dependency is a Mathlib-match node and
  needs no separate lean repair.
- `Sheaf.CategoryTheory.SimplicialPresheafLocalizationComparison`:
  `SSet.ProjectivePresheaf.simplicial_presheaf_localization_comparison` and its
  imported `CategoryTheory.BousfieldLocalization.IsLocal`/`localEquivalences`
  from `Sheaf.CategoryTheory.BousfieldLocalFibrations`. These specify the
  localization using actual projectively derived mapping spaces.
- `Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel`:
  `SSet.ProjectivePresheaf.representable`, `IsUsualEnrichment`, and
  `simplicial_presheaf_projective_model`; used for the projective presentation
  and the actual representable boundary maps.
- `Sheaf.CategoryTheory.BoundedRepresentableHypercover`:
  `CategoryTheory.DerivedHypersheaf.AugmentedOver` and
  `augmentedOverToAugmented`.
- `Sheaf.CategoryTheory.DerivedHypersheafPresentation`:
  `CategoryTheory.DerivedHypersheaf.IsHypercover` and `IsSemirepresentable`.
- `Sheaf.CategoryTheory.LocalSimplicialPresheafMaps`:
  `CategoryTheory.LocalSimplicialPresheaf.IsLocalWeakEquivalence`, whose
  positive homotopy clauses use the recorded `Pi` and `piMap`.

The four additional statement dependencies are already landed nodes for the
last four notions above; none introduces a new notion or changes the statement.
All original statement dependencies are retained. The stated proof dependencies
are reached through the comparison module and explicit proof imports
`HypercoverRelativeLifting` and `SimplicialModelCoherentDiagrams` (including
`KanQuillenRightProper`, `SimplicialModelNerveLocalization`, and the projective
model). `lem-coef-simplicial-bousfield-model-structure` has no recorded Lean
module on the base and therefore has no proof-only import yet. This does not
prevent stating the item: the localized model is stipulated in its hypotheses,
and the generic theorem is only used by its future proof.

Edge cases checked before writing and again against the completed signature:
empty category (all target conclusions and density tests are vacuous), empty
`I T` (allowed; density then fails whenever a hypercover exists), repeated family
members, empty covering sieves, nonsubcanonical sites, and sites without fibre
products are all admitted. For `n=0`, the left tensor factor has the empty
boundary and `HasLiftingProperty` requires lifts of vertices. No positive-degree
basepoint is demanded when a presheaf has no vertices; the independent sheafified
components condition remains. No projective cofibrancy of hypercovers is assumed.
Both source and target localized fibrancy are retained.

Searches for an existing statement (2026-10-17):

- `msearch.py ... leanfinder`, query “A local weak equivalence fibration between
  fibrant hypercover local simplicial presheaves is an objectwise trivial Kan
  fibration”: eight hits, on Mathlib one-hypercovers and Kan fibrations; none
  states this dense-hypercover localization theorem.
- `msearch.py ... leansearch`, query “A local weak equivalence fibration between
  fibrant hypercover-local simplicial presheaves is objectwise a trivial Kan
  fibration”: eight hits, on generic `trivialFibrations` and fibrant-object model
  lemmas; none identifies homotopy-sheaf equivalences with objectwise acyclicity
  for hypercover-local fibrants.
- `msearch.py ... loogle`, query `SSet.modelCategoryQuillen.I, HasLiftingProperty`:
  zero hits, unknown unqualified `HasLiftingProperty`. The actual qualified
  boundary/horn declarations were then read directly in
  `Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean`.
- `msearch.py ... grep`, query `hypercover|Hypercover`, directory
  `AlgebraicTopology`: zero hits.
- `rg -n 'hypercover.*fibration|fibration.*hypercover|simplicial_hypercover_fibration_test'`
  in the source `WeilConjectures` and side `lean/Sheaf`: no source hits; side hits
  are the relative-lifting/cotensor primitives and the generation proof that
  cites this item, not its assertion.
- `rg -n 'lem-cbc-simplicial-hypercover-fibration-test'` in source
  `WeilConjectures`: zero hits. Existing side hypercover and local-map modules
  were opened and reused; no duplicate definition was needed.

Validation: `scompile.py Q01 lem-cbc-simplicial-hypercover-fibration-test
<module>` compiled the module in sandbox and library positions, plus required
side overlays, with exit status zero and no errors or warnings. All variables
and the single universe are explicitly bound; `autoImplicit` is false.

## Second reading by Q01

Author's second reading, under the dispatcher protocol; the maintainer supplies
the independent review. I reopened the node statement and the final module and
checked the smallness, covering-sieve topology, representable augmentation,
semirepresentability, every matching degree, same-target refinement, density,
original and localized model classes, derived locality, both endpoint fibrancy
hypotheses, homotopy-sheaf equivalence, objectwise trivial fibration, and every
representable boundary square. Each corresponds to the binders and conclusions
listed above. The auxiliary augmentation is exactly the stored map, not an
arbitrary map of the same type. `@IsLocal` and `@localEquivalences` select the
original model explicitly. The family is globally small and includes arbitrary
refinements without requiring them to be monomorphisms or covers in each degree.
The two conclusions are equivalent descriptions included explicitly in the node,
not extra hypotheses. No semantic mismatch or statement correction was found.
An initially guessed proof import had no published module; it was removed before
compilation, and the unstated proof dependency is recorded above. The statement
and report were not independently reviewed by another worker in this session.
