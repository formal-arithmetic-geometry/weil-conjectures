## Worker report

The module `Sheaf.Paper.StratifiedCohomologySliceModels` states
`AlgebraicGeometry.Etale.stratified_cohomology_slice_models`. It has exactly one
postponed theorem and no new definitions. The node is unchanged except for `lean`.

Source read: Stacks `etale-cohomology.tex`, lemma-constructible-quasi-compact-quasi-separated
(Tag 095E), lines 11717 onward, and lemma-constructible-abelian (Tag 03RZ), lines 11828
onward; also the complete source module `Sheaf.Paper.FiniteFieldStratifiedPerfectModels`,
particularly `commonStratification`, `finiteLocalModels`, and the homology-restriction
argument in its main theorem. The private helpers there do not state this node: the
first concerns a finite family of sheaves, the second starts with a single finite locally
constant sheaf, and the public result assumes a field and concludes perfect complex
models. This item instead concerns cohomology slices over any finite commutative ring.

Hypotheses and clauses, in order:

- A Noetherian scheme is `(X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]`.
  These are precisely the node's local Noetherian and quasi-compact conditions.
- The finite commutative coefficient ring is `(B : Type (u + 1)) [CommRing B] [Finite B]`.
  This is the recorded constructible-sheaf coefficient universe, without a nonzero-ring
  or field hypothesis.
- Constant-coefficient module sheaves use `Sheaf X.smallEtaleTopology (ModuleCat B)`.
  This is exactly the encoding of both recorded `IsConstructibleEtaleModuleSheaf` and
  `Etale.upperStar`; the accepted constant-ring module/sheaf encoding convention applies.
  Morphisms and slice isomorphisms are B-linear, since they are in module-valued sheaves.
  `ringedSiteModules` is imported as the general ringed-site interface; it is not copied.
- The ordinary unbounded derived object is `L : DerivedCategory (Sheaf ... (ModuleCat B))`.
  Existing Grothendieck-abelian sheaf and derived-category instances supply its chosen
  localization, including every stratum's category. No bounded derived-category model
  or extra existence assumption is introduced.
- The integers and their order are `(a b : ℤ) (hab : a ≤ b)`.
- `hvan` says `IsZero ((DerivedCategory.homologyFunctor ... q).obj L)` for
  `q < a ∨ b < q`, exactly vanishing outside the closed interval.
- `hconstructible` quantifies over every integer q and uses the recorded
  `Scheme.IsConstructibleEtaleModuleSheaf` on that homology object.
- The existential `S : Scheme.FiniteLocallyClosedStratification X` supplies a finite
  partition, locally closed subsets, pairwise disjointness, coverage, scheme domains,
  immersions and their set-theoretic image equalities. The separate clause
  `∀ s : Fin S.n, Topology.IsConstructible (S.stratum s)` imposes constructible images.
- In every conclusion, the exact derived inverse image K_s is written out as
  `(upperStar (ModuleCat B) (S.immersion s)).mapDerivedCategory.obj L`.
  It is not an arbitrary derived object or an assumed comparison.
- The first conjunct for each stratum states `IsZero` for its cohomology outside [a,b].
- The second conjunct is quantified over all `q : ℤ`, including outside [a,b], and
  every `V : (S.domain s).Etale`.
- `(I : Type (u + 1)) (U : I → (S.domain s).Etale) (f : ∀ t, U t ⟶ V)` gives the
  covering members, with index in the coefficient universe. Every arrow is a morphism
  of the small etale category, hence is over the stratum and is etale.
- `Sieve.ofArrows U f ∈ (S.domain s).smallEtaleTopology V` is the covering condition.
  The recorded `Scheme.ofArrows_mem_smallEtaleTopology_iff` identifies it with joint
  surjectivity of the underlying scheme maps. A second conjunct repeating joint
  surjectivity would be redundant.
- `∀ t, ∃ M : ModuleCat B, Finite M ∧ Nonempty (...)` gives finite underlying module
  sets. In particular these are finitely generated; the statement does not substitute
  finite generation for finite sets.
- The isomorphism source is literally the homology sheaf's `.over (U t)` and its target
  is `(constantSheaf ((S.domain s).smallEtaleTopology.over (U t)) (ModuleCat B)).obj M`.
  Thus the site is the actual category `Over (U t)` with the localized topology; the
  target is sheafification of the constant module presheaf. No replacement by stalks,
  underlying abelian groups, or merely the small etale site of the covering scheme occurs.

Statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (available through the public imports).
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`,
  and `Scheme.ofArrows_mem_smallEtaleTopology_iff` (through the constructibility module).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent existing general-site `SheafOfModules` interface.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; its homology functors and exact functor descent are exposed by
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`. The current actual declaration uses the
  constructible `Scheme.Stratification`; its finite-value clause and required input
  category are exactly those needed here. No duplicate older Sheaf module is imported.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification` and its topological parent.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible` (the recorded Mathlib match).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar` (exposed by
  the constructibility module); additive and exact instances are already supplied there.
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`, `Sheaf.over`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` is the recorded
  localized-ringed-site module. In this accepted module-valued-sheaf encoding the actual
  restriction is `Sheaf.over`, one of that dependency's explicitly recorded declarations.
- `def-weil-size-convention` is metatheoretic. Explicit universe u and coefficient
  universe u+1 implement it; there is no declaration to import.

All recorded proof modules are imported privately: inverse-image exactness;
constant-left-module inverse image; etale restriction; the module-linear composition
core; the base-change-stable precoverage Mathlib match; geometric constant-module
comparison; constructible-stratification intersection; exact-derived-cohomology coherence;
and etale slice-site equivalence. The seven-step docstring retains the node's entire
proof route, including scalar linearity, actual fibre products, finite induction, all-degree
vanishing, actual slice transport, and the coefficient-universe reindexing argument.

Edge cases checked: no `Nonempty` requirement on X, stratum domains or covering indices;
zero strata are permitted by the stratification type when X is empty; empty individual
strata are retained. Empty V admits the identity cover and zero module. The zero ring is
allowed by `CommRing B`, and the zero complex satisfies every conclusion using zero values.
The case a=b is retained. For degrees outside [a,b], the conclusion still asks for the
local models, supplied by zero. No flatness of an immersion or freeness of a finite module
is assumed. The site object and morphism universes remain those of `Scheme.{u}.Etale`;
they are not forced equal, and the cover index and coefficient modules lie in u+1.

Searches actually run with `msearch.py Q55 lem-weil-pbc-stratified-cohomology-slice-models`:

- `leanfinder`: "Bounded constructible etale derived complexes admit a finite common
  stratification with finite constant cohomology models on every slice site": 8 hits,
  including the small etale topology/pretopology and etale composition instances; none
  states this theorem.
- `loogle`: `"Sheaf", "homology"`: 7 hits, including sheaf cohomology presheaves/functors
  and one-cohomology relations; no simultaneous stratification or finite slice models.
- `grep`: `stratif.*(homology|cohomology)|constructible.*(complex|cohomology)`: 4 hits,
  all in `Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean`; no match.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `finiteLocalModels`, `commonStratification`, and stratified cohomology names found the
  source private helpers and unrelated scalar-cohomology results, not this statement.
  The proposed declaration name also has no existing match in `dag/lean_names_upstream.json`.

No new nodes, dependency repairs, statement correction, or mathematical dispute is needed.

## Second reading by Q55

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
