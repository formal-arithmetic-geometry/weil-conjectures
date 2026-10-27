## Worker report

Stage 2, Q107, 2026-10-24. The module
`Sheaf.AlgebraicGeometry.SeparablePointCotangentFiltration` states
`AlgebraicGeometry.SeparablePointCotangentFiltration.separable_point_cotangent_filtration`.
This is the only postponed theorem. Its proof is `sorry`; its docstring supplies all seven
steps of the accepted DAG proof, with the non-elementary inputs described. Six public helpers
construct precisely the closure, inclusion, open, recursion, and evaluation used by this node.
They belong to this construction (the helper authorization in the supplied isolation brief),
contain real data, and are all listed in `lean.declarations`. No new independent notion,
new node, dependency repair, or statement correction is required.

Hypotheses, one by one:

- `k Ks : Type u`, `[Field k]`, `[Field Ks]`, `[Algebra k Ks]`, `[IsSepClosure k Ks]`
  give the field and its algebraic separable, separably closed extension. Read the actual
  `IsSepClosure` signature: its `separable` field is algebraic separability, and its
  `sep_closed` field is `IsSepClosed Ks`. Perfectness is not assumed.
- `Z : Scheme.{u}` and `f : Z ⟶ Spec (.of k)` give the k-scheme. The two instances
  `[LocallyOfFiniteType f] [QuasiCompact f]` are exactly finite type in the recorded
  finite-type-morphism interface; no separatedness or smoothness of Z is assumed.
- `M : Z.Modules` and `hM : RingedSpace.IsCoherent Z.toRingedSpace M` use the actual
  finite-type-and-finite-type-kernels coherence predicate exposed by the dependency.
  They do not replace coherence by bare quasi-coherence or finite presentation.
- `P : Set (Spec (.of Ks) ⟶ Z)` together with `hP : ∀ p ∈ P, p ≫ f = Spec.map ...`
  gives an arbitrary set of k-morphisms, allowing distinct morphisms with the same image.
  This is equivalent to a set of elements of the subtype of k-morphisms.
- All objects have an explicit common universe `u`, the scheme interface's universe;
  any given field/closure/scheme data fit after a common universe enlargement. There is
  no independently smaller universe of test algebras or an equality imposed on site universes.

Construction and conclusion, clause by clause:

- `closedHull Q` is the topological closure of the images of the specified Q, using the
  unique point `IsLocalRing.closedPoint Ks` of Spec Ks. `hull Q` is literally the
  dependency's `(vanishingIdeal (closedHull Q)).subscheme`, and `hullι Q` its subschemeι.
  In particular the closures have the specified reduced induced structure, not an
  arbitrary reduced closed scheme with unspecified identification.
- `goodOpen f M Q` is `sSup` of exactly the opens V for which
  `Smooth (V.ι ≫ hullι Q ≫ f)` and
  `(((tensorPullback (hullι Q)).obj M).over V).IsFiniteLocallyFree`.
  This is the union stipulated by the node. The existing finite locally free predicate
  means a local finite free basis and allows different finite ranks on different opens.
  In particular it imposes no global constant rank condition.
- `remaining f M P 0 = P` is P_1. The successor case retains those points of the previous
  set whose image is outside `hullι Q '' goodOpen f M Q`. Thus `remaining ... n` is P_(n+1),
  `hull (remaining ... n)` is Z_(n+1), and `goodOpen ... (remaining ... n)` is U_(n+1).
- For every n, `GeometricallyReduced (hullι (remaining ... n) ≫ f)` states geometric
  reducedness of that k-scheme. The Mathlib predicate tests the reducedness of base
  changes along field-valued maps, so over Spec k this means every field extension.
- `Dense (goodOpen ... : Set (hull ...))` is density of U_i in Z_i, for every i >= 1,
  including the empty stages after termination.
- For every `V : (hull ...).affineOpens`, the iterated infimum of `RingHom.ker
  (evaluation q V.1 hV)` is bottom. The indexing consists of p in P_i and all its lifts
  q through the specified reduced closed immersion, with `hV : ⊤ ≤ q ⁻¹ᵁ V.1`.
  Each p in P_i has a unique such lift before the open condition: its image lies in
  its closure and its field-valued map kills the defining radical ideal. Since Spec Ks
  has one point, hV means exactly that p lands in this affine open. The map is the actual
  q.appLE on sections composed with ΓSpecIso, so the codomain is Ks, not an arbitrary
  residue ring or an unconstrained evaluation. Repetitions of proofs/lifts do not
  change the intersection. This expresses precisely the stated evaluation-kernel clause.
- The existential j from the next hull to the current hull satisfies
  `IsClosedImmersion j`, `j ≫ hullι current = hullι next`, and
  `Set.range j ⊆ (goodOpen current : Set _)ᶜ`. This is the inclusion
  Z_(i+1) ⊆ Z_i minus U_i with the indicated induced closed structures.
- `∃ t : ℕ, remaining ... t = ∅` is P_(t+1) empty for finite t >= 0.
  In that same existential the equality with the union over `i : Fin t` gives the
  decomposition of P by P_(i+1) minus P_(i+2), and `Pairwise ... Disjoint` gives
  disjointness. There are exactly t parts, representing paper indices 1 through t.
- The last conjunct assumes `P.Nonempty`, `remaining ... t = ∅`, and
  `∀ s < t, remaining ... s ≠ ∅`, exactly minimal termination. It then quantifies
  `p ∈ P`. Its equivalence between image membership in `Set.range (hullι
  (remaining ... (t - 1)))` and membership in `remaining ... (t - 1)` is the
  Z_t/P_t equivalence. Its final implication places every such remaining point in
  `hullι ... '' goodOpen ...`, namely U_t. Nonempty P and minimality force t > 0,
  so natural-number subtraction here does not lose the t = 1 case.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`, and `Scheme.ΓSpecIso` (Spec and its functorial map are the recorded spectrum).
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, whose statement specifies
  the vanishingIdeal subscheme, its reducedness, image and uniqueness. Its actual
  construction uses Mathlib's `vanishingIdeal`, `subscheme`, and `subschemeι`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: public exposure of
  `AlgebraicGeometry.RingedSpace.IsCoherent`, also read in
  `WeilConjectures.AlgebraicGeometry.Coherent`. The node's recorded conjunction alone
  is not used as a substitute for coherence; its repaired public coherence interface is.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` and `IsSepClosure`; Mathlib `Field`
  supplies the field dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and its
  quasi-compact interface `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly exposes
  `Scheme.Modules.tensorPullback` from `WeilConjectures.AlgebraicGeometry.TensorPullback`;
  the definition uses its actual tensorPullbackObj, not an arbitrary adjoint.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree` (existing variable-rank finite free notion).
- `Mathlib.AlgebraicGeometry.Geometrically.Reduced`: `GeometricallyReduced`.

All stated proof-dependency modules are imported, without public visibility when used
only by the proof. In particular these include SlicingFlat.dense_smoothLocus,
ReducedPolynomialModuleGenericFreeness, GeometricReducednessFiniteInseparableTest,
AffineChartBaseChangeIso, ModulePullbackFiniteType, the quasicoherent-pullback Tilde
extension, QuasicoherentFiniteTypeAffine, SeparablyGeneratedTensorReduced,
CoherentFiniteTypeLocallyNoetherian, Mathlib Tilde, FinitePresentation, Noetherian,
Topology.NoetherianSpace and Order.WellFounded. No proof import is omitted for a cycle.

Source checking: opened the primary BLR scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
PDF p.73 (3.3 Lemma 4), p.78 (canonical reduced closures and largest smooth free opens),
and p.79 (termination and final permissible stratum). The source is the same as the node's;
the coherent-module generalization is explicitly already in the node. The current blueprint
unit is not altered. No statement fault or STATEMENT-DISPUTED concern was found.

Edge cases checked before writing and in the second pass: P empty (t = 0 and the union
indexed by Fin 0 is empty); empty Z; a single separable point (t = 1, last index 0);
nonreduced ambient Z (the hull construction takes the reduced structure); imperfect fields
(no PerfectField assumption); P omitting most separable points; distinct Ks morphisms
with the same image; zero M (rank zero is permitted); rank varying between components;
repeated empty stages; and an affine open containing none of the indexed points. In the
last case density forces the affine open to be empty, whose zero ring makes the empty
intersection top equal bottom, as required.

Searches (2026-10-24):

- msearch.py leanfinder, query "Separable rational points define reduced closures with a
  dense smooth locally free locus and finite descending filtration": 8 hits, including
  Algebra.smoothLocus, Algebra.isOpen_smoothLocus, Algebra.IsGeometricallyReduced, smooth
  presentations, and normalization reducedness; none states this filtration.
- msearch.py loogle, query "AlgebraicGeometry.IsGeometricallyReduced,
  AlgebraicGeometry.Scheme.Modules.IsLocallyFree": 0 hits; first identifier unknown.
  Direct source inspection found the correct names GeometricallyReduced and
  SheafOfModules.IsFiniteLocallyFree and reused both.
- msearch.py grep, query "separab.*[Ff]iltration|[Ff]iltration.*separab|[Ff]initeLocallyFree"
  in AlgebraicGeometry: 0 Mathlib hits. rg of both project roots for local-free predicates
  found the existing variable-rank finite local freeness definition, which is reused.
- msearch.py leansearch, query "Reduced closures of separable rational points and coherent
  modules admit a finite canonical filtration with dense smooth locally free opens":
  8 hits about separable closures and Ideal.Filtration, no matching statement.
- rg on lean/WeilConjectures and lean/Sheaf for the item id, separable-point filtration,
  and the proposed namespace found no matching declaration. The unrelated finite
  second-curve filtration is not this construction. No existing exact statement was found.

Validation: the prescribed scompile.py compiled this file both as the sandbox module and
as its final library module, exit 0, with no compiler messages. No local lake/global build
was run. autoImplicit and relaxedAutoImplicit are both false. All source lines are <= 100.

## Second reading by Q107

A separate pass reread the node and the complete final module against the clause list above.
It checked the nonconstant-rank finite local freeness interface, actual tensor pullback,
closure images and reduced structure, affine evaluation to Ks, all three recursive index
shifts, closed-subscheme inclusion, disjointness, and the universal minimal-t conclusion.
No mismatch requiring a change was found. This is the worker's self-audit; no separate
agent was started (the dispatcher brief prohibits it). The maintainer's independent review
is the independent reading requested by this delivery workflow.
