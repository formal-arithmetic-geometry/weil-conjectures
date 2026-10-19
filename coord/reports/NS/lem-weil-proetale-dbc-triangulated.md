## Worker report

The module `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` states
`AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated`, with
proof `sorry`. No definitions or additional nodes are introduced. The previous
wait is resolved: the constructible-sheaf dependency now has a reviewed Lean record.

Hypothesis and clause correspondence:

- An arbitrary scheme is `(Y : Scheme.{u})`; the finite commutative ring is
  `(A : Type u) [CommRing A] [Finite A]`. There is no Noetherian assumption on Y.
- The ambient category is the recorded `proEtaleDerivedCategory Y A`, with the
  small pro-etale site and ULift coefficient convention, module values in u+1.
- Cohomology in degree i is `(DerivedCategory.homologyFunctor
  (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K`.
  The module category and its standard localization instance are definitionally
  those of the recorded ambient category, not internal module objects.
- Vanishing in all but finitely many degrees is
  `Set.Finite {i : ℤ | ¬ IsZero (...)}`. This includes empty support.
- Constructibility of every cohomology sheaf is `∀ i : ℤ,
  IsConstructibleProEtaleModuleSheaf Y A (...)`, exactly the dependency's global
  finite-stratification predicate, including finite geometric stalks.
- Isomorphism closure is the first conjunct `P.IsClosedUnderIsomorphisms`.
- The full triangulated subcategory is the second conjunct `P.IsTriangulated`.
  Mathlib's class extends `ContainsZero`, `IsStableUnderShift ℤ` and
  `IsTriangulatedClosed₂`. Together with the first conjunct these give precisely
  the stated zero clause, the equivalence for every integer shift (use n and -n
  and the shift-composition isomorphism), and membership of the middle vertex of
  a distinguished triangle with outside vertices satisfying P. The triangle
  class's conclusion is initially isoClosure membership, which the first
  conjunct turns into P itself. No extra closure conditions are asserted.
  FullSubcategory has all ambient morphisms and its inherited triangulation.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor` (and its representing-complex factorization).
- `Sheaf.Paper.ProEtaleConstructibleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf`.
- `Mathlib.CategoryTheory.Triangulated.Subcategory`,
  `CategoryTheory.ObjectProperty.IsTriangulated`; read its fields and
  `ext_of_isTriangulatedClosed₂` and the full-subcategory instances.

All recorded proof-dependency modules are imported without `public`, unless
already public for a statement dependency. The docstring gives the node's five
proof steps, including common refinement, canonical coefficient identification,
localized restriction, finite local models and weak Serre closure. No proof was
filled. Read Stacks proetale.tex labels lemma-constructible-serre and
lemma-compare-constructible-derived; the latter's proof explicitly asserts strict
fullness and triangulatedness. The global finite-partition convention is the
blueprint's convention retained in the node, rather than an affine-local replacement.

Edge cases checked: empty scheme (one empty stratum is allowed), zero coefficient
ring, zero complex (empty support), cohomology in a single or finitely many
arbitrary degrees, positive and negative shifts, and schemes that are not
Noetherian or quasi-compact. No bound on degrees or Noetherian scheme hypothesis
has been inserted. Every universe and variable is explicitly bound. There are
no node faults, disputed statements, or statement corrections.

Searches (2026-10-15):

- msearch.py leanfinder: "Bounded complexes with constructible cohomology sheaves
  form a triangulated subcategory"; eight hits on DerivedCategory.TStructure.t,
  IsGE, IsLE and their supporting lemmas; no exact constructibility theorem.
- msearch.py loogle: "ObjectProperty.IsTriangulated,
  DerivedCategory.homologyFunctor"; zero hits, unknown identifier
  ObjectProperty.IsTriangulated. Read the actual Mathlib declarations directly.
- msearch.py grep: "constructible|Constructible" in
  Algebra/Homology/DerivedCategory; zero hits.
- rg of upstream WeilConjectures and side lean/Sheaf and lean/WeilConjectures for
  this item id and constructible/triangulated variants: no exact match. The
  upstream ProEtaleModule/DerivedCategory module was read in full: its
  `AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible` concerns internal
  module objects and requires TopologicalSpace.NoetherianSpace X. Its constructible
  predicate uses locally finite presentations, so it is not this node's statement.
  Other hits concern the etale site or a different derived constructibility class.
- Prior attempt's msearch leanfinder, loogle and Mathlib grep results are retained
  in searches.jsonl; they likewise found no matching statement. The new theorem
  name has no occurrence in either upstream or lean/Sheaf.

Validation: single-file compilation and the required delivery dry run are run
through the authorized wrappers. The independent second reading is left for the
second worker; this report does not claim it has occurred.

## Second reading by NS

I reread the node statement, its source (Stacks `proetale.tex`, Tags 09AL/09B5 and
06UQ), the dependency declarations, and the Lean module item by item.

- The scheme `Y` is rendered by `(Y : Scheme.{u})`; no Noetherian, separated, or
  quasi-compact hypothesis is added. This matches the node's arbitrary scheme.
- The finite commutative coefficient ring is `(A : Type u) [CommRing A] [Finite A]`.
  This is exactly the node's finite commutative ring and supplies the Noetherian
  condition used in the cited source proof.
- The ambient derived category is `proEtaleDerivedCategory Y A`, the recorded small
  pro-etale sheaf-of-modules category with the ULift coefficient convention.
- For each `i : ℤ`, cohomology is rendered by
  `DerivedCategory.homologyFunctor (proEtaleRingModules Y
  (proEtaleConstantRing Y A)) i`; this is the dependency's derived cohomology
  sheaf, with no replacement by internal module objects.
- Boundedness is `Set.Finite {i : ℤ | ¬ IsZero (...)}`, including empty support.
- Constructibility is `∀ i, IsConstructibleProEtaleModuleSheaf Y A (...)`, the
  dependency's global finite-stratification predicate (including finite geometric
  stalks).
- The conclusion is the conjunction of
  `ObjectProperty.IsClosedUnderIsomorphisms` and
  `ObjectProperty.IsTriangulated` for this same predicate. The latter is precisely
  the recorded full-subcategory triangulated-property interface: it supplies zero,
  all integer shifts, and closure of the middle object of distinguished triangles;
  the former supplies strict fullness/isomorphism closure. Quantifiers and shift
  directions are unchanged from the node.

No mismatch was found, so no Lean or node statement was changed. Edge cases checked
are the empty scheme and zero coefficient ring (the constructibility predicate still
permits a positive finite stratification), the zero complex (empty cohomology
support), one-degree and arbitrary finite supports, and positive and negative shifts.
Universes are explicit and the index universe is `ℤ`; no cases covered by the node
are excluded. Searches of Mathlib, `lean/Sheaf`, and upstream `WeilConjectures` found
no existing declaration of this theorem or an equivalent constructibility notion.
The module compiled cleanly with `scompile.py`; its only postponed proof is the
named theorem `proEtale_bounded_constructible_isTriangulated`.

Independent search details: LeanFinder query “Cohomology in a constructible class
closed under shifts and distinguished triangles” returned eight t-structure and
boundedness hits, none on constructibility; Loogle query `"IsTriangulated",
"homologyFunctor"` returned no hits. `rg` for constructible/Constructible in
Mathlib's DerivedCategory directory returned no hits. I also read the current
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` using
`scompile.py --source`: its `isTriangulated_boundedConstructible` has the extra
`[TopologicalSpace.NoetherianSpace X]` hypothesis and uses internal `Mod` objects.
It therefore cannot replace this arbitrary-scheme sheaf-of-modules statement.
The 51-module framework's BoundedConstructible module imports that interface;
its six-functor restrictions do not supply the theorem being stated here.
