## What changed

Retained the interrupted attempt and verified its Lean proofs of the classical image,
the counit, and the restricted-adjunction equivalence against the current sources. The original theorem has exactly its old
signature. Two new modules separate the classical image and the counit
assertion; both are fully proved. The image proof explicitly compares small-model and
standard-model homology through the localization universal property; no definition
or existing statement changes. All three modules compile with lcompile --all.

## Proved and sorry left

Closed: AlgebraicGeometry.ProEtale.classicalDerivedEquivalence (one original hole),
by a complete construction of the equivalence from the image and counit statements.
Proved: AlgebraicGeometry.ProEtale.classicalDerivedImage (new, no hole).
Proved: AlgebraicGeometry.ProEtale.classicalDerivedCounit
(lem-pe-classical-derived-counit), using the existing proved
DerivedCategory.Plus.isIso_app_of_forall_homology theorem. Its sheaf base case
comes from the comparison image and the triangle identity, and its lower-bound
hypotheses from exact inverse image and right-derived negative vanishing.
Holes closed: one, classicalDerivedEquivalence. Holes added: zero.
No sorry remains in any of the three delivered modules. The proof still depends
on the existing proEtaleClassicalSheaves theorem, whose proof is separate work;
no claim is made that the transitive axiom closure is already sorry-free.

## No longer needed

Removed direct proof imports from the item module:

- WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
- WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
- Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- Mathlib.CategoryTheory.Shift.Adjunction
- Mathlib.CategoryTheory.Triangulated.Adjunction
- WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
- Mathlib.Algebra.Homology.Embedding.CochainComplex
- Mathlib.Algebra.Homology.DerivedCategory.Plus
- WeilConjectures.CategoryTheory.TruncationTriangle
- Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
- Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
- WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
- Sheaf.SixFunctors.ClassicalDefinition

The counit support module retains the exact-functor, right-derived negative-vanishing,
shift-adjunction and triangulated-adjunction imports needed by its proof. The
remaining direct imports above are unnecessary because the comparison functors
and existing PlusDevissage theorem already supply their constructions. The image proof uses
sk-thm-pe-classical-sheaves directly, rather than the module theorem phrased using
classicality of underlying sets; this matches IsClassicalModuleFor exactly.
The original direct dependencies are replaced by the two support nodes; the image
node retains exact-functor/cohomology and classical-sheaf inputs, and the counit
node records the actual shift, exactness, negative-vanishing and classical-sheaf inputs.
The generic proved PlusDevissage theorem implements the source's finite induction
and bounded-below passage. The standalone explicit-complex truncation triangle
(lem-weil-pbc-truncation-triangle) and general morphism truncation comparison
(lem-weil-pbc-derived-functor-truncation-iso) are not needed by this proof.
The Grothendieck/K-injective construction nodes (lem-pur-ringed-site-grothendieck-abelian,
lem-sfb-grothendieck-k-injective, def-sfb-right-derived-functor) are not needed as
separate inputs: the bounded-below derived adjunction is already constructed.
The cohomology-ladder, five-lemma, truncation-cohomology and cohomology-detection
lemmas are internal to the already proved generic devissage, rather than new
obligations imported separately by this item. None is claimed globally obsolete. No unit
statement or proof step is bypassed. No module withdrawal is claimed.

The source-import closure of this item loses
Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions and
Sheaf.CategoryTheory.KInjectiveTotalDerived. Both remain reachable from
TargetsCheck through other imports, so no module is claimed pruned from the
whole targets closure.

## Where the brief, the DAG or earlier work was wrong

The saved image proof omitted the distinction between the small derived model used
by comparison and the explicit standard homology model in IsClassicalComplexFor.
The two homology functors are naturally isomorphic, rather than definitionally equal.
The saved restricted-counit proof also used the root Functor.map_id in place of
CategoryTheory.Functor.map_id. Both issues are repaired without changing definitions.

## New nodes

lem-pe-classical-derived-image: proved classicality of the image under exact comparison,
with the cohomology-model comparison and continuity-map naturality written in Lean.

lem-pe-classical-derived-counit: proved the original proof's sheaf base case and
lower-bound hypotheses, then applied existing generic bounded-below devissage.
No new open obligation and no definition/signature change.

Both new statements were checked on zero sheaves, the zero ring, single sheaves
in arbitrary degrees and bounded-below objects with no upper bound. The argument
uses neither a finite cohomological dimension nor an upper bound. Searches in
Mathlib and the blueprint found no duplicate of either classical comparison clause.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
