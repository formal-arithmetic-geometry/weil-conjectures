## Worker report

Item: `lem-trf-total-left-derived-object-ses-triangle`, group Q79, stage 2.

The module `Sheaf.CategoryTheory.LeftDerivedObjectSesTriangle` states
`CategoryTheory.Functor.leftDerived_object_ses_triangle`. Its only proof is `sorry`.
There are no new definitions, new DAG nodes, dependency repairs, or statement corrections.
The item JSON changes only in `lean`; its accepted statement and five-step split are retained.

The source was read in `literature/stacks-project/derived.tex`: the proof of
`lemma-F-acyclic-ses` (015D), the canonical connecting map in
`lemma-derived-canonical-delta-functor` (0152),
`lemma-additive-exact-homotopy-category` (014X),
`definition-right-derived-functor-defined` (05S9), and
`proposition-derived-functor` (05SE), including its left-derived assertion.
The node concerns the triangle portion of the dual argument, on the unbounded derived
categories under its explicit everywhere-defined hypothesis.

Every hypothesis and clause is rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Abelian categories A and B | `{A : Type uA} [Category.{vA} A] [Abelian A]` and the independent B binders. |
| A has enough projectives, with lifting across epimorphisms | `[EnoughProjectives A]`; Mathlib's `ProjectivePresentation` has a projective source and an epimorphic presentation map, and `Projective` has the stated lifting property. |
| V is additive | `(V : A ⥤ B) [V.Additive]`. |
| Right exact, preserving cokernels and finite sums | `[PreservesFiniteColimits V]`. For additive functors between abelian categories this is equivalent to preserving cokernels and finite sums: finite coproducts and cokernels construct finite colimits, and conversely both are finite colimits. Thus no left exactness is imposed. |
| Integer cochain homotopy categories | `HomotopyCategory A (ComplexShape.up ℤ)` and `V.mapHomotopyCategory (ComplexShape.up ℤ)`. |
| Chosen derived localizations QA and QB | `[HasDerivedCategory.{wA} A]`, `[HasDerivedCategory.{wB} B]`, `DerivedCategory A`, `DerivedCategory B`, and `DerivedCategory.Qh`. The localization morphism universes wA and wB are independent, as are uA, vA, uB, vB. |
| The total left derived pair with its canonical natural comparison | `(LV : DerivedCategory A ⥤ DerivedCategory B)`, the natural transformation `ε : DerivedCategory.Qh ⋙ LV ⟶ V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh`, and `(hLV : LV.IsRightKanExtension ε)`. This is precisely Mathlib's `IsLeftDerivedFunctor` universal property, unfolded along Qh. It specifies the given total-derived pair and its counit, rather than adding a separate exactness or resolution assumption. The reviewed sibling `lem-trf-left-derived-object-cohomology` uses this same interface. |
| Defined at every object in the essentially constant denominator-diagram sense | `hdefined` quantifies over every `X : HomotopyCategory A (ComplexShape.up ℤ)` and asserts an essential value `Y : DerivedCategory B` for the diagram `MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙ Over.forget X ⋙ V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh`. This is the body of the dependency's `IsTriangulatedLeftDerivedDefinedAt`; expanding that existing predicate avoids supplying an irrelevant proof argument of saturation. The index has all commuting triangles as morphisms, with no extra denominator condition on them. |
| A short exact sequence with maps i and p | `(S : ShortComplex A) (hS : S.ShortExact)`, with `S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g` respectively M', M, M'', i, p. `S` includes the zero-composite equation; short exactness includes exactness, the monomorphism, and the epimorphism. |
| The degree-zero single complexes | `(DerivedCategory.singleFunctor A 0).obj S.X₁` etc. By the definitions in `DerivedCategory.Basic`, these are the QA-images of the homotopy degree-zero single complexes, also the Q-images of the cochain single complexes. The functor similarly sends `S.f` and `S.g` to QA(i[0]) and QA(p[0]). |
| Canonical connecting morphism delta | `hS.singleδ` from Mathlib's `DerivedCategory.SingleTriangle`, not an arbitrary completion of the first map. |
| LV has its canonical exact triangulated structure | `∃ (_ : LV.CommShift ℤ), NatTrans.CommShift ε ℤ ∧ LV.IsTriangulated ∧ ...`. The existential shift structure is used throughout the following conjunction. `NatTrans.CommShift ε ℤ` imposes the square with the specified counit and the existing canonical shifts of Qh and the termwise functor. Right Kan uniqueness characterizes those comparisons, so this expresses the canonical structure. `LV.IsTriangulated` asserts global preservation of distinguished triangles, beyond the one displayed triangle. |
| The triangle's three objects and first two arrows | `Triangle.mk (LV.map ((DerivedCategory.singleFunctor A 0).map S.f)) (LV.map ((DerivedCategory.singleFunctor A 0).map S.g)) ...` has exactly the three LV-images specified by the node. |
| Its last arrow is sigma composed with LV(delta) | `LV.map hS.singleδ ≫ (LV.commShiftIso (1 : ℤ)).hom.app ((DerivedCategory.singleFunctor A 0).obj S.X₁)`. Lean composition `≫` is left-to-right, so the image of delta is followed by sigma. The component has domain LV(M'[0][1]) and codomain LV(M'[0])[1]. |
| Distinguished in D(B) | Membership in `distTriang (DerivedCategory B)`. |
| No acyclicity hypothesis on the objects | There is no acyclicity or invertible-counit binder for S.X₁, S.X₂ or S.X₃. |

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, publicly available through SingleTriangle.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Qh`, `DerivedCategory.singleFunctor`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, publicly available through SingleTriangle.
- `def-pur-saturated-triangulated-localization`:
  `CategoryTheory.Functor.IsTriangulatedLeftDerivedValue` and
  `CategoryTheory.Functor.IsTriangulatedLeftDerivedDefinedAt` in
  `WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`.
  Its public dependency
  `WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro` supplies the existing
  `CategoryTheory.IsEssentiallyConstantProDiagram`, used without any private replacement.
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated`,
  `CategoryTheory.IsTriangulated`, `CategoryTheory.Functor.IsTriangulated`, and
  `CategoryTheory.Pretriangulated.Triangle.mk`/`distTriang` from Mathlib's
  Triangulated modules, available through DerivedCategory.Basic.
- `lem-trf-additive-homotopy-triangulated`: the additive functor triangulation instance in
  `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`, imported for the proof.
- `lem-pur-quasi-isos-saturated-triangulated`:
  `HomotopyCategory.quasiIso_saturated_triangulated` in
  `WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`, proof import.
- `lem-pur-left-derived-defined-pointwise-kan-bridge`:
  `CategoryTheory.leftDerived_defined_pointwiseKan_bridge` in
  `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge`, proof import.
- `lem-pur-left-derived-exact-chosen-localization`:
  `CategoryTheory.Functor.leftDerived_exact_of_localization` in
  `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization`, proof import.
- `lem-pur-right-kan-extension-coherent-shift`:
  `CategoryTheory.Functor.rightKanExtension_coherentShift` in
  `WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift`, proof import.
- `lem-sf-derived-ses-triangle`:
  `CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished`, `singleTriangle`,
  `singleδ` in `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`.
  The import is public because the actual canonical connecting map occurs in the signature.

All recorded dependency signatures and docstrings were read in the local live source clone.
The theorem docstring carries the five accepted proof steps, including the pointwise Kan
bridge and uniqueness of the counit-compatible shift comparison. There is one named theorem
with one `sorry`; no definition data is postponed. No disputed statement or node fault was found.

Edge cases checked mathematically before writing:

- The zero short exact sequence gives the zero distinguished triangle; it is allowed.
- A split sequence gives the split triangle with zero canonical connecting map.
- For V = - tensor_Z Z/2 and `0 → Z →[2] Z → Z/2 → 0`, the first derived map is zero
  on Z/2[0] and its cone is Z/2[0] plus Z/2[1], the derived value of Z/2[0].
  This tests the genuinely non-exact functor case: one must not replace LV(M''[0])
  by V(M'')[0], or assume the counit invertible. The delivered statement does neither.
- An identity map at either end of a split sequence gives the contractible triangle.
- Integer, unbounded complexes and arbitrary independent source, target and localization
  universes remain available. The canonical comparison points in the required direction.

Searches for an existing exact statement (msearch results also in `searches.jsonl`):

- LeanFinder via `msearch.py`, query
  `An everywhere defined total left derived functor sends short exact sequences of objects to distinguished triangles`:
  eight hits, including `DerivedCategory.triangleOfSES_distinguished`,
  `ShortComplex.ShortExact.singleTriangle_distinguished`,
  `Functor.map_distinguished_exact`, and `Functor.instIsTriangulatedDerivedCategoryMapDerivedCategory`.
  These give either the source triangle, homological exactness, or the derived functor
  of an already exact underived functor. None states the item for a right exact V.
- Loogle via `msearch.py`, query `"IsLeftDerivedFunctor", "IsTriangulated"`:
  one hit, `CategoryTheory.LocalizerMorphism.Derives.isTriangulated_of_isLeftDerivedFunctor`.
  This is an online result using a derivability structure, not this essential-constancy
  object-SES statement, and is absent from the pinned Derived-functor sources.
- Mathlib grep via `msearch.py`, query
  `leftDerived.*[Tt]riangle|[Tt]riangle.*leftDerived|IsTriangulated`,
  subdirectory `CategoryTheory/Functor/Derived`: zero hits.
- LeanSearch via `msearch.py`, query
  `An additive right exact functor with an everywhere defined total left derived functor sends short exact sequences of objects to distinguished triangles`:
  eight hits, including `singleTriangle`, `singleTriangle_distinguished`,
  `triangleOfSES_distinguished`, and the additive homotopy functor instance; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `leftDerived.*[Ss][Ee][Ss]|[Ss][Ee][Ss].*leftDerived|leftDerived.*object.*triangle|leftDerived_object_ses_triangle`
  found no statement of the item. Broader derived-value/triangle searches found the general
  triangulated localization results already listed as proof dependencies.
- `rg`/`grep` for the item id in the upstream WeilConjectures source found no declaration.
  Searching `dag/lean_names_upstream.json` by the proposed name and SES variants found none.
  The nearby landed `LeftDerivedObjectCohomology` was read; it concerns vanishing and the
  degree-zero counit, not the triangle stated here.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.
The initial module compiled cleanly as both a sandbox module and the intended library module;
the final version additionally imports the Mathlib homotopy-triangulation proof dependency.

## Second reading by Q79

I reopened the node statement and the completed Lean signature for a sequential second
reading. This is a self-check; the maintainer's independent delivery review remains separate.
The abelian, enough-projective, additive, right-exact, chosen-localization and
everywhere-essentially-constant hypotheses are each present with independent universes.
`hLV` specifies the total-derived pair by its universal property, following the already
reviewed sibling interface, and does not posit the conclusion's exactness. I checked that
the final existential shift binder supplies the same structure to the counit compatibility,
global triangulatedness, and the explicit triangle. The compiler accepts this dependent use.
The last map is exactly `LV.map hS.singleδ` followed by the degree-one comparison at M'[0];
the canonical single connecting map is used rather than an arbitrary completion.
The target is the unbounded D(B), and neither positive/negative vanishing nor acyclicity
has been added. The zero, split, identity and tensor-with-Z/2 cases remain covered.
All five proof steps and every already stated proof dependency have the required imports.
The only adjustment from this reading was adding the direct proof import
`Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`; the statement was unchanged.
