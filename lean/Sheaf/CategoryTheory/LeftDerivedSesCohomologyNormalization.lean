module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-! # Normalization of the cohomology sequence of a total left derived functor

Source: Stacks Project, Derived Categories, Tag 015D, proof, dualized;
Tags 05RS, 05TC, 05TD and 05T5(3)--(4).
(blueprint: lem-trf-left-derived-ses-cohomology-normalization)
-/

@[expose] public section

set_option autoImplicit false

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- The functor `T^q` on objects and morphisms: insert in degree zero, apply the
specified total left derived functor, and take degree-`q` cohomology.
Source: Stacks Project, Derived Categories, dual of Tag 015D, proof, and Tag 05TD.
(blueprint: lem-trf-left-derived-ses-cohomology-normalization) -/
noncomputable def leftDerivedObjectCohomologyFunctor
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (LV : DerivedCategory A ⥤ DerivedCategory B) (q : ℤ) : A ⥤ B :=
  DerivedCategory.singleFunctor A 0 ⋙ LV ⋙ DerivedCategory.homologyFunctor B q

/-- The triangle with the specified images of the two short-complex arrows and
specified final morphism `w`. Distinguishedness is a separate hypothesis.
Source: Stacks Project, Derived Categories, dual of Tag 015D, proof.
(blueprint: lem-trf-left-derived-ses-cohomology-normalization) -/
noncomputable def leftDerivedShortComplexTriangle
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (LV : DerivedCategory A ⥤ DerivedCategory B) (S : ShortComplex A)
    (w : LV.obj ((DerivedCategory.singleFunctor A 0).obj S.X₃) ⟶
      (LV.obj ((DerivedCategory.singleFunctor A 0).obj S.X₁))⟦(1 : ℤ)⟧) :
    Triangle (DerivedCategory B) :=
  Triangle.mk (LV.map ((DerivedCategory.singleFunctor A 0).map S.f))
    (LV.map ((DerivedCategory.singleFunctor A 0).map S.g)) w

/-- The long exact cohomology sequence, canonical degree-zero normalization,
positive-degree vanishing and exact normalized tail for a short exact sequence.
Exactness is expressed by equality of the standard image and kernel subobjects;
`Epi (V.map S.g)` is exactness at the last object before zero. The connecting
morphisms are Mathlib's canonical `HomologySequence.δ` for the stipulated triangle.
No object of the sequence is assumed acyclic.
The comparison `c_N = H⁰(ε_{N[0]})` is written out as the composite of `H⁰` of the
actual counit with Mathlib's canonical identifications `quotientCompQhIso`,
`singleMapHomologicalComplex` and `singleFunctorCompHomologyFunctorIso`; it is
definitionally the comparison used by lem-trf-left-derived-object-cohomology.

Source: Stacks Project, Derived Categories, Tag 015D (lemma-F-acyclic-ses), proof,
dualized; Tag 05RS (lemma-cohomology-homological); duals of Tags 05TC and 05TD;
Tag 05T5(3)--(4).
(blueprint: lem-trf-left-derived-ses-cohomology-normalization)

Proof:
1. Apply lem-sf-derived-homology-long-exact, namely the three exactness statements
DerivedCategory.HomologySequence.exact₁, exact₂ and exact₃, to the assumed
distinguished triangle. Its first two arrows are the images of S.f and S.g,
so their cohomology maps are precisely T^q(S.f) and T^q(S.g). Its connecting
map is the cohomology of w followed by the canonical shift identification.
The image-kernel equalities at all three positions give the long exact sequence.
2. Apply lem-trf-left-derived-object-cohomology to V and each object N. The
hypotheses are exactly enough projectives, additivity, right exactness and the
everywhere-defined total derived functor. This gives positive vanishing,
invertibility of the actual counit comparison c_N displayed in the statement,
and its naturality with respect to every morphism. In particular T¹(S.X₁)=0.
3. The degree-zero segment of Step 1 therefore ends in T⁰(S.X₃) → 0. Transport
its three degree-zero objects through the canonical comparisons c. Naturality
identifies the transported middle arrows with V(S.f) and V(S.g), while the
first arrow becomes δ⁻¹ followed by c at S.X₁. Images and kernels transport
through isomorphisms by their universal properties. Thus the transported
sequence is exact at V(S.X₁), V(S.X₂), and V(S.X₃), the last giving epimorphy.
These are the three steps of the node's reviewed proof. -/
theorem leftDerived_ses_cohomology_normalization
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    [EnoughProjectives A] (V : A ⥤ B) [V.Additive] [PreservesFiniteColimits V]
    (LV : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LV ⟶
      V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLV : LV.IsRightKanExtension ε)
    (hdefined : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ Y : DerivedCategory B,
        IsEssentiallyConstantProDiagram
          (MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
            Over.forget X ⋙ V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Y)
    (S : ShortComplex A) (hS : S.ShortExact)
    (w : LV.obj ((DerivedCategory.singleFunctor A 0).obj S.X₃) ⟶
      (LV.obj ((DerivedCategory.singleFunctor A 0).obj S.X₁))⟦(1 : ℤ)⟧)
    (hT : leftDerivedShortComplexTriangle LV S w ∈ distTriang (DerivedCategory B)) :
    (∀ q : ℤ,
      imageSubobject ((leftDerivedObjectCohomologyFunctor LV q).map S.f) =
        kernelSubobject ((leftDerivedObjectCohomologyFunctor LV q).map S.g) ∧
      imageSubobject ((leftDerivedObjectCohomologyFunctor LV q).map S.g) =
        kernelSubobject (DerivedCategory.HomologySequence.δ
          (leftDerivedShortComplexTriangle LV S w) q (q + 1)) ∧
      imageSubobject (DerivedCategory.HomologySequence.δ
          (leftDerivedShortComplexTriangle LV S w) q (q + 1)) =
        kernelSubobject ((leftDerivedObjectCohomologyFunctor LV (q + 1)).map S.f)) ∧
    (∀ N : A, IsIso
      ((DerivedCategory.homologyFunctor B 0).map
          (ε.app ((HomotopyCategory.singleFunctor A 0).obj N)) ≫
        (DerivedCategory.homologyFunctor B 0).map
          ((DerivedCategory.quotientCompQhIso B).inv.app
            ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor A 0).obj N))) ≫
        (DerivedCategory.homologyFunctor B 0).map
          (DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex V (ComplexShape.up ℤ) 0).hom.app
              N)) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app (V.obj N))) ∧
    (∀ (N₁ N₂ : A) (f : N₁ ⟶ N₂),
      (leftDerivedObjectCohomologyFunctor LV 0).map f ≫
          ((DerivedCategory.homologyFunctor B 0).map
              (ε.app ((HomotopyCategory.singleFunctor A 0).obj N₂)) ≫
            (DerivedCategory.homologyFunctor B 0).map
              ((DerivedCategory.quotientCompQhIso B).inv.app
                ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  ((CochainComplex.singleFunctor A 0).obj N₂))) ≫
            (DerivedCategory.homologyFunctor B 0).map
              (DerivedCategory.Q.map
                ((HomologicalComplex.singleMapHomologicalComplex V (ComplexShape.up ℤ) 0).hom.app
                  N₂)) ≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app (V.obj N₂)) =
        ((DerivedCategory.homologyFunctor B 0).map
            (ε.app ((HomotopyCategory.singleFunctor A 0).obj N₁)) ≫
          (DerivedCategory.homologyFunctor B 0).map
            ((DerivedCategory.quotientCompQhIso B).inv.app
              ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((CochainComplex.singleFunctor A 0).obj N₁))) ≫
          (DerivedCategory.homologyFunctor B 0).map
            (DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex V (ComplexShape.up ℤ) 0).hom.app
                N₁)) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app (V.obj N₁)) ≫ V.map f) ∧
    (∀ (N : A) (q : ℤ), 0 < q →
      IsZero ((leftDerivedObjectCohomologyFunctor LV q).obj N)) ∧
    imageSubobject (DerivedCategory.HomologySequence.δ
        (leftDerivedShortComplexTriangle LV S w) (-1) 0 ≫
          ((DerivedCategory.homologyFunctor B 0).map
              (ε.app ((HomotopyCategory.singleFunctor A 0).obj S.X₁)) ≫
            (DerivedCategory.homologyFunctor B 0).map
              ((DerivedCategory.quotientCompQhIso B).inv.app
                ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  ((CochainComplex.singleFunctor A 0).obj S.X₁))) ≫
            (DerivedCategory.homologyFunctor B 0).map
              (DerivedCategory.Q.map
                ((HomologicalComplex.singleMapHomologicalComplex V (ComplexShape.up ℤ) 0).hom.app
                  S.X₁)) ≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app (V.obj S.X₁))) =
      kernelSubobject (V.map S.f) ∧
    imageSubobject (V.map S.f) = kernelSubobject (V.map S.g) ∧
    Epi (V.map S.g) := by
  sorry

end CategoryTheory.Functor
