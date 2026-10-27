module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Cohomology of the total left derived functor on objects

Source: Stacks Project, Derived Categories, duals of Tags 05TC, 05TD(3), 015C,
and Tag 05T5(3)--(4) (blueprint: lem-trf-left-derived-object-cohomology).
-/

@[expose] public section

set_option autoImplicit false

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The canonical degree-zero comparison on an object: apply cohomology to the actual
counit, identify the termwise image of the single complex with the single complex of
its image, and use the canonical degree-zero single-complex identification.

Source: Stacks Project, Derived Categories, dual of Tag 05TD(3), with the unbounded
comparison of Tag 05T5(3)--(4) (blueprint: lem-trf-left-derived-object-cohomology).
This is a composite of existing canonical maps and involves no choice of an isomorphism. -/
noncomputable def leftDerivedObjectComparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (V : A ⥤ B) [V.Additive] (LV : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LV ⟶
      V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (M : A) :
    (DerivedCategory.homologyFunctor B 0).obj
      (LV.obj ((DerivedCategory.singleFunctor A 0).obj M)) ⟶ V.obj M :=
  (DerivedCategory.homologyFunctor B 0).map
      (ε.app ((HomotopyCategory.singleFunctor A 0).obj M)) ≫
    (DerivedCategory.homologyFunctor B 0).map
      ((DerivedCategory.quotientCompQhIso B).inv.app
        ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor A 0).obj M))) ≫
    (DerivedCategory.homologyFunctor B 0).map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex V (ComplexShape.up ℤ) 0).hom.app M)) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app (V.obj M)

/-- For an additive right exact functor with enough projectives in its source and
an everywhere-defined total left derived functor, positive cohomology on objects
vanishes, the actual degree-zero counit is invertible and natural, and the counit
on an object is invertible precisely when its negative cohomology vanishes.
`hLV` specifies the universal total derived functor and its counit; `hdefined` is
exactly the essentially constant denominator condition of Definition 05S9(2).
All source, target and localization universes are independent.

Source: Stacks Project, Derived Categories, duals of Tags 05TC, 05TD(3), 015C;
Tag 05T5(3)--(4) identifies bounded-above and unbounded values on single complexes.
(blueprint: lem-trf-left-derived-object-cohomology)

Proof:
1. Recursively choose projective epimorphisms onto M and the successive kernels.
The resulting complex P is supported in nonpositive degrees, has projective terms,
and its augmentation a : P → M[0] is a quasi-isomorphism: the image of each incoming
differential is the kernel of the outgoing one, and a is the degree-zero cokernel.
2. By lem-sc-bounded-above-projective-kprojective, P is K-projective. The bijection
lem-coef-kprojective-derived-hom-bijection lifts the inverse of every denominator
s : Y → P to a unique section P → Y. Uniqueness makes these sections natural and
makes the identity denominator initial in the full denominator category, including
unbounded Y.
3. Use the retraction r and the common-stage factorization from
 def-pc-essentially-constant-pro-diagram on this initial diagram. If u is the
canonical value cone, initiality gives u_s = u_id followed by the unique transition
from the identity stage. Composing that transition with r gives an inverse to
u_id = ε_P; the retraction gives one identity and common-stage factorization the other.
4. The inverse of LV(Q(a)) followed by ε_P identifies LV(M[0]) with Q(V(P)).
Naturality of ε gives ε_M = Q(V(a)) composed with this isomorphism, so this is the
actual derived counit, before applying cohomology.
5. Additivity preserves zero objects, hence V(P) has no positive terms or positive
cohomology. Right exactness preserves the augmentation cokernel of d in degree -1,
so H⁰(V(a)) is invertible. Step 4 gives positive vanishing and invertibility of
leftDerivedObjectComparison, with its specified canonical single-complex normalization.
6. Apply H⁰ to naturality of ε at f[0]. Naturality of the standard quotient and
single-complex identifications yields exactly the stated equation with V.map f.
7. An invertible counit has zero negative cohomology because V(M)[0] does.
Conversely, negative vanishing and Steps 4--5 show that V(a) induces isomorphisms
in every degree. It is a quasi-isomorphism, so Q(V(a)) and then ε_M are invertible.
These are the seven steps of the node's reviewed projective-resolution proof. -/
theorem leftDerived_object_cohomology
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
            Over.forget X ⋙ V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Y) :
    (∀ (M : A) (q : ℤ), 0 < q →
      IsZero ((DerivedCategory.homologyFunctor B q).obj
        (LV.obj ((DerivedCategory.singleFunctor A 0).obj M)))) ∧
    (∀ M : A, IsIso (leftDerivedObjectComparison V LV ε M)) ∧
    (∀ (M N : A) (f : M ⟶ N),
      (DerivedCategory.homologyFunctor B 0).map
          (LV.map ((DerivedCategory.singleFunctor A 0).map f)) ≫
        leftDerivedObjectComparison V LV ε N =
          leftDerivedObjectComparison V LV ε M ≫ V.map f) ∧
    (∀ M : A, IsIso (ε.app ((HomotopyCategory.singleFunctor A 0).obj M)) ↔
      ∀ q : ℤ, q < 0 →
        IsZero ((DerivedCategory.homologyFunctor B q).obj
          (LV.obj ((DerivedCategory.singleFunctor A 0).obj M)))) := by
  sorry

end CategoryTheory.Functor
