/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Sheaf.CategoryTheory.KInjectiveTotalDerived

/-!
# Unit-normalized K-injective mapping-fibre comparisons

Source: Stacks Project, Derived Categories, Tags 090X, 070K, 070Y and 05SU;
blueprint main-20261015, `prop-weil-pbc-direct-image-limits`, applying direct image to
Roos triangles (blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison).

The fibre triangle is the inverse rotation of Mathlib's signed cone triangle.
Mathlib orders the cone coordinates as `(x,y)`; in the node's order `(y,x)` its
shift by -1 has differential `(-dy - ux, dx)`. All comparisons below are constructed
from the existing cone, shift and biproduct comparisons, without exactness of `G`.
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The triangle `(Cone(u)[-1], P, P; r, u, b)`, with `r(y,x)=x` and `b(z)=(z,0)`.
Source: Stacks, Tag 090X, inverse rotation of the signed cone triangle
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
noncomputable abbrev kInjectiveFiberTriangle {P : CochainComplex A ℤ} (u : P ⟶ P) :
    Triangle (CochainComplex A ℤ) :=
  (CochainComplex.mappingCone.triangle u).invRotate

/-- The diagonal map of fibre triangles induced by a commuting endomorphism square.
Source: Stacks, Tag 090X, cone-coordinate comparison
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
noncomputable def kInjectiveFiberTriangleMap
    {P R : CochainComplex A ℤ} (u : P ⟶ P) (v : R ⟶ R)
    (a : P ⟶ R) (ha : u ≫ a = a ≫ v) :
    kInjectiveFiberTriangle u ⟶ kInjectiveFiberTriangle v :=
  (invRotate (CochainComplex A ℤ)).map
    (CochainComplex.mappingCone.triangleMap u v a a ha)

/-- The actual diagonal comparison: canonical additive cone comparison followed by
`diag(c,c)`, with inverse rotation supplying the canonical shift identification.
Its first component is the node's `theta`, with coordinates `(y,x) ↦ (cy,cx)`.
Source: Stacks, Tag 090X (blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
noncomputable def kInjectiveFiberChainComparison (G : A ⥤ B) [G.Additive]
    {P : CochainComplex A ℤ} {P' : CochainComplex B ℤ}
    (u : P ⟶ P) (u' : P' ⟶ P')
    (c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ P')
    (hc : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫ c.hom = c.hom ≫ u') :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapTriangle.obj
      (kInjectiveFiberTriangle u) ⟶ kInjectiveFiberTriangle u' :=
  (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapTriangleInvRotateIso.inv.app
      (CochainComplex.mappingCone.triangle u) ≫
    (invRotate (CochainComplex B ℤ)).map
      ((CochainComplex.mappingCone.mapTriangleIso u G).hom ≫
        CochainComplex.mappingCone.triangleMap
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map u) u' c.hom c.hom hc)

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The unit normalization, spelling out both localization-shift identifications.
Source: Stacks, Tag 05SU, normalized by the universal unit of Tags 070K/070Y
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
def IsUnitNormalizedKInjectiveShift (G : A ⥤ B) [G.Additive]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (σ : shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ RG ≅
      RG ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ)) : Prop :=
  ∀ K : CochainComplex A ℤ,
    η.app (K⟦(1 : ℤ)⟧) ≫
        RG.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K) ≫
        σ.hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
          (((G.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app K) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (η.app K)⟦(1 : ℤ)⟧'

/-- Inverse of the derived unit at a computing K-injective object. Its data is the
inverse of an isomorphism, not a choice of an arbitrary comparison.
Source: Stacks, Tag 070Y (blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
noncomputable def kInjectiveInverseUnit (G : A ⥤ B) [G.Additive]
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (hη : ∀ K : CochainComplex A ℤ, K.IsKInjective → IsIso (η.app K))
    (K : CochainComplex A ℤ) (hK : K.IsKInjective) :
    RG.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (@asIso _ _ _ _ (η.app K) (hη K hK)).symm

/-- The image of the localized fibre triangle using precisely the shift `σ`.
Source: Stacks, Tags 090X and 05SU
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison). -/
noncomputable def kInjectiveDerivedFiberTriangle
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (σ : shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ RG ≅
      RG ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ))
    {P : CochainComplex A ℤ} (u : P ⟶ P) : Triangle (DerivedCategory B) :=
  Triangle.mk
    (RG.map (DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u)).mor₁)
    (RG.map (DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u)).mor₂)
    (RG.map (DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u)).mor₃ ≫
      σ.hom.app (DerivedCategory.Q.obj (kInjectiveFiberTriangle u).obj₁))

/-- There is exactly one natural shift isomorphism normalized by the universal unit,
for every complex, including complexes which are not K-injective.
Source: Stacks, Tags 05SU, 070K and 070Y
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison).

Proof: additivity preserves biproducts, differentials and homotopies, and identifies
termwise images of cone triangles with cone triangles. Thus the homotopy functor is
exact and `exists_rightDerived_of_enough_isKInjective` applies (node
lem-weil-pbc-kinjective-total-derived). On K-injective I use
eta_I[1] eta_(I[1])^{-1}; shifts are K-injective (lem-weil-pbc-kinjective-shift).
The Hom bijection into K-injectives (lem-weil-pbc-kinjective-hom-derived) extends
naturality to all derived morphisms. Transport along a K-injective replacement of
each derived object; naturality proves independence of choices. Naturality of eta
along K → I and its shift proves normalization for arbitrary K. Cancellation of
the invertible units on I and I[1], then transport, proves uniqueness. -/
theorem existsUnique_unitNormalizedKInjectiveShift
    (hA : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (G : A ⥤ B) [G.Additive]
    (hG : ∀ K : CochainComplex A ℤ, K.IsKInjective →
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (hUniversal : ∀ F : DerivedCategory A ⥤ DerivedCategory B,
      Function.Bijective (fun β : RG ⟶ F ↦ η ≫ Functor.whiskerLeft DerivedCategory.Q β))
    (hη : ∀ K : CochainComplex A ℤ, K.IsKInjective → IsIso (η.app K)) :
    ∃! σ : shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ RG ≅
      RG ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ),
      IsUnitNormalizedKInjectiveShift G RG η σ := by
  sorry

/-- K-injective mapping fibres and their unit-normalized distinguished triangle comparison.
The chain comparison is the explicitly defined diagonal map, so its triangle-morphism
laws are exactly `c G(r) = r' theta` and `theta[1] G(b) = b' c`.
Source: Stacks, Tags 090X, 070Y and 05SU
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison).

Proof: for f=(a,b) from an acyclic N to the fibre, choose s with b=ds+sd_N.
Then a+us maps N into P[-1]. K-injectivity of P[-1] gives t with
 a+us=-dt+td_N. The pair (t,s) null-homotopes f. Repeat for P'; preservation by G
gives the third K-injectivity assertion. The inverse rotation of the signed cone
triangle is distinguished (def-weil-triangulated-category), with the stated r and b.
The canonical biproduct comparison and diag(c,c) commute with differentials because
c G(u)=u' c, and commute with projection and inclusion. Invert eta at P and H
(lem-weil-pbc-kinjective-total-derived) to define bar-c and Theta. Naturality of eta
gives the first two derived squares. For the last square, normalization gives
Theta[1] sigma RG(Qb) = Q(theta)[1] eta_(H[1])^{-1} RG(Qb)
= Q(theta)[1] Q(Gb) eta_P^{-1} = Q(b') bar-c.
The three invertible components form an isomorphism of triangles; isomorphism
invariance of distinguished triangles proves the source distinguished as well. -/
theorem kInjectiveFiberTriangle_comparison
    (hA : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (G : A ⥤ B) [G.Additive]
    (hG : ∀ K : CochainComplex A ℤ, K.IsKInjective →
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (hUniversal : ∀ F : DerivedCategory A ⥤ DerivedCategory B,
      Function.Bijective (fun β : RG ⟶ F ↦ η ≫ Functor.whiskerLeft DerivedCategory.Q β))
    (hη : ∀ K : CochainComplex A ℤ, K.IsKInjective → IsIso (η.app K))
    (σ : shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ RG ≅
      RG ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ))
    (hσ : IsUnitNormalizedKInjectiveShift G RG η σ)
    (P : CochainComplex A ℤ) (P' : CochainComplex B ℤ)
    (hP : P.IsKInjective) (hP' : P'.IsKInjective)
    (u : P ⟶ P) (u' : P' ⟶ P')
    (c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ P')
    (hc : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫ c.hom = c.hom ≫ u') :
    ∃ hH : (kInjectiveFiberTriangle u).obj₁.IsKInjective,
      (kInjectiveFiberTriangle u').obj₁.IsKInjective ∧
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (kInjectiveFiberTriangle u).obj₁) ∧
      (kInjectiveFiberChainComparison G u u' c hc).hom₂ = c.hom ∧
      (kInjectiveFiberChainComparison G u u' c hc).hom₃ = c.hom ∧
      IsIso (kInjectiveFiberChainComparison G u u' c hc).hom₁ ∧
      DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u) ∈
        distTriang (DerivedCategory A) ∧
      kInjectiveDerivedFiberTriangle RG σ u ∈ distTriang (DerivedCategory B) ∧
      DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u') ∈
        distTriang (DerivedCategory B) ∧
      ∃ e : kInjectiveDerivedFiberTriangle RG σ u ≅
          DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u'),
        e.hom.hom₁ = (kInjectiveInverseUnit G RG η hη _ hH).hom ≫
          DerivedCategory.Q.map (kInjectiveFiberChainComparison G u u' c hc).hom₁ ∧
        e.hom.hom₂ = (kInjectiveInverseUnit G RG η hη P hP).hom ≫
          DerivedCategory.Q.map c.hom ∧
        e.hom.hom₃ = (kInjectiveInverseUnit G RG η hη P hP).hom ≫
          DerivedCategory.Q.map c.hom ∧
        (kInjectiveDerivedFiberTriangle RG σ u).mor₃ ≫ e.hom.hom₁⟦(1 : ℤ)⟧' =
          e.hom.hom₃ ≫
            (DerivedCategory.Q.mapTriangle.obj (kInjectiveFiberTriangle u')).mor₃ := by
  sorry

/-- Naturality of the actual diagonal chain comparison and of both unit-normalized
localized comparison components, for commuting maps of endomorphism diagrams.
Source: Stacks, Tag 090X, explicit cone comparison; Tags 070Y and 05SU
(blueprint: lem-weil-pbc-kinjective-fiber-triangle-comparison).

Proof: the fibre maps are diag(v,v) and diag(v',v'). In either coordinate,
v' c = c_tilde G(v) proves the chain comparison square. Projection and inclusion
commute with these same diagonal maps, giving naturality of all chain triangle
arrows. Naturality of eta, followed by cancellation of its invertible components
on P and H (lem-weil-pbc-kinjective-total-derived), gives respectively the bar-c
and Theta squares displayed below. These equations give naturality of the three
components of the distinguished triangle isomorphisms in
`kInjectiveFiberTriangle_comparison`. Naturality of their connecting squares uses
the natural shift isomorphism of `existsUnique_unitNormalizedKInjectiveShift`. -/
theorem kInjectiveFiberTriangle_comparison_naturality
    (hA : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (G : A ⥤ B) [G.Additive]
    (hG : ∀ K : CochainComplex A ℤ, K.IsKInjective →
      CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (hUniversal : ∀ F : DerivedCategory A ⥤ DerivedCategory B,
      Function.Bijective (fun β : RG ⟶ F ↦ η ≫ Functor.whiskerLeft DerivedCategory.Q β))
    (hη : ∀ K : CochainComplex A ℤ, K.IsKInjective → IsIso (η.app K))
    (σ : shiftFunctor (DerivedCategory A) (1 : ℤ) ⋙ RG ≅
      RG ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ))
    (hσ : IsUnitNormalizedKInjectiveShift G RG η σ)
    (P R : CochainComplex A ℤ) (P' R' : CochainComplex B ℤ)
    (hP : P.IsKInjective) (hR : R.IsKInjective)
    (hP' : P'.IsKInjective) (hR' : R'.IsKInjective)
    (u : P ⟶ P) (v : R ⟶ R) (u' : P' ⟶ P') (v' : R' ⟶ R')
    (c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ P')
    (d : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj R ≅ R')
    (hc : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map u ≫ c.hom = c.hom ≫ u')
    (hd : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map v ≫ d.hom = d.hom ≫ v')
    (a : P ⟶ R) (a' : P' ⟶ R')
    (ha : u ≫ a = a ≫ v) (ha' : u' ≫ a' = a' ≫ v')
    (hca : c.hom ≫ a' = (G.mapHomologicalComplex (ComplexShape.up ℤ)).map a ≫ d.hom)
    (hH : (kInjectiveFiberTriangle u).obj₁.IsKInjective)
    (hJ : (kInjectiveFiberTriangle v).obj₁.IsKInjective) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (kInjectiveFiberTriangleMap u v a ha).hom₁ ≫
        (kInjectiveFiberChainComparison G v v' d hd).hom₁ =
      (kInjectiveFiberChainComparison G u u' c hc).hom₁ ≫
        (kInjectiveFiberTriangleMap u' v' a' ha').hom₁ ∧
    RG.map (DerivedCategory.Q.map (kInjectiveFiberTriangleMap u v a ha).hom₁) ≫
        (kInjectiveInverseUnit G RG η hη _ hJ).hom ≫
        DerivedCategory.Q.map (kInjectiveFiberChainComparison G v v' d hd).hom₁ =
      (kInjectiveInverseUnit G RG η hη _ hH).hom ≫
        DerivedCategory.Q.map (kInjectiveFiberChainComparison G u u' c hc).hom₁ ≫
        DerivedCategory.Q.map (kInjectiveFiberTriangleMap u' v' a' ha').hom₁ ∧
    RG.map (DerivedCategory.Q.map a) ≫
        (kInjectiveInverseUnit G RG η hη R hR).hom ≫ DerivedCategory.Q.map d.hom =
      (kInjectiveInverseUnit G RG η hη P hP).hom ≫ DerivedCategory.Q.map c.hom ≫
        DerivedCategory.Q.map a' := by
  sorry

end CategoryTheory
