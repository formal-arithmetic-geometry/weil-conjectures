/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.IntegralDerivedCoefficientData
public import Sheaf.Paper.CondensedBoundedStratumBaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-! # Bounded integral base change for a stratum extension

Source: Stacks Project, Tags 09AA, 09BM, 09BN and 09AH; blueprint main-20261015,
`det-lem-int-tensor-pullback.proof.md`, Local models.
(blueprint: lem-sfb-integral-bounded-stratum-base-change)

All derived functors here apply the exact module functors termwise. Exactness of a closed
pushforward is returned as a witness, rather than assumed. The bounded inclusions retain
all bounded inputs, without a constructibility or completeness condition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

/-! Cached instances for module objects over `Λ_Z`. Every derived functor of module objects
below needs them, and the generic search costs seconds per use. -/

instance (priority := 2000) integralBoundedStratumBaseChange_hasTensorFour
    (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite.{u}) Ab.{u + 1})
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ] (Z : AlgebraicGeometry.Scheme.{u})
    (A B C D : CategoryTheory.GradedObject ℤ (CategoryTheory.Mod (CategoryTheory.Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z) Ab.{u + 1})
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ Z))) :
    CategoryTheory.GradedObject.HasTensor₄ObjExt A B C D :=
  inferInstance

instance (priority := 2000) integralBoundedStratumBaseChange_hasGoodTensor₁₂Tensor
    (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite.{u}) Ab.{u + 1})
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ] (Z : AlgebraicGeometry.Scheme.{u})
    (A B C : CategoryTheory.GradedObject ℤ (CategoryTheory.Mod (CategoryTheory.Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z) Ab.{u + 1})
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ Z))) :
    CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor A B C :=
  inferInstance

instance (priority := 2000) integralBoundedStratumBaseChange_hasGoodTensorTensor₂₃
    (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite.{u}) Ab.{u + 1})
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ] (Z : AlgebraicGeometry.Scheme.{u})
    (A B C : CategoryTheory.GradedObject ℤ (CategoryTheory.Mod (CategoryTheory.Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z) Ab.{u + 1})
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ Z))) :
    CategoryTheory.GradedObject.HasGoodTensorTensor₂₃ A B C :=
  inferInstance

instance (priority := 2000) integralBoundedStratumBaseChange_hasColimitsOfShapeInt
    (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite.{u}) Ab.{u + 1})
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ] (Z : AlgebraicGeometry.Scheme.{u})
    :
    CategoryTheory.Limits.HasColimitsOfShape ℤ (CategoryTheory.Mod (CategoryTheory.Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z) Ab.{u + 1})
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ Z)) :=
  inferInstance

instance (priority := 2000) integralBoundedStratumBaseChange_hasExactColimitsOfShapeInt
    (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite.{u}) Ab.{u + 1})
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ] (Z : AlgebraicGeometry.Scheme.{u})
    :
    CategoryTheory.HasExactColimitsOfShape ℤ (CategoryTheory.Mod (CategoryTheory.Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z) Ab.{u + 1})
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ Z)) :=
  inferInstance

instance (priority := 2000) integralBoundedStratumBaseChange_hasCountableCoproducts
    (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite.{u}) Ab.{u + 1})
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ] (Z : AlgebraicGeometry.Scheme.{u})
    :
    CategoryTheory.Limits.HasCountableCoproducts (CategoryTheory.Mod (CategoryTheory.Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z) Ab.{u + 1})
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ Z)) :=
  inferInstance

instance (priority := 2000) integralBoundedStratumBaseChange_preservesColimitsOfShapeInt_tensorLeft
    (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite.{u}) Ab.{u + 1})
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ] (Z : AlgebraicGeometry.Scheme.{u})
    (N : CategoryTheory.Mod (CategoryTheory.Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z) Ab.{u + 1})
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ Z)) :
    CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      ((CategoryTheory.MonoidalCategory.curriedTensor _).obj N) :=
  inferInstance

instance (priority := 2000) integralBoundedStratumBaseChange_preservesColimitsOfShapeInt_tensorRight
    (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite.{u}) Ab.{u + 1})
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ] (Z : AlgebraicGeometry.Scheme.{u})
    (N : CategoryTheory.Mod (CategoryTheory.Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z) Ab.{u + 1})
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ Z)) :
    CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      ((CategoryTheory.MonoidalCategory.curriedTensor _).flip.obj N) :=
  inferInstance

instance (priority := 2000) integralBoundedStratumBaseChange_hasFunctorialFlatResolution
    (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite.{u}) Ab.{u + 1})
    [CategoryTheory.MonObj Λ] [CategoryTheory.IsCommMonObj Λ] (Z : AlgebraicGeometry.Scheme.{u})
    :
    CategoryTheory.Abelian.HasFunctorialFlatResolution (CategoryTheory.Mod (CategoryTheory.Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Z) Ab.{u + 1})
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ Z)) :=
  inferInstance

namespace AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange

open CondensedRing (integralCoefficientRing)

private theorem stratum_composite_cancel
    {A B Ap Bp D Dp : Type*}
    [Category A] [Category B] [Category Ap] [Category Bp] [Category D] [Category Dp]
    {H : A ⥤ Ap} {Jp : Ap ⥤ Bp} {J : A ⥤ B} {G : B ⥤ Bp}
    {Ip : Bp ⥤ Dp} {I : B ⥤ D} {Gp : D ⥤ Dp}
    (β : H ⋙ Jp ≅ J ⋙ G) (γ : I ⋙ Gp ≅ G ⋙ Ip) (K : A) :
    (((Functor.associator H Jp Ip).symm ≪≫ Functor.isoWhiskerRight β Ip ≪≫
      Functor.associator J G Ip ≪≫ Functor.isoWhiskerLeft J γ.symm).hom.app K) ≫
        γ.hom.app (J.obj K) = Ip.map (β.hom.app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _


set_option maxHeartbeats 1600000 in
-- The large conjunction elaborates several exactness witnesses and derived functor instances.
/-- The canonical open and closed mates are natural isomorphisms on all bounded inputs,
with identity restrictions on their own stratum and zero restrictions on its complement.
The existential exactness witnesses supply the termwise closed derived functors.
Source: Stacks 09AA, 09BM, 09BN and 09AH; node proof, Steps 1--6
(blueprint: lem-sfb-integral-bounded-stratum-base-change).

Proof:
1. Finite type over the field gives Noetherian underlying spaces by the finite affine
cover argument of `lem-sfb-finite-type-noetherian-spectrum`; all the opens are retrocompact.
Open and closed immersions survive base change, and their ranges stay complementary
by the base-change image lemma.
2. Cartesian coefficients make pullback exact. Transport the actual module operations
and adjunctions to section-ring modules using the internal-module-operations transport
lemma. Tags 09AA/09BM/09BN/09AH give exact extension and closed direct image, mixed zero
restrictions and the localization short exact sequence. Apply the restrictions to this
sequence and use triangle identities to see that the actual open units and closed
counits are invertible; transfer back through the coefficient transport equivalences.
3. Apply exact-open-closed-unbounded calculus. The localized adjunctions have the actual
units and counits, the mixed restrictions vanish, and complementary restrictions jointly
reflect isomorphisms. Exact-functor cohomology identifies H^q(FK) with F(H^q K), so every
functor here preserves both cohomological bounds.
4. Descend pullback composition via exact-derived composition and natural-isomorphism
localization. The definitions `openMate` and `closedMate` are precisely the open transpose
and the closed unit--square--counit mate, and are natural before imposing bounds.
5. The open transpose identity gives the displayed open restriction equation. Both
units and the square comparison are invertible, so this is the identity after canonical
identification. Its closed restriction has zero source and target by mixed vanishing
and the square comparison. Joint reflection makes beta invertible.
6. The closed triangle identity gives the displayed closed restriction equation.
The counits identify this with the identity. Its open restriction is between zero
objects by mixed vanishing and square transport. Joint reflection makes gamma invertible.
Restriction along the full bounded inclusions gives the two asserted natural isomorphisms.
-/
theorem integral_bounded_open_closed_base_change
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    {T : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    {Up : Over (Spec (.of k))}
    [LocallyOfFiniteType Up.hom] [QuasiCompact Up.hom] [IsSeparated Up.hom]
    {Zp : Over (Spec (.of k))}
    [LocallyOfFiniteType Zp.hom] [QuasiCompact Zp.hom] [IsSeparated Zp.hom]
    {Tp : Over (Spec (.of k))}
    [LocallyOfFiniteType Tp.hom] [QuasiCompact Tp.hom] [IsSeparated Tp.hom]
    (h : Tp ⟶ T) (j : U ⟶ T) (i : Z ⟶ T)
    (hU : Up ⟶ U) (jp : Up ⟶ Tp) (hZ : Zp ⟶ Z) (ip : Zp ⟶ Tp)
    [IsOpenImmersion j.left] [IsClosedImmersion i.left]
    [IsOpenImmersion jp.left] [IsClosedImmersion ip.left]
    (hcomp : Set.range j.left = (Set.range i.left)ᶜ)
    (sqU : IsPullback hU.left jp.left j.left h.left)
    (sqZ : IsPullback hZ.left ip.left i.left h.left) :
    Exists fun [_hi : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E) i.left)] ↦
    Exists fun [_hip : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E)
            ip.left)] ↦
      (∃ beta : DerivedCategory.Bounded.ι ⋙ ((pullback (integralCoefficientRing l E) hU.left) ⋙
            (openExtension (integralCoefficientRing l E) jp.left)) ≅
          DerivedCategory.Bounded.ι ⋙ ((openExtension (integralCoefficientRing l E) j.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)),
        beta.hom = Functor.whiskerLeft DerivedCategory.Bounded.ι (openMate
            (integralCoefficientRing l E)
            sqU.toCommSq)) ∧
      (∃ gamma : DerivedCategory.Bounded.ι ⋙ ((closedDirectImage (integralCoefficientRing l E)
            i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)) ≅
          DerivedCategory.Bounded.ι ⋙ ((pullback (integralCoefficientRing l E) hZ.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) ip.left)),
        gamma.hom = Functor.whiskerLeft DerivedCategory.Bounded.ι (closedMate
            (integralCoefficientRing l E)
            sqZ.toCommSq)) ∧
      (∀ N : DerivedCategory.Bounded
          (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
            (condensedRingObj (integralCoefficientRing l E) U.left)),
        DerivedCategory.TStructure.t.bounded
            (((pullback (integralCoefficientRing l E) hU.left) ⋙
            (openExtension (integralCoefficientRing l E) jp.left)).obj N.obj) ∧
        DerivedCategory.TStructure.t.bounded
            (((openExtension (integralCoefficientRing l E) j.left)
            ⋙ (pullback (integralCoefficientRing l E) h.left)).obj N.obj) ∧
        IsIso ((openAdjunction (integralCoefficientRing l E) jp.left).unit.app ((pullback
            (integralCoefficientRing l E) hU.left).obj
            N.obj)) ∧
        IsIso ((openAdjunction (integralCoefficientRing l E) j.left).unit.app N.obj) ∧
        (openAdjunction (integralCoefficientRing l E) jp.left).unit.app
            ((pullback (integralCoefficientRing l E) hU.left).obj N.obj) ≫
            (pullback (integralCoefficientRing l E) jp.left).map
            ((openMate
            (integralCoefficientRing l
            E) sqU.toCommSq).app N.obj) =
          (pullback (integralCoefficientRing l E) hU.left).map
            ((openAdjunction (integralCoefficientRing l E) j.left).unit.app N.obj) ≫
            (pullbackSquare (integralCoefficientRing l E) sqU.toCommSq).hom.app
            ((openExtension (integralCoefficientRing l E) j.left).obj N.obj) ∧
        IsZero ((pullback (integralCoefficientRing l E) ip.left).obj
          (((pullback (integralCoefficientRing l E) hU.left) ⋙
            (openExtension (integralCoefficientRing l E) jp.left)).obj N.obj)) ∧
        IsZero ((pullback (integralCoefficientRing l E) ip.left).obj
          (((openExtension (integralCoefficientRing l E) j.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj N.obj)) ∧
        (pullback (integralCoefficientRing l E) ip.left).map
            ((openMate
            (integralCoefficientRing l E)
            sqU.toCommSq).app N.obj) = 0) ∧
      (∀ N : DerivedCategory.Bounded
          (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
            (condensedRingObj (integralCoefficientRing l E) Z.left)),
        DerivedCategory.TStructure.t.bounded
            (((closedDirectImage (integralCoefficientRing l E) i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj N.obj) ∧
        DerivedCategory.TStructure.t.bounded
            (((pullback (integralCoefficientRing l E) hZ.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) ip.left)).obj N.obj) ∧
        IsIso ((closedAdjunction (integralCoefficientRing l E) i.left).counit.app N.obj) ∧
        IsIso ((closedAdjunction (integralCoefficientRing l E) ip.left).counit.app ((pullback
            (integralCoefficientRing l E) hZ.left).obj N.obj)) ∧
        (pullback (integralCoefficientRing l E) ip.left).map
            ((closedMate
            (integralCoefficientRing l
            E) sqZ.toCommSq).app N.obj) ≫
            (closedAdjunction (integralCoefficientRing l E) ip.left).counit.app ((pullback
            (integralCoefficientRing l E) hZ.left).obj N.obj) =
          (pullbackSquare (integralCoefficientRing l E) sqZ.toCommSq).inv.app
            ((closedDirectImage (integralCoefficientRing l E) i.left).obj N.obj) ≫
            (pullback (integralCoefficientRing l E) hZ.left).map
            ((closedAdjunction (integralCoefficientRing l E) i.left).counit.app N.obj) ∧
        IsZero ((pullback (integralCoefficientRing l E) jp.left).obj
          (((closedDirectImage (integralCoefficientRing l E) i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj N.obj)) ∧
        IsZero ((pullback (integralCoefficientRing l E) jp.left).obj
          (((pullback (integralCoefficientRing l E) hZ.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) ip.left)).obj N.obj)) ∧
        (pullback (integralCoefficientRing l E) jp.left).map
            ((closedMate
            (integralCoefficientRing l
            E) sqZ.toCommSq).app N.obj) = 0) := by
  have : QuasiCompact j.left := by
    have : QuasiCompact (j.left ≫ T.hom) := by rw [Over.w j]; infer_instance
    exact QuasiCompact.of_comp j.left T.hom
  have : QuasiCompact jp.left := by
    have : QuasiCompact (jp.left ≫ Tp.hom) := by rw [Over.w jp]; infer_instance
    exact QuasiCompact.of_comp jp.left Tp.hom
  exact bounded_open_closed_base_change (integralCoefficientRing l E) hcomp sqU sqZ

/-- Locally closed base change is the composite of the open beta and the inverse closed
gamma, with a fixed open--closed factorization. The displayed equation specifies that
composite without choosing any unrelated isomorphism.
Source: blueprint `det-lem-int-tensor-pullback.proof.md`, Local models; node proof, Step 7
(blueprint: lem-sfb-integral-bounded-stratum-base-change).

Proof: Apply the preceding open result to u inside the closure and the closed result
to i, using the bounded input u_!M. Its boundedness follows from exact-functor cohomology.
First apply i'_* to beta_u,M, then compose with the inverse of gamma_i,u_!M. These maps
are natural in M; every factor is invertible, and exactness keeps both ends bounded.
The composite satisfies the displayed cancellation equation by the inverse identity.
No independence of factorization, constructibility, or derived completeness is used.
-/
theorem integral_bounded_locally_closed_base_change
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    {C : Over (Spec (.of k))}
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    {T : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    {Sp : Over (Spec (.of k))}
    [LocallyOfFiniteType Sp.hom] [QuasiCompact Sp.hom] [IsSeparated Sp.hom]
    {Cp : Over (Spec (.of k))}
    [LocallyOfFiniteType Cp.hom] [QuasiCompact Cp.hom] [IsSeparated Cp.hom]
    {Tp : Over (Spec (.of k))}
    [LocallyOfFiniteType Tp.hom] [QuasiCompact Tp.hom] [IsSeparated Tp.hom]
    (h : Tp ⟶ T) (u₀ : S ⟶ C) (i : C ⟶ T)
    (hS : Sp ⟶ S) (up : Sp ⟶ Cp) (hC : Cp ⟶ C) (ip : Cp ⟶ Tp)
    [IsOpenImmersion u₀.left] [IsClosedImmersion i.left]
    [IsOpenImmersion up.left] [IsClosedImmersion ip.left]
    (sqU : IsPullback hS.left up.left u₀.left hC.left)
    (sqI : IsPullback hC.left ip.left i.left h.left) :
    Exists fun [_hi : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E) i.left)] ↦
    Exists fun [_hip : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E)
            ip.left)] ↦
      ∃ e : DerivedCategory.Bounded.ι ⋙
          ((pullback (integralCoefficientRing l E) hS.left) ⋙
            (openExtension (integralCoefficientRing l E) up.left) ⋙ (closedDirectImage
            (integralCoefficientRing l E) ip.left)) ≅
        DerivedCategory.Bounded.ι ⋙
          ((openExtension (integralCoefficientRing l E) u₀.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) i.left) ⋙ (pullback
            (integralCoefficientRing l E) h.left)),
        ∀ M : DerivedCategory.Bounded
            (Mod (Sheaf (Scheme.ProEt.topology S.left) Ab.{u + 1})
              (condensedRingObj (integralCoefficientRing l E) S.left)),
          DerivedCategory.TStructure.t.bounded
              (((pullback (integralCoefficientRing l E) hS.left) ⋙
            (openExtension (integralCoefficientRing l E) up.left)
            ⋙ (closedDirectImage (integralCoefficientRing l E) ip.left)).obj M.obj) ∧
          DerivedCategory.TStructure.t.bounded
              (((openExtension (integralCoefficientRing l E) u₀.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj M.obj) ∧
          e.hom.app M ≫
              (closedMate (integralCoefficientRing l E) sqI.toCommSq).app
            ((openExtension (integralCoefficientRing l E) u₀.left).obj M.obj) =
            (closedDirectImage (integralCoefficientRing l E) ip.left).map
            ((openMate
            (integralCoefficientRing l
            E) sqU.toCommSq).app M.obj) := by
  let Λ := integralCoefficientRing l E
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have : IsLocallyNoetherian Tp.left := LocallyOfFiniteType.isLocallyNoetherian Tp.hom
  obtain ⟨hi, hip, hγ⟩ := closed_square_iso Λ sqI
  have hβ := open_mate_iso Λ sqU
  let β := asIso (openMate Λ sqU.toCommSq)
  let γ := asIso (closedMate Λ sqI.toCommSq)
  let e₀ :
      (pullback Λ hS.left) ⋙ (openExtension Λ up.left) ⋙ (closedDirectImage Λ ip.left) ≅
        (openExtension Λ u₀.left) ⋙ (closedDirectImage Λ i.left) ⋙ (pullback Λ h.left) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight β _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ γ.symm
  refine ⟨hi, hip, Functor.isoWhiskerLeft DerivedCategory.Bounded.ι e₀, ?_⟩
  intro M
  refine ⟨(CondensedRing.lowerStar Λ ip.left).bounded_mapDerivedCategory_obj
      ((CondensedRing.openImmersionLowerShriek Λ up.left).bounded_mapDerivedCategory_obj
        ((CondensedRing.upperStar Λ hS.left).bounded_mapDerivedCategory_obj M.property)),
    (CondensedRing.upperStar Λ h.left).bounded_mapDerivedCategory_obj
      ((CondensedRing.lowerStar Λ i.left).bounded_mapDerivedCategory_obj
        ((CondensedRing.openImmersionLowerShriek Λ u₀.left).bounded_mapDerivedCategory_obj
          M.property)), ?_⟩
  exact stratum_composite_cancel β γ M.obj


end AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange
