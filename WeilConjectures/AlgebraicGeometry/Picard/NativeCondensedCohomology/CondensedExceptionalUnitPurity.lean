/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.CondensedExceptionalUnitCoordinates
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.CondensedExceptionalUnitCoordinates
import WeilConjectures.DeligneLaumon.NativeCondensedCohomology.CondensedTatePairEncoding
import WeilConjectures.AlgebraicGeometry.Picard.NativeCondensedCohomology.CondensedUnitPurityCounit
import WeilConjectures.WeilSheaf.TateTwistCohomology

/-! # Frobenius cohomology of the ordinary condensed exceptional unit

The exceptional functor in this statement is an ordinary localizing right adjoint.
No native exceptional functor is a parameter.
Source: sk-cor-sp-all-coefficients and the geometric-Frobenius purity square.
(blueprint: lem-sf-condensed-exceptional-unit-purity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
attribute [local instance 1100] CategoryTheory.instOverClass
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.NativeCondensedCohomology

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ell : ℕ) [Fact ell.Prime]
  [Fact (ringChar k₀ ≠ ell)]
  (X : Scheme.{u}) [X.Over (Spec (.of k₀))]
  [IsSeparated (X ↘ Spec (.of k₀))] [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
  [QuasiCompact (X ↘ Spec (.of k₀))]

local instance structureIsOver : (X ↘ Spec (.of k₀)).IsOver (Spec (.of k₀)) := by
  exact ⟨Category.comp_id _⟩

variable (c : Compactification (fiberMap k₀ (X ↘ Spec (.of k₀))).hom.left)
  (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj ell)
    (AlgebraicClosure k₀))
  (E : ExceptionalUnit k₀ ell (X ↘ Spec (.of k₀)) c H)

/-- Cohomology of an equivariant single complex is the original equivariant object. -/
private def singlePairHomologyIso {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F] (K : IsoAlgebra F) (n : ℤ) :
    (IsoAlgebra.mapOfNatIso (F.mapDerivedCategoryHomologyFunctorIso n)).obj
        ((IsoAlgebra.mapOfNatIso (F.mapDerivedCategorySingleFunctor n)).obj K) ≅ K := by
  refine IsoAlgebra.isoMk
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app K.carrier) ?_
  simp only [← IsoAlgebra.str_hom, IsoAlgebra.mapOfNatIso_obj_str,
    IsoAlgebra.mapOfNatIso_obj_carrier, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hnat := (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.naturality
    K.str.hom
  simp only [Functor.comp_map, Functor.id_map] at hnat
  rw [hnat]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ K.str.hom)
    (F.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor n K.carrier).symm

private def singlePairShiftIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F] (K : IsoAlgebra F)
    (s n n' : ℤ) (h : s + n = n') :
    (IsoAlgebra.mapOfNatIso (F.mapDerivedCategory.commShiftIso s)).obj
        ((IsoAlgebra.mapOfNatIso (F.mapDerivedCategorySingleFunctor n')).obj K) ≅
      (IsoAlgebra.mapOfNatIso (F.mapDerivedCategorySingleFunctor n)).obj K := by
  refine IsoAlgebra.isoMk
    (((DerivedCategory.singleFunctors C).shiftIso s n n' h).app K.carrier) ?_
  simp only [← IsoAlgebra.str_hom, IsoAlgebra.mapOfNatIso_obj_str,
    IsoAlgebra.mapOfNatIso_obj_carrier, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc,
    F.mapDerivedCategorySingleFunctor_hom_app_shiftIso s n n' h K.carrier]
  simp only [Category.assoc]
  have hnat := ((DerivedCategory.singleFunctors C).shiftIso s n n' h).hom.naturality
    K.str.hom
  simp only [Functor.comp_map] at hnat
  rw [← hnat]

private def encoded_tate_tensor_iso (d : ℕ) :
    (sheafEncoding k₀ ell X).obj
        ((WeilSheaf.tateTwistSheaf k₀ ell X d).tensorObj
          (WeilSheaf.adicConstant k₀ ell X)
          (WeilSheaf.isLisse_tateTwistSheaf k₀ ell X d)) ≅
      (encode k₀ ell X).obj
        ((ProEtaleWeilSheaf.constantTwist k₀ ell X
          (WeilSheaf.cyclotomicUnit k₀ ell ^ (d : ℤ))).obj
            (ProEtaleWeilSheaf.adicConstant k₀ ell X)) := by
  let F := WeilSheaf.tateTwistSheaf k₀ ell X d
  let U := WeilSheaf.adicConstant k₀ ell X
  let hF := WeilSheaf.isLisse_tateTwistSheaf k₀ ell X d
  let e := WeilSheaf.tensorObjObjIsoOfIso F U hF
    (WeilSheaf.tateTwistSheafObjIso k₀ ell X (d : ℤ))
    (ProEtaleWeilSheaf.constantTwistOneObjIso U.obj).symm
  exact (encode k₀ ell X).mapIso
    (e ≪≫ ProEtaleWeilSheaf.constantTwistCongrIso (mul_one _) _)

/-- The normalized ordinary exceptional unit has the Tate cohomology datum.

Source: sk-cor-sp-all-coefficients.proof.md, apply smooth purity at the coefficient
unit; thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Steps 1--2; the
q^(-d) normalization in sk-def-sf-weil-complexes.
(blueprint: lem-sf-condensed-exceptional-unit-purity).

Proof in words. Base change the structural map to the algebraic closure; smoothness
of pure dimension d persists. Apply condensed_smooth_unit_comparison at the closure coefficient
and its coefficient unit. Compare its explicit adjunction to E.adjunction by the unique
counit-compatible right-adjoint isomorphism. Pullback of the unit and tensor unitors
identify the smooth source with the actual condensed Tate line shifted by 2d.

For the semilinear geometric-Frobenius square, normalized smooth base change identifies
the smooth-source pullback map with the pullback/tensor/root-line comparison. Its mate
is normalized compact-support exchange. Hence the purity/counit squares identify the
induced exceptional datum with E.theta, using E.normalized and adjunction uniqueness.
This is an equivariant purity isomorphism of ordinary derived objects, not a claim
that every underlying isomorphism is equivariant.

A compatible system of roots over the algebraically closed field trivializes the
positive Tate line. Frobenius on its d-th power is q^(-d); a change of root basis
conjugates this scalar and leaves it unchanged. The exact native heart encoding sends
the native scalar unit to the ordinary unit, and preserves this scalar action, tensor
unitors and positive tensor powers. Thus the root-normalized condensed line is the
encoded native Tate sheaf tensor the encoded native constant. Apply degree -2d
cohomology to the equivariant purity isomorphism and the single-functor shift identity.
For d=0 use the zeroth power and shift zero; empty X uses the same maps, with no
nonempty or connectedness assumption. -/
theorem condensed_exceptional_unit_purity (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of k₀))] :
    Nonempty
      ((pairHomology k₀ ell X (-2 * (d : ℤ))).obj E.pair ≅
        (sheafEncoding k₀ ell X).obj
          ((WeilSheaf.tateTwistSheaf k₀ ell X d).tensorObj
            (WeilSheaf.adicConstant k₀ ell X)
            (WeilSheaf.isLisse_tateTwistSheaf k₀ ell X d))) := by
  obtain ⟨p, ⟨e⟩⟩ := condensed_exceptional_unit_source k₀ ell X c H E d
  obtain ⟨eT⟩ := condensed_tate_pair_encoding k₀ ell X p d
  let eS := singlePairShiftIso (action k₀ ell X) (tatePair k₀ ell X p d)
    (2 * (d : ℤ)) (-2 * (d : ℤ)) 0 (by simp only [neg_mul, add_neg_cancel])
  exact ⟨(pairHomology k₀ ell X (-2 * (d : ℤ))).mapIso (e ≪≫ eS) ≪≫
    singlePairHomologyIso (action k₀ ell X) (tatePair k₀ ell X p d) (-2 * (d : ℤ)) ≪≫
      eT ≪≫ (encoded_tate_tensor_iso k₀ ell X d).symm⟩

end WeilConjectures.NativeCondensedCohomology
