/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.ProperOpenSquareSupport.ProperOpenSquareDerivedSupport
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.SemilinearProperOpenNormalization

/-! # Unbounded proper/open support for the actual quotient-ring towers

Source: Stacks 0F7B and the Postnikov proof of proper/open derived support.
(blueprint: lem-sp-coefficient-tower-unbounded-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.VaryingRing

private def intrinsicOpenIso (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    StrictTower.moduleJ (ULift.{u + 1} A) j ≅ sfIntrinsicExtensionByZero j A :=
  (StrictTower.moduleJAdj (ULift.{u + 1} A) j).leftAdjointUniq
    ((sfIntrinsicOpenAdjunction A j).ofNatIsoRight (openSquarePullbackModel A j).symm)

private theorem level_supported_counit
    (A : Type u) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : DerivedCategory (StrictTower.Modules (ULift.{u + 1} A) U)) :
    IsIso ((levelJAdj (fun _ : ℕ ↦ CommRingCat.of (ULift.{u + 1} A)) i 0).counit.app
      ((StrictTower.moduleDirectImage (ULift.{u + 1} A) p).rightDerivedFunctor.obj
        ((StrictTower.moduleJ (ULift.{u + 1} A) k).mapDerivedCategory.obj M))) := by
  let R : ℕ → CommRingCat.{u + 1} := fun _ ↦ CommRingCat.of (ULift.{u + 1} A)
  let adj := levelJAdj R i 0
  have := level_derived_open_unit_iso R i 0
  let ff := adj.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let Jk := (StrictTower.moduleJ (ULift.{u + 1} A) k).mapDerivedCategory
  let P := (StrictTower.moduleDirectImage (ULift.{u + 1} A) p).rightDerivedFunctor
  let N := P.obj (Jk.obj M)
  let dP : P ≅ proEtaleConstantDerivedDirectImage p A :=
    Functor.rightDerivedFunctorNatIso (openSquare_directImageModel A p)
  let dJ := Functor.mapDerivedCategoryNatIso (intrinsicOpenIso A k)
  let dI := Functor.mapDerivedCategoryNatIso (intrinsicOpenIso A i)
  let d : N ≅ (proEtaleConstantDerivedDirectImage p A).obj
      ((sfIntrinsicDerivedOpen A k).obj M) :=
    dP.app (Jk.obj M) ≪≫ (proEtaleConstantDerivedDirectImage p A).mapIso (dJ.app M)
  have hs := ProperOpenSquareSupport.derived_support_square p k i r h A M
  let a := exceptionalOpenAdjunction i A
  let s := asIso (a.counit.app
    ((proEtaleConstantDerivedDirectImage p A).obj ((sfIntrinsicDerivedOpen A k).obj M)))
  let e : N ≅ (StrictTower.moduleJ (ULift.{u + 1} A) i).mapDerivedCategory.obj
      ((sfIntrinsicDerivedPullback A i).obj
        ((proEtaleConstantDerivedDirectImage p A).obj ((sfIntrinsicDerivedOpen A k).obj M))) :=
    d ≪≫ s.symm ≪≫ (dI.app _).symm
  exact adj.isIso_counit_app_of_iso e

private theorem evaluated_counit_isIso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {J : C ⥤ D} {P : D ⥤ C} {j : C' ⥤ D'} {p : D' ⥤ C'}
    (a : J ⊣ P) (b : j ⊣ p) (F : C ⥤ C') (G : D ⥤ D')
    (e : J ⋙ G ≅ F ⋙ j) (t : P ⋙ F ≅ G ⋙ p)
    (he : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ t.hom)).natTrans = e.inv)
    (M : D) [IsIso (b.counit.app (G.obj M))] :
    IsIso (G.map (a.counit.app M)) := by
  have hm := mateEquiv_counit_symm a b (TwoSquare.mk _ _ _ _ t.hom) M
  change j.map (t.hom.app M) ≫ b.counit.app (G.obj M) =
    (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ t.hom)).natTrans).app (P.obj M) ≫
      G.map (a.counit.app M) at hm
  rw [he] at hm
  have : IsIso (e.inv.app (P.obj M) ≫ G.map (a.counit.app M)) := by
    rw [← hm]
    infer_instance
  exact IsIso.of_isIso_comp_left (e.inv.app (P.obj M)) _

/-- Direct image of an open extension is supported on the target open on every
unbounded quotient-ring system. No common cohomological bound is imposed.
Source: Stacks 0F7B
(blueprint: lem-sp-coefficient-tower-unbounded-support).

Proof: at level n use the actual proper-image and exact-open evaluation isomorphisms.
The coefficient ring is the literal lift of A_n, so its module category is the
intrinsic constant-ring category. Uniqueness of the open left adjoint identifies
its essential image with the intrinsic open extension. The finite-coefficient
unbounded support theorem gives membership in this essential image after proper
image. Therefore the level open counit is invertible. The counit mate equation
identifies evaluation of the system counit with this finite counit up to the
invertible open and pullback comparisons. Joint conservativity of actual system
evaluations proves the assertion, including empty opens and empty schemes. -/
theorem quotient_system_supported_counit
    (A : ℕ → Type u) [∀ n, CommRing (A n)] [∀ n, Finite (A n)]
    (φ : ∀ n, CommRingCat.of (ULift.{u + 1} (A (n + 1))) ⟶
      CommRingCat.of (ULift.{u + 1} (A n)))
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : Derived (fun n ↦ CommRingCat.of (ULift.{u + 1} (A n))) φ U) :
    IsIso ((jAdj (fun n ↦ CommRingCat.of (ULift.{u + 1} (A n))) φ i).counit.app
      ((P (fun n ↦ CommRingCat.of (ULift.{u + 1} (A n))) φ p).obj
        ((J (fun n ↦ CommRingCat.of (ULift.{u + 1} (A n))) φ k).obj M))) := by
  let R n := CommRingCat.of (ULift.{u + 1} (A n))
  let N := (P R φ p).obj ((J R φ k).obj M)
  let d := (WeilConjectures.SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
    (ProEt.topology Z) (coefficients R Z) (coefficientTransition R φ Z)).some
  apply d.systems.detects
  intro n
  let e : (ev R φ Z n).obj N ≅
      (StrictTower.moduleDirectImage (R n) p).rightDerivedFunctor.obj
        ((StrictTower.moduleJ (R n) k).mapDerivedCategory.obj ((ev R φ U n).obj M)) :=
    (evalP R φ p n).app ((J R φ k).obj M) ≪≫
      (StrictTower.moduleDirectImage (R n) p).rightDerivedFunctor.mapIso
        ((evalJ R φ k n).app M)
  have hs := level_supported_counit (A n) k r p i h ((ev R φ U n).obj M)
  have hn : IsIso ((levelJAdj R i n).counit.app ((ev R φ Z n).obj N)) :=
    (NatTrans.isIso_app_iff_of_iso (levelJAdj R i n).counit e).2 hs
  exact evaluated_counit_isIso (jAdj R φ i) (levelJAdj R i n)
    (ev R φ W n) (ev R φ Z n) (evalJ R φ i n) (evalG R φ i n) rfl N

private theorem counit_transport
    {C D : Type*} [Category C] [Category D]
    {J J' : C ⥤ D} {P P' : D ⥤ C} (hJ : J = J') (hP : P = P')
    (a : J ⊣ P) (a' : J' ⊣ P') (ha : HEq a a')
    {N N' : D} (hN : N = N') [IsIso (a'.counit.app N')] :
    IsIso (a.counit.app N) := by
  subst J' P' N'
  cases eq_of_heq ha
  infer_instance

private theorem transformation_isIso_transport
    {C D : Type*} [Category C] [Category D]
    {F F' G G' : C ⥤ D} (hF : F = F') (hG : G = G')
    (a : F ⟶ G) (a' : F' ⟶ G') (ha : HEq a a') [IsIso a] : IsIso a' := by
  subst F' G'
  cases eq_of_heq ha
  infer_instance

/-- The literal proper/open mate is invertible on unbounded finite-ring systems.
Source: Stacks 0F7B
(blueprint: lem-sp-coefficient-tower-unbounded-support).

Proof: support makes the open counit invertible. Normalize the semilinear and
varying-ring open adjunctions, and use the already proved adjunct formula: gamma
is open extension of inverse lambda followed by this counit. Both factors are
invertible. Finally transport through the proved equality of the actual gamma
words. No equality of maps is deduced from level evaluations. -/
theorem quotient_gamma_isIso
    (A : ℕ → Type u) [∀ n, CommRing (A n)] [∀ n, Finite (A n)]
    (φ : ∀ n, CommRingCat.of (ULift.{u + 1} (A (n + 1))) ⟶
      CommRingCat.of (ULift.{u + 1} (A n)))
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    IsIso (gamma (fun n ↦ CommRingCat.of (ULift.{u + 1} (A n))) φ k r p i h) := by
  let R n := CommRingCat.of (ULift.{u + 1} (A n))
  have hc (M : Derived R φ U) :
      IsIso ((SemilinearProperOpen.jAdj R φ i).counit.app
        ((SemilinearProperOpen.R R φ p).obj
          ((SemilinearProperOpen.J R φ k).obj M))) := by
    let N := (P R φ p).obj ((J R φ k).obj M)
    have : IsIso ((jAdj R φ i).counit.app N) :=
      quotient_system_supported_counit A φ k r p i h M
    exact counit_transport (SemilinearProperOpen.J_eq R φ i)
      (SemilinearProperOpen.P_eq R φ i) (SemilinearProperOpen.jAdj R φ i)
      (jAdj R φ i) (SemilinearProperOpen.Normalization.jadj_heq R φ i)
      (by rw [SemilinearProperOpen.R_eq, SemilinearProperOpen.J_eq])
  have hi (M : Derived R φ U) :
      IsIso ((SemilinearProperOpen.gamma R φ k r p i h).app M) := by
    let : IsIso ((SemilinearProperOpen.jAdj R φ i).counit.app
        ((SemilinearProperOpen.J R φ k ⋙ SemilinearProperOpen.R R φ p).obj M)) := hc M
    have he := (SemilinearProperOpen.gamma_adjunct R φ k r p i h M).1
    have hm := congrArg ((SemilinearProperOpen.jAdj R φ i).homEquiv _ _).symm he
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at hm
    rw [hm]
    infer_instance
  have : IsIso (SemilinearProperOpen.gamma R φ k r p i h) :=
    NatIso.isIso_of_isIso_app _
  exact transformation_isIso_transport
    (congrArg₂ Functor.comp (SemilinearProperOpen.R_eq R φ r)
      (SemilinearProperOpen.J_eq R φ i))
    (congrArg₂ Functor.comp (SemilinearProperOpen.J_eq R φ k)
      (SemilinearProperOpen.R_eq R φ p))
    (SemilinearProperOpen.gamma R φ k r p i h) (gamma R φ k r p i h)
    (SemilinearProperOpen.Normalization.gamma_normalization R φ k r p i h)

end AlgebraicGeometry.ProEtale.VaryingRing
