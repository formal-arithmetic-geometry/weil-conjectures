/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
import WeilConjectures.TateTwist.ProEtale
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueQuotient
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.AlgebraicGeometry.Affine.AffineRootsRepresentability
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateTowerLimit
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRootTower
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportTateLimit

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-canonical-pullback). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

private theorem pullNormalized_unique
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)}
    {N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)}
    (e e' : (CondensedRing.upperStar R f).obj M ≅ N)
    {B : Type (u + 1)} (raw : B)
    (h : PullNormalized R f e raw) (h' : PullNormalized R f e' raw) : e = e' := by
  apply Iso.ext
  let a := (Functor.isoWhiskerLeft
    ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj R Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom R f))).inv.app M
  have heq : (Mod.forget (condensedRingObj R X)).map (a ≫ e.hom) =
      (Mod.forget (condensedRingObj R X)).map (a ≫ e'.hom) :=
    eq_of_heq (h.trans h'.symm)
  have heq' := (Mod.forget (condensedRingObj R X)).map_injective heq
  exact (cancel_epi a).mp heq'

/-- The projection-normalized integral root comparison.
Source: Bhatt--Scholze 6.8 (blueprint: def-pur-transport-canonical-pullback).
Proof: finite roots commute with inverse image since ell is invertible. On a
compatible primitive-root cover both inverse-limit modules are the coefficient
unit. Their finite projections fix the comparison uniquely. -/
theorem integralComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    ∃! e : (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).obj
      (tateModule Y ell) ≅ tateModule X ell,
      ∀ n : ℕ, ∃ en :
        (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).obj
          (tateModuleLevel Y ell n) ≅ tateModuleLevel X ell n,
        PullNormalized (Profinite.continuousMapRingObj ℤ_[ell]) f en
          (rootTensorPull ell f n) ∧
        e.hom ≫ limit.π (tateModuleSystem X ell) (Opposite.op n) =
          (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).map
            (limit.π (tateModuleSystem Y ell) (Opposite.op n)) ≫ en.hom := by
  obtain ⟨c, hc⟩ := normalizedRootTower ell f
  obtain ⟨hlim⟩ := tateLimitCone ell f
  let C := (Cone.postcompose c.hom).obj
    ((CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).mapCone
      (limit.cone (tateModuleSystem Y ell)))
  let hC : IsLimit C := (IsLimit.postcomposeHomEquiv c _).symm hlim
  let e := hC.conePointUniqueUpToIso (limit.isLimit (tateModuleSystem X ell))
  have he (n : ℕ) :
      e.hom ≫ limit.π (tateModuleSystem X ell) (Opposite.op n) =
        (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).map
          (limit.π (tateModuleSystem Y ell) (Opposite.op n)) ≫
            (c.app (Opposite.op n)).hom :=
    hC.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (Opposite.op n)
  refine ⟨e, fun n ↦ ⟨c.app (Opposite.op n), hc n, he n⟩, ?_⟩
  intro e' he'
  apply Iso.ext
  apply limit.hom_ext
  intro n
  obtain ⟨en, hn, he'n⟩ := he' n.unop
  have hn' : en = c.app n :=
    pullNormalized_unique _ f en (c.app n) (rootTensorPull ell f n.unop) hn (hc n.unop)
  rw [hn'] at he'n
  exact he'n.trans (he n.unop).symm

/-- Scalar association applied to an integral-root comparison, in a generic
coefficient ring. Source: Cartesianity of scalar extension
(blueprint: def-pur-transport-canonical-pullback). -/
def scalarPull
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)}
    {N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)}
    (e : (CondensedRing.upperStar R f).obj M ≅ N) :=
  (CondensedRing.pullIso a f).symm.app M ≪≫
    (Mod.extendScalars (coefficientMap a X)).mapIso e

end AlgebraicGeometry.ProEtale.PurityTransport
