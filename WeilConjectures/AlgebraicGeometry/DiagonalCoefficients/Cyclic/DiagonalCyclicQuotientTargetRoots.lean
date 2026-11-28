/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientAugmentation
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteRootNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFiniteRootsCanonicalMap
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralRootMap
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootTowerFiniteTensor

/-! # Root projections for the cyclic normalized target endpoint -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The ordinary limit projection of the root system, read on underlying sheaves, is the
limit projection of the roots of unity tower. -/
theorem rootLimitComparison_projection (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (H : DiagonalSystems l X)
    (roots : H ⋙ diagonalForget l X ≅
      Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (n : ℕ) :
    (diagonalRootLimitComparison l X H roots).inv ≫
        (diagonalForget l X).map (limit.π H (op n)) =
      limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) ≫
        roots.inv.app (op n) := by
  unfold diagonalRootLimitComparison
  simp only [Iso.trans_inv, Category.assoc, preservesLimitIso_inv_π, HasLimit.isoOfNatIso_inv_π,
    Functor.comp_obj]

/-- Under the normalizations of the completed root limit and the finite root endpoint,
the finite projection of the completed Tate line followed by the root endpoint is the
canonical root map on the projection of the roots tower. -/
theorem cyclic_target_root_projection (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (t0 : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H)
    (ht0 : HEq ((diagonalForget l (diagonalSurface Y)).map t0.hom)
      (diagonalRootLimitComparison l (diagonalSurface Y) H roots).inv)
    (n : ℕ)
    (t : H.obj (op n) ≅ (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y)))
    (ht : DiagonalTrace.FiniteRootNormalization l Y hY H roots n t) :
    (diagonalForget l (diagonalSurface Y)).map (t0.hom ≫ limit.π H (op n)) ≫
        (diagonalForget l (diagonalSurface Y)).map t.hom =
      limit.π (Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
          (op n) ≫
        cartierProRootMap (diagonalResidue.{u} l n) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) (diagonalSurface Y)
          (pow_pos (Fact.out : l.Prime).pos _) (diagonalSurface_power_unit l Y hY n) := by
  unfold DiagonalTrace.FiniteRootNormalization at ht
  rw [Functor.map_comp, Category.assoc, eq_of_heq ht0]
  erw [reassoc_of% rootLimitComparison_projection,
    eq_of_heq ht, Iso.inv_hom_id_app_assoc]
  rfl

/-- The finite projection of the completed root limit is an epimorphism on underlying
sheaves. -/
theorem cyclic_target_root_projection_epi (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (t0 : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H)
    (ht0 : HEq ((diagonalForget l (diagonalSurface Y)).map t0.hom)
      (diagonalRootLimitComparison l (diagonalSurface Y) H roots).inv)
    (n : ℕ) :
    Epi ((diagonalForget l (diagonalSurface Y)).map (t0.hom ≫ limit.π H (op n))) := by
  have hX : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa using diagonalSurface_power_unit l Y hY 0
  have hT (x : diagonalSurface Y) : IsUnit (l : (diagonalSurface Y).presheaf.stalk x) := by
    simpa only [map_natCast] using hX.map ((diagonalSurface Y).presheaf.germ ⊤ x trivial).hom
  have : Epi (limit.π (Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l
      (Fact.out : l.Prime)) (op n)) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).mp
      (Scheme.rootTower_finite_tensor (diagonalSurface Y) l hT n).1
  rw [Functor.map_comp, eq_of_heq ht0]
  erw [rootLimitComparison_projection]
  exact @epi_comp _ _ _ _ _ _ this _ (inferInstanceAs (Epi (roots.app (op n)).inv))

/-- The underlying cyclic line map, followed by the finite line endpoint, is the canonical
root map on the projection of the roots tower. -/
theorem cyclic_line_root_projection (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤))) (n : ℕ)
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    eW.underlying.inv.app (Scheme.purTwistZlModule (diagonalSurface Y) l) ≫
        eW.lineIso.hom.hom ≫ cyclicLineMap l n (diagonalSurface Y) ≫
        (cyclicFiniteUnderlying l Y n p).inv.app (cyclicLine l n (diagonalSurface Y)) ≫
        (diagonalForget l (diagonalSurface Y)).map
          ((diagonalFiniteToPadic l n (diagonalSurface Y)).map p.lineEndpoint.iso.hom) =
      limit.π (Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
          (op n) ≫
        cartierProRootMap (diagonalResidue.{u} l n) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) (diagonalSurface Y)
          (pow_pos (Fact.out : l.Prime).pos _) (diagonalSurface_power_unit l Y hY n) := by
  have hline := eq_of_heq eW.line_normalization
  have hroots := diagonalIntegralRoots_unique l (diagonalSurface Y) (bottomField l)
    eW.roots p.integralRoots
  have hp := p.lineEndpoint.normalization
  unfold FiniteRealization.LineNormalization at hp
  rw [← finiteRoots_toLine_eq_cartierProRootMap p.finiteRoots]
  have hmid : (cyclicFiniteUnderlying l Y n p).inv.app (cyclicLine l n (diagonalSurface Y)) ≫
      (diagonalForget l (diagonalSurface Y)).map
        ((diagonalFiniteToPadic l n (diagonalSurface Y)).map p.lineEndpoint.iso.hom) =
      p.eW.underlying.inv.app (cyclicLine l n (diagonalSurface Y)) ≫
        (sheafCompose (Scheme.ProEt.topology (diagonalSurface Y))
          (forget₂ (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) Ab.{u + 1})).map
            p.lineEndpoint.iso.hom := by
    unfold cyclicFiniteUnderlying diagonalFiniteForgetIso
    simp only [Functor.comp_obj, Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
    congr 1
  erw [hmid, ← Category.assoc]
  erw [hline]
  rw [hroots]
  exact (Category.assoc _ _ _).symm.trans hp

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
