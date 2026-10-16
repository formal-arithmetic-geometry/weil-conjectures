/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import all Sheaf.AlgebraicGeometry.FormalSystemsPullback
import all Sheaf.AlgebraicGeometry.TorsionControlledFormalRestriction
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Restricting one torsion-controlled local model

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness; equation 0880.
(blueprint: lem-weil-pbc-torsion-local-model-restriction).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem coherent_of_iso {X : Scheme.{u}} [IsNoetherian X]
    {F G : X.Modules} (e : F ≅ G)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    RingedSpace.IsCoherent X.toRingedSpace F := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- A single local coherent model restricts, with its actual torsion bounds and
normalized quotient maps, to every smaller open. This asserts no comparison map
between different local models.

Source: Stacks Project, Tag 0889(1), first sentence of proof; equation 0880.
(blueprint: lem-weil-pbc-torsion-local-model-restriction).

Proof: Let f : W → U be the open immersion, R its restriction functor, and T
its tensor pullback. Their adjunctions to the same pushforward give t : T ≅ R.
Construct Fw = R(F). The proved coherent_pullback helper of FormalSystemsPullback
and invariance under isomorphism prove coherence. Set lw = overMapCompOverEquiv(L)
followed by R(l). The over-site comparisons and hHlocal identify R(Hlocal) with Hw;
call that isomorphism eH, and define aw = R(a) followed by eH. Naturality of
overMapCompOverEquiv and R(hb), followed by cancellation of the comparison
isomorphisms, prove the required b equation.

The proved powerQuotientIso helpers of FormalSystemsPullback construct a normalized
completion comparison for T(F). Conjugate by t to obtain gamma for R(F). Naturality
of t, powerQuotientIso_π, and the cokernel descent equation show that R(π) followed
by gamma is π for R(F). Assemble beta_w using overFunctorMap inverse,
overMapCompOverEquiv, overFunctorEquiv U, R(beta), and gamma. To check q, postcompose
with beta_w, cancel overFunctorMap, use naturality of overMapCompOverEquiv and R(hq),
cancel R(beta inverse) against R(beta), and apply the normalized gamma equation.

The actual kernel and cokernel of a are quasi-coherent. The proved
powerProduct_pullback_zero helper transfers their zero ideal-power products to T;
the powerProduct_zero_of_iso helper of TorsionControlledFormalRestriction transfers
them through t. Restriction preserves kernels and cokernels, and postcomposition
with eH preserves their isomorphism classes. Transfer the zero products through
these comparisons to get the same positive exponent for aw. The ideal on W is
identified using comap_comp and homOfLE_ι. Nothing assumes a cover or affineness;
empty opens, zero modules, and zero or unit ideals use these same constructions.
-/
theorem torsionLocalModel_restriction
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (U W : X.Opens) (h : W ≤ U)
    (Hlocal F : CoherentModules U.toScheme)
    (hHlocal : Hlocal.obj = (Scheme.Modules.restrictFunctor U.ι).obj H.obj)
    (a : F ⟶ Hlocal)
    (β : N.obj ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      formalCompletionSystem (J.comap U.ι) F.obj)
    (ha : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap U.ι).toModulesι s).2 (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap U.ι).toModulesι s).2 (cokernel a.hom)))
    (L : SheafOfModules ((moduleRings X.toRingedSpace).over U))
    (l : (Scheme.Modules.overEquiv U).functor.obj L ≅ F.obj)
    (b : L ⟶ H.obj.over U) (q : ∀ n : ℕᵒᵖ, L ⟶ (N.obj.obj n).over U)
    (hb : (Scheme.Modules.overEquiv U).functor.map b ≫
      (Scheme.Modules.overFunctorEquiv U).hom.app H.obj ≫ eqToHom hHlocal.symm =
        l.hom ≫ a.hom)
    (hq : ∀ n : ℕᵒᵖ, (Scheme.Modules.overEquiv U).functor.map (q n) ≫
      (Scheme.Modules.overFunctorEquiv U).hom.app (N.obj.obj n) =
        l.hom ≫ formalModuleQuotientπ (J.comap U.ι) (n.unop + 1) F.obj ≫ β.inv.app n)
    (Hw : CoherentModules W.toScheme)
    (hHw : Hw.obj = (Scheme.Modules.overEquiv W).functor.obj (H.obj.over W)) :
    ∃ (Fw : CoherentModules W.toScheme)
      (lw : (Scheme.Modules.overEquiv W).functor.obj
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE h : W ⟶ U)).obj L) ≅ Fw.obj)
      (aw : Fw ⟶ Hw)
      (βw : (N.obj ⋙ SheafOfModules.overFunctor (moduleRings X.toRingedSpace) W ⋙
          (Scheme.Modules.overEquiv W).functor) ≅
        formalCompletionSystem (J.comap W.ι) Fw.obj),
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap W.ι).toModulesι s).2 (kernel aw.hom)) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap W.ι).toModulesι s).2 (cokernel aw.hom))) ∧
      (Scheme.Modules.overEquiv W).functor.map
          ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
              (homOfLE h : W ⟶ U)).map b ≫
            (SheafOfModules.overFunctorMap (moduleRings X.toRingedSpace)
              (homOfLE h : W ⟶ U)).hom.app H.obj) ≫ eqToHom hHw.symm =
        lw.hom ≫ aw.hom ∧
      (∀ n : ℕᵒᵖ, (Scheme.Modules.overEquiv W).functor.map
          ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
              (homOfLE h : W ⟶ U)).map (q n) ≫
            (SheafOfModules.overFunctorMap (moduleRings X.toRingedSpace)
              (homOfLE h : W ⟶ U)).hom.app (N.obj.obj n)) =
        lw.hom ≫ formalModuleQuotientπ (J.comap W.ι) (n.unop + 1) Fw.obj ≫ βw.inv.app n) := by
  sorry

end AlgebraicGeometry
