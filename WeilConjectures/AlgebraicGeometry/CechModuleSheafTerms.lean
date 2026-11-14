/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CechModuleSheafFunctor

/-! # The terms of the concrete module-sheaf Čech complex -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Over-site extension is scheme-theoretic extension from the open subscheme. -/
private noncomputable def cechIntersectionSheafIsoPushforward
    {X : Scheme.{u}} (F : X.Modules) (W : X.Opens) :
    cechIntersectionSheaf F W ≅ (Scheme.Modules.pushforward W.ι).obj
      (F.restrict W.ι) := by
  let adj := (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) W).comp
    (Scheme.Modules.overEquiv W).toAdjunction
  let adj' := adj.ofNatIsoLeft (Scheme.Modules.overFunctorEquiv W)
  let e := Adjunction.rightAdjointUniq adj' (Scheme.Modules.restrictAdjunction W.ι)
  exact (SheafOfModules.pushforward (SheafOfModules.pushforwardOver W)).mapIso
      ((Scheme.Modules.overEquiv W).unitIso.app (F.over W)) ≪≫
    e.app ((Scheme.Modules.overEquiv W).functor.obj (F.over W)) ≪≫
    (Scheme.Modules.pushforward W.ι).mapIso ((Scheme.Modules.overFunctorEquiv W).app F)

/-- Finite products of opens are their infima. -/
private noncomputable def cechOpensProductIsoInf
    {X : Scheme.{u}} {α : Type} [Finite α] (V : α → X.Opens) :
    (∏ᶜ V) ≅ ⨅ a, V a where
  hom := homOfLE (le_iInf fun a => leOfHom (Pi.π V a))
  inv := Pi.lift fun a => homOfLE (iInf_le V a)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Each concrete Čech term is the product of extensions from the corresponding
finite intersections. -/
theorem cechModuleSheafComplex_term_iso
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules) (p : ℕ) :
    Nonempty ((cechModuleSheafComplex U F).X p ≅ ∏ᶜ fun y : Fin (p + 1) → ι =>
      (Scheme.Modules.pushforward (⨅ l, U (y l)).ι).obj
        (F.restrict (⨅ l, U (y l)).ι)) := by
  refine ⟨Pi.mapIso fun y : Fin (p + 1) → ι => ?_⟩
  exact (cechModuleSheafFunctor F).mapIso
      (cechOpensProductIsoInf (fun l => U (y l))).symm.op ≪≫
    cechIntersectionSheafIsoPushforward F (⨅ l, U (y l))

end AlgebraicGeometry
