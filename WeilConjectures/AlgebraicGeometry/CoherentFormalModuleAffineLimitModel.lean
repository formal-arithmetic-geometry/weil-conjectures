/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineLimitEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineLimitComparison

/-! # The finite completed-module model of the affine section-limit functor

## References

* Stacks Project, Tags 087W and 087X
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- On an affine open, the section-limit functor is naturally the restriction functor
followed by the finite completed-module equivalence, inclusion and restriction of scalars.
(Stacks, Tags 087W and 087X). -/
theorem coherentFormalModule_affine_limit_model
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) (V : X.affineOpens)
    [IsNoetherian V.1.toScheme] :
    ∃ E : CoherentFormalModule V.1.toScheme (I.comap V.1.ι) ≌
      ObjectProperty.FullSubcategory
        (fun N : ModuleCat.{u} (AdicCompletion (I.ideal V) Γ(X, V.1)) ↦
          Module.Finite (AdicCompletion (I.ideal V) Γ(X, V.1)) N),
    Nonempty
      (((IsCoherentFormalModule I).ι ⋙
          (Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat Γ(X, V.1))).obj
            (SheafOfModules.evaluation X.ringCatSheaf (op V.1)) ⋙ lim) ≅
        coherentFormalModulesRestriction I V.1 ⋙ E.functor ⋙
          ObjectProperty.ι
            (fun N : ModuleCat.{u} (AdicCompletion (I.ideal V) Γ(X, V.1)) ↦
              Module.Finite (AdicCompletion (I.ideal V) Γ(X, V.1)) N) ⋙
          ModuleCat.restrictScalars
            (algebraMap Γ(X, V.1) (AdicCompletion (I.ideal V) Γ(X, V.1)))) := by
  classical
  obtain ⟨E, p, hlimit, hnatural⟩ := coherentFormalModule_affine_limit_equivalence X I V
  obtain ⟨d⟩ := coherentFormalModule_affine_limit_comparison X I V
  let A := Γ(X, V.1)
  let T := SheafOfModules.evaluation V.1.toScheme.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars V.1.topIso.inv.hom
  let D := (IsCoherentFormalModule (I.comap V.1.ι)).ι ⋙
    (Functor.whiskeringRight ℕᵒᵖ V.1.toScheme.Modules (ModuleCat A)).obj T
  let L := E.functor ⋙ ObjectProperty.ι
    (fun N : ModuleCat.{u} (AdicCompletion (I.ideal V) A) ↦
      Module.Finite (AdicCompletion (I.ideal V) A) N) ⋙
    ModuleCat.restrictScalars (algebraMap A (AdicCompletion (I.ideal V) A))
  let e (F : CoherentFormalModule V.1.toScheme (I.comap V.1.ι)) :
      L.obj F ≅ limit (D.obj F) :=
    (hlimit F).some.conePointUniqueUpToIso (limit.isLimit _)
  have he (F : CoherentFormalModule V.1.toScheme (I.comap V.1.ι)) (n : ℕ) :
      (e F).hom ≫ limit.π (D.obj F) (op n) = (p F).app (op n) := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ _
  let c : L ≅ D ⋙ lim := NatIso.ofComponents e (by
    intro F G f
    apply limit.hom_ext
    intro n
    have hn := hnatural F G f n.unop
    change L.map f ≫ (e G).hom ≫ limit.π (D.obj G) n =
      ((e F).hom ≫ lim.map (D.map f)) ≫ limit.π (D.obj G) n
    rw [← Category.assoc, Category.assoc, he G n.unop]
    rw [Category.assoc, lim_map, limMap_π, ← Category.assoc, he F n.unop]
    exact hn)
  refine ⟨E, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight d lim ≪≫
    (Functor.associator _ _ _) ≪≫
    (Functor.isoWhiskerLeft (coherentFormalModulesRestriction I V.1) c.symm)

end AlgebraicGeometry
