/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent

/-!
# Blueprint statements

thm-galois-lc-etale.
-/

@[expose] public section

universe v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Blueprint: thm-galois-lc-etale. -/
theorem exists_finiteEtale_flc_equivalence (Y : Scheme.{v}) :
    ∃ Φ : Y.FiniteEtale ≌ Y.FiniteLocallyConstant,
      Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
      (∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙
            (pointSmallEtale s).sheafFiber (A := Type (v + 1)) ≅
          FiniteEtale.fiber s ⋙ CategoryTheory.forget FintypeCat.{v} ⋙ uliftFunctor.{v + 1, v})) ∧
      (∀ (X : Scheme.{v}) (f : X ⟶ Y), ∃ Ψ : X.FiniteEtale ≌ X.FiniteLocallyConstant,
        Nonempty (Ψ.functor ⋙ ObjectProperty.ι _ ≅
          ObjectProperty.ι _ ⋙ X.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙ etaleSetPullback f ≅
          FiniteEtale.pullback f ⋙ Ψ.functor ⋙ ObjectProperty.ι _)) := by
  sorry

/-- Blueprint: thm-galois-lc-etale. -/
theorem finiteEtale_flc_preserves_torsors {Y : Scheme.{v}}
    (Φ : Y.FiniteEtale ≌ Y.FiniteLocallyConstant)
    (α : Φ.functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) :
    ∀ (M : Type (v + 1)) [AddCommGroup M] [Finite M] (t : EtaleTorsor M Y),
      ∃ ε : (Φ.functor.obj ⟨t.toEtale, t.isFinite⟩).obj ≅ t.toSheafTorsor.sheaf,
        ε = α.app ⟨t.toEtale, t.isFinite⟩ ∧
        ∀ (U : Y.Etale) (m : M)
          (x : (Φ.functor.obj ⟨t.toEtale, t.isFinite⟩).obj.obj.obj (op U)),
          ε.hom.hom.app (op U)
            ((Φ.functor.map (ObjectProperty.homMk
              (MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)))).hom.hom.app (op U) x) =
            ⟨(ε.hom.hom.app (op U) x).down ≫
              MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)⟩ := by
  sorry

end AlgebraicGeometry.Scheme
