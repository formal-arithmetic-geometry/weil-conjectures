/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Transport of coherent formal modules along a scheme isomorphism

Source: Stacks Project, Section 0EHN, and the affine identification in Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme isomorphism transports the category of coherent formal modules
(Stacks, Tags 0EHN and 087W). -/
theorem coherentFormalModules_iso_equivalence {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (I : X.IdealSheafData) (e : X ≅ Y) :
    Nonempty (CoherentFormalModule X I ≌ CoherentFormalModule Y (I.comap e.inv)) := by
  have hI : (I.comap e.inv).comap e.hom = I := by
    rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
  obtain ⟨P, _, hP, _, _⟩ := (exists_formalSystemsPullback e.inv I).1
  have hQ := (exists_formalSystemsPullback e.hom (I.comap e.inv)).1
  rw [hI] at hQ
  obtain ⟨Q, _, hQ, _, _⟩ := hQ
  obtain ⟨cX⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.hom e.inv
  obtain ⟨cY⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.inv e.hom
  rw [e.hom_inv_id] at cX
  rw [e.inv_hom_id] at cY
  obtain ⟨iX⟩ := Scheme.Modules.nonempty_tensorPullbackId X
  obtain ⟨iY⟩ := Scheme.Modules.nonempty_tensorPullbackId Y
  let aX := cX.symm ≪≫ iX
  let aY := cY.symm ≪≫ iY
  let WX := Functor.whiskeringRight ℕᵒᵖ X.Modules X.Modules
  let WY := Functor.whiskeringRight ℕᵒᵖ Y.Modules Y.Modules
  let IX := ObjectProperty.ι (IsCoherentFormalModule I)
  let IY := ObjectProperty.ι (IsCoherentFormalModule (I.comap e.inv))
  have hPX : (P ⋙ Q) ⋙ IX = IX ⋙ WX.obj
      (Scheme.Modules.tensorPullback e.inv ⋙ Scheme.Modules.tensorPullback e.hom) := by
    rw [Functor.assoc, hQ, ← Functor.assoc, hP]
    rfl
  have hQY : (Q ⋙ P) ⋙ IY = IY ⋙ WY.obj
      (Scheme.Modules.tensorPullback e.hom ⋙ Scheme.Modules.tensorPullback e.inv) := by
    rw [Functor.assoc, hP, ← Functor.assoc, hQ]
    rfl
  -- Both composites already lie in the full subcategories; lift the ambient isomorphisms.
  let u : (P ⋙ Q) ⋙ IX ≅ (𝟭 _) ⋙ IX :=
    eqToIso hPX ≪≫ Functor.isoWhiskerLeft IX (WX.mapIso aX) ≪≫
      Functor.rightUnitor IX ≪≫ (Functor.leftUnitor IX).symm
  let v : (Q ⋙ P) ⋙ IY ≅ (𝟭 _) ⋙ IY :=
    eqToIso hQY ≪≫ Functor.isoWhiskerLeft IY (WY.mapIso aY) ≪≫
      Functor.rightUnitor IY ≪≫ (Functor.leftUnitor IY).symm
  let T := CategoryTheory.Equivalence.mk P Q
    (Functor.fullyFaithfulCancelRight IX u).symm
    (Functor.fullyFaithfulCancelRight IY v)
  exact ⟨T⟩

end AlgebraicGeometry
