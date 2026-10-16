/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Gluing schemes along open subschemes

A family of schemes `U i`, opens `V i j ⊆ U i` with `V i i = ⊤`, and morphisms
`t i j : V i j ⟶ V j i` with `t i i = 𝟙`, mapping `V i j ⊓ V i k` into `V j k` and satisfying
the triple cocycle condition `t j k ∘ t i j = t i k` on `V i j ⊓ V i k`, glue to a scheme.
This is the form of the gluing theorem in which the overlaps are recorded as opens of the
charts, rather than as abstract schemes with open immersions as in `Scheme.GlueData`.

## Main definitions

- `AlgebraicGeometry.Scheme.OpensGlueData`: the gluing data.
- `AlgebraicGeometry.Scheme.OpensGlueData.toGlueData`: the associated `Scheme.GlueData`.
- `AlgebraicGeometry.Scheme.OpensGlueData.glued`, `AlgebraicGeometry.Scheme.OpensGlueData.ι`:
  the glued scheme and the open immersions of the charts.
- `AlgebraicGeometry.Scheme.OpensGlueData.glueMorphisms`: morphisms out of the glued scheme
  are glued from morphisms out of the charts which are compatible on the overlaps.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Gluing data for schemes in which the overlaps are given as opens of the charts. -/
structure OpensGlueData where
  /-- The index type of the charts. -/
  J : Type u
  /-- The charts. -/
  U : J → Scheme.{u}
  /-- The overlap of the `i`-th chart with the `j`-th chart, as an open of the `i`-th chart. -/
  V : ∀ i j, (U i).Opens
  V_self : ∀ i, V i i = ⊤
  /-- The transition morphisms. -/
  t : ∀ i j, (V i j).toScheme ⟶ (V j i).toScheme
  t_self : ∀ i, t i i = 𝟙 _
  /-- `t i j` maps `V i j ⊓ V i k` into `V j k`. -/
  t_mem : ∀ i j k (x : V i j), x.1 ∈ V i k → (t i j x).1 ∈ V j k
  /-- The cocycle condition on `V i j ⊓ V i k`. -/
  cocycle : ∀ i j k,
    IsOpenImmersion.lift (V j k).ι
        ((U i).homOfLE (inf_le_left : V i j ⊓ V i k ≤ V i j) ≫ t i j ≫ (V j i).ι) (by
          rintro _ ⟨x, rfl⟩
          rw [Scheme.Opens.range_ι]
          exact t_mem i j k _ (by
            have h := Scheme.homOfLE_apply (X := U i) (inf_le_left : V i j ⊓ V i k ≤ V i j) x
            exact h ▸ x.2.2)) ≫ t j k ≫ (V k j).ι =
      (U i).homOfLE (inf_le_right : V i j ⊓ V i k ≤ V i k) ≫ t i k ≫ (V k i).ι

namespace OpensGlueData

variable (D : OpensGlueData.{u})

/-- The `Scheme.GlueData` associated to gluing data along opens. -/
noncomputable def toGlueData (D : OpensGlueData.{u}) : Scheme.GlueData.{u} where
  J := D.J
  U := D.U
  V ij := D.V ij.1 ij.2
  f i j := (D.V i j).ι
  f_id i := sorry
  f_hasPullback := inferInstance
  f_open := inferInstance
  t := D.t
  t_id := D.t_self
  t' i j k := sorry
  t_fac := sorry
  cocycle := sorry

/-- The glued scheme. -/
noncomputable def glued : Scheme.{u} := D.toGlueData.glued

/-- The open immersion of the `i`-th chart into the glued scheme. -/
noncomputable def ι (i : D.J) : D.U i ⟶ D.glued := D.toGlueData.ι i

instance (i : D.J) : IsOpenImmersion (D.ι i) := sorry

lemma glue_condition (i j : D.J) : D.t i j ≫ (D.V j i).ι ≫ D.ι j = (D.V i j).ι ≫ D.ι i := sorry

lemma iSup_opensRange_ι : ⨆ i, (D.ι i).opensRange = ⊤ := sorry

lemma preimage_opensRange_ι (i j : D.J) : D.ι i ⁻¹ᵁ (D.ι j).opensRange = D.V i j := sorry

/-- The charts as an open cover of the glued scheme. -/
noncomputable def openCover : D.glued.OpenCover := D.toGlueData.openCover

/-- Glue morphisms out of the charts that are compatible on the overlaps. -/
noncomputable def glueMorphisms {Y : Scheme.{u}} (g : ∀ i, D.U i ⟶ Y)
    (hg : ∀ i j, D.t i j ≫ (D.V j i).ι ≫ g j = (D.V i j).ι ≫ g i) : D.glued ⟶ Y := sorry

@[reassoc (attr := simp)]
lemma ι_glueMorphisms {Y : Scheme.{u}} (g : ∀ i, D.U i ⟶ Y)
    (hg : ∀ i j, D.t i j ≫ (D.V j i).ι ≫ g j = (D.V i j).ι ≫ g i) (i : D.J) :
    D.ι i ≫ D.glueMorphisms g hg = g i := sorry

lemma hom_ext {Y : Scheme.{u}} {f₁ f₂ : D.glued ⟶ Y} (h : ∀ i, D.ι i ≫ f₁ = D.ι i ≫ f₂) :
    f₁ = f₂ := sorry

end OpensGlueData

end AlgebraicGeometry.Scheme
