/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.Limit
public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FiniteApproximation

/-!
# Integral morphisms are limits of finite morphisms of finite presentation

We show that an integral morphism `f : X ⟶ S` to a quasi-compact quasi-separated scheme presents
`X` as a cofiltered limit of schemes which are finite and of finite presentation over `S`
(`AlgebraicGeometry.Scheme.Hom.exists_finiteApproximation_of_isIntegralHom`, Stacks Project
Tag 09YZ).

Start from a presentation `X = lim Tᵢ` with `Tᵢ` finite over `S`
(`AlgebraicGeometry.Scheme.Hom.nonempty_finiteApproximation_of_isIntegralHom`). Every finite
`S`-scheme `Tᵢ` is a closed subscheme of a finite `S`-scheme `Yᵢ` of finite presentation
(`AlgebraicGeometry.Scheme.Hom.nonempty_closedFPEmbedding`), and `Tᵢ` is the limit of the closed
subschemes `V(K) ⊆ Yᵢ` cut out by the subideal sheaves `K` of finite type of the ideal sheaf of
`Tᵢ` (Stacks Project Tag 09ZP); these are finite and of finite presentation over `S`. The index
category has objects the pairs `(i, K)` and morphisms the `S`-morphisms `V(K) ⟶ V(K')` under `X`.
It is cofiltered because morphisms from a limit to a scheme of finite presentation factor through
a stage, uniquely up to passing to a further stage (Stacks Project Tag 01ZC).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A closed immersion of an `S`-scheme into a finite `S`-scheme of finite presentation. -/
structure Scheme.Hom.ClosedFPEmbedding {T S : Scheme.{u}} (p : T ⟶ S) where
  /-- The ambient scheme. -/
  Y : Scheme.{u}
  /-- The closed immersion. -/
  e : T ⟶ Y
  /-- The structure morphism of the ambient scheme. -/
  q : Y ⟶ S
  [isClosedImmersion_e : IsClosedImmersion e]
  [isFinite_q : IsFinite q]
  [locallyOfFinitePresentation_q : LocallyOfFinitePresentation q]
  e_q : e ≫ q = p

attribute [instance] Scheme.Hom.ClosedFPEmbedding.isClosedImmersion_e
  Scheme.Hom.ClosedFPEmbedding.isFinite_q
  Scheme.Hom.ClosedFPEmbedding.locallyOfFinitePresentation_q

/-- **A finite scheme over a quasi-compact quasi-separated base is a closed subscheme of a finite
scheme of finite presentation.** Write it as the limit of schemes of finite presentation with
closed immersions as transition maps (Stacks Project Tag 09ZQ); some stage is finite
(`AlgebraicGeometry.Scheme.exists_isFinite_of_isLimit`). -/
theorem Scheme.Hom.nonempty_closedFPEmbedding {T S : Scheme.{u}} (p : T ⟶ S) [IsFinite p]
    [CompactSpace S] [QuasiSeparatedSpace S] : Nonempty p.ClosedFPEmbedding := by
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated p
  obtain ⟨A⟩ := p.nonempty_finitePresentationApproximation
  obtain ⟨K, hK⟩ := Scheme.exists_isFinite_of_isLimit A.D _ A.isLimit (fun K ↦ A.p.app K)
    (fun g ↦ (A.p.naturality g).trans (Category.comp_id _)) p A.w
  exact ⟨{ Y := A.D.obj K, e := A.π.app K, q := A.p.app K, e_q := A.w K }⟩

namespace Scheme.Hom.FiniteApproximation

open Scheme.IdealSheafData

variable {X S : Scheme.{u}} {f : X ⟶ S} (F : f.FiniteApproximation)
  (E : ∀ i, (F.p i).ClosedFPEmbedding)

/-- (Implementation) The index type of the finitely presented approximation: pairs of an index
`i` of `F` and a subideal sheaf of finite type of the ideal sheaf of `F.D.obj i` in its finitely
presented ambient. -/
abbrev FPIndex : Type u := Σ i : F.I, ((E i).e.ker.FGSub)

variable {F E}

/-- (Implementation) The stage `V(K)` attached to an index. -/
noncomputable abbrev fpObj (c : FPIndex F E) : Scheme.{u} := c.2.1.subscheme

/-- (Implementation) The structure morphism of a stage. -/
noncomputable abbrev fpP (c : FPIndex F E) : fpObj c ⟶ S := c.2.1.subschemeι ≫ (E c.1).q

lemma ker_le_ker (c : FPIndex F E) : c.2.1.subschemeι.ker ≤ (E c.1).e.ker := by
  rw [ker_subschemeι]; exact c.2.2.1

/-- (Implementation) The closed immersion of `F.D.obj i` into a stage. -/
noncomputable abbrev fpT (c : FPIndex F E) : F.D.obj c.1 ⟶ fpObj c :=
  IsClosedImmersion.lift c.2.1.subschemeι (E c.1).e (ker_le_ker c)

@[reassoc (attr := simp)]
lemma fpT_ι (c : FPIndex F E) : fpT c ≫ c.2.1.subschemeι = (E c.1).e :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma fpT_fpP (c : FPIndex F E) : fpT c ≫ fpP c = F.p c.1 := by
  simp [fpP, (E c.1).e_q]

/-- (Implementation) The morphism from `X` to a stage. -/
noncomputable abbrev fpH (c : FPIndex F E) : X ⟶ fpObj c := F.π.app c.1 ≫ fpT c

lemma π_app_map {i j : F.I} (g : i ⟶ j) : F.π.app i ≫ F.D.map g = F.π.app j := by
  simpa using (F.π.naturality g).symm

/-- (Implementation) The morphisms of the index category: `S`-morphisms under `X`. -/
def FPHom (c d : FPIndex F E) : Type u :=
  {g : fpObj c ⟶ fpObj d // fpH c ≫ g = fpH d ∧ g ≫ fpP d = fpP c}

noncomputable instance : SmallCategory (FPIndex F E) where
  Hom := FPHom
  id c := ⟨𝟙 _, Category.comp_id _, Category.id_comp _⟩
  comp g g' := ⟨g.1 ≫ g'.1, by rw [← Category.assoc, g.2.1, g'.2.1],
    by rw [Category.assoc, g'.2.2, g.2.2]⟩
  id_comp g := Subtype.ext (Category.id_comp _)
  comp_id g := Subtype.ext (Category.comp_id _)
  assoc g g' g'' := Subtype.ext (Category.assoc _ _ _)

lemma fpHom_comp_val {c d e : FPIndex F E} (g : c ⟶ d) (g' : d ⟶ e) :
    (g ≫ g').1 = g.1 ≫ g'.1 := rfl

lemma fpHom_id_val (c : FPIndex F E) : (𝟙 c : c ⟶ c).1 = 𝟙 _ := rfl

/-- (Implementation) The morphism `V(K') ⟶ V(K)` for `K ≤ K'`. -/
noncomputable def fpIncl (i : F.I) {K K' : (E i).e.ker.FGSub} (h : K ≤ K') :
    (⟨i, K'⟩ : FPIndex F E) ⟶ ⟨i, K⟩ :=
  ⟨inclusion h, by
    simp only [fpH, Category.assoc]
    congr 1
    rw [← cancel_mono (K.1.subschemeι), Category.assoc, inclusion_subschemeι, fpT_ι, fpT_ι],
    by simp [fpP]⟩

end Scheme.Hom.FiniteApproximation

end AlgebraicGeometry
