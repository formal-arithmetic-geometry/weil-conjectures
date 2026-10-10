/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Diagram
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# The cone of stage schemes

The cone `ExtensionData.stageCone` with point `X` over the diagram of stage schemes, obtained by
gluing the projections from `U` and from `V` (`Stage.fromX`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
namespace Scheme.NoetherianApproximation
namespace ExtensionData

variable (E : ExtensionData.{u})
variable {E}

/-! ### The cone -/

lemma sVle (E : ExtensionData.{u}) : (⊤ : E.Wc.pt.Opens) ≤ (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.V := by
  rw [Scheme.Hom.comp_preimage, ← E.hW₀, Scheme.Opens.ι_preimage_self]

lemma sV_eq (E : ExtensionData.{u}) :
    E.sV = (E.WU.ι ≫ E.U.ι).appLE E.V ⊤ E.sVle := rfl

lemma range_WUι_comp_Uι_subset (E : ExtensionData.{u}) :
    Set.range (E.WU.ι ≫ E.U.ι) ⊆ Set.range E.V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro - ⟨x, rfl⟩
  have hx : (E.WU.ι ≫ E.U.ι) x ∈ (E.WU.ι ≫ E.U.ι).opensRange := ⟨x, rfl⟩
  rw [E.opensRange_WUι_comp_Uι] at hx
  exact hx.2

/-- (Implementation) The canonical morphism from the intersection `W = U ⊓ V` to `V`. -/
noncomputable def ζ (E : ExtensionData.{u}) : E.Wc.pt ⟶ E.V.toScheme :=
  IsOpenImmersion.lift E.V.ι (E.WU.ι ≫ E.U.ι) E.range_WUι_comp_Uι_subset

@[reassoc (attr := simp)]
lemma ζ_ι (E : ExtensionData.{u}) : E.ζ ≫ E.V.ι = E.WU.ι ≫ E.U.ι :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
lemma Wc_π_Wι (E : ExtensionData.{u}) (j : Over E.i₀) :
    E.Wc.π.app j ≫ E.Wι j = E.WU.ι ≫ E.N.π.app j.left :=
  Scheme.Hom.resLE_comp_ι _ _

lemma toSpecΓ_ζ (E : ExtensionData.{u}) :
    E.ζ ≫ E.V.toSpecΓ = E.Wc.pt.toSpecΓ ≫ Spec.map E.sV := by
  have : IsIso ((⊤ : E.Wc.pt.Opens).ι) := by
    rw [← Scheme.topIso_hom]; infer_instance
  have hres : (E.WU.ι ≫ E.U.ι).resLE E.V ⊤ E.sVle = (⊤ : E.Wc.pt.Opens).ι ≫ E.ζ := by
    rw [← cancel_mono E.V.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, E.ζ_ι]
  have h := Scheme.Opens.toSpecΓ_SpecMap_appLE (E.WU.ι ≫ E.U.ι) E.V (⊤ : E.Wc.pt.Opens) E.sVle
  rw [← E.sV_eq, hres, Scheme.Opens.toSpecΓ_top, Category.assoc, Category.assoc] at h
  exact ((cancel_epi ((⊤ : E.Wc.pt.Opens).ι)).mp h).symm

/-- (Implementation) Comparing `W` with `Spec A` via `V` and via `Wⱼ` gives the same
morphism: this is where the fiber product condition on the coefficient algebra enters. -/
@[reassoc]
lemma Stage.ζ_toSpecΓ_SpecMap_φ (T : E.Stage) :
    E.ζ ≫ E.V.toSpecΓ ≫ Spec.map T.φ = E.Wc.π.app T.j ≫ T.toSpec := by
  rw [Stage.toSpec, ← Category.assoc E.ζ, E.toSpecΓ_ζ, Category.assoc, ← Spec.map_comp,
    ← Category.assoc (E.Wc.π.app T.j), Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
  exact T.hA _ a.2

/-- (Implementation) The open cover of `X` by `U` and `V`. -/
noncomputable def cover (E : ExtensionData.{u}) : E.X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b ↦ (bif b then E.U else E.V).toScheme)
    (fun b ↦ (bif b then E.U else E.V).ι)
    (fun x ↦ by
      have hx : x ∈ E.U ⊔ E.V := by rw [E.hUV]; trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hx with h | h
      · exact ⟨true, ⟨x, h⟩, rfl⟩
      · exact ⟨false, ⟨x, h⟩, rfl⟩)
    (fun b ↦ by cases b <;> exact inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _)))

@[simp] lemma cover_f_true (E : ExtensionData.{u}) : E.cover.f true = E.U.ι := rfl

@[simp] lemma cover_f_false (E : ExtensionData.{u}) : E.cover.f false = E.V.ι := rfl

/-- (Implementation) The morphism `U ⟶ Sₜ` of the cone. -/
noncomputable def Stage.fromU (T : E.Stage) : E.U.toScheme ⟶ E.stageDiagram.obj T :=
  E.N.π.app T.j.left ≫ pushout.inl (E.Wι T.j) T.toSpec

/-- (Implementation) The morphism `V ⟶ Sₜ` of the cone. -/
noncomputable def Stage.fromV (T : E.Stage) : E.V.toScheme ⟶ E.stageDiagram.obj T :=
  E.V.toSpecΓ ≫ Spec.map T.φ ≫ pushout.inr (E.Wι T.j) T.toSpec

lemma Stage.WUι_fromU (T : E.Stage) : E.WU.ι ≫ T.fromU = E.ζ ≫ T.fromV := by
  rw [Stage.fromU, Stage.fromV, ← E.Wc_π_Wι_assoc T.j, pushout.condition,
    T.ζ_toSpecΓ_SpecMap_φ_assoc]

/-- (Implementation) The isomorphism between `U ⊓ V` and the intersection `W`. -/
noncomputable def θ (E : ExtensionData.{u}) : (E.U ⊓ E.V).toScheme ≅ E.Wc.pt :=
  IsOpenImmersion.isoOfRangeEq (E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U)) E.WU.ι (by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE,
      Scheme.Opens.opensRange_ι, ExtensionData.WU, E.hW₀]
    congr 1
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq])

@[reassoc (attr := simp)]
lemma θ_hom_WUι (E : ExtensionData.{u}) :
    E.θ.hom ≫ E.WU.ι = E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
lemma θ_hom_ζ (E : ExtensionData.{u}) :
    E.θ.hom ≫ E.ζ = E.X.homOfLE (inf_le_right : E.U ⊓ E.V ≤ E.V) := by
  rw [← cancel_mono E.V.ι, Category.assoc, E.ζ_ι, ← Category.assoc, E.θ_hom_WUι,
    Scheme.homOfLE_ι, Scheme.homOfLE_ι]

@[reassoc (attr := simp)]
lemma θ_inv_homOfLE (E : ExtensionData.{u}) :
    E.θ.inv ≫ E.X.homOfLE (inf_le_left : E.U ⊓ E.V ≤ E.U) = E.WU.ι := by
  rw [← E.θ_hom_WUι, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma θ_inv_infι (E : ExtensionData.{u}) : E.θ.inv ≫ (E.U ⊓ E.V).ι = E.WU.ι ≫ E.U.ι := by
  rw [← Scheme.homOfLE_ι E.X (inf_le_left : E.U ⊓ E.V ≤ E.U), ← Category.assoc,
    θ_inv_homOfLE]

lemma Stage.homOfLE_fromU (T : E.Stage) {W : E.X.Opens} (h₁ : W ≤ E.U) (h₂ : W ≤ E.V) :
    E.X.homOfLE h₁ ≫ T.fromU = E.X.homOfLE h₂ ≫ T.fromV := by
  rw [← E.X.homOfLE_homOfLE (le_inf h₁ h₂) (inf_le_left : E.U ⊓ E.V ≤ E.U),
    ← E.X.homOfLE_homOfLE (le_inf h₁ h₂) (inf_le_right : E.U ⊓ E.V ≤ E.V), Category.assoc,
    Category.assoc, ← E.θ_hom_WUι, ← E.θ_hom_ζ, Category.assoc, Category.assoc, T.WUι_fromU]

/-- (Implementation) The morphism from `X` to the stage scheme of a stage: it restricts to
the projection of the approximation of `U` on `U`, and to the map induced by the first
projection of the coefficient algebra on `V`. -/
noncomputable def Stage.fromX (T : E.Stage) : E.X ⟶ E.stageDiagram.obj T :=
  E.cover.glueMorphisms (fun b ↦ match b with | true => T.fromU | false => T.fromV) (by
    rintro (_ | _) (_ | _)
    · change pullback.fst E.V.ι E.V.ι ≫ T.fromV = pullback.snd E.V.ι E.V.ι ≫ T.fromV
      rw [(cancel_mono E.V.ι).mp
        (pullback.condition : pullback.fst E.V.ι E.V.ι ≫ _ = pullback.snd _ _ ≫ _)]
    · change pullback.fst E.V.ι E.U.ι ≫ T.fromV = pullback.snd E.V.ι E.U.ι ≫ T.fromU
      rw [← cancel_epi (isPullback_opens_inf E.V E.U).isoPullback.hom, ← Category.assoc,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
      exact (T.homOfLE_fromU inf_le_right inf_le_left).symm
    · change pullback.fst E.U.ι E.V.ι ≫ T.fromU = pullback.snd E.U.ι E.V.ι ≫ T.fromV
      rw [← cancel_epi (isPullback_opens_inf E.U E.V).isoPullback.hom, ← Category.assoc,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
      exact T.homOfLE_fromU inf_le_left inf_le_right
    · change pullback.fst E.U.ι E.U.ι ≫ T.fromU = pullback.snd E.U.ι E.U.ι ≫ T.fromU
      rw [(cancel_mono E.U.ι).mp
        (pullback.condition : pullback.fst E.U.ι E.U.ι ≫ _ = pullback.snd _ _ ≫ _)])

@[reassoc (attr := simp)]
lemma Stage.Uι_fromX (T : E.Stage) : E.U.ι ≫ T.fromX = T.fromU :=
  E.cover.ι_glueMorphisms _ _ true

@[reassoc (attr := simp)]
lemma Stage.Vι_fromX (T : E.Stage) : E.V.ι ≫ T.fromX = T.fromV :=
  E.cover.ι_glueMorphisms _ _ false

@[reassoc]
lemma N_π_naturality (E : ExtensionData.{u}) {i i' : E.N.I} (g : i ⟶ i') :
    E.N.π.app i ≫ E.N.D.map g = E.N.π.app i' :=
  E.cone.w g

/-- (Implementation) The cone with point `X` over the system of stage schemes. -/
noncomputable def stageCone (E : ExtensionData.{u}) : Cone E.stageDiagram where
  pt := E.X
  π :=
    { app := fun T ↦ T.fromX
      naturality := fun T T' f ↦ by
        change 𝟙 E.X ≫ T'.fromX = T.fromX ≫ E.stageDiagram.map f
        rw [Category.id_comp]
        refine E.cover.hom_ext _ _ fun b ↦ ?_
        cases b
        · simp only [cover_f_false, Stage.Vι_fromX, Stage.Vι_fromX_assoc, Stage.fromV,
            Category.assoc, inr_stageDiagram_map, Stage.Hom.SpecMap_φ_assoc]
        · simp only [cover_f_true, Stage.Uι_fromX, Stage.Uι_fromX_assoc, Stage.fromU,
            Category.assoc, inl_stageDiagram_map, E.N_π_naturality_assoc] }

@[simp] lemma stageCone_pt (E : ExtensionData.{u}) : E.stageCone.pt = E.X := rfl

@[simp] lemma stageCone_π_app (E : ExtensionData.{u}) (T : E.Stage) :
    E.stageCone.π.app T = T.fromX := rfl

end ExtensionData

end Scheme.NoetherianApproximation

end AlgebraicGeometry
