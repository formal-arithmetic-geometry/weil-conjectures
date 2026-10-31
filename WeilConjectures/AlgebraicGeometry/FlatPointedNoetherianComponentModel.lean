/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.SectionComponentPullback
import WeilConjectures.TraceFormula.GeometricReducedFibreLocusBaseChange

/-!
# A flat pointed Noetherian model preserving section components

Source: Stacks Project, More on Morphisms, Tag 055Q,
`lemma-connected-along-section-open-neighbourhood`, first paragraph.
(blueprint: lem-trf-flat-pointed-noetherian-component-model)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem exists_flat_affine_stage {S : Scheme.{u}} [IsAffine S]
    {i : (Scheme.NoetherianApproximation.ofIsAffine S).I} {Y X : Scheme.{u}}
    (p : Y ⟶ (Scheme.NoetherianApproximation.ofIsAffine S).D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (f : X ⟶ S) [Flat f] (a : X ⟶ Y)
    (H : IsPullback a f p ((Scheme.NoetherianApproximation.ofIsAffine S).π.app i)) :
    ∃ j : Over i, Flat (pullback.snd p
      ((Scheme.NoetherianApproximation.ofIsAffine S).D.map j.hom)) := by
  classical
  let N := Scheme.NoetherianApproximation.ofIsAffine S
  let I := {A : Subalgebra ℤ Γ(S, ⊤) // A.FG}
  have : IsDirected I (· ≤ ·) := ⟨fun A B ↦
    ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
      show A.1 ≤ A.1 ⊔ B.1 from le_sup_left,
      show B.1 ≤ A.1 ⊔ B.1 from le_sup_right⟩⟩
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  let φ : Over.mk p ⟶ Over.mk (𝟙 (N.D.obj i)) := Over.homMk p
  have hflat : Flat (pullback.snd p (N.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have hφ : Flat (((Over.pullback (N.π.app i)).map φ).left) := by
    apply (MorphismProperty.cancel_right_of_respectsIso @Flat _
      (pullback.snd (𝟙 (N.D.obj i)) (N.π.app i))).mp
    have hw := Over.w ((Over.pullback (N.π.app i)).map φ)
    change ((Over.pullback (N.π.app i)).map φ).left ≫
      pullback.snd (𝟙 (N.D.obj i)) (N.π.app i) = pullback.snd p (N.π.app i) at hw
    rwa [hw]
  have : CompactSpace (Over.mk p).left := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace (Over.mk p).left := inferInstanceAs (QuasiSeparatedSpace Y)
  have : CompactSpace (Over.mk (𝟙 (N.D.obj i))).left :=
    inferInstanceAs (CompactSpace (N.D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (N.D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (N.D.obj i))
  have : LocallyOfFinitePresentation φ.left := inferInstanceAs (LocallyOfFinitePresentation p)
  obtain ⟨j, hij, hj⟩ := exists_flat_stage_of_limit (I := I) N.D (Cone.mk S N.π)
    N.isLimit i.unop (Over.mk p) (Over.mk (𝟙 (N.D.obj i))) φ hφ
  let v : Opposite.op j ⟶ i := (homOfLE hij).op
  refine ⟨Over.mk v, ?_⟩
  have : Flat (((Over.pullback (N.D.map v)).map φ).left) := hj
  have hw := Over.w ((Over.pullback (N.D.map v)).map φ)
  change ((Over.pullback (N.D.map v)).map φ).left ≫
    pullback.snd (𝟙 (N.D.obj i)) (N.D.map v) = pullback.snd p (N.D.map v) at hw
  have hh : Flat (((Over.pullback (N.D.map v)).map φ).left ≫
      pullback.snd (𝟙 (N.D.obj i)) (N.D.map v)) := inferInstance
  rw [hw] at hh
  exact hh

private theorem exists_flat_noetherian_model_with_section {X S : Scheme.{u}}
    [IsAffine S] (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    ∃ (X₀ S₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀) (σ₀ : S₀ ⟶ X₀)
      (a : X ⟶ X₀) (b : S ⟶ S₀),
      IsNoetherian X₀ ∧ IsNoetherian S₀ ∧ IsAffine S₀ ∧ Flat f₀ ∧
      LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
      σ₀ ≫ f₀ = 𝟙 S₀ ∧ IsPullback a f f₀ b ∧ σ ≫ a = b ≫ σ₀ := by
  classical
  let N := Scheme.NoetherianApproximation.ofIsAffine S
  obtain ⟨i₁, Y₁, q₁, hqfp, hqqc, hqqs, a₁, H₁⟩ :=
    Scheme.exists_isPullback_of_finitePresentation (D := N.D) N.isLimit f
  let : LocallyOfFinitePresentation q₁ := hqfp
  let : QuasiCompact q₁ := hqqc
  let : QuasiSeparated q₁ := hqqs
  obtain ⟨j₁, hj₁⟩ := exists_flat_affine_stage q₁ f a₁ H₁
  let i := j₁.left
  let Y := Limits.pullback q₁ (N.D.map j₁.hom)
  let q : Y ⟶ N.D.obj i := Limits.pullback.snd _ _
  let : Flat q := hj₁
  let a : X ⟶ Y := Limits.pullback.lift a₁ (f ≫ N.π.app i) (by
    rw [H₁.w, Category.assoc, (Limits.Cone.mk S N.π).w j₁.hom])
  have H : IsPullback a f q (N.π.app i) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback q₁ (N.D.map j₁.hom))
    · simpa only [a, Limits.pullback.lift_fst, i, (Limits.Cone.mk S N.π).w j₁.hom] using H₁
    · simp [a]
  let D := Over.forget i ⋙ N.D
  have : ∀ {j k : Over i} (v : j ⟶ k), IsAffineHom (D.map v) := fun v ↦
    inferInstanceAs (IsAffineHom (N.D.map v.left))
  have : ∀ j : Over i, CompactSpace (D.obj j) := fun j ↦
    inferInstanceAs (CompactSpace (N.D.obj j.left))
  have : ∀ j : Over i, QuasiSeparatedSpace (D.obj j) := fun j ↦
    inferInstanceAs (QuasiSeparatedSpace (N.D.obj j.left))
  let c := (Limits.Cone.mk S N.π).whisker (Over.forget i)
  let t : D ⟶ (Functor.const (Over i)).obj (N.D.obj i) :=
    { app := fun j ↦ N.D.map j.hom
      naturality := fun j k v ↦ by
        change N.D.map v.left ≫ N.D.map k.hom = N.D.map j.hom ≫ 𝟙 _
        rw [← N.D.map_comp, Over.w v, Category.comp_id] }
  obtain ⟨j, τ, hτ, hτq⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t q c
      ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (Limits.Cone.mk S N.π)).symm
        N.isLimit) (σ ≫ a) (by
        ext j
        change N.π.app j.left ≫ N.D.map j.hom = (σ ≫ a) ≫ q
        rw [Category.assoc, H.w, ← Category.assoc, hσ, Category.id_comp]
        exact (Limits.Cone.mk S N.π).w j.hom)
  change N.π.app j.left ≫ τ = σ ≫ a at hτ
  change τ ≫ q = N.D.map j.hom at hτq
  let X₀ := Limits.pullback q (N.D.map j.hom)
  let f₀ : X₀ ⟶ N.D.obj j.left := Limits.pullback.snd _ _
  let σ₀ : N.D.obj j.left ⟶ X₀ := Limits.pullback.lift τ (𝟙 _) (by simp [hτq])
  let a₀ : X ⟶ X₀ := Limits.pullback.lift a (f ≫ N.π.app j.left) (by
    rw [H.w, Category.assoc, (Limits.Cone.mk S N.π).w j.hom])
  have Ha : IsPullback a₀ f f₀ (N.π.app j.left) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback q (N.D.map j.hom))
    · simpa [a₀, (Limits.Cone.mk S N.π).w j.hom] using H
    · simp [a₀]
  have hsection : σ ≫ a₀ = N.π.app j.left ≫ σ₀ := by
    apply Limits.pullback.hom_ext
    · simpa [a₀, σ₀, Category.assoc] using hτ.symm
    · simp only [a₀, σ₀, Category.assoc, Limits.pullback.lift_snd, Category.comp_id]
      rw [← Category.assoc, hσ, Category.id_comp]
  have : Flat f₀ := inferInstanceAs
    (Flat (Limits.pullback.snd q (N.D.map j.hom)))
  have : LocallyOfFinitePresentation f₀ := inferInstanceAs
    (LocallyOfFinitePresentation (Limits.pullback.snd q (N.D.map j.hom)))
  have : QuasiCompact f₀ := inferInstanceAs (QuasiCompact (Limits.pullback.snd q (N.D.map j.hom)))
  have : QuasiSeparated f₀ := inferInstanceAs
    (QuasiSeparated (Limits.pullback.snd q (N.D.map j.hom)))
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian f₀
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have : IsAffine (N.D.obj j.left) := inferInstanceAs (IsAffine (Spec (.of j.left.unop.1)))
  exact ⟨X₀, N.D.obj j.left, f₀, σ₀, a₀, N.π.app j.left, ⟨⟩,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    by simp [σ₀, f₀], Ha, hsection⟩

private theorem isReduced_geometric_fibre {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (hred : GeometricallyReduced (f.fiberToSpecResidueField s))
    (Ω : Type u) [Field Ω] [Algebra (S.residueField s) Ω] :
    IsReduced (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField s) Ω)) ≫ S.fromSpecResidueField s)) := by
  let k := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω))
  have : IsReduced (pullback (pullback.snd f (S.fromSpecResidueField s)) k) :=
    hred.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
  exact isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso f
    (S.fromSpecResidueField s) k).inv

/-- A flat finitely presented family with section has an affine local Noetherian model
retaining the reduced geometric fibre at the distinguished point and the component locus.
The point of the model base is `b ⟨g q, hq⟩`: cartesianness identifies this with
`g₀ (ρ qV)` for the unique point `qV` of the open base change above `q`.

Source: Stacks Project, Tag 055Q, first paragraph of the proof of
`lemma-connected-along-section-open-neighbourhood`.

Proof:
1. Choose an affine open `V` containing `g q` by `lem-weil-pbc-affine-opens-basis`.
   Base change preserves flatness and finite presentation by
   `lem-weil-pbc-flat-morphism-base-change` and `lem-weil-pbc-qcqs-morphism-permanence`.
   The fibre-product lift `sectionBaseChange` gives the induced section.
2. Write `V` as the limit of spectra of its finitely generated integer subalgebras by
   `lemma-nagata-noetherian-inverse-system-affine`. They form a nonempty directed set:
   the image of the integers is a stage and adjoining two finite generating sets gives
   an upper bound. Each stage is Noetherian by `lem-weil-pbc-finite-type-over-noetherian`
   and qcqs by `lem-weil-pbc-qcqs-over-affine`.
3. Apply `thm-pd-spreading-out` to descend the finitely presented family. Later models
   remain finitely presented and qcqs by `lem-weil-pbc-qcqs-morphism-permanence`.
   Every upper tail has the same limit: extend a cone using common upper bounds;
   directedness proves that the extension is independent of those bounds.
4. Apply the morphism clause of `thm-pd-spreading-out` in the category over the base
   to descend the section. Its over-base condition is the section identity, and its
   recovered base change gives compatibility with the original section.
5. Apply `lem-weil-pbc-descend-flat-finite-presentation` to advance to a flat stage.
   Pull back the descended section to this stage. Finite presentation is retained;
   `def-sbc-locally-finite-presentation` and `lem-weil-pbc-lft-pointwise-criterion`
   imply local finite type, so `lem-weil-pbc-finite-type-over-noetherian` makes the
   source Noetherian too. Pullback pasting retains the cartesian square: the maps
   `((p,u),v) ↦ (p,v)` and `(p,v) ↦ ((p,b v),v)` are inverse by their projections.
   The same projection identities give compatibility of sections and identify the
   image of the distinguished base point with `b ⟨g q, hq⟩`.
6. The assumed geometrically reduced fibre over `g q` has reduced algebraic-closure
   base change. Apply `lem-trf-geometric-reduced-fibre-locus-base-change` to the model
   square. Membership in the inverse-image locus gives reducedness of the model's
   geometric fibre at `b ⟨g q, hq⟩`, with no condition on other fibres.
7. Both families are locally of finite type by the same pointwise criterion. Apply
   `lem-sbc-section-component-cartesian` to the model square and to restriction along
   `V.ι`. The two identities give precisely the displayed equality of loci.

(blueprint: lem-trf-flat-pointed-noetherian-component-model) -/
theorem exists_flat_pointed_noetherian_component_model
    {P T : Scheme.{u}} (g : P ⟶ T) [Flat g] [LocallyOfFinitePresentation g]
    [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T)
    (q : P) (hred : GeometricallyReduced (g.fiberToSpecResidueField (g q))) :
    ∃ (V : T.Opens) (hq : g q ∈ V) (P₀ T₀ : Scheme.{u}) (g₀ : P₀ ⟶ T₀)
      (σ₀ : T₀ ⟶ P₀) (b : V.toScheme ⟶ T₀) (ρ : pullback g V.ι ⟶ P₀),
      IsAffineOpen V ∧ IsNoetherian P₀ ∧ IsNoetherian T₀ ∧ IsAffine T₀ ∧
      Flat g₀ ∧ LocallyOfFinitePresentation g₀ ∧ QuasiCompact g₀ ∧ QuasiSeparated g₀ ∧
      IsPullback ρ (pullback.snd g V.ι) g₀ b ∧ σ₀ ≫ g₀ = 𝟙 T₀ ∧
      sectionBaseChange g σ hσ (Over.mk V.ι) ≫ ρ = b ≫ σ₀ ∧
      IsReduced (pullback g₀
        (Spec.map (CommRingCat.ofHom
          (algebraMap (T₀.residueField (b ⟨g q, hq⟩))
            (AlgebraicClosure (T₀.residueField (b ⟨g q, hq⟩))))) ≫
          T₀.fromSpecResidueField (b ⟨g q, hq⟩))) ∧
      ρ ⁻¹' {p : P₀ | p ∈ connectedComponentIn (g₀ ⁻¹' {g₀ p}) (σ₀ (g₀ p))} =
        (pullback.fst g V.ι) ⁻¹'
          {p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))} := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hq, _⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g q)) isOpen_univ
  let V : T.Opens := V
  let : IsAffine V.toScheme := hV
  let f := pullback.snd g V.ι
  let τ := sectionBaseChange g σ hσ (Over.mk V.ι)
  have hτ : τ ≫ f = 𝟙 _ := sectionBaseChange_snd g σ hσ (Over.mk V.ι)
  obtain ⟨P₀, T₀, g₀, σ₀, ρ, b, hP₀, hT₀, haff, hg₀, hfp, hqc, hqs,
    hσ₀, H, hcompat⟩ := exists_flat_noetherian_model_with_section f τ hτ
  have := hP₀
  have := hT₀
  have := haff
  have := hg₀
  have := hfp
  have := hqc
  have := hqs
  refine ⟨V, hq, P₀, T₀, g₀, σ₀, b, ρ, hV, hP₀, hT₀, haff, hg₀, hfp,
    hqc, hqs, H, hσ₀, hcompat, ?_, ?_⟩
  · let v : V.toScheme := ⟨g q, hq⟩
    have hredV : GeometricallyReduced (f.fiberToSpecResidueField v) :=
      MorphismProperty.of_isPullback
        (isPullback_fiberToSpecResidueField_of_isPullback
          (IsPullback.of_hasPullback g V.ι) v) hred
    have hVred : v ∈ {t : V.toScheme |
        ∀ (Ω : Type u) [Field Ω] [Algebra (V.toScheme.residueField t) Ω]
          [IsAlgClosure (V.toScheme.residueField t) Ω],
          IsReduced (pullback (pullback.snd g₀ b)
            (Spec.map (CommRingCat.ofHom (algebraMap (V.toScheme.residueField t) Ω)) ≫
              V.toScheme.fromSpecResidueField t))} := by
      intro Ω _ _ _
      let η := Spec.map (CommRingCat.ofHom (algebraMap (V.toScheme.residueField v) Ω)) ≫
        V.toScheme.fromSpecResidueField v
      have : IsReduced (pullback f η) := isReduced_geometric_fibre f v hredV Ω
      let e := pullback.map f η (pullback.snd g₀ b) η H.isoPullback.hom (𝟙 _) (𝟙 _)
        (by simp) (by simp)
      exact isReduced_of_isOpenImmersion (inv e)
    have hmodel := (Set.ext_iff.mp (geometricReduced_fibre_locus_baseChange g₀ b) v).mp hVred
    exact hmodel (AlgebraicClosure (T₀.residueField (b v)))
  · rw [section_component_preimage_of_isPullback g₀ σ₀ hσ₀ ρ f b H τ hτ hcompat,
      section_component_preimage_of_isPullback g σ hσ (pullback.fst g V.ι) f V.ι
        (IsPullback.of_hasPullback g V.ι) τ hτ (pullback.lift_fst ..)]

end AlgebraicGeometry
