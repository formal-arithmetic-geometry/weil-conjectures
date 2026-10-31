/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.NormalConstantFieldBasic
/-! Marked lift for the distinguished component.
(blueprint: lem-dl-a1-normal-constant-field-component-marked-lift).
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/--
The marked geometric point determines one embedding of the finite constant field into
`D.k`, and the pullback along that embedding carries the marked point.

Proof.  Let `P, Q` be the two projections of `X = U₀ ×_{k₀} Spec D.k`.
1. `η ≫ P ≫ b.g` and `η ≫ Q` are morphisms from `Spec Ω` to spectra of fields, hence
   (`Spec` fully faithful) come from ring maps `ψ : b.L → Ω` and `χ : D.k → Ω`.  The
   pullback square of `X` and `b.factor` show that `ψ` and `χ` agree on `D.k₀`, so both
   are `D.k₀`-algebra maps for the `D.k₀`-algebra structure on `Ω` given by `χ`.
2. `b.L` is finite over `D.k₀` and `D.k` is algebraically closed, so every minimal
   polynomial of `b.L` splits in the field range `R` of `χ`; hence `ψ` factors through
   `R` (`IntermediateField.algHomEquivAlgHomOfSplits`).  Since `χ : D.k ≃ R`, this gives
   `σ : b.L →ₐ[D.k₀] D.k` with `χ ∘ σ = ψ`.
3. Put `C = U₀ ×_{b.L, σ} Spec D.k` with projections `p, s`; it is a pullback by
   construction.  `σ` is a `D.k₀`-map, so the canonical map `j : C → X` of pullbacks
   exists and satisfies `j ≫ P = p`, `j ≫ Q = s`.
4. By step 2, `(η ≫ P) ≫ b.g = (η ≫ Q) ≫ Spec σ`; the induced `ηC : Spec Ω → C`
   satisfies `ηC ≫ j = η` by the pullback extensionality of `X`.
The genericity hypothesis `hη` is not needed.

Source: Stacks Project, fields.tex, Tag 0CKN (embeddings of an algebraic extension into
an algebraically closed field), and varieties.tex, Tags 054Q and 0C3M.
(blueprint: lem-dl-a1-normal-constant-field-component-marked-lift).
-/
theorem normal_constant_field_component_marked_lift
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] [IsIntegral U₀.left] [Algebra D.k₀ U₀.left.functionField]
    (b : NormalConstantFieldBasicData D U₀) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ (D.geometricFiber U₀).left)
    (hη : ∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
      IsGenericPoint ((Scheme.SpecToEquivOfField Ω (D.geometricFiber U₀).left) η).1 Z) :
    ∃ (σ : b.L →ₐ[D.k₀] D.k) (C : Scheme.{u})
      (p : C ⟶ U₀.left) (s : C ⟶ Spec (CommRingCat.of D.k))
      (j : C ⟶ (D.geometricFiber U₀).left),
      IsPullback p s b.g (Spec.map (CommRingCat.ofHom σ.toRingHom)) ∧
      j ≫ pullback.fst U₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = p ∧
      j ≫ pullback.snd U₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = s ∧
      (∃ ηC : Spec (CommRingCat.of Ω) ⟶ C, ηC ≫ j = η) := by
  classical
  clear hη
  let f := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let X := (D.geometricFiber U₀).left
  let P : X ⟶ U₀.left := pullback.fst U₀.hom f
  let Q : X ⟶ Spec (CommRingCat.of D.k) := pullback.snd U₀.hom f
  have hbase : η ≫ P ≫ U₀.hom = η ≫ Q ≫ f := by
    dsimp [P, Q]
    exact congrArg (fun t : X ⟶ Spec (CommRingCat.of D.k₀) => η ≫ t)
      pullback.condition
  let ψ : b.L →+* Ω := (Spec.preimage (η ≫ P ≫ b.g)).hom
  let χ : D.k →+* Ω := (Spec.preimage (η ≫ Q)).hom
  let _ : Algebra D.k₀ Ω := (χ.comp (algebraMap D.k₀ D.k)).toAlgebra
  have hχmap : Spec.map (CommRingCat.ofHom χ) = η ≫ Q := by
    simp [χ]
  have hψbase : ψ.comp (algebraMap D.k₀ b.L) = algebraMap D.k₀ Ω := by
    have hspec : Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap D.k₀ b.L))) =
        Spec.map (CommRingCat.ofHom (algebraMap D.k₀ Ω)) := by
      calc
        Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap D.k₀ b.L))) =
            Spec.map (CommRingCat.ofHom ψ) ≫
              Spec.map (CommRingCat.ofHom (algebraMap D.k₀ b.L)) := by
                rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        _ = (η ≫ P ≫ b.g) ≫
              Spec.map (CommRingCat.ofHom (algebraMap D.k₀ b.L)) := by
                simp [ψ]
        _ = η ≫ P ≫ U₀.hom := by
                simp only [Category.assoc, b.factor]
        _ = η ≫ Q ≫ f := hbase
        _ = Spec.map (CommRingCat.ofHom (algebraMap D.k₀ Ω)) := by
                rw [← Category.assoc, ← hχmap]
                rw [← Spec.map_comp]
                congr 1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)
  let ψa : b.L →ₐ[D.k₀] Ω :=
    { toRingHom := ψ
      commutes' := fun a => congrArg (fun t : D.k₀ →+* Ω => t a) hψbase }
  have hχbase : χ.comp (algebraMap D.k₀ D.k) = algebraMap D.k₀ Ω := rfl
  let χa : D.k →ₐ[D.k₀] Ω :=
    { toRingHom := χ
      commutes' := fun a => congrArg (fun t : D.k₀ →+* Ω => t a) hχbase }
  have : Module.Finite D.k₀ b.L := b.finite
  have : Algebra.IsAlgebraic D.k₀ b.L := Algebra.IsAlgebraic.of_finite _ _
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let R := χa.fieldRange
  have hsplit (x : b.L) :
      (Polynomial.map (algebraMap D.k₀ R) (minpoly D.k₀ x)).Splits := by
    exact Polynomial.Splits.of_algHom (IsAlgClosed.splits _) χa.rangeRestrict
  let e : (b.L →ₐ[D.k₀] R) ≃ (b.L →ₐ[D.k₀] Ω) :=
    IntermediateField.algHomEquivAlgHomOfSplits Ω R hsplit
  let σR : b.L →ₐ[D.k₀] R := e.symm ψa
  let χR : D.k →ₐ[D.k₀] R := χa.rangeRestrict
  let eχ : D.k ≃ₐ[D.k₀] R :=
    AlgEquiv.ofBijective χR ⟨by
      intro x y h
      apply χa.injective
      exact congrArg Subtype.val h, χa.rangeRestrict_surjective⟩
  let σ : b.L →ₐ[D.k₀] D.k := eχ.symm.toAlgHom.comp σR
  have hσ : χa.comp σ = ψa := by
    ext z
    have hz := eχ.apply_symm_apply (σR z)
    have hz' := congrArg Subtype.val hz
    have hz'' := congrArg (fun q : b.L →ₐ[D.k₀] Ω => q z)
      (e.apply_symm_apply ψa)
    exact hz'.trans hz''.symm
  have hring : χ.comp σ.toRingHom = ψ := congrArg AlgHom.toRingHom hσ
  have hcomp : (η ≫ P) ≫ b.g =
      (η ≫ Q) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
    rw [Category.assoc, ← Spec.map_preimage (η ≫ P ≫ b.g), ← Category.assoc, ← hχmap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom (χ.comp σ.toRingHom))
    rw [hring]
  let q := Spec.map (CommRingCat.ofHom σ.toRingHom)
  let C : Scheme.{u} := pullback b.g q
  let p : C ⟶ U₀.left := pullback.fst b.g q
  let s : C ⟶ Spec (CommRingCat.of D.k) := pullback.snd b.g q
  have hσbase : q ≫ Spec.map
      (CommRingCat.ofHom (algebraMap D.k₀ b.L)) = f := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext z
    exact σ.commutes z
  let j : C ⟶ X := pullback.map b.g q U₀.hom f (𝟙 _) (𝟙 _)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ b.L)))
    (by simp [b.factor]) (by simp [hσbase])
  have hpb : IsPullback p s b.g q := IsPullback.of_hasPullback _ _
  have hp : j ≫ P = p := by
    simp [j, P, p]
  have hs : j ≫ Q = s := by
    simp [j, Q, s]
  let ηC : Spec (CommRingCat.of Ω) ⟶ C :=
    pullback.lift (η ≫ P) (η ≫ Q) hcomp
  have hηC : ηC ≫ j = η := by
    apply pullback.hom_ext
    · rw [Category.assoc, hp]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, hs]
      exact pullback.lift_snd _ _ _
  exact ⟨σ, C, p, s, j, hpb, hp, hs, ⟨ηC, hηC⟩⟩
end AlgebraicGeometry
