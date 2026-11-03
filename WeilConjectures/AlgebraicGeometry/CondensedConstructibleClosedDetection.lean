/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.PointCount
import WeilConjectures.AlgebraicGeometry.CondensedLisseRankLoci
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Closed-point detection for constructible condensed coefficient modules

Source: current Weil blueprint, sec-deligne-laumon-general,
`sk-lem-wgen-punctual-cutoff/lem-zl-mixed-punctual-cutoff.proof.md`, paragraph 2
(blueprint: lem-zl-condensed-constructible-closed-detection).

The fibre is the underlying abelian group of terminal sections after the actual module
inverse image. Nontriviality of that group is exactly nonvanishing of the fibre as a
vector space over `PadicAlgCl ℓ`, acting by constant coefficient sections. The two projection
equations specify the geometric point associated to the residue-field embedding.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry.ProEtale

-- Match the tensor structure used by the imported coefficient and module constructions.
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  Sheaf.monoidalCategory

section Auxiliary

private theorem closedDetection_coefficient_field (ℓ : ℕ) [Fact ℓ.Prime] :
    IsField (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) := by
  have hne : (1 : MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) ≠ 0 := by
    intro h
    apply Profinite.PadicAlgCl.one_ne_zero_end_regular.{u} ℓ
    simpa only [map_one, map_zero] using congrArg Mod.regularEndRingHom h
  refine ⟨⟨1, 0, hne⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨x, rfl⟩ := Profinite.PadicAlgCl.constRingHom_surjective ℓ a
  have hx : x ≠ 0 := by
    intro h
    apply ha
    rw [h, map_zero]
  refine ⟨Profinite.PadicAlgCl.constRingHom ℓ x⁻¹, ?_⟩
  rw [← map_mul, mul_inv_cancel₀ hx, map_one]

/-- A nonempty Noetherian open over an algebraically closed field has a rational point. -/
private theorem closedDetection_open_point
    (k : Type u) [Field k] [IsAlgClosed k] (S : Scheme.{u})
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    (U : S.Opens) [IsNoetherian U.toScheme] [Nonempty U.toScheme] :
    ∃ c : Spec (.of k) ⟶ S, c ≫ aS = 𝟙 _ ∧
      (Scheme.SpecToEquivOfField k S c).1 ∈ U := by
  let f := U.ι ≫ aS
  have : LocallyOfFiniteType f := inferInstance
  obtain ⟨z, _, hz⟩ := isClosed_univ.exists_closed_singleton
    (X := U.toScheme) Set.univ_nonempty
  refine ⟨pointOfClosedPoint f z hz ≫ U.ι, ?_, ?_⟩
  · rw [Category.assoc]
    exact pointOfClosedPoint_comp f z hz
  · have hmem (t : Spec (.of k)) : (pointOfClosedPoint f z hz ≫ U.ι) t ∈ (U : Set S) := by
      erw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (pointOfClosedPoint f z hz t).property
    exact hmem _

set_option cleanup.letToHave false in
/-- The positive-rank argument, with the scheme and module kept as parameters. -/
private theorem closedDetection_lisse_point
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (hF : IsField (MonObj.Γ R.X))
    (k : Type u) [Field k] [IsAlgClosed k] (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj R.X S))
    (hL : IsLisseCoefficientModule R.X L)
    (hNZ : ¬ IsZero L) :
    ∃ c : Spec (.of k) ⟶ S, c ≫ aS = 𝟙 _ ∧
      Nontrivial (Mod.regular (condensedRingObj R.X
        (Spec (.of k))) ⟶ (CondensedRing.upperStar R.X c).obj L) := by
  classical
  obtain ⟨r, _, hf, _, hU⟩ := condensedLisse_rank_loci
    R hF S L hL
  have hpos : ∃ x : S, r x ≠ 0 := by
    by_contra! hz
    obtain ⟨U, hUeq, _, _, hzero⟩ := hU 0
    have hsurj : Surjective U.ι := ⟨by
      intro x
      have hx : x ∈ U := by
        change x ∈ (U : Set S)
        rw [hUeq]
        exact hz x
      exact ⟨⟨x, hx⟩, rfl⟩⟩
    have : IsIso U.ι := (isIso_iff_isOpenImmersion_and_surjective _).mpr
      ⟨inferInstance, hsurj⟩
    exact hNZ (IsZero.of_full_of_faithful_of_isZero
      (CondensedRing.upperStar R.X U.ι) L (hzero rfl))
  obtain ⟨x, hx⟩ := hpos
  obtain ⟨U, hUeq, _, _, _⟩ := hU (r x)
  have hxU : x ∈ U := by
    change x ∈ (U : Set S)
    rw [hUeq]
    rfl
  have : Nonempty U.toScheme := ⟨⟨x, hxU⟩⟩
  have : IsNoetherian U.toScheme :=
    (coefficientHeart_locallyClosedExtension R.X S).1
      U.toScheme U.ι inferInstance |>.1
  obtain ⟨c, hc, hcU⟩ := closedDetection_open_point k S aS U
  have hrc : r ((Scheme.SpecToEquivOfField k S c).1) = r x := by
    exact (show (Scheme.SpecToEquivOfField k S c).1 ∈
      {y | r y = r x} from hUeq ▸ hcU)
  obtain ⟨e, _⟩ := (hf k c).2
  have : Nonempty (Fin (r ((Scheme.SpecToEquivOfField k S c).1))) := by
    rw [hrc]
    exact Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hx)
  have : Nontrivial (MonObj.Γ R.X) :=
    hF.nontrivial
  exact ⟨c, hc, e.toEquiv.nontrivial⟩

/-- Pullback composition and terminal evaluation transport nontriviality of sections. -/
private theorem closedDetection_composite_sections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] (S Y : Scheme.{u}) (c : Spec (.of k) ⟶ S) (a : S ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (h : Nontrivial (Mod.regular (condensedRingObj Λ (Spec (.of k))) ⟶
      (CondensedRing.upperStar Λ c).obj ((CondensedRing.upperStar Λ a).obj M))) :
    Nontrivial (((CondensedRing.upperStar Λ (c ≫ a)).obj M).X.obj.obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := by
  have := h
  let N := (CondensedRing.upperStar Λ (c ≫ a)).obj M
  let e : N ≅ (CondensedRing.upperStar Λ c).obj ((CondensedRing.upperStar Λ a).obj M) :=
    (CondensedRing.upperStarComp Λ c a).app M
  have : Nontrivial (Mod.regular (condensedRingObj Λ (Spec (.of k))) ⟶ N) :=
    (Iso.homCongr (Iso.refl _) e).nontrivial
  exact ((Mod.regularHomAddEquiv N).trans
    (Sheaf.unitHomEvalAddEquiv (Scheme.ProEt.isTerminalMkId _) N.X)).symm.toEquiv.nontrivial

/-- Detection of monomorphisms on strata detects a nonzero restriction. -/
private theorem closedDetection_nonzero_stratum
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] (Y : Scheme.{u}) [IsNoetherian Y]
    (R : Y.FiniteLocallyClosedStratification)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) Y)) (hM : ¬ IsZero M) :
    ∃ i : Fin R.n, ¬ IsZero
      ((CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion i)).obj M) := by
  classical
  by_contra! hz
  apply hM
  have hm := (coefficientHeart_commonStratification_exactness Λ Y R).2.1
    M M (0 : M ⟶ M)
  have : Mono (0 : M ⟶ M) := hm.1.mpr fun i ↦ (hz i).mono _
  exact IsZero.of_mono_zero M M

private theorem closedDetection_bundle_functor
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (Y Z : Scheme.{u}) (b : Z ⟶ Y) :
    CondensedRing.upperStar A b =
      (let R : Profinite.CondensedRing.{u} := Mon.mk A
       CondensedRing.upperStar R.X b) := by
  rfl

private theorem closedDetection_bundle_hom
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (k : Type u) [Field k] (Y : Scheme.{u}) (b : Spec (.of k) ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y)) :
    Nontrivial (Mod.regular (condensedRingObj A (Spec (.of k))) ⟶
      (CondensedRing.upperStar A b).obj M) =
      (let R : Profinite.CondensedRing.{u} := Mon.mk A
       Nontrivial (Mod.regular (condensedRingObj R.X (Spec (.of k))) ⟶
         (CondensedRing.upperStar R.X b).obj M)) := by
  exact congrArg (fun F ↦ Nontrivial (Mod.regular (condensedRingObj A (Spec (.of k))) ⟶
    F.obj M)) (closedDetection_bundle_functor A Y (Spec (.of k)) b)

/-- Specialize only the abstract lisse module, before it is a stratum restriction. -/
private theorem closedDetection_raw_lisse_point
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (hF : IsField (MonObj.Γ A))
    (k : Type u) [Field k] [IsAlgClosed k] (S : Scheme.{u}) [IsNoetherian S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S))
    (hL : IsLisseCoefficientModule A L) (hNZ : ¬ IsZero L) :
    ∃ c : Spec (.of k) ⟶ S, c ≫ aS = 𝟙 _ ∧
      Nontrivial (Mod.regular (condensedRingObj A (Spec (.of k))) ⟶
        (CondensedRing.upperStar A c).obj L) := by
  obtain ⟨c, hc, hHom⟩ := closedDetection_lisse_point (Mon.mk A) hF k S aS L hL hNZ
  exact ⟨c, hc, Eq.mpr (closedDetection_bundle_hom A k S c L) hHom⟩

/-- A nonzero lisse restriction along an immersion gives a nonzero fibre of the original. -/
private theorem closedDetection_immersion_point
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] (hF : IsField (MonObj.Γ A))
    (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] (S : Scheme.{u}) [IsNoetherian S]
    (a : S ⟶ Y) [LocallyOfFiniteType a]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y))
    (hL : IsLisseCoefficientModule A ((CondensedRing.upperStar A a).obj M))
    (hNZ : ¬ IsZero ((CondensedRing.upperStar A a).obj M)) :
    ∃ b : Spec (.of k) ⟶ Y, b ≫ aY = 𝟙 _ ∧
      Nontrivial (((CondensedRing.upperStar A b).obj M).X.obj.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := by
  obtain ⟨c, hc, hHom⟩ := closedDetection_raw_lisse_point A hF k S (a ≫ aY)
    ((CondensedRing.upperStar A a).obj M) hL hNZ
  refine ⟨c ≫ a, ?_, closedDetection_composite_sections A k S Y c a M hHom⟩
  simpa only [Category.assoc] using hc

/-- Extract only the finite-lisse-stratification clause of the coefficient-heart theorem. -/
private theorem closedDetection_stratification (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (Y : Scheme.{u}) [IsNoetherian Y]
    (M : ConstantModelConstructible (coefficientHeartRingObj Λ) Y) :
    ∃ R : Y.FiniteLocallyClosedStratification, ∀ i : Fin R.n,
      IsLisseCoefficientModule (coefficientHeartRingObj Λ)
        ((CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion i)).obj M.obj) := by
  have hc := (coefficientHeart_closure ℓ Λ hΛ).2 Y
  exact (hc.2.2.2.2.2.2 M.obj).mp M.property

/-- A locally closed stratum inherits Noetherianness before the geometric-point argument. -/
private theorem closedDetection_stratum_point
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] (hF : IsField (MonObj.Γ A))
    (k : Type u) [Field k] [IsAlgClosed k] (Y : Scheme.{u}) [IsNoetherian Y]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    (S : Scheme.{u}) (a : S ⟶ Y) [IsImmersion a]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y))
    (hL : IsLisseCoefficientModule A ((CondensedRing.upperStar A a).obj M))
    (hNZ : ¬ IsZero ((CondensedRing.upperStar A a).obj M)) :
    ∃ b : Spec (.of k) ⟶ Y, b ≫ aY = 𝟙 _ ∧
      Nontrivial (((CondensedRing.upperStar A b).obj M).X.obj.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := by
  have : IsNoetherian S :=
    (coefficientHeart_locallyClosedExtension A Y).1 S a inferInstance |>.1
  exact closedDetection_immersion_point A hF k Y aY S a M hL hNZ

/-- Algebraicity of the closure makes the arithmetic image of a rational point closed. -/
private theorem closedDetection_arithmetic_point
    (D : WeilConjectures.FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (b : Spec (.of D.k) ⟶ pullback Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (hb : b ≫ pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = 𝟙 _) :
    ∃ (y : Y₀.left) (_hy : y ∈ closedPoints Y₀.left)
      (ι : Y₀.left.residueField y →+* D.k),
      ι.comp (Y₀.hom.residueFieldAlgebraMap y) = algebraMap D.k₀ D.k ∧
      b ≫ pullback.fst Y₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
          Spec.map (CommRingCat.ofHom ι) ≫ Y₀.left.fromSpecResidueField y := by
  let q := b ≫ pullback.fst Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let y := (Scheme.SpecToEquivOfField D.k Y₀.left q).1
  let ι := (Scheme.SpecToEquivOfField D.k Y₀.left q).2
  have hq : Spec.map ι ≫ Y₀.left.fromSpecResidueField y = q :=
    (Scheme.SpecToEquivOfField D.k Y₀.left).symm_apply_apply q
  have hbase : q ≫ Y₀.hom = Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
    dsimp only [q]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hb, Category.id_comp]
  have hι : ι.hom.comp (Y₀.hom.residueFieldAlgebraMap y) = algebraMap D.k₀ D.k := by
    have hh : CommRingCat.ofHom (ι.hom.comp (Y₀.hom.residueFieldAlgebraMap y)) =
        CommRingCat.ofHom (algebraMap D.k₀ D.k) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom (Y₀.hom.residueFieldAlgebraMap y) ≫ ι) = _
      rw [Spec.map_comp, Y₀.hom.specMap_residueFieldAlgebraMap,
        ← Category.assoc, hq, hbase]
    exact congrArg CommRingCat.Hom.hom hh
  let := (Y₀.hom.residueFieldAlgebraMap y).toAlgebra
  let j : Y₀.left.residueField y →ₐ[D.k₀] D.k :=
    { toRingHom := ι.hom
      commutes' := fun t ↦ RingHom.congr_fun hι t }
  have : Algebra.IsAlgebraic D.k₀ (Y₀.left.residueField y) :=
    Algebra.IsAlgebraic.of_injective j j.injective
  have hy : y ∈ closedPoints Y₀.left :=
    (closedPoint_iff_residueField_trdeg_zero_and_finite Y₀.hom y).1.mpr
      ((trdeg_eq_zero_iff).mpr inferInstance)
  exact ⟨y, hy, ι.hom, hι, hq.symm⟩

private theorem closedDetection_padic_functor (ℓ : ℕ) [Fact ℓ.Prime]
    (Y Z : Scheme.{u}) (b : Z ⟶ Y) :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b =
      CondensedRing.upperStar
        (coefficientHeartRingObj (Profinite.padicAlgClCondensedRing ℓ)) b := by
  rfl

private theorem closedDetection_padic_fibre (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (Y : Scheme.{u}) (b : Spec (.of k) ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj (Profinite.padicAlgClCondensedRing ℓ)) Y)) :
    Nontrivial (((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj M).X.obj.obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) =
      Nontrivial (((CondensedRing.upperStar
        (coefficientHeartRingObj (Profinite.padicAlgClCondensedRing ℓ)) b).obj M).X.obj.obj
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := by
  exact congrArg (fun F ↦ Nontrivial ((F.obj M).X.obj.obj
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))))
    (closedDetection_padic_functor ℓ Y (Spec (.of k)) b)

end Auxiliary

set_option cleanup.letToHave false in
/-- A nonzero constructible module with the finite-subextension-valued condensed
`ℚ̄_ℓ` coefficients has a nonzero actual fibre over a closed point of the finite-field model.
Source: current blueprint `lem-zl-mixed-punctual-cutoff.proof.md`, paragraph 2
(blueprint: lem-zl-condensed-constructible-closed-detection).

Proof:
1. Finite-type base change makes the geometric fibre Noetherian. Algebraic closedness
   comes from the finite-field datum. Use the lisse stratification from
   det-lem-coefficient-heart-closure and restriction detection from
   det-lem-coefficient-heart-common-stratification to obtain a nonzero lisse restriction L.
   Its stratum is Noetherian by lem-sfb-coefficient-heart-locally-closed-extension.
2. The terminal-section coefficient ring is a field by the constant-section description
   in sk-def-sfb-qlbar-condensed. Apply lem-zl-condensed-lisse-rank-loci to L. If every rank
   were zero, the rank-zero open immersion would be an isomorphism and its faithful
   pullback would force L to vanish. Thus some positive-rank open locus is nonempty.
3. This open locus is Noetherian and locally of finite type over the algebraic closure.
   It has a closed point, and Mathlib's pointOfClosedPoint supplies a rational point on it
   whose composition with its structural morphism is the identity.
4. The actual-fibre clause of lem-zl-condensed-lisse-rank-loci identifies the regular-module
   Hom space with a positive power of the coefficient field, so it is nontrivial.
   Pullback composition (sk-def-sfb-module-pushforward-pullback), the regular-module Hom
   equivalence, and terminal evaluation transfer this nontriviality to the required group.
5. Project the point to Y₀. Its residue field embeds over k₀ into k and is algebraic over
   k₀, so lem-kun-closed-point-field makes the image closed. The residue-field description
   of a field-valued point and the pullback projection equation give both required
   identities. No Weil structure or purity is used. -/
theorem condensed_constructible_closed_detection
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (M : ConstantModelConstructible (Profinite.padicAlgClRingObj ℓ)
      (D.geometricFiber Y₀).left) (hM : ¬ IsZero M.obj) :
    ∃ (y : Y₀.left) (_hy : y ∈ closedPoints Y₀.left)
      (ι : Y₀.left.residueField y →+* D.k),
      ι.comp (Y₀.hom.residueFieldAlgebraMap y) = algebraMap D.k₀ D.k ∧
      ∃ b : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left,
        b ≫ pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
          Spec.map (CommRingCat.ofHom ι) ≫ Y₀.left.fromSpecResidueField y ∧
        b ≫ (D.geometricFiber Y₀).hom = 𝟙 (Spec (.of D.k)) ∧
        Nontrivial
          (((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj M.obj).X.obj.obj
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))) := by
  classical
  have _ := hℓ
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : LocallyOfFiniteType (D.geometricFiber Y₀).hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact (D.geometricFiber Y₀).hom := inferInstanceAs
    (QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsNoetherian (D.geometricFiber Y₀).left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber Y₀).hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber Y₀).hom }
  obtain ⟨Q, hQ⟩ := closedDetection_stratification ℓ
    (Profinite.padicAlgClCondensedRing ℓ) (Or.inr rfl) (D.geometricFiber Y₀).left M
  obtain ⟨i, hi⟩ := closedDetection_nonzero_stratum
    (Profinite.padicAlgClCondensedRing ℓ) (D.geometricFiber Y₀).left Q M.obj hM
  have := Q.isImmersion i
  obtain ⟨b, hb, hN⟩ := closedDetection_stratum_point
    (coefficientHeartRingObj (Profinite.padicAlgClCondensedRing ℓ))
    (closedDetection_coefficient_field ℓ) D.k (D.geometricFiber Y₀).left
    (D.geometricFiber Y₀).hom (Q.domain i) (Q.immersion i)
    M.obj (hQ i) hi
  have hN' := Eq.mpr (closedDetection_padic_fibre ℓ D.k (D.geometricFiber Y₀).left b M.obj) hN
  obtain ⟨y, hy, ι, hι, hq⟩ := closedDetection_arithmetic_point D Y₀ b hb
  exact ⟨y, hy, ι, hι, b, hq, hb, hN'⟩

end AlgebraicGeometry.ProEtale
