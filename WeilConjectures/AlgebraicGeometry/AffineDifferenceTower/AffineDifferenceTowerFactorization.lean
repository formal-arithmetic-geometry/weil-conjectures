/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPastingData
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Affine difference charts in a Cartesian tower

Source: blueprint main-20261015, thm-pur-composition-coherence, proof Step 1
(blueprint: lem-pur-affine-difference-tower-factorization).

The coordinate type is the established `ULift (Fin (d+e))`, with the x block first.
The graph and difference maps are reused from the existing diagonal-pasting module.
We use the explicit model `R = 𝔸^d_Q`; the theorem asserts the universal property
identifying this model with the displayed pullback over affine e-space.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.AffineDifferenceTower

open WeilConjectures.PurityFiniteSetting.DiagonalPasting

/-- The coordinate indices of a finite affine space. Source: blueprint composition proof,
Step 1 (blueprint: lem-pur-affine-difference-tower-factorization). -/
abbrev Coords (r : ℕ) : Type u := ULift.{u} (Fin r)

variable {U V T : Scheme.{u}} {d e : ℕ}

/-- The intermediate fibred product Q. Source: blueprint composition proof, Step 1
(blueprint: lem-pur-affine-difference-tower-factorization). -/
abbrev Q (f : U ⟶ V) (g : V ⟶ T) : Scheme.{u} := pullback (f ≫ g) g

/-- The twofold product W over T. Source: blueprint composition proof, Step 1
(blueprint: lem-pur-affine-difference-tower-factorization). -/
abbrev W (f : U ⟶ V) (g : V ⟶ T) : Scheme.{u} := pullback (f ≫ g) (f ≫ g)

/-- The untranslated base change of the g chart. Source: blueprint composition proof, Step 1
(blueprint: lem-pur-affine-difference-tower-factorization). -/
noncomputable def Graw (f : U ⟶ V) (g : V ⟶ T)
    (cg : V ⟶ AffineSpace (Coords e) T) : Q f g ⟶ AffineSpace (Coords e) U :=
  AffineSpace.homOfVector (pullback.fst _ _)
    (fun i ↦ (pullback.snd (f ≫ g) g ≫ cg).appTop (AffineSpace.coord T i))

/-- The explicit polynomial model of R. Source: blueprint composition proof, Step 1
(blueprint: lem-pur-affine-difference-tower-factorization). -/
abbrev R (d : ℕ) (f : U ⟶ V) (g : V ⟶ T) : Scheme.{u} :=
  AffineSpace (Coords d) (Q f g)

/-- The untranslated base change of the f chart. Source: blueprint composition proof, Step 1
(blueprint: lem-pur-affine-difference-tower-factorization). -/
noncomputable def Hraw (f : U ⟶ V) (g : V ⟶ T)
    (cf : U ⟶ AffineSpace (Coords d) V) : W f g ⟶ R d f g :=
  AffineSpace.homOfVector (a f g)
    (fun i ↦ (pullback.snd (f ≫ g) (f ≫ g) ≫ cf).appTop (AffineSpace.coord V i))

/-- The translated f chart H, with coordinates x(u')-x(u). Source: blueprint composition
proof, Step 1 (blueprint: lem-pur-affine-difference-tower-factorization). -/
noncomputable def H (f : U ⟶ V) (g : V ⟶ T)
    (cf : U ⟶ AffineSpace (Coords d) V) : W f g ⟶ R d f g :=
  AffineSpace.homOfVector (a f g) (fun i ↦
    (pullback.snd (f ≫ g) (f ≫ g) ≫ cf).appTop (AffineSpace.coord V i) -
    (pullback.fst (f ≫ g) (f ≫ g) ≫ cf).appTop (AffineSpace.coord V i))

/-- J inserts the last block G and preserves the first block. Source: blueprint composition
proof, Step 1 (blueprint: lem-pur-affine-difference-tower-factorization). -/
noncomputable def J (d : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    (cg : V ⟶ AffineSpace (Coords e) T) :
    R d f g ⟶ A (d + e) U :=
  AffineSpace.homOfVector (R d f g ↘ Q f g ≫ pullback.fst _ _)
    (fun i ↦ Fin.addCases
      (fun j ↦ AffineSpace.coord (Q f g) (ULift.up j))
      (fun j ↦ (R d f g ↘ Q f g ≫ differenceSecond e f g cg).appTop
        (AffineSpace.coord U (ULift.up j))) i.down)

/-- The map 𝔸^d_U to R induced by s, retaining its coordinates. Source: blueprint composition
proof, Step 1 (blueprint: lem-pur-affine-difference-tower-factorization). -/
noncomputable def includeR (d : ℕ) (f : U ⟶ V) (g : V ⟶ T) :
    AffineSpace (Coords d) U ⟶ R d f g := AffineSpace.map (Coords d) (s f g)

private lemma appTop_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : Γ(Z, ⊤)) : f.appTop (g.appTop r) = (f ≫ g).appTop r := rfl

private lemma comp_translation_coord {n : Type u} {X B : Scheme.{u}}
    (f : X ⟶ AffineSpace n B) (v : n → Γ(B, ⊤)) (i : n) :
    (f ≫ AffineSpace.translation v).appTop (AffineSpace.coord B i) =
      f.appTop (AffineSpace.coord B i) + (f ≫ (AffineSpace n B ↘ B)).appTop (v i) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.translation_appTop_coord, map_add]
  rfl

private lemma translation_isIso {n : Type u} {B : Scheme.{u}} (v : n → Γ(B, ⊤)) :
    IsIso (AffineSpace.translation v) := by
  let E : AffineSpace n B ≅ AffineSpace n B :=
    { hom := AffineSpace.translation v
      inv := AffineSpace.translation (-v)
      hom_inv_id := by rw [← AffineSpace.translation_add, add_neg_cancel,
        AffineSpace.translation_zero]
      inv_hom_id := by rw [← AffineSpace.translation_add, neg_add_cancel,
        AffineSpace.translation_zero] }
  exact E.isIso_hom

private lemma chart_pullback {n : Type u} {L B X S : Scheme.{u}}
    (p : L ⟶ B) (r : L ⟶ X) (b : B ⟶ S) (f : X ⟶ S)
    (hp : IsPullback p r b f) (c : X ⟶ AffineSpace n S)
    (hc : c ≫ (AffineSpace n S ↘ S) = f) :
    IsPullback (AffineSpace.homOfVector p
      (fun i ↦ (r ≫ c).appTop (AffineSpace.coord S i))) r
      (AffineSpace.map n b) c := by
  let h := AffineSpace.homOfVector p
    (fun i ↦ (r ≫ c).appTop (AffineSpace.coord S i))
  have hcomm : h ≫ AffineSpace.map n b = r ≫ c := by
    apply AffineSpace.hom_ext
    · dsimp only [h]
      rw [Category.assoc, AffineSpace.map_over, AffineSpace.homOfVector_over_assoc,
        Category.assoc, hc]
      exact hp.w
    · intro i
      simp [h]
  have hout : IsPullback (h ≫ (AffineSpace n B ↘ B)) r b
      (c ≫ (AffineSpace n S ↘ S)) := by
    simpa only [h, AffineSpace.homOfVector_over, hc] using hp
  exact hout.of_right hcomm (AffineSpace.isPullback_map (n := n) b).flip

private lemma affine_product (d e : ℕ) (B : Scheme.{u}) :
    IsPullback (first d e B) (q d e B) (A d B ↘ B) (A e B ↘ B) := by
  apply IsPullback.mk'
  · simp [first, q]
  · intro L φ ψ h₁ h₂
    apply AffineSpace.hom_ext
    · simpa [first] using congrArg (fun h ↦ h ≫ (A d B ↘ B)) h₁
    · rintro ⟨i⟩
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simpa [first, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
          congrArg (fun h ↦ h.appTop (AffineSpace.coord B (ULift.up j))) h₁
      · simpa [q, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
          congrArg (fun h ↦ h.appTop (AffineSpace.coord B (ULift.up j))) h₂
  · intro L α β hαβ
    refine ⟨AffineSpace.homOfVector (α ≫ (A d B ↘ B)) (fun i ↦ Fin.addCases
      (fun j ↦ α.appTop (AffineSpace.coord B (ULift.up j)))
      (fun j ↦ β.appTop (AffineSpace.coord B (ULift.up j))) i.down), ?_, ?_⟩
    · apply AffineSpace.hom_ext
      · simp [first]
      · rintro ⟨j⟩
        simp [first]
    · apply AffineSpace.hom_ext
      · simpa [q] using hαβ
      · rintro ⟨j⟩
        simp [q]

private lemma differenceFirst_diagonal {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    (c : X ⟶ A d Y) :
    pullback.diagonal f ≫ differenceFirst d f c = AffineSpace.zeroSection (Coords d) X := by
  apply AffineSpace.hom_ext
  · simp [differenceFirst]
  · intro i
    simp only [differenceFirst, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord, map_sub]
    simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Category.assoc, pullback.diagonal_snd, pullback.diagonal_fst, Category.id_comp,
      sub_self, AffineSpace.zeroSection_appTop_coord]

private lemma differenceFirst_etale {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    (c : X ⟶ A d Y) [Etale c] (hc : c ≫ (A d Y ↘ Y) = f) :
    Etale (differenceFirst d f c) := by
  let raw := AffineSpace.homOfVector (pullback.fst f f)
    (fun i ↦ (pullback.snd f f ≫ c).appTop (AffineSpace.coord Y i))
  have hp : IsPullback raw (pullback.snd f f) (AffineSpace.map (Coords d) f) c :=
    chart_pullback _ _ _ _ (IsPullback.of_hasPullback f f) c hc
  have : Etale raw := MorphismProperty.of_isPullback hp.flip inferInstance
  let v : Coords d → Γ(X, ⊤) := fun i ↦ -c.appTop (AffineSpace.coord Y i)
  have : IsIso (AffineSpace.translation v) := translation_isIso v
  have heq : differenceFirst d f c = raw ≫ AffineSpace.translation v := by
    apply AffineSpace.hom_ext
    · simp [raw, differenceFirst]
    · intro i
      rw [comp_translation_coord]
      simp only [differenceFirst, raw, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_over, v, map_neg, sub_eq_add_neg]
      simp only [appTop_comp_apply]
  rw [heq]
  infer_instance

/-- All assertions of the affine difference tower, including its two restriction squares.
Source: blueprint main-20261015, thm-pur-composition-coherence, proof Step 1
(blueprint: lem-pur-affine-difference-tower-factorization).

Proof plan (the node's steps 1-9 and 11):
1. Polynomial substitutions Z_i↦Z_i±c_i are inverse. Split the polynomial variables
   into ordered x and y blocks (def-sbc-affine-space, def-pc-fibre-product).
2. This identifies the pullback defining R with affine d-space over Q. Products of
   affine spectra are affine (lem-weil-pbc-fibre-product-affine-spectra).
3. Base change the g chart and translate by -y(fu) to obtain G. Etaleness follows from
   lem-weil-pbc-etale-base-change-finite-limits, def-weil-open-immersion and
   lem-weil-pbc-etale-composition-cancellation.
4. Identify W with Q×_V U. Base change the f chart, translate by -x(u), and obtain H.
   J is the base change of G; F is their composite, so both are etale by the same nodes.
5. Evaluate the polynomial generators to get all five identities and the ordered
   coordinates of F. These are identities of scheme maps, not only of ordinary points.
6. Affine sources give separatedness (lem-weil-pbc-affine-source-morphism-separated).
   Affine targets are quasi-separated (lem-weil-pbc-quasicompact-affine-surjection,
   lem-weil-pbc-quasi-separated-affine-cover-criterion). Etaleness and
   lem-weil-pbc-qcqs-morphism-permanence give finite presentation; use
   def-sbc-locally-finite-presentation, lem-weil-pbc-lft-pointwise-criterion and
   def-weil-finite-type-morphism for finite type.
7. The projections have the claimed dimensions by sbc-lem-affine-space-smooth and
   lem-sbc-smooth-relative-dimension-permanence; q is the base change of P_d.
8. In the pullback of H along includeR, fu'=fu and the first coordinates are forced.
   Thus it is W_f, giving its Cartesian square and the diagonal-zero identity.
9. Pulling V×_T V back over f gives Q. Its difference chart pulls back to G. Both
   difference charts are etale by the same base-change/translation argument.
11. All polynomial constructions allow zero rings and empty coordinate blocks;
    thus empty affines and d=0 or e=0 require no extra hypothesis.
-/
theorem factorization {k : Type u} [Field k]
    [U.Over (Spec (.of k))] [V.Over (Spec (.of k))] [T.Over (Spec (.of k))]
    [IsAffine U] [IsAffine V] [IsAffine T]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (f : U ⟶ V) (g : V ⟶ T) [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [IsSeparated f] [IsSeparated g] [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : U ⟶ AffineSpace (Coords d) V) (cg : V ⟶ AffineSpace (Coords e) T)
    [Etale cf] [Etale cg]
    (hcf : cf ≫ (AffineSpace (Coords d) V ↘ V) = f)
    (hcg : cg ≫ (AffineSpace (Coords e) T ↘ T) = g) :
    H f g cf ≫ J d f g cg = differenceTotal d e f g cf cg ∧
    H f g cf ≫ (R d f g ↘ Q f g) = a f g ∧
    differenceSecond e f g cg ≫ (AffineSpace (Coords e) U ↘ U) = pullback.fst (f ≫ g) g ∧
    J d f g cg ≫ q d e U =
      (R d f g ↘ Q f g) ≫ differenceSecond e f g cg ∧
    s f g ≫ differenceSecond e f g cg = AffineSpace.zeroSection (Coords e) U ∧
    pullback.diagonal (f ≫ g) ≫ differenceTotal d e f g cf cg =
      zero (d + e) U ∧
    (∀ i : Coords d,
      (differenceTotal d e f g cf cg).appTop
        (AffineSpace.coord U (ULift.up (Fin.castAdd e i.down))) =
        (pullback.snd (f ≫ g) (f ≫ g) ≫ cf).appTop (AffineSpace.coord V i) -
        (pullback.fst (f ≫ g) (f ≫ g) ≫ cf).appTop (AffineSpace.coord V i)) ∧
    (∀ i : Coords e,
      (differenceTotal d e f g cf cg).appTop
        (AffineSpace.coord U (ULift.up (Fin.natAdd d i.down))) =
        (pullback.snd (f ≫ g) (f ≫ g) ≫ f ≫ cg).appTop (AffineSpace.coord T i) -
        (pullback.fst (f ≫ g) (f ≫ g) ≫ f ≫ cg).appTop (AffineSpace.coord T i)) ∧
    differenceTotal d e f g cf cg ≫ (A (d + e) U ↘ U) =
      pullback.fst (f ≫ g) (f ≫ g) ∧
    Etale (differenceSecond e f g cg) ∧ IsSeparated (differenceSecond e f g cg) ∧
      LocallyOfFiniteType (differenceSecond e f g cg) ∧ QuasiCompact (differenceSecond e f g cg) ∧
    Etale (H f g cf) ∧ IsSeparated (H f g cf) ∧
      LocallyOfFiniteType (H f g cf) ∧ QuasiCompact (H f g cf) ∧
    Etale (J d f g cg) ∧ IsSeparated (J d f g cg) ∧
      LocallyOfFiniteType (J d f g cg) ∧ QuasiCompact (J d f g cg) ∧
    Etale (differenceTotal d e f g cf cg) ∧ IsSeparated (differenceTotal d e f g cf cg) ∧
      LocallyOfFiniteType (differenceTotal d e f g cf cg) ∧
      QuasiCompact (differenceTotal d e f g cf cg) ∧
    IsAffine (Q f g) ∧ IsAffine (W f g) ∧ IsAffine (R d f g) ∧
    IsAffine (pullback f f) ∧ IsAffine (pullback g g) ∧
    IsAffine (AffineSpace (Coords d) U) ∧ IsAffine (AffineSpace (Coords e) U) ∧
    IsAffine (A (d + e) U) ∧
    IsAffine (AffineSpace (Coords d) V) ∧ IsAffine (AffineSpace (Coords e) T) ∧
    IsAffine (AffineSpace (Coords e) V) ∧
    IsPullback (Graw f g cg) (pullback.snd (f ≫ g) g)
      (AffineSpace.map (Coords e) (f ≫ g)) cg ∧
    differenceSecond e f g cg = Graw f g cg ≫ AffineSpace.translation
      (fun i ↦ -((f ≫ cg).appTop (AffineSpace.coord T i))) ∧
    IsPullback (Hraw f g cf) (pullback.snd (f ≫ g) (f ≫ g))
      (AffineSpace.map (Coords d) (pullback.snd (f ≫ g) g)) cf ∧
    H f g cf = Hraw f g cf ≫ AffineSpace.translation
      (fun i ↦ -((pullback.fst (f ≫ g) g ≫ cf).appTop (AffineSpace.coord V i))) ∧
    IsPullback (J d f g cg) (R d f g ↘ Q f g)
      (q d e U) (differenceSecond e f g cg) ∧
    IsPullback (first d e U) (q d e U)
      (AffineSpace (Coords d) U ↘ U) (AffineSpace (Coords e) U ↘ U) ∧
    SmoothOfRelativeDimension d
      (q d e U) ∧
    SmoothOfRelativeDimension e (AffineSpace (Coords e) U ↘ U) ∧
    SmoothOfRelativeDimension (d + e)
      (q d e U ≫ (AffineSpace (Coords e) U ↘ U)) ∧
    SmoothOfRelativeDimension d (R d f g ↘ Q f g) ∧
    IsPullback (differenceFirst d f cf) (i f g) (includeR d f g) (H f g cf) ∧
    IsPullback (differenceSecond e f g cg) (j f g) (AffineSpace.map (Coords e) f)
      (differenceFirst e g cg) ∧
    Etale (differenceFirst d f cf) ∧ Etale (differenceFirst e g cg) ∧
    pullback.diagonal f ≫ differenceFirst d f cf = AffineSpace.zeroSection (Coords d) U ∧
    pullback.diagonal g ≫ differenceFirst e g cg = AffineSpace.zeroSection (Coords e) V := by
  have hH : H f g cf ≫ (R d f g ↘ Q f g) = a f g :=
    AffineSpace.homOfVector_over _ _
  have hG : differenceSecond e f g cg ≫ (A e U ↘ U) = pullback.fst (f ≫ g) g :=
    AffineSpace.homOfVector_over _ _
  have ha₁ : a f g ≫ pullback.fst (f ≫ g) g =
      pullback.fst (f ≫ g) (f ≫ g) := by simp [a]
  have ha₂ : a f g ≫ pullback.snd (f ≫ g) g =
      pullback.snd (f ≫ g) (f ≫ g) ≫ f := by simp [a]
  have hJ : J d f g cg ≫ q d e U =
      (R d f g ↘ Q f g) ≫ differenceSecond e f g cg := by
    apply AffineSpace.hom_ext
    · simp [J, q, differenceSecond]
    · rintro ⟨j⟩
      simp [J, q]
  have hF : H f g cf ≫ J d f g cg = differenceTotal d e f g cf cg := by
    apply AffineSpace.hom_ext
    · simp [J, H, differenceTotal, ha₁]
    · rintro ⟨i⟩
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simp [J, H, differenceTotal]
      · simp only [J, differenceTotal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.homOfVector_appTop_coord, Fin.addCases_right]
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hH]
        simp only [differenceSecond, AffineSpace.homOfVector_appTop_coord, map_sub]
        simp only [appTop_comp_apply]
        simp only [← Category.assoc, ha₁, ha₂]
  have hpG : IsPullback (Graw f g cg) (pullback.snd (f ≫ g) g)
      (AffineSpace.map (Coords e) (f ≫ g)) cg :=
    chart_pullback _ _ _ _ (IsPullback.of_hasPullback (f ≫ g) g) cg hcg
  have hpA : IsPullback (a f g) (pullback.snd (f ≫ g) (f ≫ g))
      (pullback.snd (f ≫ g) g) f := by
    have hout : IsPullback (a f g ≫ pullback.fst (f ≫ g) g)
        (pullback.snd (f ≫ g) (f ≫ g)) (f ≫ g) (f ≫ g) := by
      simpa only [ha₁] using IsPullback.of_hasPullback (f ≫ g) (f ≫ g)
    exact hout.of_right ha₂ (IsPullback.of_hasPullback (f ≫ g) g)
  have hpH : IsPullback (Hraw f g cf) (pullback.snd (f ≫ g) (f ≫ g))
      (AffineSpace.map (Coords d) (pullback.snd (f ≫ g) g)) cf :=
    chart_pullback _ _ _ _ hpA cf hcf
  have htG : differenceSecond e f g cg = Graw f g cg ≫ AffineSpace.translation
      (fun i ↦ -((f ≫ cg).appTop (AffineSpace.coord T i))) := by
    apply AffineSpace.hom_ext
    · simp [differenceSecond, Graw]
    · intro i
      rw [comp_translation_coord]
      simp only [differenceSecond, Graw, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_over, map_neg, sub_eq_add_neg]
      simp only [appTop_comp_apply, Category.assoc]
  have htH : H f g cf = Hraw f g cf ≫ AffineSpace.translation
      (fun i ↦ -((pullback.fst (f ≫ g) g ≫ cf).appTop (AffineSpace.coord V i))) := by
    apply AffineSpace.hom_ext
    · simp [H, Hraw]
    · intro i
      rw [comp_translation_coord]
      simp only [H, Hraw, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_over, map_neg, sub_eq_add_neg]
      simp only [appTop_comp_apply, ← Category.assoc, ha₁]
  have hpProd := affine_product d e U
  have hJfirst : J d f g cg ≫ first d e U =
      AffineSpace.map (Coords d) (pullback.fst (f ≫ g) g) := by
    apply AffineSpace.hom_ext
    · simp [J, first]
    · rintro ⟨i⟩
      simp [J, first]
  have hpJ : IsPullback (J d f g cg) (R d f g ↘ Q f g)
      (q d e U) (differenceSecond e f g cg) := by
    have hout : IsPullback (J d f g cg ≫ first d e U) (R d f g ↘ Q f g)
        (A d U ↘ U) (differenceSecond e f g cg ≫ (A e U ↘ U)) := by
      simpa only [hJfirst, hG] using
        AffineSpace.isPullback_map (n := Coords d) (pullback.fst (f ≫ g) g)
    exact hout.of_right hJ hpProd
  have : Etale (Graw f g cg) := MorphismProperty.of_isPullback hpG.flip inferInstance
  have : Etale (Hraw f g cf) := MorphismProperty.of_isPullback hpH.flip inferInstance
  have : Etale (differenceSecond e f g cg) := by
    rw [htG]
    have := translation_isIso (fun i ↦ -((f ≫ cg).appTop (AffineSpace.coord T i)))
    infer_instance
  have : Etale (H f g cf) := by
    rw [htH]
    have := translation_isIso
      (fun i ↦ -((pullback.fst (f ≫ g) g ≫ cf).appTop (AffineSpace.coord V i)))
    infer_instance
  have : Etale (J d f g cg) := MorphismProperty.of_isPullback hpJ.flip inferInstance
  have : Etale (differenceTotal d e f g cf cg) := by rw [← hF]; infer_instance
  have hpI : IsPullback (i f g) (pullback.fst f f) (a f g) (s f g) := by
    apply IsPullback.mk'
    · apply pullback.hom_ext <;> simp [i, a, s]
    · intro L φ ψ h₁ h₂
      apply pullback.hom_ext
      · exact h₂
      · simpa [i] using congrArg
          (fun h ↦ h ≫ pullback.snd (f ≫ g) (f ≫ g)) h₁
    · intro L α β hαβ
      have h₁ : α ≫ pullback.fst (f ≫ g) (f ≫ g) = β := by
        simpa [a, s] using congrArg (fun h ↦ h ≫ pullback.fst (f ≫ g) g) hαβ
      have h₂ : (α ≫ pullback.snd (f ≫ g) (f ≫ g)) ≫ f = β ≫ f := by
        simpa [a, s] using congrArg (fun h ↦ h ≫ pullback.snd (f ≫ g) g) hαβ
      refine ⟨pullback.lift β (α ≫ pullback.snd (f ≫ g) (f ≫ g)) h₂.symm, ?_, by simp⟩
      apply pullback.hom_ext <;> simp [i, h₁]
  have hpj : IsPullback (j f g) (pullback.fst (f ≫ g) g) (pullback.fst g g) f := by
    have hout : IsPullback (j f g ≫ pullback.snd g g) (pullback.fst (f ≫ g) g)
        g (f ≫ g) := by
      simpa [j] using (IsPullback.of_hasPullback (f ≫ g) g).flip
    exact hout.of_right (by simp [j]) (IsPullback.of_hasPullback g g).flip
  have hiH : differenceFirst d f cf ≫ includeR d f g = i f g ≫ H f g cf := by
    apply AffineSpace.hom_ext
    · simp [differenceFirst, includeR, H, ← hpI.w]
    · intro i₀
      simp only [differenceFirst, includeR, H, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
        AffineSpace.homOfVector_appTop_coord, map_sub]
      simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Category.assoc, i, pullback.lift_snd, pullback.lift_fst, Category.comp_id]
  have hpRestrictH : IsPullback (differenceFirst d f cf) (i f g)
      (includeR d f g) (H f g cf) := by
    have hout : IsPullback (differenceFirst d f cf ≫ (A d U ↘ U)) (i f g)
        (s f g) (H f g cf ≫ (R d f g ↘ Q f g)) := by
      simpa only [differenceFirst, AffineSpace.homOfVector_over, hH] using hpI.flip
    exact hout.of_right hiH (AffineSpace.isPullback_map (n := Coords d) (s f g)).flip
  have hjG : differenceSecond e f g cg ≫ AffineSpace.map (Coords e) f =
      j f g ≫ differenceFirst e g cg := by
    apply AffineSpace.hom_ext
    · simp [differenceSecond, differenceFirst, j]
    · intro i₀
      simp only [differenceSecond, differenceFirst, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
        AffineSpace.homOfVector_appTop_coord, map_sub]
      simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Category.assoc, j, pullback.lift_snd, pullback.lift_fst, Category.comp_id]
  have hpRestrictG : IsPullback (differenceSecond e f g cg) (j f g)
      (AffineSpace.map (Coords e) f) (differenceFirst e g cg) := by
    have hout : IsPullback (differenceSecond e f g cg ≫ (A e U ↘ U)) (j f g)
        f (differenceFirst e g cg ≫ (A e V ↘ V)) := by
      simpa only [hG, differenceFirst, AffineSpace.homOfVector_over] using hpj.flip
    exact hout.of_right hjG (AffineSpace.isPullback_map (n := Coords e) f).flip
  have hsG : s f g ≫ differenceSecond e f g cg = AffineSpace.zeroSection (Coords e) U := by
    apply AffineSpace.hom_ext
    · simp [differenceSecond, s]
    · intro i₀
      simp only [differenceSecond, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.homOfVector_appTop_coord, map_sub]
      simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Category.assoc, s, pullback.lift_snd, pullback.lift_fst, Category.id_comp,
        sub_self, AffineSpace.zeroSection_appTop_coord]
  have htF : pullback.diagonal (f ≫ g) ≫ differenceTotal d e f g cf cg =
      zero (d + e) U := by
    apply AffineSpace.hom_ext
    · simp [differenceTotal]
    · rintro ⟨i₀⟩
      refine Fin.addCases (fun j₀ ↦ ?_) (fun j₀ ↦ ?_) i₀ <;>
        simp only [differenceTotal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.homOfVector_appTop_coord,
          Fin.addCases_left, Fin.addCases_right, map_sub]
      all_goals simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        pullback.diagonal_snd_assoc, pullback.diagonal_fst_assoc, sub_self,
        AffineSpace.zeroSection_appTop_coord]
  have hsmooth (r : ℕ) (B : Scheme.{u}) : SmoothOfRelativeDimension r (A r B ↘ B) := by
    simpa [Coords] using AffineSpace.smoothOfRelativeDimension_over (Coords r) B
  have hsq : SmoothOfRelativeDimension d (q d e U) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback hpProd (hsmooth d U)
  have hsqe : SmoothOfRelativeDimension (d + e) (q d e U ≫ (A e U ↘ U)) := by
    have : SmoothOfRelativeDimension d (q d e U) := hsq
    have : SmoothOfRelativeDimension e (A e U ↘ U) := hsmooth e U
    infer_instance
  refine ⟨hF, hH, hG, hJ, hsG, htF, ?_, ?_, ?_,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hpG, htG, hpH, htH, hpJ, hpProd, hsq, hsmooth e U, hsqe, hsmooth d (Q f g),
    hpRestrictH, hpRestrictG, differenceFirst_etale d f cf hcf,
    differenceFirst_etale e g cg hcg, differenceFirst_diagonal d f cf,
    differenceFirst_diagonal e g cg⟩
  · rintro ⟨i₀⟩
    simp [differenceTotal]
  · rintro ⟨i₀⟩
    simp [differenceTotal]
  · exact AffineSpace.homOfVector_over _ _

end AlgebraicGeometry.AffineDifferenceTower
