/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.InvariantOpenEffectiveDescent
import Sheaf.AlgebraicGeometry.FpqcInvariantIntersectionNeighbourhoods
import Sheaf.AlgebraicGeometry.IndQuasiAffinePermanence
import Sheaf.AlgebraicGeometry.InvariantOpenAffinizationEquivariance
import WeilConjectures.AlgebraicGeometry.AffineFlatDescent
import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Invariant
import WeilConjectures.AlgebraicGeometry.FpqcEffectivityAffineBaseGluing
import WeilConjectures.AlgebraicGeometry.FpqcSingletonAffineRefinement
import WeilConjectures.AlgebraicGeometry.FpqcCanonicalPullbackDatum
import WeilConjectures.AlgebraicGeometry.FpqcRefinementReflectsEffectivity

/-!
# Effective fpqc descent for ind-quasi-affine morphisms

Source: Stacks Project, More on Groupoids in Spaces, Tag 0APK, lemma-ind-quasi-affine,
specialized to a singleton fpqc covering; More on Morphisms, Tag 0F1U, condition (2)
(blueprint: lem-a1-ind-quasi-affine-fpqc-effective-descent).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Over.DescentDatum

-- Effectivity is preserved by an equivariant open embedding into an effective datum.
private theorem effective_open_embedding {X S : Scheme.{u}} {p : X ⟶ S}
    [Flat p] [Surjective p] [QuasiCompact p] {V Z : Over X}
    (D : Over.DescentDatum p V) (F : Over.DescentDatum p Z)
    (j : V.left ⟶ Z.left) [IsOpenImmersion j] (hj : j ≫ Z.hom = V.hom)
    (ht : ∀ {T : Scheme.{u}} (a b : T ⟶ X) (h : a ≫ p = b ≫ p)
      (v : Over.mk a ⟶ V),
      (D.transport a b h v).left ≫ j =
        (F.transport a b h (Over.homMk (v.left ≫ j) (by
          rw [Category.assoc, hj]; exact Over.w v))).left)
    (hF : F.IsEffective) : D.IsEffective := by
  classical
  let J := j.opensRange
  have hJ : F.IsInvariant J := by
    intro T a b h v hv
    let w : Over.mk a ⟶ V :=
      Over.homMk (IsOpenImmersion.lift j v.left hv) (by
        rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac]
        exact Over.w v)
    have hw : w.left ≫ j = v.left := IsOpenImmersion.lift_fac _ _ _
    have htr := ht a b h w
    have he : Over.homMk (w.left ≫ j) (by rw [Category.assoc, hj]; exact Over.w w) = v :=
      Over.OverMorphism.ext hw
    rw [he] at htr
    rintro _ ⟨x, rfl⟩
    rw [← htr, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  obtain ⟨Z₀, q, hq, hinv⟩ := hF
  have : Flat q := MorphismProperty.of_isPullback hq.flip inferInstance
  have : Surjective q := MorphismProperty.of_isPullback hq.flip inferInstance
  have : QuasiCompact q := MorphismProperty.of_isPullback hq.flip inferInstance
  have hJJ : Limits.pullback.fst q q ⁻¹ᵁ J = Limits.pullback.snd q q ⁻¹ᵁ J := by
    apply le_antisymm
    all_goals
      intro x hx
      let l := Limits.pullback.fst q q
      let r := Limits.pullback.snd q q
    · have h : (l ≫ Z.hom) ≫ p = (r ≫ Z.hom) ≫ p := by
        simp only [Category.assoc, ← hq.w]
        exact pullback.condition_assoc (f := q) (g := q) Z₀.hom
      let O := l ⁻¹ᵁ J
      have hh : (O.ι ≫ l ≫ Z.hom) ≫ p = (O.ι ≫ r ≫ Z.hom) ≫ p := by
        simpa only [Category.assoc] using congrArg (fun k ↦ O.ι ≫ k) h
      have he' := F.transport_eq_of_isPullback hq hinv _ _ hh
        (Over.homMk (O.ι ≫ l) (by simp))
        (Over.homMk (O.ι ≫ r) (by simp)) (by simp [l, r, pullback.condition])
      have hm := hJ _ _ hh (Over.homMk (O.ι ≫ l) (by simp)) (by
        rintro _ ⟨z, rfl⟩
        exact z.property)
      rw [he'] at hm
      exact hm ⟨⟨x, hx⟩, rfl⟩
    · let O := r ⁻¹ᵁ J
      have h : (r ≫ Z.hom) ≫ p = (l ≫ Z.hom) ≫ p := by
        simp only [Category.assoc, ← hq.w]
        exact (pullback.condition_assoc (f := q) (g := q) Z₀.hom).symm
      have hh : (O.ι ≫ r ≫ Z.hom) ≫ p = (O.ι ≫ l ≫ Z.hom) ≫ p := by
        simpa only [Category.assoc] using congrArg (fun k ↦ O.ι ≫ k) h
      have he' := F.transport_eq_of_isPullback hq hinv _ _ hh
        (Over.homMk (O.ι ≫ r) (by simp))
        (Over.homMk (O.ι ≫ l) (by simp)) (by simp [l, r, pullback.condition])
      have hm := hJ _ _ hh (Over.homMk (O.ι ≫ r) (by simp)) (by
        rintro _ ⟨z, rfl⟩
        exact z.property)
      rw [he'] at hm
      exact hm ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨O, hO, _⟩ := openSubscheme_existsUnique_of_fpqc
    (fun _ : PUnit.{1} ↦ q)
    (by simpa only [Presieve.ofArrows_pUnit] using q.singleton_mem_fpqcPrecoverage)
    (fun _ ↦ J) (fun _ _ ↦ hJJ)
  have hpre : q ⁻¹ᵁ O = J := hO PUnit.unit
  let k : V.left ⟶ O.toScheme := IsOpenImmersion.lift O.ι (j ≫ q) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : j x ∈ q ⁻¹ᵁ O := by rw [hpre]; exact ⟨x, rfl⟩
    exact hx)
  have hk : k ≫ O.ι = j ≫ q := IsOpenImmersion.lift_fac _ _ _
  have hcart : IsPullback k j O.ι q :=
    IsOpenImmersion.isPullback k j O.ι q hk.symm (by
      simpa only [Scheme.Opens.opensRange_ι] using hpre)
  refine ⟨Over.mk (O.ι ≫ Z₀.hom), k, ?_, ?_⟩
  · simpa only [hj, Over.mk_left, Over.mk_hom] using hcart.paste_vert hq
  · intro T a b h v
    apply (cancel_mono O.ι).mp
    rw [Category.assoc, hk, ← Category.assoc, ht, hinv]
    simp only [Over.homMk_left, Category.assoc, hk]

private theorem effective_spec {R A : CommRingCat.{u}} (r : R ⟶ A)
    [Flat (Spec.map r)] [Surjective (Spec.map r)]
    {V : Over (Spec A)} [QuasiSeparatedSpace V.left]
    (hV : ∀ Q : V.left.Opens, IsCompact (Q : Set V.left) →
      Scheme.IsQuasiAffine Q.toScheme)
    (D : Over.DescentDatum (Spec.map r) V) : D.IsEffective := by
  classical
  suffices H : ∀ v : V.left, ∃ (W : V.left.Opens) (hW : D.IsInvariant W),
      v ∈ W ∧ (D.restrict W hW).IsEffective by
    choose W hW hv heff using H
    exact isEffective_of_effective_open_cover
      (Spec.map r).singleton_mem_fpqcPrecoverage D W
      (fun v ↦ ⟨v, hv v⟩) (fun v ↦ D.restrict (W v) (hW v))
      (fun v _ a b h w ↦ D.restrict_transport_left_ι (W v) (hW v) a b h w) heff
  intro v
  obtain ⟨W, E, hv, hWE, ⟨𝒰, h𝒰, hqc, hE⟩, hW, hEinv⟩ :=
    D.exists_fpqc_invariant_intersection_neighbourhood (Spec.map r) v
  let U : 𝒰 → V.left.Opens := Subtype.val
  have hI : Nonempty 𝒰 := h𝒰.to_subtype
  have hqc' : ∀ i, IsCompact (U i : Set V.left) := fun i ↦ hqc i.val i.property
  have hmem (x : V.left) : x ∈ E ↔ ∀ i, x ∈ U i := by
    rw [hE]
    simp [U]
  have hWU : ∀ x : W, ∀ i, x.val ∈ U i := fun x ↦ (hmem x.val).mp (hWE x.property)
  have hEinv' : ∀ x : ↥(Limits.pullback (V.hom ≫ Spec.map r) (Spec.map r) : Scheme.{u}),
      (∀ i, pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) x ∈ U i) ↔
        ∀ i, D.toHom x ∈ U i := by
    intro x
    rw [← hmem, ← hmem]
    exact Set.ext_iff.mp hEinv x
  have hWinv : D.IsInvariant W := by
    rw [D.isInvariant_iff]
    intro x hx
    have hx' : x ∈ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ W := hx
    rw [hW] at hx'
    exact hx'
  obtain ⟨ψ, _, _, _, F, _, J, e, he, _, hj, htr⟩ :=
    invariant_open_affinization_equivariance r V hV D U hI hqc' W hWU hEinv' hW
  have : IsAffineHom (Scheme.intersectionAffineModel V U).hom := by
    dsimp [Scheme.intersectionAffineModel]
    infer_instance
  let j := Scheme.intersectionOpenAffinization U W hWU
  have hjopen : IsOpenImmersion j := by
    rw [show j = e.hom ≫ J.ι from he.symm]
    infer_instance
  refine ⟨W, hWinv, hv, ?_⟩
  apply effective_open_embedding (D.restrict W hWinv) F j hj ?_
    (F.isEffective_of_isAffineHom_flat_affine (Spec.map r) inferInstance inferInstance)
  intro T a b h w
  obtain ⟨w', hw', hw'j⟩ := htr T a b h w
  have hw : ((D.restrict W hWinv).transport a b h w).left = w'.left := by
    apply (cancel_mono W.ι).mp
    rw [restrict_transport_left_ι, hw']
  rw [hw]
  exact hw'j

-- Change coordinates on the cover and base, leaving the total space fixed.
private theorem effective_of_affine {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (p : X ⟶ S) [Flat p] [Surjective p] {V : Over X}
    (hV : indQuasiAffineProperty V.hom) (D : Over.DescentDatum p V) :
    D.IsEffective := by
  classical
  let r := p.appTop
  let f := Spec.map r
  have hf : X.isoSpec.inv ≫ p = f ≫ S.isoSpec.inv :=
    (Scheme.isoSpec_inv_naturality p).symm
  have : Flat f := by
    apply (MorphismProperty.cancel_right_of_respectsIso @Flat f S.isoSpec.inv).mp
    rw [← hf]
    infer_instance
  have : Surjective f := by
    apply (MorphismProperty.cancel_right_of_respectsIso @Surjective f S.isoSpec.inv).mp
    rw [← hf]
    infer_instance
  let V' : Over (Spec Γ(X, ⊤)) := Over.mk (V.hom ≫ X.isoSpec.hom)
  let point {T : Scheme.{u}} (a : T ⟶ Spec Γ(X, ⊤))
      (v : Over.mk a ⟶ V') : Over.mk (a ≫ X.isoSpec.inv) ⟶ V :=
    Over.homMk v.left (by
      have hh := congrArg (fun k ↦ k ≫ X.isoSpec.inv) (Over.w v)
      simpa [V'] using hh)
  let E : Over.DescentDatum f V' := {
    transport := fun a b h v ↦ Over.homMk
      (D.transport (a ≫ X.isoSpec.inv) (b ≫ X.isoSpec.inv)
        (by simpa only [Category.assoc, hf] using congrArg (fun k ↦ k ≫ S.isoSpec.inv) h)
        (point a v)).left (by
          change _ ≫ (V.hom ≫ X.isoSpec.hom) = b
          calc
            _ = (b ≫ X.isoSpec.inv) ≫ X.isoSpec.hom :=
              (Category.assoc _ _ _).symm.trans
                (congrArg (fun k ↦ k ≫ X.isoSpec.hom) (Over.w _))
            _ = b := by simp)
    transport_homMk_comp := by
      intro T T' g a b h v
      apply Over.OverMorphism.ext
      exact D.transport_left_eq_comp g (a ≫ X.isoSpec.inv) (b ≫ X.isoSpec.inv)
        _ (point a v) _ (by simp) (by simp) _ rfl
    transport_self := by
      intro T a v
      apply Over.OverMorphism.ext
      exact congrArg (fun z ↦ z.left) (D.transport_self _ (point a v))
    transport_transport := by
      intro T a b c hab hbc v
      apply Over.OverMorphism.ext
      let hab' : (a ≫ X.isoSpec.inv) ≫ p = (b ≫ X.isoSpec.inv) ≫ p := by
        simpa only [Category.assoc, hf] using
          congrArg (fun k ↦ k ≫ S.isoSpec.inv) hab
      let hbc' : (b ≫ X.isoSpec.inv) ≫ p = (c ≫ X.isoSpec.inv) ≫ p := by
        simpa only [Category.assoc, hf] using
          congrArg (fun k ↦ k ≫ S.isoSpec.inv) hbc
      trans (D.transport (b ≫ X.isoSpec.inv) (c ≫ X.isoSpec.inv) hbc'
        (D.transport (a ≫ X.isoSpec.inv) (b ≫ X.isoSpec.inv) hab' (point a v))).left
      · exact D.transport_left_congr _ _ _ _ rfl rfl rfl
      · simpa only [Over.homMk_left] using
          congrArg (fun z : Over.mk (c ≫ X.isoSpec.inv) ⟶ V ↦ z.left)
            (D.transport_transport (a ≫ X.isoSpec.inv) (b ≫ X.isoSpec.inv)
              (c ≫ X.isoSpec.inv) hab' hbc' (point a v)) }
  obtain ⟨hqc, _, hqs⟩ := (indQuasiAffineProperty_permanence.{u, u} V.hom).2.2
    inferInstance hV
  have : QuasiSeparatedSpace V'.left := hqs
  obtain ⟨W, q, hq, hqinv⟩ := effective_spec r hqc E
  refine ⟨Over.mk (W.hom ≫ S.isoSpec.inv), q, ?_, ?_⟩
  · apply hq.of_iso (Iso.refl _) (Iso.refl _) X.isoSpec.symm S.isoSpec.symm
    · simp
    · simp [V']
    · simp
    · exact hf.symm
  · intro T a b h v
    let v' : Over.mk (a ≫ X.isoSpec.hom) ⟶ V' :=
      Over.homMk v.left (by simp [V', ← Category.assoc, Over.w v])
    have hh : (a ≫ X.isoSpec.hom) ≫ f = (b ≫ X.isoSpec.hom) ≫ f := by
      change (a ≫ X.isoSpec.hom) ≫ Spec.map p.appTop =
        (b ≫ X.isoSpec.hom) ≫ Spec.map p.appTop
      rw [Category.assoc, Category.assoc, Scheme.isoSpec_hom_naturality]
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ S.isoSpec.hom) h
    have hi := hqinv (a ≫ X.isoSpec.hom) (b ≫ X.isoSpec.hom) hh v'
    dsimp only [E] at hi
    simp only [Over.homMk_left] at hi
    have he := D.transport_left_congr
      (by simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h)
      h (point _ v') v
      (Category.assoc _ _ _ |>.trans ((congrArg (fun k ↦ a ≫ k)
        X.isoSpec.hom_inv_id).trans (Category.comp_id a)))
      (Category.assoc _ _ _ |>.trans ((congrArg (fun k ↦ b ≫ k)
        X.isoSpec.hom_inv_id).trans (Category.comp_id b))) rfl
    rw [he] at hi
    exact hi

/-- A descent datum over a singleton fpqc covering is effective if every quasi-compact
open in the inverse image of every affine open of the base is quasi-affine over that open.
No quasi-compactness or local finite-presentation assumption on `V.hom` is required.

Source: Stacks Project, More on Groupoids in Spaces, Tag 0APK, lemma-ind-quasi-affine;
More on Morphisms, Tag 0F1U, condition (2).
(blueprint: lem-a1-ind-quasi-affine-fpqc-effective-descent)

`D.IsEffective` supplies a scheme over `B` whose pullback is `V`, with the pullback
identification compatible with the given datum, not merely an underlying scheme isomorphism.

Proof:
1. Let P be the condition in hV. By lem-a1-ind-quasi-affine-permanence it is stable under
   arbitrary base change and local on the target. It is stable under finite disjoint unions:
   check on affine opens in each target component, using lem-weil-pbc-scheme-coproduct-family.
   The empty coproduct case is vacuous. Apply lem-galois-fpqc-descending-types-morphisms to
   reduce to a flat surjection X -> S between affines.
2. Write S = Spec R and X = Spec A. The permanence lemma makes V ind-quasi-affine and
   quasi-separated. The cover is fpqc since a map between affines is affine, by
   lem-weil-pbc-morphism-affine-schemes-affine. At each v in V use
   lem-a1-fpqc-invariant-intersection-neighbourhoods to choose v in W contained in E,
   where W is invariant open and E is an invariant intersection of a nonempty family of
   quasi-compact opens. No openness or scheme structure on E is assumed.
3. Put C = Gamma(E, O_V restricted to E). The datum restricts to the two inverse images
   E_0 and E_1. By lem-a1-intersection-sections-flat-base-change their section rings are
   C tensor_R A and A tensor_R C. Its comorphism gives the algebra isomorphism psi from
   A tensor_R C to C tensor_R A. Apply the same lemma after another flat base change,
   using lem-weil-pbc-flat-morphism-base-change. Its naturality and iterated compatibility
   turn the geometric cocycle into psi_02 = psi_01 composed with psi_12; taking sections
   reverses composition. This verifies the omitted cocycle without making E a scheme.
4. Let Z = Spec C over X. By lem-weil-pbc-fibre-product-affine-spectra and
   def-weil-affine-spectrum, Spec psi defines the descent isomorphism on Z and the algebra
   cocycle gives its geometric cocycle. The structure morphism is affine by
   lem-weil-pbc-morphism-affine-schemes-affine. Apply lem-galois-fpqc-affine-descent-effective
   to obtain Z_0 over S and a datum-compatible pullback identification with Z.
5. By lem-a1-intersection-canonical-affine-embedding the canonical map j_E identifies W
   with an open J in Z. Check its base-change comparison on affine opens L in W: writing
   D_L = Gamma(L, O_L), its map to Z corresponds to restriction C -> D_L by
   lem-weil-pbc-morphism-into-affine-scheme. The tensor square identifies its base change
   by lem-weil-pbc-fibre-product-affine-spectra. Naturality of
   lem-a1-intersection-sections-flat-base-change sends c tensor a to its restriction
   tensor a, so the canonical maps agree. These local comparisons glue. Since psi is the
   comorphism of the original datum on E_0, Spec psi carries the full inverse image of J
   onto its other inverse image. Under Z = Z_0 times_S X these are the two inverse images
   of J in Z times_{Z_0} Z.
6. By lem-galois-fpqc-covering-base-change, Z -> Z_0 is fpqc. Thus
   lem-weil-pbc-open-subscheme-fpqc-descent descends J to an open W_0 in Z_0. Its pullback
   is W, compatibly with the restricted datum: the canonical embedding intertwines the
   datum by the restriction calculation in step 5. Hence the datum on W is effective.
7. The W obtained for every v cover V and their inclusions respect the restricted data.
   By lem-pd-effective-invariant-open-cover their effective models glue. This proves the
   affine case in step 1 and hence the original singleton-cover assertion. No step used
   quasi-compactness or local finite presentation of V -> A. When V is empty, the empty
   invariant open cover gives the empty scheme over B. -/
theorem isEffective_of_indQuasiAffine_fpqc {A B : Scheme.{u}} (p : A ⟶ B)
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage B) {V : Over A}
    (hV : ∀ (U : A.Opens), IsAffineOpen U →
      ∀ (K : (Limits.pullback V.hom U.ι).Opens),
        IsCompact (K : Set (Limits.pullback (C := Scheme.{u}) V.hom U.ι)) →
          IsQuasiAffineHom (K.ι ≫ Limits.pullback.snd V.hom U.ι))
    (D : Over.DescentDatum p V) : D.IsEffective := by
  classical
  apply fpqc_effectivity_of_affine_bases (@indQuasiAffineProperty)
    (fun g h hg ↦ (indQuasiAffineProperty_permanence.{u, u} g).1 _ h hg) ?_ p hp D hV
  intro X S hS f hf V D hV
  obtain ⟨n, U, hU, h, g, _, hg, hX, hflat, hsurj, hcover⟩ :=
    Scheme.exists_fpqc_singleton_affine_refinement f hf
  obtain ⟨E, hE⟩ := exists_canonical_pullback_descent_datum f g h hg.symm D
  have hP := (indQuasiAffineProperty_permanence.{u, u} V.hom).1 _ h hV
  have heff := effective_of_affine g hP E
  exact fpqc_refinement_reflects_effectivity f g h hf hcover hg.symm
    (pullback.fst V.hom h) pullback.condition D E (IsPullback.of_hasPullback _ _) hE heff

end CategoryTheory.Over.DescentDatum
