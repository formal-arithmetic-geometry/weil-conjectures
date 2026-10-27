/-
Copyright (c) 2026 The weil-conjectures-sheaf contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Split an affine étale morphism near a marked geometric fibre

Source: literature/stacks-project/etale.tex, Tags 04HM and 04HU
(blueprint: lem-trf-affine-etale-split-neighbourhood).

## Main statements

* `exists_affine_etale_split_neighbourhood` states the affine étale splitting near a
  geometric point, including the singleton fibre, the empty remainder over the marked
  point, and the resulting enumeration of geometric lifts. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false

-- Assemble disjoint open copies and a remainder, retaining the map to the base.
private theorem split_coproduct_iso {Z V W : Scheme.{u}} (p : Z ⟶ V) (w : W ⟶ V)
    (n : ℕ) (a : Fin n → (V ⟶ Z)) (b : W ⟶ Z)
    [∀ i, IsOpenImmersion (a i)] [IsOpenImmersion b]
    (ha : ∀ i, a i ≫ p = 𝟙 V) (hb : b ≫ p = w)
    (hdisj : Pairwise (fun i j ↦ Disjoint (a i).opensRange (a j).opensRange))
    (hab : ∀ i, Disjoint (a i).opensRange b.opensRange)
    (hcov : (⨆ i, (a i).opensRange) ⊔ b.opensRange = ⊤) :
    ∃ e : Z ≅ (∐ fun _ : Fin n => V) ⨿ W,
      e.hom ≫ coprod.desc (Sigma.desc (fun _ : Fin n => 𝟙 V)) w = p := by
  classical
  have hd : IsOpenImmersion (Sigma.desc a) := by
    apply isOpenImmersion_sigmaDesc
    intro i j hij
    exact TopologicalSpace.Opens.coe_disjoint.mpr (hdisj hij)
  let := hd
  have hr : (Sigma.desc a).opensRange = ⨆ i, (a i).opensRange := by
    apply TopologicalSpace.Opens.ext
    ext z
    change z ∈ Set.range (Sigma.desc a) ↔ _
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨i, x, rfl⟩ := (sigmaOpenCover (fun _ : Fin n => V)).exists_eq v
      change (Sigma.desc a) (Sigma.ι (fun _ : Fin n => V) i x) ∈ _
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      exact (le_iSup (fun i ↦ (a i).opensRange) i) ⟨x, rfl⟩
    · intro hz
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      obtain ⟨x, hx⟩ := hi
      exact ⟨Sigma.ι (fun _ : Fin n => V) i x, by
        simpa [← Scheme.Hom.comp_apply] using hx⟩
  have hcompl : IsCompl (Sigma.desc a).opensRange b.opensRange := by
    rw [hr]
    exact ⟨iSup_disjoint_iff.mpr hab, codisjoint_iff.mpr hcov⟩
  obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl (Sigma.desc a) b hcompl
  let e := hc.coconePointUniqueUpToIso (coprodIsCoprod _ _)
  have hfold : Sigma.desc a ≫ p = Sigma.desc (fun _ : Fin n => 𝟙 V) := by
    apply Sigma.hom_ext
    intro i
    simpa only [Sigma.ι_desc_assoc, Sigma.ι_desc] using ha i
  have he : e.inv ≫ p = coprod.desc (Sigma.desc (fun _ : Fin n => 𝟙 V)) w := by
    apply coprod.hom_ext
    · have hι : coprod.inl ≫ e.inv = Sigma.desc a :=
        IsColimit.comp_coconePointUniqueUpToIso_inv hc (coprodIsCoprod _ _)
          ⟨WalkingPair.left⟩
      rw [← Category.assoc, hι, hfold]
      simp
    · have hι : coprod.inr ≫ e.inv = b :=
        IsColimit.comp_coconePointUniqueUpToIso_inv hc (coprodIsCoprod _ _)
          ⟨WalkingPair.right⟩
      rw [← Category.assoc, hι, hb]
      simp
  refine ⟨e, ?_⟩
  rw [← he]
  simp

-- Restrict each open piece to an open contained in its image.
private theorem split_restrict_clopen {S U T : Scheme.{u}} (f : U ⟶ S) (g : T ⟶ S)
    [Etale f] (t : T) (s : S)
    (n : ℕ) (C : Fin n → (pullback f g).Opens) (R : (pullback f g).Opens)
    (hC : ∀ i, IsOpenImmersion ((C i).ι ≫ pullback.snd f g))
    (hd : Pairwise (fun i j ↦ Disjoint (C i) (C j)))
    (hR : ∀ i, Disjoint R (C i)) (hcov : R ⊔ iSup C = ⊤)
    (hRt : ∀ z : ↥(pullback f g), z ∈ R → pullback.snd f g z ≠ t)
    (B : T.Opens)
    (hB : ∀ i, (B : Set T) ⊆ Set.range ((C i).ι ≫ pullback.snd f g))
    (hBs : ∀ x ∈ B, g x = s ↔ x = t) :
    ∃ (W : Scheme.{u}) (w : W ⟶ B.toScheme) (_ : Etale w),
      ∃ e : pullback f (B.ι ≫ g) ≅ (∐ fun _ : Fin n => B.toScheme) ⨿ W,
        e.hom ≫ coprod.desc (Sigma.desc (fun _ : Fin n => 𝟙 B.toScheme)) w =
          pullback.snd f (B.ι ≫ g) ∧
        ∀ z : W, (w ≫ B.ι ≫ g) z ≠ s := by
  classical
  let p := pullback.snd f g
  let P := pullback p B.ι
  let q : P ⟶ B.toScheme := pullback.snd p B.ι
  let r : P ⟶ pullback f g := pullback.fst p B.ι
  let (i : Fin n) : IsOpenImmersion ((C i).ι ≫ p) := hC i
  let l (i : Fin n) : B.toScheme ⟶ (C i).toScheme :=
    IsOpenImmersion.lift ((C i).ι ≫ p) B.ι (by
      simpa only [Scheme.Opens.range_ι] using hB i)
  have hl (i : Fin n) : l i ≫ (C i).ι ≫ p = B.ι :=
    IsOpenImmersion.lift_fac _ _ _
  let a (i : Fin n) : B.toScheme ⟶ P :=
    pullback.lift (l i ≫ (C i).ι) (𝟙 _) (by simpa using hl i)
  have har (i : Fin n) : a i ≫ r = l i ≫ (C i).ι := pullback.lift_fst _ _ _
  have haq (i : Fin n) : a i ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hlopen (i : Fin n) : IsOpenImmersion (l i) := by
    have : IsOpenImmersion (l i ≫ ((C i).ι ≫ p)) := by rw [hl]; infer_instance
    exact IsOpenImmersion.of_comp _ ((C i).ι ≫ p)
  let (i : Fin n) : IsOpenImmersion (l i) := hlopen i
  have haopen (i : Fin n) : IsOpenImmersion (a i) := by
    have : IsOpenImmersion (a i ≫ r) := by rw [har]; infer_instance
    exact IsOpenImmersion.of_comp _ r
  let (i : Fin n) : IsOpenImmersion (a i) := haopen i
  have hrq (z : P) : p (r z) = B.ι (q z) :=
    congrArg (fun k : P ⟶ T ↦ k z) (pullback.condition (f := p) (g := B.ι))
  have hra (i : Fin n) (z : P) : z ∈ (a i).opensRange ↔ r z ∈ C i := by
    constructor
    · rintro ⟨x, rfl⟩
      change (a i ≫ r) x ∈ C i
      rw [har]
      exact (l i x).property
    · intro hz
      have hx : l i (q z) = (⟨r z, hz⟩ : (C i).toScheme) := by
        apply ((C i).ι ≫ p).isOpenEmbedding.injective
        change (l i ≫ (C i).ι ≫ p) (q z) = p (r z)
        rw [hl]
        exact (hrq z).symm
      refine ⟨q z, r.isOpenEmbedding.injective ?_⟩
      change (a i ≫ r) (q z) = r z
      rw [har]
      exact congrArg (fun x : (C i).toScheme ↦ x.val) hx
  let R' : P.Opens := r ⁻¹ᵁ R
  let b : R'.toScheme ⟶ P := R'.ι
  have hab (i : Fin n) : Disjoint (a i).opensRange b.opensRange := by
    apply disjoint_iff.mpr
    apply TopologicalSpace.Opens.ext
    ext z
    simp only [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot,
      Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hz, hzR⟩
    have hzC := (hra i z).mp hz
    have hzR' : r z ∈ R := by simpa [b, R'] using hzR
    exact (TopologicalSpace.Opens.coe_disjoint.mpr (hR i)).le_bot ⟨hzR', hzC⟩
  have had : Pairwise (fun i j ↦ Disjoint (a i).opensRange (a j).opensRange) := by
    intro i j hij
    apply disjoint_iff.mpr
    apply TopologicalSpace.Opens.ext
    ext z
    simp only [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot,
      Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hi, hj⟩
    exact (TopologicalSpace.Opens.coe_disjoint.mpr (hd hij)).le_bot
      ⟨(hra i z).mp hi, (hra j z).mp hj⟩
  have hacov : (⨆ i, (a i).opensRange) ⊔ b.opensRange = ⊤ := by
    apply top_unique
    intro z _
    have hz : r z ∈ R ⊔ iSup C := by rw [hcov]; trivial
    rcases hz with hz | hz
    · exact Or.inr (by simpa [b, R'] using hz)
    · left
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      exact (le_iSup (fun i ↦ (a i).opensRange) i) ((hra i z).mpr hi)
  let w : R'.toScheme ⟶ B.toScheme := b ≫ q
  obtain ⟨e, he⟩ := split_coproduct_iso q w n a b haq rfl had hab hacov
  let ep := pullbackLeftPullbackSndIso f g B.ι
  refine ⟨R'.toScheme, w, inferInstance, ep.symm ≪≫ e, ?_, ?_⟩
  · change (ep.inv ≫ e.hom) ≫ coprod.desc _ w = _
    rw [Category.assoc, he]
    exact pullbackLeftPullbackSndIso_inv_snd_snd f g B.ι
  · intro z hz
    have hzq : g (B.ι (w z)) = s := hz
    have hqt : B.ι (w z) = t := (hBs _ (w z).property).mp hzq
    apply hRt (r (b z)) z.property
    exact (hrq (b z)).trans hqt

-- The splitting isomorphism identifies the second projection on each copy with the identity.
private theorem split_copy_snd {S U V W : Scheme.{u}} (f : U ⟶ S) (g : V ⟶ S)
    (w : W ⟶ V) (n : ℕ) (e : pullback f g ≅ (∐ fun _ : Fin n => V) ⨿ W)
    (he : e.hom ≫ coprod.desc (Sigma.desc (fun _ : Fin n => 𝟙 V)) w =
      pullback.snd f g) (i : Fin n) :
    Sigma.ι (fun _ : Fin n => V) i ≫ coprod.inl ≫ e.inv ≫ pullback.snd f g = 𝟙 V := by
  rw [← he]
  simp

-- Enumerate lifts by the summands through which their one-point spectra factor.
private theorem split_geometric_lifts {S U V W : Scheme.{u}} (f : U ⟶ S) (g : V ⟶ S)
    (w : W ⟶ V) (n : ℕ) (e : pullback f g ≅ (∐ fun _ : Fin n => V) ⨿ W)
    (he : e.hom ≫ coprod.desc (Sigma.desc (fun _ : Fin n => 𝟙 V)) w =
      pullback.snd f g)
    (Ω : Type u) [Field Ω] (bar_s : Spec (.of Ω) ⟶ S)
    (bar_v : Spec (.of Ω) ⟶ V) (hbar : bar_v ≫ g = bar_s) (s : S)
    (hs : bar_s (IsLocalRing.closedPoint Ω) = s)
    (hW : ∀ x : W, (w ≫ g) x ≠ s) :
    ∃ (a : Fin n → (Spec (.of Ω) ⟶ U)),
      (∀ i : Fin n,
        a i = bar_v ≫ Sigma.ι (fun _ : Fin n => V) i ≫ coprod.inl ≫ e.inv ≫
          pullback.fst f g) ∧
      ∃ (ha : ∀ i : Fin n, a i ≫ f = bar_s),
        ∃ (E : Fin n ≃ {q : Spec (.of Ω) ⟶ U // q ≫ f = bar_s}),
          ∀ i : Fin n, E i = ⟨a i, ha i⟩ := by
  classical
  let c (i : Fin n) : V ⟶ pullback f g :=
    Sigma.ι (fun _ : Fin n => V) i ≫ coprod.inl ≫ e.inv
  have hc (i : Fin n) : c i ≫ pullback.snd f g = 𝟙 V :=
    split_copy_snd f g w n e he i
  let a (i : Fin n) : Spec (.of Ω) ⟶ U := bar_v ≫ c i ≫ pullback.fst f g
  have ha (i : Fin n) : a i ≫ f = bar_s := by
    dsimp [a]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (c i), hc]
    simpa using hbar
  let A (i : Fin n) : {q : Spec (.of Ω) ⟶ U // q ≫ f = bar_s} := ⟨a i, ha i⟩
  have hinj : Function.Injective A := by
    intro i j hij
    have hij' : bar_v ≫ c i = bar_v ≫ c j := by
      apply pullback.hom_ext
      · exact congrArg Subtype.val hij
      · simp [hc]
    have hpoint := congrArg
      (fun k : Spec (.of Ω) ⟶ (∐ fun _ : Fin n => V) ⨿ W ↦
        k (IsLocalRing.closedPoint Ω))
      (congrArg (fun k ↦ k ≫ e.hom) hij')
    have hsig : Sigma.ι (fun _ : Fin n => V) i (bar_v (IsLocalRing.closedPoint Ω)) =
        Sigma.ι (fun _ : Fin n => V) j (bar_v (IsLocalRing.closedPoint Ω)) := by
      apply (coprod.inl : (∐ fun _ : Fin n => V) ⟶
        (∐ fun _ : Fin n => V) ⨿ W).isOpenEmbedding.injective
      simpa [c, Scheme.Hom.comp_apply] using hpoint
    exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp hsig)
  have hsurj : Function.Surjective A := by
    intro q
    let l : Spec (.of Ω) ⟶ pullback f g :=
      pullback.lift q.val bar_v (q.property.trans hbar.symm)
    let k := l ≫ e.hom
    have hk : k ≫ coprod.desc (Sigma.desc (fun _ : Fin n => 𝟙 V)) w = bar_v := by
      dsimp [k]
      rw [Category.assoc, he, pullback.lift_snd]
    obtain ⟨z, hz⟩ := (coprodMk (∐ fun _ : Fin n => V) W).surjective
      (k (IsLocalRing.closedPoint Ω))
    rcases z with z | z
    · obtain ⟨i, v, hv⟩ := (sigmaOpenCover (fun _ : Fin n => V)).exists_eq z
      have hv' : Sigma.ι (fun _ : Fin n => V) i v = z := hv
      have hp : k (IsLocalRing.closedPoint Ω) =
          (Sigma.ι (fun _ : Fin n => V) i ≫
            (coprod.inl : (∐ fun _ : Fin n => V) ⟶ (∐ fun _ : Fin n => V) ⨿ W)) v := by
        calc
          k (IsLocalRing.closedPoint Ω) =
              (coprod.inl : (∐ fun _ : Fin n => V) ⟶ _) z := by
            simpa only [coprodMk_inl] using hz.symm
          _ = (coprod.inl : (∐ fun _ : Fin n => V) ⟶
              (∐ fun _ : Fin n => V) ⨿ W) (Sigma.ι (fun _ : Fin n => V) i v) :=
            congrArg _ hv'.symm
          _ = _ := rfl
      let j : V ⟶ (∐ fun _ : Fin n => V) ⨿ W :=
        Sigma.ι (fun _ : Fin n => V) i ≫ coprod.inl
      have hr : Set.range k ⊆ Set.range j := by
        rintro _ ⟨t, rfl⟩
        have ht : t = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
        exact ⟨v, ht ▸ hp.symm⟩
      let b : Spec (.of Ω) ⟶ V := IsOpenImmersion.lift j k hr
      have hb : b ≫ j = k := IsOpenImmersion.lift_fac _ _ _
      have hb' : b = bar_v := by
        rw [← hk, ← hb]
        simp [j]
      refine ⟨i, Subtype.ext ?_⟩
      change a i = q.val
      have hl : bar_v ≫ c i = l := by
        apply (cancel_mono e.hom).mp
        simpa [c, j, k, hb'] using hb
      change (bar_v ≫ c i) ≫ pullback.fst f g = q.val
      rw [hl, pullback.lift_fst]
    · have hp : k (IsLocalRing.closedPoint Ω) =
          (coprod.inr : W ⟶ (∐ fun _ : Fin n => V) ⨿ W) z := by
        simpa using hz.symm
      apply False.elim
      apply hW z
      have hp' := congrArg (fun m : Spec (.of Ω) ⟶ V ↦
        m (IsLocalRing.closedPoint Ω)) hk
      have : w z = bar_v (IsLocalRing.closedPoint Ω) := by
        simpa [Scheme.Hom.comp_apply, hp, ← Scheme.Hom.comp_apply] using hp'
      change g (w z) = s
      rw [this, ← Scheme.Hom.comp_apply, hbar, hs]
  exact ⟨a, fun _ ↦ rfl, ha, Equiv.ofBijective A ⟨hinj, hsurj⟩, fun _ ↦ rfl⟩

/--
The affine étale splitting of an affine étale morphism near a marked geometric fibre.

Source: literature/stacks-project/etale.tex, Tag 04HM, lemma-etale-etale-local-technical,
applied to all points of the finite fibre; the affine and single-`s`-fibre-point refinement is
the third paragraph of the proof of etale-cohomology.tex Tag 04HU,
lemma-points-small-etale-site; fibre structure from morphisms.tex Tag 02GL,
lemma-etale-over-field (2).
(blueprint: lem-trf-affine-etale-split-neighbourhood)

Proof (the node's steps):
1. `U` is affine, so `f` is separated (lem-weil-pbc-affine-source-morphism-separated); an
   étale morphism is unramified (def-weil-etale-morphism).
2. The fibre `U_s` is affine (lem-weil-pbc-fibre-product-affine-spectra), hence quasi-compact
   (lem-weil-pbc-affine-scheme-qcqs), and discrete
   (lem-weil-pbc-etale-fibre-discrete-separable-points); so `f⁻¹(s)` is finite. List it
   without repetitions as `x₁, …, x_r`, allowing `r = 0` (def-pc-scheme-fibre).
3. Apply lem-weil-pbc-unramified-etale-local-decomposition (Tag 04HI) to `f` and all `xᵢ`:
   an étale `T₀ → S`, a point `t` over `s`, and `U ×_S T₀ = W₀ ⊔ ∐ₐ Pₐ` with each
   `hₐ : Pₐ → T₀` a closed immersion whose image contains `t`, and `(W₀)_t = ∅`.
4. The projection `U ×_S T₀ → T₀` is étale (lem-weil-pbc-etale-scheme-base-change); the
   pieces are open in it, so every `hₐ` and `W₀ → T₀` is étale
   (lem-weil-pbc-etale-composition-cancellation).
5. A closed immersion is a monomorphism (def-weil-closed-immersion).
6. Each `hₐ` is flat, locally of finite presentation and a monomorphism, hence an open
   immersion (lem-pe-flat-lfp-monomorphism-open, Tag 025G) onto an open `Oₐ ∋ t`.
7. Choose an affine open `t ∈ T ⊆ ⋂ₐ Oₐ` (lem-weil-pbc-affine-opens-basis) and restrict
   (lem-weil-pbc-open-fibre-product): `U ×_S T ≅ W_T ⊔ ∐_{a=1}^n T` with `(W_T)_t = ∅`;
   `T → S` is étale.
8. The fibre of `T → S` over `s` is finite and discrete: `t, y₁, …, y_m`.
9. By discreteness `t ∉ closure {y_j}`; choose an affine open `V ∋ t` inside
   `T \ ⋃ⱼ closure {y_j}`. The fibre of `V → S` over `s` is the single point `v = t`, and
   `V → S` is étale.
10. Restrict the decomposition to `V`: `U ×_S V ≅ (∐_{a=1}^n V) ⊔ W` with `W → V` étale;
   a point of `W` over `s` would lie over `v`, which is excluded, so `W` has no point over `s`.
11. Lift `s̄` to `v̄ : Spec Ω → V` with image `v`
   (lem-weil-pbc-etale-cover-geometric-point-lift, Tag 03PR, for the jointly surjective
   family `{V → S, id_S}`); `(V, v̄)` is an affine pointed étale neighbourhood
   (def-weil-pbc-pointed-etale-neighbourhoods).
12. By the universal property of the fibre product, `S`-morphisms `Spec Ω → U` correspond to
   `V`-morphisms `Spec Ω → U ×_S V` over `v̄`; `Spec Ω` has one point, so each factors
   through exactly one piece, never through `W`, and exactly once through each copy of `V`.
   Projecting to `U` gives the bijection `Fin n ≃ Hom_S(Spec Ω, U)`, also for `n = 0`.
-/
theorem exists_affine_etale_split_neighbourhood
    {S U : Scheme.{u}} [IsAffine S] [IsAffine U] (f : U ⟶ S) [Etale f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (bar_s : Spec (.of Ω) ⟶ S) (s : S)
    (hs : bar_s (IsLocalRing.closedPoint Ω) = s) :
    ∃ (V : Scheme.{u}) (g : V ⟶ S) (_ : IsAffine V) (_ : Etale g),
      ∃ (bar_v : Spec (.of Ω) ⟶ V),
        bar_v ≫ g = bar_s ∧
        ∃ (n : ℕ) (W : Scheme.{u}) (w : W ⟶ V) (_ : Etale w),
          ∃ (e : pullback f g ≅ (∐ fun _ : Fin n => V) ⨿ W),
            e.hom ≫ coprod.desc (Sigma.desc (fun _ : Fin n => 𝟙 V)) w =
                pullback.snd f g ∧
            (∀ x : V, g x = s ↔ x = bar_v (IsLocalRing.closedPoint Ω)) ∧
            (∀ x : W, (w ≫ g) x ≠ s) ∧
            ∃ (a : Fin n → (Spec (.of Ω) ⟶ U)),
              (∀ i : Fin n,
                  a i = bar_v ≫ Sigma.ι (fun _ : Fin n => V) i ≫ coprod.inl ≫ e.inv ≫
                    pullback.fst f g) ∧
              ∃ (ha : ∀ i : Fin n, a i ≫ f = bar_s),
                ∃ (E : Fin n ≃
                    {q : Spec (.of Ω) ⟶ U // q ≫ f = bar_s}),
                  ∀ i : Fin n, E i = ⟨a i, ha i⟩ := by
  classical
  let F := f ⁻¹' {s}
  let : Fintype F := (f.finite_preimage_singleton s).fintype
  let r := Fintype.card F
  let x (i : Fin r) : U := ((Fintype.equivFin F).symm i).val
  have hx (i : Fin r) : f (x i) = s := ((Fintype.equivFin F).symm i).property
  have hall (y : U) : f y = s ↔ ∃ i, y = x i := by
    constructor
    · intro hy
      refine ⟨Fintype.equivFin F ⟨y, hy⟩, ?_⟩
      simp [x]
    · rintro ⟨i, rfl⟩
      exact hx i
  have hu (i : Fin r) : ∃ O : U.Opens, x i ∈ O ∧
      LocallyOfFiniteType (O.ι ≫ f) ∧ IsOpenImmersion (pullback.diagonal (O.ι ≫ f)) :=
    ⟨⊤, trivial, inferInstance, inferInstance⟩
  obtain ⟨T, g, t, hg, ht, m, R, C, hRclosed, hCclosed, hd, hRd, hcov, hC, hR, hRt⟩ :=
    exists_etale_closed_immersion_decomposition_of_unramified_at_points f s r x hx hu
  let : Etale g := hg
  let J := Σ i : Fin r, Fin (m i)
  let : Fintype J := inferInstance
  let n := Fintype.card J
  let C' (i : Fin n) := C ((Fintype.equivFin J).symm i)
  have hCopen (i : Fin n) : IsOpenImmersion ((C' i).ι ≫ pullback.snd f g) := by
    let : IsClosedImmersion ((C' i).ι ≫ pullback.snd f g) := (hC _).1
    exact IsOpenImmersion.of_flat_of_mono _
  let (i : Fin n) : IsOpenImmersion ((C' i).ι ≫ pullback.snd f g) := hCopen i
  have hCd : Pairwise (fun i j ↦ Disjoint (C' i) (C' j)) := by
    intro i j hij
    exact hd (fun he ↦ hij ((Fintype.equivFin J).symm.injective he))
  have hCcov : R ⊔ iSup C' = ⊤ := by
    have hi : iSup C' = iSup C := by
      apply le_antisymm
      · exact iSup_le fun i ↦ le_iSup C _
      · apply iSup_le
        intro j
        obtain ⟨i, rfl⟩ := (Fintype.equivFin J).symm.surjective j
        exact le_iSup C' i
    rwa [hi]
  obtain ⟨N, hNo, hN⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (g.isDiscrete_preimage_singleton s) t ht
  let O : T.Opens := ⟨N, hNo⟩ ⊓
    ⨅ i : Fin n, ((C' i).ι ≫ pullback.snd f g).opensRange
  have htN : t ∈ N := by
    have : t ∈ N ∩ g ⁻¹' {s} := by rw [hN]; exact Set.mem_singleton t
    exact this.1
  have htO : t ∈ O := by
    refine ⟨htN, ?_⟩
    change t ∈ ((⨅ i : Fin n,
      ((C' i).ι ≫ pullback.snd f g).opensRange : T.Opens) : Set T)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun i ↦ (hC _).2
  obtain ⟨B, hBaff, htB, hBO⟩ := exists_isAffineOpen_mem_and_subset htO
  let : IsAffine B.toScheme := hBaff
  have hBrange (i : Fin n) : (B : Set T) ⊆
      Set.range ((C' i).ι ≫ pullback.snd f g) := by
    intro y hy
    have hyO := (hBO hy).2
    change y ∈ ((⨅ i : Fin n,
      ((C' i).ι ≫ pullback.snd f g).opensRange : T.Opens) : Set T) at hyO
    rw [TopologicalSpace.Opens.coe_iInf] at hyO
    exact Set.mem_iInter.mp hyO i
  have hBs (y : T) (hy : y ∈ B) : g y = s ↔ y = t := by
    constructor
    · intro hys
      have : y ∈ N ∩ g ⁻¹' {s} := ⟨(hBO hy).1, hys⟩
      rw [hN] at this
      exact this
    · rintro rfl
      exact ht
  obtain ⟨W, w, hw, e, he, hWs⟩ := split_restrict_clopen f g t s n C' R
    hCopen hCd (fun i ↦ hRd _) hCcov (hRt hall) B hBrange hBs
  let : Etale w := hw
  let g' : B.toScheme ⟶ S := B.ι ≫ g
  let v : B.toScheme := ⟨t, htB⟩
  have hv : g' v = bar_s default := by
    change g t = bar_s default
    rw [ht, ← hs]
    congr 1
    exact Subsingleton.elim _ _
  obtain ⟨bar_v, hbar, hbarv⟩ := Scheme.exists_fac_of_etale_of_isSepClosed g' bar_s v hv
  have hbarv' : bar_v (IsLocalRing.closedPoint Ω) = v := by
    exact (congrArg bar_v (Subsingleton.elim _ _)).trans hbarv
  refine ⟨B.toScheme, g', inferInstance, inferInstance, bar_v, hbar,
    n, W, w, hw, e, he, ?_, hWs, ?_⟩
  · intro y
    rw [hbarv']
    change g y.val = s ↔ y = v
    exact (hBs y.val y.property).trans
      ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  · exact split_geometric_lifts f g' w n e he Ω bar_s bar_v hbar s hs hWs

end AlgebraicGeometry
