module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent

/-!
# Effective fpqc descent of a labelled coproduct over an affine chart

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-stratified-lattice-scheme, proof (2); Stacks Tags 0AP6, 0F1U and 0APK
(blueprint: lem-sfb-coproduct-fpqc-effectivity).
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private lemma coproduct_open_inclusion {A B : Scheme.{u}} (b : A ⟶ B)
    [IsOpenImmersion b] {I J : Type v} [Small.{u} I] [Small.{u} J]
    (t : I → J) (ht : Function.Injective t) :
    IsOpenImmersion (Sigma.desc (fun i : I => b ≫ Sigma.ι (fun _ : J => B) (t i))) := by
  apply isOpenImmersion_sigmaDesc
  intro i j hij
  apply Set.disjoint_iff_forall_ne.mpr
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  have h' : Sigma.ι (fun _ : J => B) (t i) (b x) =
      Sigma.ι (fun _ : J => B) (t j) (b y) := by
    simpa only [Scheme.Hom.comp_apply] using h
  exact hij (ht (congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp h')))

private lemma coproduct_open_pullback {A B : Scheme.{u}} (b : A ⟶ B)
    [IsOpenImmersion b] (I : Type v) [Small.{u} I] :
    IsPullback (Sigma.desc (fun i : I => b ≫ Sigma.ι (fun _ : I => B) i))
      (Sigma.desc (fun _ : I => 𝟙 A)) (Sigma.desc (fun _ : I => 𝟙 B)) b := by
  have := coproduct_open_inclusion b (fun i : I => i) Function.injective_id
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · apply Sigma.hom_ext
    intro i
    simp
  · apply TopologicalSpace.Opens.ext
    ext x
    obtain ⟨i, x, rfl⟩ := (sigmaOpenCover (fun _ : I => B)).exists_eq x
    change (Sigma.desc (fun _ : I => 𝟙 B)) (Sigma.ι (fun _ : I => B) i x) ∈
      Set.range b ↔ _
    simp only [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    change x ∈ Set.range b ↔
      (Sigma.ι (fun _ : I => B) i) x ∈
        Set.range (Sigma.desc (fun i : I => b ≫ Sigma.ι (fun _ : I => B) i))
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Sigma.ι (fun _ : I => A) i y, ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, Scheme.Hom.comp_apply]
    · rintro ⟨y, hy⟩
      obtain ⟨j, y, rfl⟩ := (sigmaOpenCover (fun _ : I => A)).exists_eq y
      simp only [sigmaOpenCover_f] at hy
      have he : Sigma.ι (fun _ : I => B) j (b y) =
          Sigma.ι (fun _ : I => B) i x := by
        rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, Scheme.Hom.comp_apply] at hy
        exact hy
      have hi := (sigmaι_eq_iff _ _ _ _ _).mp he
      cases hi
      exact ⟨y, rfl⟩

private lemma compact_coproduct_factor {A T : Scheme.{u}} [CompactSpace T]
    (S : Type v) [Small.{u} S] (q : T ⟶ ∐ fun _ : S => A) [IsOpenImmersion q] :
    ∃ (J : Finset S) (j : T ⟶ ∐ fun _ : J => A), IsOpenImmersion j ∧
      j ≫ Sigma.desc (fun s : J => Sigma.ι (fun _ : S => A) s.val) = q := by
  classical
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover
    (fun s : S => q ⁻¹' Set.range (Sigma.ι (fun _ : S => A) s))
    (fun s => (Sigma.ι (fun _ : S => A) s).isOpenEmbedding.isOpen_range.preimage
      q.continuous) (by
      intro x _
      obtain ⟨s, a, ha⟩ := (sigmaOpenCover (fun _ : S => A)).exists_eq (q x)
      exact Set.mem_iUnion.mpr ⟨s, a, ha⟩)
  let c := Sigma.desc (fun s : J => Sigma.ι (fun _ : S => A) s.val)
  have hc : IsOpenImmersion c := by
    simpa only [Category.id_comp] using
      coproduct_open_inclusion (𝟙 A) (fun s : J => s.val) Subtype.val_injective
  have hr : Set.range q ⊆ Set.range c := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨s, hx⟩ := Set.mem_iUnion.mp (hJ (Set.mem_univ x))
    obtain ⟨hs, a, ha⟩ := Set.mem_iUnion.mp hx
    refine ⟨Sigma.ι (fun _ : J => A) ⟨s, hs⟩ a, ?_⟩
    simpa only [c, ← Scheme.Hom.comp_apply, Sigma.ι_desc] using ha
  exact ⟨J, IsOpenImmersion.lift c q hr, inferInstance,
    IsOpenImmersion.lift_fac c q hr⟩

private lemma coproduct_compact_open {V : Scheme.{u}}
    (S : Type v) [Small.{u} S] :
    ∀ (B : V.Opens), IsAffineOpen B →
      ∀ (K : (pullback (C := Scheme.{u}) (Sigma.desc (fun _ : S => 𝟙 V)) B.ι).Opens),
        IsCompact (K : Set (pullback (C := Scheme.{u}) (Sigma.desc (fun _ : S => 𝟙 V)) B.ι)) →
        ∃ (J : Finset S),
          IsAffine (∐ fun _ : J => B.toScheme) ∧
          (∃ (j : K.toScheme ⟶ ∐ fun _ : J => B.toScheme),
            IsOpenImmersion j ∧
            j ≫ Sigma.desc (fun s : J => B.ι ≫ Sigma.ι (fun _ : S => V) s.val) =
              K.ι ≫ pullback.fst (Sigma.desc (fun _ : S => 𝟙 V)) B.ι ∧
            j ≫ Sigma.desc (fun _ : J => 𝟙 B.toScheme) =
              K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι ∧
            (∀ (B' : B.toScheme.Opens), IsAffineOpen B' →
              IsAffine (∐ fun _ : J => B'.toScheme) ∧
              CompactSpace (pullback (C := Scheme.{u})
                (K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι) B'.ι) ∧
              ∃ (j' : pullback (C := Scheme.{u})
                  (K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι) B'.ι ⟶
                  ∐ fun _ : J => B'.toScheme),
                IsOpenImmersion j' ∧
                j' ≫ Sigma.desc (fun s : J =>
                  B'.ι ≫ Sigma.ι (fun _ : J => B.toScheme) s) =
                  pullback.fst
                    (K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι) B'.ι ≫ j ∧
                j' ≫ Sigma.desc (fun _ : J => 𝟙 B'.toScheme) =
                  pullback.snd
                    (K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι) B'.ι)) ∧
          IsQuasiAffineHom
            (K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι) := by
  classical
  intro B hB K hK
  have : IsAffine B.toScheme := hB
  have : CompactSpace K.toScheme := isCompact_iff_compactSpace.mp hK
  let f := Sigma.desc (fun _ : S => 𝟙 V)
  let c := Sigma.desc (fun s : S => B.ι ≫ Sigma.ι (fun _ : S => V) s)
  let fold := Sigma.desc (fun _ : S => 𝟙 B.toScheme)
  have H := coproduct_open_pullback B.ι S
  let e := H.isoPullback
  let q := K.ι ≫ e.inv
  have : IsOpenImmersion q := inferInstance
  obtain ⟨J, j, hj, hjq⟩ := compact_coproduct_factor S q
  have : IsOpenImmersion j := hj
  have : IsAffine (∐ fun _ : J => B.toScheme) := inferInstance
  let cJ := Sigma.desc (fun s : J => Sigma.ι (fun _ : S => B.toScheme) s.val)
  let foldJ := Sigma.desc (fun _ : J => 𝟙 B.toScheme)
  have hcJ : cJ ≫ c =
      Sigma.desc (fun s : J => B.ι ≫ Sigma.ι (fun _ : S => V) s.val) := by
    apply Sigma.hom_ext
    intro s
    simp [cJ, c]
  have hfoldJ : cJ ≫ fold = foldJ := by
    apply Sigma.hom_ext
    intro s
    simp [cJ, fold, foldJ]
  have hjc : j ≫ Sigma.desc (fun s : J =>
      B.ι ≫ Sigma.ι (fun _ : S => V) s.val) = K.ι ≫ pullback.fst f B.ι := by
    rw [← hcJ, ← Category.assoc, hjq]
    dsimp [q]
    rw [Category.assoc, H.isoPullback_inv_fst]
  have hjfold : j ≫ foldJ = K.ι ≫ pullback.snd f B.ι := by
    rw [← hfoldJ, ← Category.assoc, hjq]
    dsimp [q]
    rw [Category.assoc, H.isoPullback_inv_snd]
  have : QuasiCompact (K.ι ≫ pullback.snd f B.ι) := inferInstance
  have : K.toScheme.IsQuasiAffine := .of_isImmersion j
  refine ⟨J, inferInstance, ⟨j, hj, hjc, hjfold, ?_⟩, inferInstance⟩
  intro B' hB'
  have : IsAffine B'.toScheme := hB'
  have : CompactSpace (pullback (C := Scheme.{u}) (K.ι ≫ pullback.snd f B.ι) B'.ι) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)
  let c' := Sigma.desc (fun s : J => B'.ι ≫ Sigma.ι (fun _ : J => B.toScheme) s)
  let fold' := Sigma.desc (fun _ : J => 𝟙 B'.toScheme)
  have H' := coproduct_open_pullback B'.ι J
  let a := pullback.fst (K.ι ≫ pullback.snd f B.ι) B'.ι
  let b := pullback.snd (K.ι ≫ pullback.snd f B.ι) B'.ι
  have hw : (a ≫ j) ≫ foldJ = b ≫ B'.ι := by
    rw [Category.assoc, hjfold]
    exact pullback.condition
  let j' := H'.lift (a ≫ j) b hw
  have hj'c : j' ≫ c' = a ≫ j := H'.lift_fst _ _ _
  have hj'fold : j' ≫ fold' = b := H'.lift_snd _ _ _
  have Hbig : IsPullback a b (j ≫ foldJ) B'.ι := by
    rw [hjfold]
    exact IsPullback.of_hasPullback _ _
  have Hleft : IsPullback a j' j c' := by
    rw [← hj'fold] at Hbig
    exact IsPullback.of_bot Hbig hj'c.symm H'
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback Hleft hj
  exact ⟨inferInstance, inferInstance, j', inferInstance, hj'c, hj'fold⟩

/-- Every quasi-compact open of the labelled coproduct over an affine open is contained
in a finite affine subcoproduct. The same labels work after restriction to any smaller
affine open, with quasi-compact open inverse image. Its morphism to the affine base is
quasi-affine, and every descent datum on the original coproduct is effective.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-stratified-lattice-scheme, proof (2); Stacks Tags 0AP6, 0F1U and 0APK.
(blueprint: lem-sfb-coproduct-fpqc-effectivity)

Proof:
1. Pulling back the disjoint covering open components identifies the inverse image of
   an affine open B with the coproduct of copies of B. Use def-weil-open-immersion,
   def-pc-fibre-product and lem-weil-pbc-scheme-coproduct-family.
2. The component intersections cover K. By def-weil-pbc-quasi-compact-scheme choose
   finitely many labels J covering K. The finite coproduct D of copies of B is affine
   by lem-weil-pbc-affine-morphism-permanence (4), including the empty coproduct.
   The inclusion of K factors as an open immersion into D.
3. For any affine B' in B the finite coproduct D' of copies of B' is affine by the
   same permanence lemma. Inside D, K and D' are quasi-compact opens; their intersection
   is quasi-compact by lem-weil-pbc-affine-scheme-qcqs. This intersection is the pullback
   K', so it is a quasi-compact open of D'. This verifies
   def-nagata-quasi-affine-morphism for K to B.
4. Apply lem-a1-ind-quasi-affine-fpqc-effective-descent with covering V to X and
   object the labelled coproduct to V. Steps 1--3 give its open condition. Its conclusion
   gives a datum-compatible model over X. Empty labels and empty V are permitted;
   neither quasi-compactness of the whole coproduct nor Noetherianness is used. -/
theorem coproduct_fpqc_effectivity {X V : Scheme.{u}} [IsAffine V]
    (p : V ⟶ X) (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage X)
    (S : Type v) [Small.{u} S]
    (D : Over.DescentDatum p (Over.mk (Sigma.desc (fun _ : S => 𝟙 V)))) :
    (∀ (B : V.Opens), IsAffineOpen B →
      ∀ (K : (pullback (C := Scheme.{u}) (Sigma.desc (fun _ : S => 𝟙 V)) B.ι).Opens),
        IsCompact (K : Set (pullback (C := Scheme.{u}) (Sigma.desc (fun _ : S => 𝟙 V)) B.ι)) →
        ∃ (J : Finset S),
          IsAffine (∐ fun _ : J => B.toScheme) ∧
          (∃ (j : K.toScheme ⟶ ∐ fun _ : J => B.toScheme),
            IsOpenImmersion j ∧
            j ≫ Sigma.desc (fun s : J => B.ι ≫ Sigma.ι (fun _ : S => V) s.val) =
              K.ι ≫ pullback.fst (Sigma.desc (fun _ : S => 𝟙 V)) B.ι ∧
            j ≫ Sigma.desc (fun _ : J => 𝟙 B.toScheme) =
              K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι ∧
            (∀ (B' : B.toScheme.Opens), IsAffineOpen B' →
              IsAffine (∐ fun _ : J => B'.toScheme) ∧
              CompactSpace (pullback (C := Scheme.{u})
                (K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι) B'.ι) ∧
              ∃ (j' : pullback (C := Scheme.{u})
                  (K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι) B'.ι ⟶
                  ∐ fun _ : J => B'.toScheme),
                IsOpenImmersion j' ∧
                j' ≫ Sigma.desc (fun s : J =>
                  B'.ι ≫ Sigma.ι (fun _ : J => B.toScheme) s) =
                  pullback.fst
                    (K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι) B'.ι ≫ j ∧
                j' ≫ Sigma.desc (fun _ : J => 𝟙 B'.toScheme) =
                  pullback.snd
                    (K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι) B'.ι)) ∧
          IsQuasiAffineHom
            (K.ι ≫ pullback.snd (Sigma.desc (fun _ : S => 𝟙 V)) B.ι)) ∧
      D.IsEffective := by
  have h := coproduct_compact_open (V := V) S
  refine ⟨h, ?_⟩
  apply Over.DescentDatum.isEffective_of_indQuasiAffine_fpqc p hp _ D
  intro B hB K hK
  obtain ⟨J, _, _, hq⟩ := h B hB K hK
  exact hq

end AlgebraicGeometry
