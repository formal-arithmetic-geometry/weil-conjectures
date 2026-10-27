module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Stability

/-!
# Returning a flat model principal quotient to an affine chart

Source: Stacks Project, Tag 056Y, `lemma-slice-given-element`, second proof paragraph,
return from the cartesian model (blueprint: lem-trf-model-principal-quotient-return).
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem principalQuotientBaseChange
    {R A B₀ B : Type*} [CommRing R] [CommRing A] [CommRing B₀] [CommRing B]
    [Algebra R A] [Algebra R B₀] [Algebra A B]
    (e : A ⊗[R] B₀ ≃ₐ[A] B) (a₀ g₀ : B₀) (a g : B)
    (ha : a = e (1 ⊗ₜ[R] a₀)) (hg : g = e (1 ⊗ₜ[R] g₀)) :
    ∃ E : A ⊗[R] (Localization.Away g₀ ⧸
          Ideal.span {algebraMap B₀ (Localization.Away g₀) a₀}) ≃ₐ[A]
        (Localization.Away g ⧸ Ideal.span {algebraMap B (Localization.Away g) a}),
      ∀ (c : A) (b₀ : B₀) (n : ℕ),
        E (c ⊗ₜ[R] Ideal.Quotient.mk _
            (algebraMap B₀ (Localization.Away g₀) b₀ *
              IsLocalization.Away.invSelf g₀ ^ n)) =
          Ideal.Quotient.mk _
            (algebraMap B (Localization.Away g)
                (algebraMap A B c * e (1 ⊗ₜ[R] b₀)) *
              IsLocalization.Away.invSelf g ^ n) := by
  let L₀ := IsLocalization.Away.tensorProductEquivTMulRight R A g₀ (Localization.Away g₀)
  let L₁ := IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers ((1 : A) ⊗ₜ[R] g₀)) (T := Submonoid.powers g)
    (Localization.Away ((1 : A) ⊗ₜ[R] g₀)) (Localization.Away g) e
    (by simpa only [Submonoid.map_powers] using congrArg Submonoid.powers hg.symm)
  let L := L₀.trans L₁
  have hL (c : A) (b : B₀) :
      L (c ⊗ₜ[R] algebraMap B₀ (Localization.Away g₀) b) =
        algebraMap B (Localization.Away g) (algebraMap A B c * e (1 ⊗ₜ[R] b)) := by
    simp only [L, AlgEquiv.trans_apply, L₀,
      IsLocalization.Away.tensorProductEquivTMulRight_tmul, L₁,
      IsLocalization.algEquivOfAlgEquiv_eq]
    congr 1
    rw [← e.commutes c, ← map_mul]
    congr 1
    simp
  have hLg : L (1 ⊗ₜ[R] algebraMap B₀ (Localization.Away g₀) g₀) =
      algebraMap B (Localization.Away g) g := by simpa [hg] using hL 1 g₀
  have hLi : L (1 ⊗ₜ[R] (IsLocalization.Away.invSelf g₀ : Localization.Away g₀)) =
      IsLocalization.Away.invSelf g := by
    apply (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).mul_left_cancel
    rw [← hLg, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      IsLocalization.Away.mul_invSelf, ← Algebra.TensorProduct.one_def, map_one,
      hLg, IsLocalization.Away.mul_invSelf]
  let I₀ := Ideal.span {algebraMap B₀ (Localization.Away g₀) a₀}
  let I := I₀.map (Algebra.TensorProduct.includeRight (R := R) (A := A)).toRingHom
  let J := Ideal.span {algebraMap B (Localization.Away g) a}
  have hIJ : J = I.map L.toRingEquiv.toRingHom := by
    simp only [I, I₀, Ideal.map_span, Set.image_singleton, J]
    congr 1
    simpa [ha] using (hL 1 a₀).symm
  let E := (Algebra.TensorProduct.tensorQuotientEquiv (R := R) A
    (Localization.Away g₀) A I₀).trans (Ideal.quotientEquivAlg I J L hIJ)
  refine ⟨E, fun c b₀ n ↦ ?_⟩
  change Ideal.Quotient.mk J
    (L (c ⊗ₜ[R] (algebraMap B₀ (Localization.Away g₀) b₀ *
      IsLocalization.Away.invSelf g₀ ^ n))) = _
  congr 1
  have ht : c ⊗ₜ[R] (algebraMap B₀ (Localization.Away g₀) b₀ *
      IsLocalization.Away.invSelf g₀ ^ n) =
      (c ⊗ₜ[R] algebraMap B₀ (Localization.Away g₀) b₀) *
        (1 ⊗ₜ[R] (IsLocalization.Away.invSelf g₀ : Localization.Away g₀)) ^ n := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one]
  rw [ht, map_mul, map_pow, hL, hLi]

/-- Return the localized principal quotient of a flat model to the original affine chart.
The rings `A` and `B` of the source are written as `Γ(S, V)` and `Γ(X, U₁)`;
`hcompat` says their algebra structure is the one induced by the given morphism.

Source: Stacks Project, Tag 056Y, `lemma-slice-given-element`, second proof paragraph
(blueprint: lem-trf-model-principal-quotient-return).

Proof plan:
1. Use the affine basic-open section and prime lemmas
   (`lem-weil-pbc-affine-open-section-vanishing-prime`) to put `x` in `D(g)`, identify
   this affine open with `Spec B_g`, and use restriction followed by germs to retain the
   germ of `a`. The quotient spectrum is a closed immersion containing `x`, by
   `lem-weil-pbc-spec-quotient-closed-immersion` and
   `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`. The compatibility with the
   original chart follows from `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`.
2. Exchange tensor factors, localize the given isomorphism and its inverse, and use
   `lem-weil-pbc-algebra-localization-away-base-change`,
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`, and
   `lem-weil-pbc-localization-away-universal-property`. This gives the isomorphism from
   `A ⊗ (B₀)_{g₀}` to `B_g`, with the specified fraction formula.
3. Apply `lem-weil-pbc-tensor-quotient-base-change` and the tensor pushout universal
   property to quotient by `a₀`. The resulting isomorphism has the displayed formula;
   `lem-weil-pbc-flat-module-base-change` gives flatness over `A`.
4. Present `B_g` as `B[z]/(gz - 1)` using
   `lem-weil-pbc-localization-away-polynomial-quotient`. Its finite presentation and
   `lem-weil-pbc-finite-presentation-quotient-fg-ideal` give finite presentation of the
   principal quotient over `A`.
5. The induced-ring-map square identifies the actual composite to `S` with the
   spectrum map followed by the inclusion of `V`. Use
   `lem-weil-pbc-affine-open-stalk-localization` and
   `lem-weil-pbc-spec-map-stalk-localization` to identify its stalk maps with
   `A_p → H_P`. Apply `lem-weil-pbc-localization-flat`,
   `lem-weil-pbc-flat-ring-map-comp`, and `lem-weil-pbc-flat-over-localization` to get
   flatness. The charts `Spec H` and `V` give local finite presentation. No condition on
   the morphism outside the chosen charts is used.
-/
theorem modelPrincipalQuotientReturn
    {X S : Scheme.{u}} (f : X ⟶ S) (U₁ : X.Opens) (V : S.Opens)
    (hU₁ : IsAffineOpen U₁) (hV : IsAffineOpen V) (hUV : U₁ ≤ f ⁻¹ᵁ V)
    (A₀ : Type v) (B₀ : Type w) [CommRing A₀] [CommRing B₀]
    [Algebra A₀ Γ(S, V)] [Algebra A₀ B₀] [Algebra Γ(S, V) Γ(X, U₁)]
    (hcompat : algebraMap Γ(S, V) Γ(X, U₁) = (f.appLE V U₁ hUV).hom)
    [Algebra.FinitePresentation Γ(S, V) Γ(X, U₁)]
    (e : Γ(S, V) ⊗[A₀] B₀ ≃ₐ[Γ(S, V)] Γ(X, U₁)) (x : U₁) (a₀ g₀ : B₀)
    (a g : Γ(X, U₁)) (ha : a = e (1 ⊗ₜ[A₀] a₀)) (hg : g = e (1 ⊗ₜ[A₀] g₀))
    (haq : a ∈ (hU₁.primeIdealOf x).asIdeal)
    (hgq : g ∉ (hU₁.primeIdealOf x).asIdeal)
    [Module.Flat A₀ (Localization.Away g₀ ⧸
      Ideal.span {algebraMap B₀ (Localization.Away g₀) a₀})] :
    IsAffineOpen (X.basicOpen g) ∧
    ∃ hxg : x.1 ∈ X.basicOpen g,
      X.presheaf.germ (X.basicOpen g) x.1 hxg
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op a) =
        X.presheaf.germ U₁ x.1 x.2 a ∧
      ∃ i : Spec (CommRingCat.of (Localization.Away g)) ≅ (X.basicOpen g).toScheme,
        i.hom ≫ (X.basicOpen g).ι =
          Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₁) (Localization.Away g))) ≫
            hU₁.fromSpec ∧
        IsClosedImmersion
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}))) ≫ i.hom) ∧
        (∃ y : Spec (CommRingCat.of (Localization.Away g ⧸
            Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a})),
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}))) ≫
              i.hom ≫ (X.basicOpen g).ι) y = x.1) ∧
        Flat (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}))) ≫
            i.hom ≫ (X.basicOpen g).ι ≫ f) ∧
        LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}))) ≫
            i.hom ≫ (X.basicOpen g).ι ≫ f) ∧
        ∃ E : Γ(S, V) ⊗[A₀] (Localization.Away g₀ ⧸
              Ideal.span {algebraMap B₀ (Localization.Away g₀) a₀}) ≃ₐ[Γ(S, V)]
            (Localization.Away g ⧸
              Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}),
          (∀ (c : Γ(S, V)) (b₀ : B₀) (n : ℕ),
            E (c ⊗ₜ[A₀] Ideal.Quotient.mk _
                (algebraMap B₀ (Localization.Away g₀) b₀ *
                  IsLocalization.Away.invSelf g₀ ^ n)) =
              Ideal.Quotient.mk _
                (algebraMap Γ(X, U₁) (Localization.Away g)
                    (algebraMap Γ(S, V) Γ(X, U₁) c * e (1 ⊗ₜ[A₀] b₀)) *
                  IsLocalization.Away.invSelf g ^ n)) ∧
          Module.Flat Γ(S, V) (Localization.Away g ⧸
            Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}) ∧
          Algebra.FinitePresentation Γ(S, V) (Localization.Away g ⧸
            Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}) := by
  obtain ⟨E, hE⟩ := principalQuotientBaseChange e a₀ g₀ a g ha hg
  have hflat : Module.Flat Γ(S, V) (Localization.Away g ⧸
      Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}) :=
    Module.Flat.of_linearEquiv E.symm.toLinearEquiv
  have hfp : Algebra.FinitePresentation Γ(S, V) (Localization.Away g ⧸
      Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  have hxa : hU₁.fromSpec (hU₁.primeIdealOf x) = x.1 := hU₁.fromSpec_primeIdealOf x
  have hxg : x.1 ∈ X.basicOpen g := by
    rw [← hxa]
    change hU₁.primeIdealOf x ∈ hU₁.fromSpec ⁻¹ᵁ X.basicOpen g
    rw [hU₁.fromSpec_preimage_basicOpen]
    exact hgq
  let j := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₁) (Localization.Away g))) ≫
    hU₁.fromSpec
  have hj : Set.range j = (X.basicOpen g : Set X) := by
    change Set.range (hU₁.fromSpec ∘
      PrimeSpectrum.comap (algebraMap Γ(X, U₁) (Localization.Away g))) = _
    rw [Set.range_comp, PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact congrArg (fun W : X.Opens ↦ (W : Set X)) (hU₁.fromSpec_image_basicOpen g)
  let i := IsOpenImmersion.isoOfRangeEq j (X.basicOpen g).ι (by simpa using hj)
  have hi : i.hom ≫ (X.basicOpen g).ι = j :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let J := Ideal.span {algebraMap Γ(X, U₁) (Localization.Away g) a}
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have hpoint : ∃ y : Spec (CommRingCat.of (Localization.Away g ⧸ J)),
      (q ≫ i.hom ≫ (X.basicOpen g).ι) y = x.1 := by
    have hp : hU₁.primeIdealOf x ∈ Set.range
        (PrimeSpectrum.comap (algebraMap Γ(X, U₁) (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hgq
    obtain ⟨p, hp⟩ := hp
    have hap : algebraMap Γ(X, U₁) (Localization.Away g) a ∈ p.asIdeal := by
      change a ∈ (p.comap (algebraMap Γ(X, U₁) (Localization.Away g))).asIdeal
      rw [hp]
      exact haq
    have hyp : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
      rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
      change RingHom.ker (Ideal.Quotient.mk J) ≤ p.asIdeal
      rw [Ideal.mk_ker]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hap)
    obtain ⟨y, hy⟩ := hyp
    refine ⟨y, ?_⟩
    rw [hi]
    change hU₁.fromSpec
      (PrimeSpectrum.comap (algebraMap Γ(X, U₁) (Localization.Away g))
        (PrimeSpectrum.comap (Ideal.Quotient.mk J) y)) = x.1
    rw [hy, hp, hxa]
  have hcomp : q ≫ i.hom ≫ (X.basicOpen g).ι ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) (Localization.Away g ⧸ J))) ≫
        hV.fromSpec := by
    calc
      q ≫ i.hom ≫ (X.basicOpen g).ι ≫ f = q ≫ j ≫ f := by
        rw [← Category.assoc i.hom, hi]
      _ = q ≫ Spec.map
          (CommRingCat.ofHom (algebraMap Γ(X, U₁) (Localization.Away g))) ≫
          Spec.map (f.appLE V U₁ hUV) ≫ hV.fromSpec := by
        rw [IsAffineOpen.SpecMap_appLE_fromSpec f hV hU₁ hUV]
        rfl
      _ = Spec.map (CommRingCat.ofHom
          (algebraMap Γ(S, V) (Localization.Away g ⧸ J))) ≫ hV.fromSpec := by
        rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
        congr 2
        apply CommRingCat.hom_ext
        ext c
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
          ← hcompat, IsScalarTower.algebraMap_apply Γ(S, V) Γ(X, U₁) (Localization.Away g),
          IsScalarTower.algebraMap_apply Γ(S, V) (Localization.Away g)
            (Localization.Away g ⧸ J)]
        rfl
  have hsf : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, V) (Localization.Away g ⧸ J)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  have hsp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, V) (Localization.Away g ⧸ J)))) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr hfp)
  refine ⟨hU₁.basicOpen g, hxg, ?_, i, hi, ?_, hpoint, ?_, ?_, E, hE, hflat, hfp⟩
  · exact X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le g)) x.1 hxg a
  · change IsClosedImmersion (q ≫ i.hom)
    have : IsClosedImmersion q := IsClosedImmersion.spec_of_quotient_mk
      (R := CommRingCat.of (Localization.Away g)) J
    infer_instance
  · rw [hcomp]
    infer_instance
  · rw [hcomp]
    infer_instance

end AlgebraicGeometry
