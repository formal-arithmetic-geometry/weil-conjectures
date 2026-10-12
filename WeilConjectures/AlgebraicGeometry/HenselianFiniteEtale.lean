/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.HenselianConnectedness
public import WeilConjectures.AlgebraicGeometry.IdempotentBasicOpen
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Section
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.RepresentableLocallyConstant
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Topology.SpectralSpace.ClopenExtension

/-!
# Finite étale schemes over a proper scheme over a henselian pair

Let `(A, I)` be a henselian pair, `f : Y ⟶ Spec A` a proper morphism and
`Y₀ = Y ×_A A/I` its closed fibre, with closed immersion `i : Y₀ ⟶ Y`. The closed fibre
controls the "discrete" invariants of `Y`:

* the idempotents of `Γ(Y, 𝒪_Y)` and of `Γ(Y₀, 𝒪_{Y₀})` correspond under restriction, i.e.
  the open and closed subschemes of `Y` and `Y₀` correspond;
* base change along `i` is an equivalence between the categories of finite étale schemes
  over `Y` and over `Y₀`;
* restriction is a bijection `H¹(Y, M) ≃ H¹(Y₀, M)` for every finite abelian group `M`.

The last statement goes through the dictionary between finite locally constant sheaves of
sets on the small étale site of a scheme and finite étale schemes over it, which is also
recorded here.

The category of finite étale `Y`-schemes is `(@IsFinite ⊓ @Etale).Over ⊤ Y`, and base
change along `i` is `CategoryTheory.MorphismProperty.Over.pullback`. The closed fibre is
given by a cartesian square
```
Y₀ ---i---> Y
|           |
f₀          f
v           v
Spec A/I --> Spec A
```

## Main statements

- `AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing`: idempotent lifting
  for the structure sheaf of a proper scheme over a henselian pair.
- `AlgebraicGeometry.Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing`:
  finite étale lifting over a proper scheme over a henselian pair.
- `AlgebraicGeometry.Scheme.isEquivalence_pullback_finiteEtale_of_henselianLocalRing`:
  the same over a henselian local ring and its residue field.
- `AlgebraicGeometry.Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso`: the sheaf of
  sections of a finite étale scheme is finite locally constant, and every finite locally
  constant sheaf of sets is of this form.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_one_constantSheaf_of_henselianRing`:
  the `H¹` comparison for a finite constant sheaf.

## References

- Stacks Project, Section 59.91, <https://stacks.math.columbia.edu/tag/0A3S>
- Stacks Project, Étale Cohomology, Section "Locally constant sheaves" (finite locally
  constant sheaves of sets and finite étale schemes)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ### Auxiliary lemmas -/

/-- Finite étale morphisms are stable under base change. -/
instance isStableUnderBaseChange_isFinite_inf_etale :
    (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- A sheaf of sets `E` on the small étale site of `T` is *finite locally constant* if there
is an étale cover of `T` (`AlgebraicGeometry.Scheme.etalePrecoverage`) such that the
restriction of `E` to each member of the cover is constant, and the stalks of `E` at all
geometric points are finite. This is the analogue for sheaves of sets of
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf`, which is stated for abelian
coefficients. -/
def Scheme.IsFiniteLocallyConstantSheafOfTypes {T : Scheme.{u}}
    (E : Sheaf T.smallEtaleTopology (Type (u + 1))) : Prop :=
  (∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage T, ∀ i,
    (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))) ∧ Scheme.IsFiniteSheaf E

/-! ### Finite locally constant sheaves and finite étale schemes -/

/-- **Finite locally constant sheaves of sets are finite étale schemes.** For a scheme `T`:

* for every finite étale `π : P ⟶ T`, the presheaf of sections `U ↦ Hom_T(U, P)` on the small
  étale site (the Yoneda presheaf of `P`, viewed as an étale `T`-scheme) is a sheaf, and it
  is finite locally constant;
* every finite locally constant sheaf of sets `E` is isomorphic to the sheaf of sections of
  a finite étale `T`-scheme.

These are the two object-level halves of the blueprint node. Together with the Yoneda lemma
(morphisms of the sheaves of sections are `T`-morphisms) they give the equivalence between
finite étale `T`-schemes and finite locally constant sheaves of sets, and with it the
statement about finite group actions; neither is stated here.
(blueprint: `lemma-weil-pbc-finite-locally-constant-etale-equivalence`) -/
theorem Scheme.isFiniteLocallyConstant_yoneda_and_exists_iso (T : Scheme.{u}) :
    (∀ (P : Scheme.{u}) (π : P ⟶ T) [IsFinite π] [Etale π],
      ∃ h : Presheaf.IsSheaf T.smallEtaleTopology (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk π)),
        IsFiniteLocallyConstantSheafOfTypes ⟨_, h⟩) ∧
    ∀ E : Sheaf T.smallEtaleTopology (Type (u + 1)), IsFiniteLocallyConstantSheafOfTypes E →
      ∃ (P : Scheme.{u}) (π : P ⟶ T) (_ : IsFinite π) (_ : Etale π),
        Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Scheme.Etale.mk π)) := by
  refine ⟨fun P π _ _ ↦ ?_, fun E hE ↦ ?_⟩
  · let X : T.Etale := Scheme.Etale.mk π
    have : IsFinite X.hom := ‹IsFinite π›
    refine ⟨(T.smallEtaleTopology.uliftYoneda.{u + 1}.obj X).property, ?_, ?_⟩
    · choose U g hg S hS fst hy hpb using
        fun y ↦ FiniteEtale.exists_etale_isPullback_sigma ⟨X, this⟩ y
      let 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage T :=
        Scheme.Cover.mkOfCovers T U g (fun y ↦ ⟨y, hy y⟩) hg
      exact ⟨𝒰, fun y ↦ Etale.isConstant_over_uliftYoneda_of_isPullback (hpb y)⟩
    · exact ⟨fun Ω _ _ s ↦ (ConcreteCategory.isFinitelyGenerated_iff_finite _).2
        (Etale.finite_sheafFiber_uliftYoneda X s)⟩
  · obtain ⟨𝒰, h𝒰⟩ := hE.1
    obtain ⟨X, hX, ⟨r⟩⟩ := Etale.exists_representableBy_of_isConstant E 𝒰 h𝒰 hE.2
    exact ⟨X.left, X.hom, hX, X.prop,
      ⟨((Functor.RepresentableBy.equivUliftYonedaIso _ _) r).symm⟩⟩

section Henselian

variable {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
  {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
  (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))

omit [HenselianRing A I] [IsProper f] in
include I in
/-- The closed fibre of a scheme over `Spec A` over `Spec A/I` is a closed immersion. -/
lemma Scheme.isClosedImmersion_of_isPullback_quotient
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    IsClosedImmersion i :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
    (IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective)

omit [HenselianRing A I] [IsProper f] in
/-- The closed fibre of a scheme `Y` over `Spec A` over `Spec A/I` has image `f⁻¹ V(I)`. -/
lemma Scheme.range_of_isPullback_quotient
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    Set.range i = f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
  have hq : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
    have := range_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker] at this
    exact this
  rw [← hq, ← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.2 h.isoPullback.hom.surjective,
    Set.image_univ]

/-- Over a henselian pair, an open subset of a proper `Y` containing the closed fibre is all of
`Y`: its complement is closed, hence meets the closed fibre if it is nonempty. -/
lemma Scheme.eq_top_of_range_subset_of_henselianRing
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) {U : Y.Opens}
    (hU : Set.range i ⊆ (U : Set Y)) : U = ⊤ := by
  by_contra hne
  have hne' : ((U : Set Y)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact fun h' ↦ hne (SetLike.coe_injective (h'.trans TopologicalSpace.Opens.coe_top.symm))
  obtain ⟨y, hyU, hy⟩ := f.nonempty_inter_preimage_zeroLocus I HenselianRing.jac
    U.isOpen.isClosed_compl hne'
  rw [← Scheme.range_of_isPullback_quotient I f i f₀ h] at hy
  exact hyU (hU hy)

/-- **Clopen lifting over a henselian pair.** Every open and closed subset of the closed fibre
`Y₀` of a proper `Y` over a henselian pair is the preimage of an open and closed subset of `Y`.
This is the clopen extension `exists_isClopen_inter_eq_of_isConnected_inter` applied to the
closed fibre, whose hypothesis is the connectedness input
`AlgebraicGeometry.Scheme.Hom.spectralSpace_and_isClosed_and_isConnected_inter`. -/
lemma Scheme.exists_isClopen_preimage_eq_of_henselianRing
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    {U₀ : Set Y₀} (hU₀ : IsClopen U₀) :
    ∃ U : Set Y, IsClopen U ∧ i ⁻¹' U = U₀ := by
  have hi := Scheme.isClosedImmersion_of_isPullback_quotient I f i f₀ h
  have hrange := Scheme.range_of_isPullback_quotient I f i f₀ h
  obtain ⟨_, -, hC⟩ := f.spectralSpace_and_isClosed_and_isConnected_inter I
  have hinj : Function.Injective i := i.isClosedEmbedding.injective
  have hAT : i '' U₀ ⊆ f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) :=
    hrange ▸ Set.image_subset_range _ _
  have hB : f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) \ i '' U₀ = i '' U₀ᶜ := by
    rw [Set.image_compl_eq_range_sdiff_image hinj, hrange]
  obtain ⟨U, hU, hUA⟩ := exists_isClopen_inter_eq_of_isConnected_inter hC hAT
    (i.isClosedEmbedding.isClosedMap _ hU₀.isClosed)
    (hB ▸ i.isClosedEmbedding.isClosedMap _ hU₀.isOpen.isClosed_compl)
  refine ⟨U, hU, Set.ext fun z ↦ ?_⟩
  have hz : i z ∈ f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := hrange ▸ Set.mem_range_self z
  change i z ∈ U ↔ z ∈ U₀
  rw [← hinj.mem_set_image, ← hUA]
  exact ⟨fun h ↦ ⟨h, hz⟩, fun h ↦ h.1⟩

/-- **Rigidity over a henselian pair.** Two morphisms `a b : Y ⟶ W` from a proper `Y` over a
henselian pair into a scheme `W` unramified over `Z`, which agree over `Z` and on the closed
fibre `Y₀`, are equal: the open locus where they agree contains the closed fibre. -/
lemma Scheme.eq_of_comp_eq_of_henselianRing
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    {W Z : Scheme.{u}} (p : W ⟶ Z) [FormallyUnramified p] [LocallyOfFiniteType p]
    {a b : Y ⟶ W} (hab : a ≫ p = b ≫ p)
    (hi : i ≫ a = i ≫ b) : a = b := by
  have hE := Scheme.eq_top_of_range_subset_of_henselianRing I f i f₀ h
    (FormallyUnramified.range_subset_eqLocus p a b hab i hi)
  have key : (⊤ : Y.Opens).ι ≫ a = (⊤ : Y.Opens).ι ≫ b := by
    rw [← Y.isoOfEq_hom_ι hE.symm, Category.assoc, Category.assoc,
      FormallyUnramified.eqLocus_ι_comp_eq]
  rwa [← Scheme.topIso_hom, cancel_epi] at key

/-- **Isomorphisms lift over a henselian pair.** A finite étale morphism `p : W ⟶ Y` to a proper
`Y` over a henselian pair whose base change to the closed fibre is an isomorphism is an
isomorphism: its rank is locally constant and equal to `1` along the closed fibre. -/
lemma Scheme.isIso_of_isPullback_of_henselianRing
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    {W W₀ : Scheme.{u}} (p : W ⟶ Y) [IsFinite p] [Etale p]
    (p₀ : W₀ ⟶ Y₀) (j : W₀ ⟶ W) (hp : IsPullback j p₀ p i) [IsIso p₀] : IsIso p := by
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  let U : Y.Opens := ⟨{y | p.finrank y = 1}, p.isLocallyConstant_finrank.isOpen_fiber 1⟩
  have hU := Scheme.eq_top_of_range_subset_of_henselianRing I f i f₀ h (U := U) (by
    rintro _ ⟨y₀, rfl⟩
    change p.finrank (i y₀) = 1
    rw [← Scheme.Hom.finrank_of_isPullback j p₀ p i hp, Scheme.Hom.finrank_eq_one_of_isIso]
    rfl)
  funext y
  have : y ∈ U := hU ▸ trivial
  exact this

/-- **Sections lift over a henselian pair.** Let `π : Z ⟶ Y` be finite étale over a proper `Y`
over a henselian pair, with closed fibre `i : Y₀ ⟶ Y`. Every section `σ₀` of the base change
`Z ×_Y Y₀ ⟶ Y₀` is the restriction of a section `s` of `π`.

The image of `σ₀` is open and closed, hence the closed fibre of an open and closed `U ⊆ Z`
(`AlgebraicGeometry.Scheme.exists_isClopen_preimage_eq_of_henselianRing` for the proper scheme
`Z`); then `U ⟶ Y` is finite étale and an isomorphism over `Y₀`, hence an isomorphism
(`AlgebraicGeometry.Scheme.isIso_of_isPullback_of_henselianRing`), and its inverse is `s`. -/
lemma Scheme.exists_section_of_henselianRing
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    {Z : Scheme.{u}} (π : Z ⟶ Y) [IsFinite π] [Etale π] (σ₀ : Y₀ ⟶ pullback π i)
    (hσ₀ : σ₀ ≫ pullback.snd π i = 𝟙 Y₀) :
    ∃ s : Y ⟶ Z, s ≫ π = 𝟙 Y ∧ i ≫ s = σ₀ ≫ pullback.fst π i := by
  have hZ : IsPullback (pullback.fst π i) (pullback.snd π i ≫ f₀) (π ≫ f)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    (IsPullback.of_hasPullback π i).paste_vert h
  have : IsOpenImmersion σ₀ := IsOpenImmersion.of_section_of_etale (pullback.snd π i) σ₀ hσ₀
  have : IsClosedImmersion σ₀ :=
    IsClosedImmersion.of_section_of_isSeparated (pullback.snd π i) σ₀ hσ₀
  have hcl : IsClopen (Set.range σ₀) :=
    ⟨σ₀.isClosedEmbedding.isClosed_range, σ₀.isOpenEmbedding.isOpen_range⟩
  obtain ⟨U, hU, hUpre⟩ := Scheme.exists_isClopen_preimage_eq_of_henselianRing I (π ≫ f)
    (pullback.fst π i) (pullback.snd π i ≫ f₀) hZ hcl
  let V : Z.Opens := ⟨U, hU.isOpen⟩
  have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by rw [V.range_ι]; exact hU.isClosed)
  let p := V.ι ≫ π
  let V₀ := pullback.fst π i ⁻¹ᵁ V
  let p₀ := V₀.ι ≫ pullback.snd π i
  have hp : IsPullback (pullback.fst π i ∣_ V) p₀ p i :=
    (isPullback_morphismRestrict (pullback.fst π i) V).paste_vert (IsPullback.of_hasPullback π i)
  have hσV : Set.range σ₀ ⊆ Set.range V₀.ι := by
    rw [V₀.range_ι]
    exact hUpre.symm.subset
  let σ₀' := IsOpenImmersion.lift V₀.ι σ₀ hσV
  have hσ₀' : σ₀' ≫ V₀.ι = σ₀ := IsOpenImmersion.lift_fac _ _ _
  have hσp : σ₀' ≫ p₀ = 𝟙 Y₀ := by
    rw [← Category.assoc, hσ₀', hσ₀]
  have : IsIso σ₀' := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨?_, ⟨fun v ↦ ?_⟩⟩
    · have : IsOpenImmersion (σ₀' ≫ V₀.ι) := by rw [hσ₀']; infer_instance
      exact IsOpenImmersion.of_comp σ₀' V₀.ι
    · have hv : V₀.ι v ∈ Set.range σ₀ := by
        rw [← hUpre]
        exact v.2
      obtain ⟨y, hy⟩ := hv
      refine ⟨y, V₀.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hσ₀', hy]
  have : IsIso p₀ := by
    have : IsIso (σ₀' ≫ p₀) := by rw [hσp]; infer_instance
    exact IsIso.of_isIso_comp_left σ₀' p₀
  have : IsIso p := Scheme.isIso_of_isPullback_of_henselianRing I f i f₀ h p p₀ _ hp
  refine ⟨inv p ≫ V.ι, by simp [p], ?_⟩
  let τ₀ : Y₀ ⟶ V₀ := hp.lift (i ≫ inv p) (𝟙 Y₀) (by simp)
  have hτ₀ : τ₀ = σ₀' := by
    rw [← cancel_mono p₀, hσp]
    exact hp.lift_snd _ _ _
  have h₁ : i ≫ inv p = τ₀ ≫ (pullback.fst π i ∣_ V) := (hp.lift_fst _ _ _).symm
  rw [← Category.assoc, h₁, Category.assoc, morphismRestrict_ι, hτ₀, ← Category.assoc, hσ₀']

/-- **Idempotent lifting for the structure sheaf over a henselian pair.** Let `(A, I)` be a
henselian pair, `f : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre over `Spec A/I`.
Then restriction `Γ(Y, 𝒪_Y) ⟶ Γ(Y₀, 𝒪_{Y₀})` induces a bijection between the idempotents
of the two rings; equivalently the open and closed subschemes of `Y₀` are exactly the closed
fibres of those of `Y`. The restriction map itself need not be bijective.
(blueprint: `thm-weil-pbc-henselian-idempotent-lifting`) -/
@[stacks 0A0B]
theorem Scheme.bijective_appTop_idempotent_of_henselianRing
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    Function.Bijective (fun e : {e : Γ(Y, ⊤) // IsIdempotentElem e} ↦
      (⟨i.appTop.hom e.1, e.2.map i.appTop.hom⟩ : {e : Γ(Y₀, ⊤) // IsIdempotentElem e})) := by
  have hi := Scheme.isClosedImmersion_of_isPullback_quotient I f i f₀ h
  have hrange := Scheme.range_of_isPullback_quotient I f i f₀ h
  obtain ⟨_, -, hC⟩ := f.spectralSpace_and_isClosed_and_isConnected_inter I
  set T₀ := f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)
  have hinj : Function.Injective i := i.isClosedEmbedding.injective
  have hpre (e : Γ(Y, ⊤)) : i ⁻¹' (Y.basicOpen e : Set Y) = Y₀.basicOpen (i.appTop e) := by
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  refine ⟨fun ⟨e, he⟩ ⟨e', he'⟩ hee ↦ ?_, fun ⟨e₀, he₀⟩ ↦ ?_⟩
  · have hee' : i.appTop e = i.appTop e' := congrArg Subtype.val hee
    have hsub {a b : Γ(Y, ⊤)} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
        (hab : i.appTop a = i.appTop b) : (Y.basicOpen a : Set Y) ⊆ Y.basicOpen b := by
      rw [← Set.sdiff_eq_empty]
      by_contra hne
      have hS := (Scheme.isClopen_basicOpen_of_isIdempotentElem ha).diff
        (Scheme.isClopen_basicOpen_of_isIdempotentElem hb)
      obtain ⟨y, ⟨hya, hyb⟩, hyT⟩ := f.nonempty_inter_preimage_zeroLocus I HenselianRing.jac
        hS.isClosed (Set.nonempty_iff_ne_empty.2 hne)
      obtain ⟨z, rfl⟩ : y ∈ Set.range i := hrange ▸ hyT
      have h₁ : z ∈ i ⁻¹' (Y.basicOpen a : Set Y) := hya
      rw [hpre, hab, ← hpre] at h₁
      exact hyb h₁
    refine Subtype.ext (Scheme.eq_of_basicOpen_eq_of_isIdempotentElem he he' ?_)
    exact SetLike.coe_injective ((hsub he he' hee').antisymm (hsub he' he hee'.symm))
  · let U₀ : Set Y₀ := Y₀.basicOpen e₀
    have hU₀ : IsClopen U₀ := Scheme.isClopen_basicOpen_of_isIdempotentElem he₀
    have hAT : i '' U₀ ⊆ T₀ := hrange ▸ Set.image_subset_range _ _
    have hB : T₀ \ i '' U₀ = i '' U₀ᶜ := by
      rw [Set.image_compl_eq_range_sdiff_image hinj, hrange]
    obtain ⟨U, hU, hUA⟩ := exists_isClopen_inter_eq_of_isConnected_inter hC hAT
      (i.isClosedEmbedding.isClosedMap _ hU₀.isClosed)
      (hB ▸ i.isClosedEmbedding.isClosedMap _ hU₀.isOpen.isClosed_compl)
    obtain ⟨e, he, hDe⟩ := Scheme.exists_isIdempotentElem_basicOpen_eq hU
    refine ⟨⟨e, he⟩, Subtype.ext (Scheme.eq_of_basicOpen_eq_of_isIdempotentElem
      (he.map i.appTop.hom) he₀ (SetLike.coe_injective ?_))⟩
    change (Y₀.basicOpen (i.appTop e) : Set Y₀) = U₀
    rw [← hpre, hDe]
    ext z
    have hz : i z ∈ T₀ := hrange ▸ Set.mem_range_self z
    change i z ∈ U ↔ z ∈ U₀
    rw [← hinj.mem_set_image, ← hUA]
    exact ⟨fun h ↦ ⟨h, hz⟩, fun h ↦ h.1⟩

/-- **Finite étale lifting over a proper scheme over a henselian pair.** Let `(A, I)` be a
henselian pair, `f : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre over `Spec A/I`.
Then base change along `i` is an equivalence from the category of finite étale `Y`-schemes
to the category of finite étale `Y₀`-schemes. In particular morphisms, and hence finite
group actions (finitely many automorphisms subject to finitely many equations), lift
uniquely.
(blueprint: `thm-weil-pbc-finite-etale-lifting`) -/
@[stacks 0A48]
theorem Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence :=
  sorry

end Henselian

/-- **Finite étale lifting over a henselian local ring.** Let `A` be a henselian local ring,
`f : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre over the residue field. Then base
change along `i` is an equivalence from the category of finite étale `Y`-schemes to the
category of finite étale `Y₀`-schemes; in particular morphisms and finite group actions
lift uniquely. This is the case `I = 𝔪` of
`AlgebraicGeometry.Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing`.
(blueprint: `lemma-weil-pbc-finite-etale-henselian-lifting`) -/
theorem Scheme.isEquivalence_pullback_finiteEtale_of_henselianLocalRing
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
    (f₀ : Y₀ ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence :=
  Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing (IsLocalRing.maximalIdeal A) f i
    f₀ h

/-- **The `H¹` comparison for a finite constant sheaf over a henselian pair.** Let `(A, I)` be
a henselian pair, `f : Y ⟶ Spec A` proper and `i : Y₀ ⟶ Y` the closed fibre over `Spec A/I`.
For every finite abelian group `M`, restriction `H¹(Y, M) ⟶ H¹(Y₀, M)` along `i` is
bijective. Both sides classify `M`-torsors, i.e. finite étale schemes with a simply
transitive `M`-action (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_quotientEquivSheafH`),
and these correspond under the finite étale lifting
`AlgebraicGeometry.Scheme.isEquivalence_pullback_finiteEtale_of_henselianRing`.
(blueprint: `lemma-weil-pbc-h1-torsor-comparison`) -/
theorem Etale.bijective_cohomologyMap_one_constantSheaf_of_henselianRing
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
    (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] :
    Function.Bijective (Etale.cohomologyMap i
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) 1) :=
  sorry

end AlgebraicGeometry
