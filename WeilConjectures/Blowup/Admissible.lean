/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Exceptional
public import WeilConjectures.Blowup.Proper
public import WeilConjectures.Blowup.BlowupUniversal
public import WeilConjectures.Blowup.FiniteDegree
public import WeilConjectures.Compactification.FiniteTypeExtension
public import WeilConjectures.Compactification.StrictTransform

/-!

# Admissible blow-ups and boundary separation

This file records the admissible blow-up vocabulary and the boundary-separation
interface of the proof of Nagata's compactification theorem, following the *revised*
blueprint (`blueprint/src/version/detailed/nagata/nagata_new.tex`).

## Route

The development follows the Stacks Project route (Tags 080A/0807/080B/080L/0F3V,
then 081S/0F3X–0F3Z). The revision of the blueprint recorded there concerns the
*comparison* step only: the comparison of blow-ups after a boundary separation is
obtained from blow-ups of sums of ideals (Tag 0F3V) instead of from the module
flattening of Tags 081P/081L, so none of the results *in this file* needs flattening.

This is not the same thing as a flattening-free proof of Nagata's theorem. The
elimination of indeterminacy, Stacks Tag 081S
(`AlgebraicGeometry.exists_admissibleBlowup_strictTransform_open` in
`WeilConjectures.Compactification.Modification`), is still proved by
Raynaud–Gruson flattening (Tags 0815 and 081R), and it is the load-bearing input of
the whole modification layer (Tags 0F3X, 0F3Y, 0F3Z, 0F3W) and hence of the two-open
theorem. Those flattening theorems are **not yet stated anywhere in this
development**: Tag 081S is currently the one primitive obligation, and closing it
requires either formalising Tags 0815/081R or replacing the modification layer
wholesale by a flattening-free argument (Deligne–Conrad, Lütkebohmert). See the
module docstring of `WeilConjectures.Compactification.Modification` and the
"Route revision" note of
`blueprint/src/version/detailed/nagata/nagata_new_proof_order.md`.

## Definitions

- `AlgebraicGeometry.AdmissibleBlowup`: a `U`-admissible blow-up datum: a finite-type
  quasi-coherent ideal whose support is disjoint from `U`, together with a morphism
  identified with the blow-up of that ideal (blueprint: `def:nagata-admissible-blowup`);
- `AlgebraicGeometry.separationBlowup`: the boundary-separation blow-up of the sum of
  two center ideals (revised blueprint: `def:nagata-separate-closed-subschemes`).

The predicates `Scheme.IdealSheafData.FiniteType` and
`Scheme.IdealSheafData.IsEffectiveCartier`, the extended ideal
`Scheme.IdealSheafData.extendedToBlowup` and the principalization theorem
`Scheme.IdealSheafData.extendedToBlowup_isEffectiveCartier`
(blueprint: `thm:nagata-blowup-principalizes-center`) are provided by
`WeilConjectures.Blowup.Exceptional`.

## Proved results

- `AlgebraicGeometry.AdmissibleBlowup.isIso_π_restrict`: a `U`-admissible blow-up is an
  isomorphism over `U` (blueprint: `lemma:nagata-admissible-blowup-over-open`);
- separatedness, quasi-compactness and local finite type of the strict transform along
  an admissible blow-up, inherited from the transformed morphism;
- `AlgebraicGeometry.exists_admissibleBlowup_cartierBoundary` and its locally
  Noetherian variant `exists_admissibleBlowup_cartierBoundary_of_locallyNoetherian`,
  both specialisations of `exists_admissibleBlowup_cartierBoundary_of_ideal`:
  preparation of a Cartier boundary (`lemma:nagata-cartier-boundary-preparation`,
  Stacks Tag 080Y);
- `AlgebraicGeometry.separationBlowup` together with its `U`-admissibility
  (`coe_support_sup_subset`);
- `Scheme.exists_finiteType_ideal_extension`: finite-type ideals extend from
  quasi-compact opens (`def:nagata-finite-type-ideal-extension`, Stacks Tag 01PF),
  from the gluing induction `Scheme.IdealSheafData.exists_finiteType_le_comap_eq` of
  `WeilConjectures.Compactification.FiniteTypeExtension` (proof order item 26,
  `blueprint/src/version/detailed/nagata/nagata_new_proof_order.md`);
- `Scheme.exists_finiteType_ideal_zeroLocus_compl_qcOpen`: a quasi-compact open of a
  qcqs scheme is the complement of the vanishing locus of a finite-type ideal
  (`def:nagata-qc-open-complement-ideal`, Stacks Tag 01PH), by applying the same
  gluing induction inside the vanishing ideal of the reduced boundary;
- `AdmissibleBlowup.exists_comp`: a composite of admissible blow-ups is an admissible
  blow-up (`lemma:nagata-admissible-blowup-comp`, Stacks Tag 080L), derived — via the
  image/preimage disjointness of the composite center — from the composition theorem
  for arbitrary blow-ups `Scheme.IdealSheafData.exists_blowup_comp` below;
- `Scheme.IdealSheafData.exists_blowup_comp`: the composition theorem for arbitrary
  blow-ups (`thm:nagata-composition-of-blowups`, Stacks Tag 080B), in existential
  interface form. The composite center is `K = I * L` for the finite-degree descent
  `L` of the second center; finite-typeness, the support formula and the comparison of
  blow-ups (product comparison, then removal of the effective Cartier exceptional
  factor `(I.comap π)^d` of `L.comap π`) are assembled here from the finite-degree
  descent and the two universal-property comparisons below;
- `Scheme.IdealSheafData.exists_blowup_mul_iso`: the product-ideal comparison
  `Bl_{I·L}(X) ≅ Bl_{L·O}(Bl_I X)` over `X` (`thm:nagata-blowup-product-ideal`,
  Stacks Tag 080A), and
  `Scheme.IdealSheafData.exists_blowup_mul_isEffectiveCartier_iso`: multiplying a
  center by an effective Cartier ideal does not change the blow-up
  (`lemma:nagata-blowup-invertible-factor`, Stacks Tag 0807); both are proved from
  the universal property of blowing up (Tag 0806) and the effective Cartier kit of
  `WeilConjectures.Blowup.BlowupUniversal`;
- `separationBlowup_disjoint_strictTransforms`: disjointness of strict transforms
  after the separation blow-up (`lemma:nagata-separate-closed-subschemes`, Stacks
  Tag 0F3V), by the chart-level argument of the revised blueprint: the charts of
  `Bl_{I₁ ⊔ I₂}` at degree-one elements coming from local sections of `I₁` or `I₂`
  cover the blow-up (`Scheme.IdealSheafData.exists_mem_range_chart_sup`), and the
  strict transform of `V(Iᵢ)` misses every `Iᵢ`-chart because there the extended
  center is generated by a section of `Iᵢ`
  (`Scheme.IdealSheafData.disjoint_range_strictTransformMap_of_probe`); the
  quasi-compactness inputs are `AffineBlowup.compactSpace_of_fg`,
  `Scheme.IdealSheafData.quasiCompact_blowupMap` and
  `Scheme.IdealSheafData.isCompact_coe_compl_support`.

## Further inputs (Stacks citations of the revised blueprint)

The finite-degree approximation on the blow-up itself
(`Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup`, Stacks Tag 0803,
`lemma:nagata-proj-closed-center-finite-degree-exists`) is proved in
`WeilConjectures.Blowup.FiniteDegree`; its transport to an abstractly
identified total space (`exists_finiteDegree_center_le`) and the support formula of
the full finite-degree statement (`coe_support_eq_of_comap_pow_mul`) are proved here.

The universal property of blowing up (Stacks Tag 0806) and the effective Cartier
kit (`exists_lift_blowup`, `hom_ext_of_isEffectiveCartier_comap`,
`IsEffectiveCartier.mul`/`of_mul_left`/`of_mul_right`/`comap_blowupMap`) are provided
by `WeilConjectures.Blowup.BlowupUniversal`.

The affine-chart algebra of module strict transforms (Stacks Tag 080W) is proved in
`WeilConjectures.Compactification.PowerTorsion`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (U : X.Opens)

/-- A `U`-admissible blow-up datum on `X`: a finite-type quasi-coherent ideal sheaf `I`
whose support is disjoint from `U` (equivalently, `I` restricts to the unit ideal on
`U`), together with a morphism `π : X' ⟶ X` and an identification of `π` with the
blow-up of `I` over `X`.
(Blueprint: `def:nagata-admissible-blowup`.) -/
structure AdmissibleBlowup where
  /-- The center ideal of the blow-up. -/
  I : X.IdealSheafData
  /-- The center is a finite-type ideal sheaf. -/
  finiteType : I.FiniteType
  /-- The center is disjoint from the preserved open `U`; equivalently `I` restricts to
  the unit ideal on `U`. -/
  disjoint_support : Disjoint (U : Set X) (I.support : Set X)
  /-- The total space of the admissible blow-up. -/
  X' : Scheme.{u}
  /-- The structure morphism of the admissible blow-up. -/
  π : X' ⟶ X
  /-- The identification of the total space with the blow-up of the center. -/
  iso : X' ≅ I.blowup
  /-- The identification is a morphism over `X`. -/
  iso_π : iso.hom ≫ I.blowupMap = π

namespace AdmissibleBlowup

variable {X U}

/-- The tautological `U`-admissible blow-up attached to a finite-type ideal sheaf whose
support is disjoint from `U`: the blow-up of the ideal itself. -/
@[simps I X' π]
def ofIdeal (I : X.IdealSheafData) (hft : I.FiniteType)
    (hdisj : Disjoint (U : Set X) (I.support : Set X)) : AdmissibleBlowup X U where
  I := I
  finiteType := hft
  disjoint_support := hdisj
  X' := I.blowup
  π := I.blowupMap
  iso := Iso.refl _
  iso_π := Category.id_comp _

variable (B : AdmissibleBlowup X U)

/-- The complement of the center of an admissible blow-up, i.e. the open locus over
which the blow-up is tautologically an isomorphism. The preserved open `U` is contained
in it (`AdmissibleBlowup.le_preservedOpen`). -/
abbrev preservedOpen : X.Opens := B.I.support.compl

lemma le_preservedOpen : U ≤ B.preservedOpen := by
  intro x hx
  exact Set.disjoint_left.mp B.disjoint_support hx

/-- **A `U`-admissible blow-up is proper**: transport of the properness of the blow-up
(`Scheme.IdealSheafData.isProper_blowupMap`, blueprint
`thm:nagata-global-blowup-proper`) across the chosen identification with the blow-up
of the center. -/
theorem isProper_π : IsProper B.π := by
  rw [← B.iso_π, MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)]
  exact B.I.isProper_blowupMap B.finiteType

/-- A `U`-admissible blow-up is an isomorphism over `U`. This transports the blow-up
complement theorem (`thm:nagata-global-blowup-complement`) across the chosen
identification with the blow-up of the center.
(Blueprint: `lemma:nagata-admissible-blowup-over-open`.) -/
theorem isIso_π_restrict : IsIso (B.π ∣_ U) := by
  rw [← B.iso_π, morphismRestrict_comp]
  have h1 : IsIso (B.iso.hom ∣_ B.I.blowupMap ⁻¹ᵁ U) := inferInstance
  have h2 : IsIso (B.I.blowupMap ∣_ U) :=
    B.I.isIso_blowupMap_restrict B.disjoint_support
  exact IsIso.comp_isIso' h1 h2

/-- The strict transform of a morphism `q : Z ⟶ X` along a `U`-admissible blow-up: the
scheme-theoretic closure, inside `Z ×_X X'`, of the locus over the complement of the
center. (Blueprint: `def:nagata-strict-transform`.) -/
abbrev strictTransform {Z : Scheme.{u}} (q : Z ⟶ X) : Scheme.{u} :=
  StrictTransform q B.π B.preservedOpen

/-- The projection of the strict transform along an admissible blow-up to the total
space of the blow-up. -/
def strictTransformMap {Z : Scheme.{u}} (q : Z ⟶ X) : B.strictTransform q ⟶ B.X' :=
  AlgebraicGeometry.strictTransformMap q B.π B.preservedOpen

section Permanence

/-! The strict transform of a morphism along an admissible blow-up is a closed
subscheme of the base change, so separatedness, quasi-compactness and local finite
type are inherited from `q`. These permanence instances feed the inductive
applications of the flattening theorems. -/

variable {Z : Scheme.{u}} (q : Z ⟶ X)

instance [IsSeparated q] : IsSeparated (B.strictTransformMap q) := by
  have : IsSeparated (pullback.snd q B.π) := MorphismProperty.pullback_snd _ _ ‹_›
  unfold strictTransformMap AlgebraicGeometry.strictTransformMap
  infer_instance

instance [QuasiCompact q] : QuasiCompact (B.strictTransformMap q) := by
  unfold strictTransformMap AlgebraicGeometry.strictTransformMap
  infer_instance

instance [LocallyOfFiniteType q] : LocallyOfFiniteType (B.strictTransformMap q) := by
  have : LocallyOfFiniteType (pullback.snd q B.π) := MorphismProperty.pullback_snd _ _ ‹_›
  unfold strictTransformMap AlgebraicGeometry.strictTransformMap
  infer_instance

end Permanence

/-- Finite-type ideal sheaves are stable under products. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType.mul
    {X : Scheme.{u}} {I J : X.IdealSheafData} (hI : I.FiniteType) (hJ : J.FiniteType) :
    (I * J).FiniteType := by
  intro U
  have h1 : (I * J).ideal U = I.ideal U * J.ideal U := by
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  rw [h1]
  exact (hI U).mul (hJ U)

/-- Powers of an effective Cartier ideal are effective Cartier: a power of a local
single nonzerodivisor generator generates the power. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.pow
    {X : Scheme.{u}} {C : X.IdealSheafData} (hC : C.IsEffectiveCartier) (d : ℕ) :
    (C ^ d).IsEffectiveCartier := by
  intro x
  obtain ⟨U, hxU, a, ha, hgen⟩ := hC x
  refine ⟨U, hxU, a ^ d, pow_mem ha d, ?_⟩
  have h1 : (C ^ d).ideal U = C.ideal U ^ d := by
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  rw [h1, hgen, Ideal.span_singleton_pow]

/-- The pullback of an effective Cartier ideal along an isomorphism of schemes is
effective Cartier: local generators transport along the section isomorphisms. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.comap_of_isIso
    {Y Z : Scheme.{u}} {C : Z.IdealSheafData} (hC : C.IsEffectiveCartier) (f : Y ⟶ Z)
    [IsIso f] : (C.comap f).IsEffectiveCartier := by
  intro y
  obtain ⟨V, hyV, a, ha, hgen⟩ := hC (f y)
  have hle : V.1 ≤ f.opensRange := by
    intro z _
    refine ⟨inv f z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have haff : IsAffineOpen (f ⁻¹ᵁ V.1) := V.2.preimage_of_isOpenImmersion f hle
  have hiso : IsIso (f.appLE V.1 (f ⁻¹ᵁ V.1) le_rfl) := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact f.isIso_app V.1 hle
  refine ⟨⟨f ⁻¹ᵁ V.1, haff⟩, hyV, (f.appLE V.1 (f ⁻¹ᵁ V.1) le_rfl).hom a,
    AlgebraicGeometry.map_mem_nonZeroDivisors _
      (ConcreteCategory.bijective_of_isIso (f.appLE V.1 (f ⁻¹ᵁ V.1) le_rfl)) ha, ?_⟩
  rw [Scheme.IdealSheafData.ideal_comap_eq_map_appLE f C V ⟨f ⁻¹ᵁ V.1, haff⟩ le_rfl,
    hgen, Ideal.map_span, Set.image_singleton]

/-- Transport of the blow-up structure morphism along an equality of centers. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.eqToHom_blowupMap
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.blowup h) ≫ J.blowupMap = I.blowupMap := by
  subst h
  simp

/-- **Finite-degree approximation of a second blow-up center** (the core of Stacks
Project Tag 0803): transport of `exists_finiteDegree_center_le_blowup` along the chosen
identification of the total space with the blow-up. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteDegree_center_le
    {X X₁ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I.FiniteType) {π : X₁ ⟶ X} (g : X₁ ≅ I.blowup)
    (hg : g.hom ≫ I.blowupMap = π) (J : X₁.IdealSheafData) (hJ : J.FiniteType) :
    ∃ (d : ℕ) (L : X.IdealSheafData), 0 < d ∧ L.FiniteType ∧ L ≤ I ^ d ∧
      L.comap π = (I.comap π) ^ d * J := by
  obtain ⟨d, L, hd, hLft, hLle, hLcomap⟩ :=
    Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup I hI (J.comap g.inv)
      (Scheme.IdealSheafData.FiniteType.comap_of_isOpenImmersion hJ g.inv)
  refine ⟨d, L, hd, hLft, hLle, ?_⟩
  have h1 : L.comap π = (L.comap I.blowupMap).comap g.hom := by
    rw [← Scheme.IdealSheafData.comap_comp, hg]
  have h2 : I.comap π = (I.comap I.blowupMap).comap g.hom := by
    rw [← Scheme.IdealSheafData.comap_comp, hg]
  rw [h1, h2, hLcomap, Scheme.IdealSheafData.comap_mul,
    Scheme.IdealSheafData.comap_pow]
  congr 1
  rw [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]

/-- **The support of a finite-degree center** (the support computation in the proofs of
Stacks Project Tags 0803/080B): if `L ≤ I^d` (`d ≥ 1`) is an ideal sheaf whose inverse
image on the blow-up of `I` is `I_E^d · J`, then the support of `L` is
`supp I ∪ π(supp J)`. Indeed `L ≤ I^d` forces `supp I ⊆ supp L`; the support of the
inverse image ideal is `π⁻¹(supp I) ∪ supp J`, which gives `π(supp J) ⊆ supp L`; and
away from `supp I` the blow-up is an isomorphism, under which `L` cuts out exactly
`supp J`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.coe_support_eq_of_comap_pow_mul
    {X X₁ : Scheme.{u}} (I : X.IdealSheafData) {π : X₁ ⟶ X} (g : X₁ ≅ I.blowup)
    (hg : g.hom ≫ I.blowupMap = π) (J : X₁.IdealSheafData) {d : ℕ} (hd : d ≠ 0)
    {L : X.IdealSheafData} (hle : L ≤ I ^ d)
    (hcomap : L.comap π = (I.comap π) ^ d * J) :
    (L.support : Set X) = (I.support : Set X) ∪ π '' (J.support : Set X₁) := by
  set U₀ : X.Opens := I.support.compl with hU₀def
  -- the blow-up is an isomorphism over the complement of the support of `I`
  have hiso : IsIso (π ∣_ U₀) := by
    rw [← hg, morphismRestrict_comp]
    have h1 : IsIso (g.hom ∣_ I.blowupMap ⁻¹ᵁ U₀) := inferInstance
    have h2 : IsIso (I.blowupMap ∣_ U₀) := by
      rw [hU₀def]
      exact I.isIso_blowupMap_restrict_support_compl
    exact IsIso.comp_isIso' h1 h2
  -- the support identity upstairs
  have hsupp₁ : (π ⁻¹' (L.support : Set X) : Set X₁) =
      π ⁻¹' (I.support : Set X) ∪ (J.support : Set X₁) := by
    have h1 : ((L.comap π).support : Set X₁) = π ⁻¹' (L.support : Set X) := by
      rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    have h2 : ((((I.comap π) ^ d) * J).support : Set X₁) =
        π ⁻¹' (I.support : Set X) ∪ (J.support : Set X₁) := by
      rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup,
        Scheme.IdealSheafData.support_pow _ _ hd, Scheme.IdealSheafData.support_comap,
        TopologicalSpace.Closeds.coe_preimage]
    rw [← h1, hcomap, h2]
  refine subset_antisymm ?_ ?_
  · -- `supp L ⊆ supp I ∪ π(supp J)`
    intro z hz
    by_cases hzI : z ∈ (I.support : Set X)
    · exact Or.inl hzI
    refine Or.inr ?_
    -- lift `z` through the isomorphism over the complement of `supp I`
    obtain ⟨z', rfl⟩ : z ∈ Set.range U₀.ι := by
      rwa [Scheme.Opens.range_ι, hU₀def]
    have hstep : (π ∣_ U₀) (inv (π ∣_ U₀) z') = z' := by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    have hπx₁ : π ((π ⁻¹ᵁ U₀).ι (inv (π ∣_ U₀) z')) = U₀.ι z' := by
      calc π ((π ⁻¹ᵁ U₀).ι (inv (π ∣_ U₀) z'))
          = ((π ⁻¹ᵁ U₀).ι ≫ π) (inv (π ∣_ U₀) z') := (Scheme.Hom.comp_apply _ _ _).symm
        _ = ((π ∣_ U₀) ≫ U₀.ι) (inv (π ∣_ U₀) z') := by rw [morphismRestrict_ι]
        _ = U₀.ι ((π ∣_ U₀) (inv (π ∣_ U₀) z')) := Scheme.Hom.comp_apply _ _ _
        _ = U₀.ι z' := by rw [hstep]
    have hx₁L : (π ⁻¹ᵁ U₀).ι (inv (π ∣_ U₀) z') ∈ π ⁻¹' (L.support : Set X) := by
      rwa [Set.mem_preimage, hπx₁]
    rw [hsupp₁] at hx₁L
    rcases hx₁L with hx₁I | hx₁J
    · exact absurd (by rw [← hπx₁]; exact hx₁I) hzI
    · exact ⟨(π ⁻¹ᵁ U₀).ι (inv (π ∣_ U₀) z'), hx₁J, hπx₁⟩
  · -- `supp I ∪ π(supp J) ⊆ supp L`
    rintro z (hzI | ⟨x₁, hx₁, rfl⟩)
    · have h1 : ((I ^ d).support : Set X) ⊆ (L.support : Set X) :=
        Scheme.IdealSheafData.support_antitone hle
      have h2 : (I ^ d).support = I.support := Scheme.IdealSheafData.support_pow I d hd
      exact h1 (h2 ▸ hzI)
    · have hmem : x₁ ∈ π ⁻¹' (L.support : Set X) := by
        rw [hsupp₁]
        exact Or.inr hx₁
      exact hmem

/-- **Finite-degree descent of a second blow-up center** (Stacks Project Tag 0803
together with the support computation of the proof of Tag 080B; blueprint
`lemma:nagata-proj-closed-center-finite-degree-exists`,
`lemma:nagata-composition-center-ideal`): given a finite-type center `I` on a qcqs
scheme `X` with blow-up `π : X₁ ⟶ X` and a finite-type center `J` on `X₁`, there are a
degree `d` and a finite-type ideal `L` on `X` such that the support of `L` is
`supp I ∪ π(supp J)` and the inverse image ideal of `L` on `X₁` is `I_E^d · J`.

This combines the finite-degree approximation `exists_finiteDegree_center_le`
(Tag 0803) with the support computation `coe_support_eq_of_comap_pow_mul`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteDegree_center
    {X X₁ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I.FiniteType) {π : X₁ ⟶ X} (g : X₁ ≅ I.blowup)
    (hg : g.hom ≫ I.blowupMap = π) (J : X₁.IdealSheafData) (hJ : J.FiniteType) :
    ∃ (d : ℕ) (L : X.IdealSheafData), L.FiniteType ∧
      (L.support : Set X) = (I.support : Set X) ∪ π '' (J.support : Set X₁) ∧
      L.comap π = (I.comap π) ^ d * J := by
  obtain ⟨d, L, hd, hLft, hLle, hLcomap⟩ :=
    Scheme.IdealSheafData.exists_finiteDegree_center_le I hI g hg J hJ
  exact ⟨d, L, hLft,
    Scheme.IdealSheafData.coe_support_eq_of_comap_pow_mul I g hg J hd.ne' hLle hLcomap,
    hLcomap⟩

/-- **Blow-up of a product ideal** (Stacks Project Tag 080A; blueprint
`thm:nagata-blowup-product-ideal`, `cor:nagata-blowup-product-common-refinement`):
blowing up a product `I * L` is the same over `X` as first blowing up `I` and then the
inverse image ideal of `L` on the blow-up.

The proof follows `blueprint/src/version/detailed/nagata/nagata_new.tex` and runs entirely
through the universal property of blowing up
(`Scheme.IdealSheafData.existsUnique_lift_blowup`, Stacks Project Tag 0806): on the
iterated blow-up the pullback of `I * L` is invertible, giving `α`; on the blow-up of
`I * L` the pullbacks of `I` and of `L` are invertible by the factor lemma
(`IsEffectiveCartier.of_mul_left/right`), giving the lift `β` to `X₁` and then
`γ` to the iterated blow-up; the two composites are identities by the uniqueness of
lifts. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_mul_iso
    {X X₁ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) {π : X₁ ⟶ X} (g : X₁ ≅ I.blowup)
    (hg : g.hom ≫ I.blowupMap = π) (L : X.IdealSheafData) :
    ∃ e : (I * L).blowup ≅ (L.comap π).blowup,
      e.hom ≫ (L.comap π).blowupMap ≫ π = (I * L).blowupMap := by
  -- notation: the second blow-up `q`, the iterated map `ρ` and the product blow-up `c`
  set q := (L.comap π).blowupMap with hq
  set c := (I * L).blowupMap with hc
  -- the pullback of `I` to `X₁` is effective Cartier
  have hE1 : (I.comap π).IsEffectiveCartier := by
    have h1 : I.comap π = (I.comap I.blowupMap).comap g.hom := by
      rw [← hg, Scheme.IdealSheafData.comap_comp]
    rw [h1]
    exact (I.extendedToBlowup_isEffectiveCartier).comap_of_isIso g.hom
  -- hence so is its further pullback along the second blow-up
  have hE3 : ((I.comap π).comap q).IsEffectiveCartier :=
    hE1.comap_blowupMap (L.comap π)
  -- the pullback of `L.comap π` to the second blow-up is effective Cartier
  have hE2 : ((L.comap π).comap q).IsEffectiveCartier :=
    (L.comap π).extendedToBlowup_isEffectiveCartier
  -- Step 1: the pullback of `I * L` along `ρ = q ≫ π` is effective Cartier
  have hE4 : ((I * L).comap (q ≫ π)).IsEffectiveCartier := by
    have h4 : (I * L).comap (q ≫ π) =
        ((I.comap π).comap q) * ((L.comap π).comap q) := by
      rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_mul,
        Scheme.IdealSheafData.comap_mul]
    rw [h4]
    exact hE3.mul hE2
  obtain ⟨α, hα⟩ := (I * L).exists_lift_blowup hE4
  -- Step 2: the pullbacks of `I` and `L` to the product blow-up are effective Cartier
  have hECc : ((I * L).comap c).IsEffectiveCartier :=
    (I * L).extendedToBlowup_isEffectiveCartier
  have hprod : ((I.comap c) * (L.comap c)).IsEffectiveCartier := by
    rwa [← Scheme.IdealSheafData.comap_mul]
  have hIc : (I.comap c).IsEffectiveCartier :=
    Scheme.IdealSheafData.IsEffectiveCartier.of_mul_left hprod
  have hLc : (L.comap c).IsEffectiveCartier :=
    Scheme.IdealSheafData.IsEffectiveCartier.of_mul_right hprod
  obtain ⟨β₀, hβ₀⟩ := I.exists_lift_blowup hIc
  -- the lift `β` of the product blow-up to `X₁`
  have hβπ : (β₀ ≫ g.inv) ≫ π = c := by
    rw [Category.assoc, ← hg, Iso.inv_hom_id_assoc, hβ₀]
  -- Step 3: the pullback of `L.comap π` along `β` is effective Cartier
  have hLβ : ((L.comap π).comap (β₀ ≫ g.inv)).IsEffectiveCartier := by
    have h6 : (L.comap π).comap (β₀ ≫ g.inv) = L.comap c := by
      rw [← Scheme.IdealSheafData.comap_comp, hβπ]
    rwa [h6]
  obtain ⟨γ, hγ⟩ := (L.comap π).exists_lift_blowup hLβ
  -- Step 4: the two composites are identities, by uniqueness of lifts
  have hγα : γ ≫ α = 𝟙 (I * L).blowup := by
    refine (I * L).hom_ext_of_isEffectiveCartier_comap hECc ?_ (Category.id_comp c)
    rw [Category.assoc, hα, ← Category.assoc, hγ, hβπ]
  have hαβ₀ : α ≫ β₀ = q ≫ g.hom := by
    have hEρ : (I.comap (q ≫ π)).IsEffectiveCartier := by
      rwa [Scheme.IdealSheafData.comap_comp]
    refine I.hom_ext_of_isEffectiveCartier_comap hEρ ?_ ?_
    · rw [Category.assoc, hβ₀, hα]
    · rw [Category.assoc, hg]
  have hαγ : α ≫ γ = 𝟙 (L.comap π).blowup := by
    refine (L.comap π).hom_ext_of_isEffectiveCartier_comap hE2 ?_ (Category.id_comp q)
    rw [Category.assoc, hγ, ← Category.assoc, hαβ₀, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine ⟨⟨γ, α, hγα, hαγ⟩, ?_⟩
  change γ ≫ q ≫ π = c
  rw [← Category.assoc, hγ, hβπ]

/-- **Multiplying a center by an effective Cartier ideal does not change the blow-up**
(consequence of Stacks Project Tags 0807 and 080A; blueprint
`lemma:nagata-blowup-invertible-factor`): the blow-up of `C * M` for an effective
Cartier ideal `C` is the blow-up of `M`, over the base.

The proof runs through the universal property of blowing up
(`Scheme.IdealSheafData.existsUnique_lift_blowup`, Stacks Project Tag 0806): the
pullback of `C * M` to the blow-up of `M` is a product of effective Cartier ideals,
giving a lift `α : M.blowup ⟶ (C * M).blowup`; conversely the pullback of `M` to the
blow-up of `C * M` is effective Cartier by the factor lemma
(`IsEffectiveCartier.of_mul_right`), giving `β` in the other direction; the two
composites are identities by the uniqueness of lifts. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_mul_isEffectiveCartier_iso
    {Y : Scheme.{u}} {C : Y.IdealSheafData} (hC : C.IsEffectiveCartier)
    (M : Y.IdealSheafData) :
    ∃ e : (C * M).blowup ≅ M.blowup, e.hom ≫ M.blowupMap = (C * M).blowupMap := by
  -- the pullback of `C * M` to the blow-up of `M` is effective Cartier
  have hCM : ((C * M).comap M.blowupMap).IsEffectiveCartier := by
    rw [Scheme.IdealSheafData.comap_mul]
    exact (hC.comap_blowupMap M).mul M.extendedToBlowup_isEffectiveCartier
  obtain ⟨α, hα⟩ := (C * M).exists_lift_blowup hCM
  -- the pullback of `M` to the blow-up of `C * M` is effective Cartier
  have hECcm : ((C * M).comap (C * M).blowupMap).IsEffectiveCartier :=
    (C * M).extendedToBlowup_isEffectiveCartier
  have hMcm : (M.comap (C * M).blowupMap).IsEffectiveCartier := by
    refine Scheme.IdealSheafData.IsEffectiveCartier.of_mul_right
      (K₁ := C.comap (C * M).blowupMap) ?_
    rwa [← Scheme.IdealSheafData.comap_mul]
  obtain ⟨β, hβ⟩ := M.exists_lift_blowup hMcm
  -- the two composites are identities, by uniqueness of lifts
  have hβα : β ≫ α = 𝟙 (C * M).blowup := by
    refine (C * M).hom_ext_of_isEffectiveCartier_comap hECcm ?_ (Category.id_comp _)
    rw [Category.assoc, hα, hβ]
  have hαβ : α ≫ β = 𝟙 M.blowup := by
    refine M.hom_ext_of_isEffectiveCartier_comap M.extendedToBlowup_isEffectiveCartier ?_
      (Category.id_comp _)
    rw [Category.assoc, hβ, hα]
  exact ⟨⟨β, α, hβα, hαβ⟩, hβ⟩

/-- **Composition of blow-ups** (Stacks Project Tag 080B), interface form: on a qcqs
scheme `X`, given a finite-type center `I` with blow-up `π : X₁ ⟶ X` (identified with
`I.blowup` by `g`) and a finite-type center `J` on the total space `X₁`, there is a
single finite-type center `K` on `X` whose support is the union of the support of `I`
and the image of the support of `J`, and whose blow-up is isomorphic over `X` to the
blow-up of `J`.

The composite center is `K = I * L` with `L` the finite-degree descent of `J`
(`Scheme.IdealSheafData.exists_finiteDegree_center`, Stacks Tag 0803): `K` is finite
type as a product of finite-type ideals, its support is
`supp I ∪ (supp I ∪ π(supp J)) = supp I ∪ π(supp J)`, and its blow-up is computed by
the product comparison (`exists_blowup_mul_iso`, Tag 080A) followed by removal of the
invertible exceptional factor `(I.comap π)^d` of the inverse image ideal
`L.comap π = (I.comap π)^d * J` (`exists_blowup_mul_isEffectiveCartier_iso`, Tag 0807),
the exceptional ideal being effective Cartier by the principalization theorem
transported along `g`.
(Blueprint: `thm:nagata-composition-of-blowups`.) -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp
    {X X₁ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I.FiniteType) {π : X₁ ⟶ X} (g : X₁ ≅ I.blowup)
    (hg : g.hom ≫ I.blowupMap = π) (J : X₁.IdealSheafData) (hJ : J.FiniteType) :
    ∃ K : X.IdealSheafData, K.FiniteType ∧
      (K.support : Set X) = (I.support : Set X) ∪ π '' (J.support : Set X₁) ∧
      ∃ e : K.blowup ≅ J.blowup, e.hom ≫ J.blowupMap ≫ π = K.blowupMap := by
  obtain ⟨d, L, hLft, hLsupp, hLpull⟩ :=
    Scheme.IdealSheafData.exists_finiteDegree_center I hI g hg J hJ
  refine ⟨I * L, hI.mul hLft, ?_, ?_⟩
  · -- support of the product center
    rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup, hLsupp,
      ← Set.union_assoc, Set.union_self]
  · -- comparison of the blow-ups
    obtain ⟨e₁, he₁⟩ := Scheme.IdealSheafData.exists_blowup_mul_iso I g hg L
    -- the exceptional ideal is effective Cartier, hence so is its `d`-th power
    have hEC : ((I.comap π) ^ d).IsEffectiveCartier := by
      have h1 : I.comap π = (I.comap I.blowupMap).comap g.hom := by
        rw [← hg, Scheme.IdealSheafData.comap_comp]
      rw [h1]
      exact (I.extendedToBlowup_isEffectiveCartier.comap_of_isIso g.hom).pow d
    obtain ⟨e₂, he₂⟩ :=
      Scheme.IdealSheafData.exists_blowup_mul_isEffectiveCartier_iso hEC J
    refine ⟨e₁ ≪≫ eqToIso (congrArg Scheme.IdealSheafData.blowup hLpull) ≪≫ e₂, ?_⟩
    calc (e₁ ≪≫ eqToIso (congrArg Scheme.IdealSheafData.blowup hLpull) ≪≫ e₂).hom ≫
          J.blowupMap ≫ π
        = e₁.hom ≫ eqToHom (congrArg Scheme.IdealSheafData.blowup hLpull) ≫
            (e₂.hom ≫ J.blowupMap) ≫ π := by
          simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
      _ = e₁.hom ≫ (eqToHom (congrArg Scheme.IdealSheafData.blowup hLpull) ≫
            ((I.comap π) ^ d * J).blowupMap) ≫ π := by
          rw [he₂, Category.assoc]
      _ = e₁.hom ≫ (L.comap π).blowupMap ≫ π := by
          rw [Scheme.IdealSheafData.eqToHom_blowupMap hLpull]
      _ = (I * L).blowupMap := he₁

/-- **Composition of admissible blow-ups** (Stacks Project Tag 080L): for `X` qcqs
with `U` a quasi-compact open, the composite of a `U`-admissible blow-up of `X` with a
`π⁻¹(U)`-admissible blow-up of its total space is, up to isomorphism over `X`, again a
`U`-admissible blow-up of `X`.

The proof applies the composition theorem for arbitrary blow-ups
(`Scheme.IdealSheafData.exists_blowup_comp`, Stacks Tag 080B): the composite center
`K` has support `|Z| ∪ π₁(|Z'|)`; the first part misses `U` by admissibility of `B₁`,
and the second part misses `U` because a point of `π₁(|Z'|) ∩ U` would lift to a point
of `|Z'| ∩ π₁⁻¹(U)`, contradicting admissibility of `B₂`. Hence `K` is a `U`-admissible
center and the over-`X` isomorphism supplied by the composition theorem, composed with
the chosen identification of `B₂`, gives the required equality of morphisms.
(Blueprint: `lemma:nagata-admissible-blowup-comp`.) -/
theorem exists_comp [CompactSpace X] [QuasiSeparatedSpace X] (_hU : IsCompact (U : Set X))
    (B₁ : AdmissibleBlowup X U) (B₂ : AdmissibleBlowup B₁.X' (B₁.π ⁻¹ᵁ U)) :
    ∃ (B : AdmissibleBlowup X U) (e : B.X' ≅ B₂.X'), e.hom ≫ B₂.π ≫ B₁.π = B.π := by
  obtain ⟨K, hKft, hKsupp, e', he'⟩ :=
    Scheme.IdealSheafData.exists_blowup_comp B₁.I B₁.finiteType B₁.iso B₁.iso_π
      B₂.I B₂.finiteType
  -- admissibility of the composite center: `(|Z| ∪ π₁(|Z'|)) ∩ U = ∅`
  have hdisj : Disjoint (U : Set X) (K.support : Set X) := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    rw [hKsupp] at hxK
    rcases hxK with hxI | ⟨x', hx', rfl⟩
    · exact Set.disjoint_left.mp B₁.disjoint_support hxU hxI
    · exact Set.disjoint_left.mp B₂.disjoint_support
        (show x' ∈ ((B₁.π ⁻¹ᵁ U : B₁.X'.Opens) : Set B₁.X') from hxU) hx'
  refine ⟨.ofIdeal K hKft hdisj, e' ≪≫ B₂.iso.symm, ?_⟩
  have h2 : B₂.iso.inv ≫ B₂.π = B₂.I.blowupMap := by
    rw [← B₂.iso_π, Iso.inv_hom_id_assoc]
  calc (e' ≪≫ B₂.iso.symm).hom ≫ B₂.π ≫ B₁.π
      = e'.hom ≫ (B₂.iso.inv ≫ B₂.π) ≫ B₁.π := by
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    _ = e'.hom ≫ B₂.I.blowupMap ≫ B₁.π := by rw [h2]
    _ = (AdmissibleBlowup.ofIdeal K hKft hdisj).π := by rwa [ofIdeal_π]

end AdmissibleBlowup

variable {X U}

/-- On a quasi-compact quasi-separated scheme, every quasi-compact open is the
complement of the vanishing locus of a finite-type quasi-coherent ideal. This is the
finite-type approximation of the vanishing ideal of the reduced boundary, obtained by
extending finitely generated pieces over a finite affine cover.
(Blueprint: `lemma:nagata-qc-open-complement-ideal-exists`; Stacks Project Tag 01PH.) -/
theorem _root_.AlgebraicGeometry.Scheme.exists_finiteType_ideal_zeroLocus_compl_qcOpen
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ I : X.IdealSheafData, I.FiniteType ∧ (I.support : Set X) = (U : Set X)ᶜ := by
  have : QuasiCompact U.ι := Scheme.Opens.quasiCompact_ι U hU
  set H₀ : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ with hH₀def
  -- the vanishing ideal of the boundary restricts to the unit ideal on `U`
  have hcomap : H₀.comap U.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    ext1
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      hH₀def, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    ext x
    simp
  -- the finite-type approximation of the vanishing ideal (Stacks Tag 01PF)
  obtain ⟨I, hle, hft, hIcomap⟩ := Scheme.IdealSheafData.exists_finiteType_le_comap_eq
    H₀ U hU (fun U' ↦ by rw [hcomap]; exact ⟨{1}, by simp⟩)
  refine ⟨I, hft, subset_antisymm ?_ ?_⟩
  · -- `I` restricts to the unit ideal on `U`, so its support misses `U`
    have h1 : I.comap U.ι = ⊤ := by rw [hIcomap, hcomap]
    have h2 : U.ι ⁻¹' (I.support : Set X) = ∅ := by
      have h3 : ((I.comap U.ι).support : Set U.toScheme) = ∅ := by
        rw [h1]
        simp
      rwa [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage] at h3
    rw [Set.subset_compl_iff_disjoint_right, Set.disjoint_iff_inter_eq_empty,
      ← Scheme.Opens.range_ι (U := U), ← Set.image_preimage_eq_inter_range, h2,
      Set.image_empty]
  · -- `I` is contained in the vanishing ideal of the boundary, so its support covers it
    have h4 : (H₀.support : Set X) = (U : Set X)ᶜ := by
      rw [hH₀def, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    rw [← h4]
    exact Scheme.IdealSheafData.support_antitone hle

/-- On a locally Noetherian scheme, the finite-type ideal cutting out the complement of
an open is simply the vanishing ideal of the (reduced) boundary: every ideal sheaf is
of finite type. This is the Noetherian instance of
`Scheme.exists_finiteType_ideal_zeroLocus_compl_qcOpen`, sufficient for the Noetherian
compactification theorem (`thm:nagata-noetherian`). -/
theorem _root_.AlgebraicGeometry.Scheme.exists_finiteType_ideal_zeroLocus_compl_of_locallyNoetherian
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens) :
    ∃ I : X.IdealSheafData, I.FiniteType ∧ (I.support : Set X) = (U : Set X)ᶜ := by
  refine ⟨Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩,
    fun V ↦ ?_, ?_⟩
  · have := IsLocallyNoetherian.component_noetherian (X := X) V
    exact IsNoetherian.noetherian _
  · simp [Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- **Preparation of a Cartier boundary from a boundary ideal**: blowing up a
finite-type ideal whose support is the complement of `U` produces a `U`-admissible
blow-up whose boundary is the support of an effective Cartier ideal, namely the
extension of the center. This is the geometric half of Stacks Project Tag 080Y; the
two theorems below only differ in how the boundary ideal is produced.
(Blueprint: `lemma:nagata-cartier-boundary-preparation`; proof order item 24.) -/
theorem exists_admissibleBlowup_cartierBoundary_of_ideal (I : X.IdealSheafData)
    (hft : I.FiniteType) (hsupp : (I.support : Set X) = (U : Set X)ᶜ) :
    ∃ (B : AdmissibleBlowup X U) (J : B.X'.IdealSheafData), J.IsEffectiveCartier ∧
      (J.support : Set B.X') = ((B.π ⁻¹ᵁ U) : Set B.X')ᶜ := by
  have hdisj : Disjoint (U : Set X) (I.support : Set X) := by
    rw [hsupp]
    exact disjoint_compl_right
  refine ⟨.ofIdeal I hft hdisj, I.extendedToBlowup,
    I.extendedToBlowup_isEffectiveCartier, ?_⟩
  change (I.extendedToBlowup.support : Set I.blowup) =
    ((I.blowupMap ⁻¹ᵁ U : I.blowup.Opens) : Set I.blowup)ᶜ
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hsupp,
    Set.preimage_compl]
  rfl

/-- **Preparation of a Cartier boundary** (Stacks Project Tag 080Y): on a
quasi-compact quasi-separated scheme `X` with a quasi-compact open `U`, there is a
`U`-admissible blow-up whose boundary — the complement of the preimage of `U` — is the
support of an effective Cartier ideal.
(Blueprint: `lemma:nagata-cartier-boundary-preparation`; proof order item 24.) -/
theorem exists_admissibleBlowup_cartierBoundary [CompactSpace X] [QuasiSeparatedSpace X]
    (hU : IsCompact (U : Set X)) :
    ∃ (B : AdmissibleBlowup X U) (J : B.X'.IdealSheafData), J.IsEffectiveCartier ∧
      (J.support : Set B.X') = ((B.π ⁻¹ᵁ U) : Set B.X')ᶜ :=
  let ⟨I, hft, hsupp⟩ := X.exists_finiteType_ideal_zeroLocus_compl_qcOpen U hU
  exists_admissibleBlowup_cartierBoundary_of_ideal (X := X) (U := U) I hft hsupp

/-- **Preparation of a Cartier boundary, locally Noetherian case**: on a locally
Noetherian scheme every open has a `U`-admissible blow-up with effective Cartier
boundary. Here, in contrast to `exists_admissibleBlowup_cartierBoundary`, no
compactness of `U` is needed: the finite-type boundary ideal is the vanishing ideal of
the reduced boundary itself.
This is the instance needed for the Noetherian compactification theorem
(`thm:nagata-noetherian`).
(Blueprint: `lemma:nagata-cartier-boundary-preparation`; proof order item 24.) -/
theorem exists_admissibleBlowup_cartierBoundary_of_locallyNoetherian
    [IsLocallyNoetherian X] :
    ∃ (B : AdmissibleBlowup X U) (J : B.X'.IdealSheafData), J.IsEffectiveCartier ∧
      (J.support : Set B.X') = ((B.π ⁻¹ᵁ U) : Set B.X')ᶜ :=
  let ⟨I, hft, hsupp⟩ :=
    X.exists_finiteType_ideal_zeroLocus_compl_of_locallyNoetherian U
  exists_admissibleBlowup_cartierBoundary_of_ideal (X := X) (U := U) I hft hsupp

/-- **Extension of finite-type ideals from a quasi-compact open** (Stacks Project
Tag 01PF): on a qcqs scheme, a finite-type quasi-coherent ideal on a quasi-compact
open extends to a finite-type quasi-coherent ideal on the whole scheme. The revised
blueprint uses this to extend blow-up centers from opens
(`def:nagata-finite-type-ideal-extension`, `lemma:nagata-extend-finite-type-ideal`). -/
theorem _root_.AlgebraicGeometry.Scheme.exists_finiteType_ideal_extension
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (W : X.Opens)
    (hW : IsCompact (W : Set X)) (J : W.toScheme.IdealSheafData) (hJ : J.FiniteType) :
    ∃ I : X.IdealSheafData, I.FiniteType ∧ I.comap W.ι = J := by
  have : QuasiCompact W.ι := Scheme.Opens.quasiCompact_ι W hW
  have hcomap : (J.map W.ι).comap W.ι = J := Scheme.IdealSheafData.comap_map_ι W J
  obtain ⟨I, -, hft, hIcomap⟩ := Scheme.IdealSheafData.exists_finiteType_le_comap_eq
    (J.map W.ι) W hW (fun U' ↦ by rw [hcomap]; exact hJ U')
  exact ⟨I, hft, by rw [hIcomap, hcomap]⟩

section BoundarySeparation

/-! ### Boundary separation

The revised blueprint replaces the flattening route of the original blueprint by the
boundary-separation route: two finite-presentation closed subschemes which are disjoint
over `U` acquire disjoint strict transforms after blowing up the sum of their ideals
(Stacks Project Tag 0F3V; revised blueprint `def:nagata-separate-closed-subschemes`,
`lemma:nagata-separate-closed-subschemes`). -/

/-- The support of a sum of ideal sheaves is contained in the intersection of the
supports. -/
lemma coe_support_sup_subset (I₁ I₂ : X.IdealSheafData) :
    ((I₁ ⊔ I₂).support : Set X) ⊆ (I₁.support : Set X) ∩ (I₂.support : Set X) := by
  intro x hx
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff] at hx
  refine ⟨?_, ?_⟩ <;>
    · rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff]
      intro V
      have h := hx V
      rw [Scheme.mem_zeroLocus_iff] at h ⊢
      intro f hf
      refine h f ?_
      rw [SetLike.mem_coe,
        congrFun (Scheme.IdealSheafData.ideal_sup (I := I₁) (J := I₂)) V, Pi.sup_apply]
      first
        | exact Submodule.mem_sup_left hf
        | exact Submodule.mem_sup_right hf

/-- **The boundary-separation blow-up** (revised blueprint
`def:nagata-separate-closed-subschemes`): the `U`-admissible blow-up of the sum of the
ideals of two finite-type centers whose common support is disjoint from `U`. -/
def separationBlowup (I₁ I₂ : X.IdealSheafData) (h₁ : I₁.FiniteType) (h₂ : I₂.FiniteType)
    (hdisj : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X))) :
    AdmissibleBlowup X U :=
  .ofIdeal (I₁ ⊔ I₂)
    (fun V ↦ by
      have := congrFun (Scheme.IdealSheafData.ideal_sup (I := I₁) (J := I₂)) V
      rw [Pi.sup_apply] at this
      rw [this]
      exact Submodule.FG.sup (h₁ V) (h₂ V))
    (hdisj.mono_right (coe_support_sup_subset I₁ I₂))

/-- **Compactness of the complement of the support** of a finite-type ideal sheaf on a
quasi-compact scheme: on each member of a finite affine cover the complement is the
complement of the vanishing locus of a finitely generated ideal, which is a finite union
of basic opens. -/
lemma Scheme.IdealSheafData.isCompact_coe_compl_support {X : Scheme.{u}} [CompactSpace X]
    {K : X.IdealSheafData} (hK : K.FiniteType) :
    IsCompact ((K.support.compl : X.Opens) : Set X) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens ↦ (V.1 : Set X)) (fun V ↦ V.1.isOpen) (by
      intro x _
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X] at hx
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨V, hV⟩)
  have hpiece : ∀ V : X.affineOpens,
      (K.support : Set X)ᶜ ∩ (V.1 : Set X) =
        V.2.fromSpec '' (PrimeSpectrum.zeroLocus ((K.ideal V : Ideal _) : Set _))ᶜ := by
    intro V
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_image]
    constructor
    · rintro ⟨hxs, hxV⟩
      have hxr : x ∈ Set.range V.2.fromSpec := by rwa [V.2.range_fromSpec]
      obtain ⟨p, rfl⟩ := hxr
      refine ⟨p, fun hp ↦ hxs ?_, rfl⟩
      have hmem : V.2.fromSpec p ∈ X.zeroLocus (U := V.1) (K.ideal V : Set _) ∩ V.1 := by
        rw [← V.2.fromSpec_image_zeroLocus]
        exact ⟨p, hp, rfl⟩
      exact ((K.coe_support_inter V).symm ▸ hmem).1
    · rintro ⟨p, hp, rfl⟩
      have hxV : V.2.fromSpec p ∈ (V.1 : Set X) := by
        rw [← V.2.range_fromSpec]
        exact ⟨p, rfl⟩
      refine ⟨fun hsupp ↦ hp ?_, hxV⟩
      have hmem : V.2.fromSpec p ∈ X.zeroLocus (U := V.1) (K.ideal V : Set _) ∩ V.1 :=
        (K.coe_support_inter V) ▸ ⟨hsupp, hxV⟩
      have := V.2.fromSpec_preimage_zeroLocus (K.ideal V : Set _)
      exact this ▸ (Set.mem_preimage.mpr hmem.1)
  have hcover : ((K.support.compl : X.Opens) : Set X) =
      ⋃ V ∈ t, ((K.support : Set X)ᶜ ∩ (V.1 : Set X)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact Set.mem_iUnion₂.mpr ⟨V, hVt, hx, hxV⟩
    · rintro hx
      obtain ⟨V, -, hx, -⟩ := Set.mem_iUnion₂.mp hx
      exact hx
  rw [hcover]
  refine t.finite_toSet.isCompact_biUnion fun V _ ↦ ?_
  rw [hpiece V]
  exact ((hK V).isCompact_compl_zeroLocus).image V.2.fromSpec.continuous

set_option maxHeartbeats 1600000 in
-- The chart rings of the blow-up are large `HomogeneousLocalization` types; unifying
-- them exceeds the default heartbeat limit (as in
-- `Scheme.IdealSheafData.extendedToBlowup_isEffectiveCartier`).
/-- **The charts at pure degree-one elements cover the blow-up of a sum**: every point
of `Bl_{I₁ ⊔ I₂}(X)` lies in a chart at a degree-one element coming from a local
section of `I₁` or of `I₂`, since `D₊(b₁ + b₂) ⊆ D₊(b₁) ∪ D₊(b₂)`. -/
lemma Scheme.IdealSheafData.exists_mem_range_chart_sup {X : Scheme.{u}}
    (I₁ I₂ : X.IdealSheafData) (x : (I₁ ⊔ I₂).blowup) :
    ∃ (U : X.affineOpens) (b : Γ(X, U.1)) (hb : b ∈ (I₁ ⊔ I₂).ideal U),
      (b ∈ I₁.ideal U ∨ b ∈ I₂.ideal U) ∧
      x ∈ Set.range (AffineBlowup.chart ((I₁ ⊔ I₂).ideal U)
        (reesX ((I₁ ⊔ I₂).ideal U) b hb) (reesX_mem ((I₁ ⊔ I₂).ideal U) b hb) ≫
          (I₁ ⊔ I₂).blowupι U) := by
  have hx : (I₁ ⊔ I₂).blowupMap x ∈ (⊤ : X.Opens) := trivial
  rw [← iSup_affineOpens_eq_top X] at hx
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hx2 : x ∈ (I₁ ⊔ I₂).blowupMap ⁻¹ᵁ U.1 := hU
  rw [(I₁ ⊔ I₂).blowupMap_preimage U] at hx2
  obtain ⟨y, rfl⟩ := hx2
  have hy : y ∈ (⊤ : (AffineBlowup ((I₁ ⊔ I₂).ideal U)).Opens) := trivial
  rw [← AffineBlowup.iSup_basicOpen_reesX_eq_top ((I₁ ⊔ I₂).ideal U)] at hy
  obtain ⟨a, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  obtain ⟨av, hav⟩ := a
  have hav' : av ∈ I₁.ideal U ⊔ I₂.ideal U := by
    have hsup : (I₁ ⊔ I₂).ideal U = I₁.ideal U ⊔ I₂.ideal U := by
      rw [congrFun (Scheme.IdealSheafData.ideal_sup (I := I₁) (J := I₂)) U, Pi.sup_apply]
    exact hsup ▸ hav
  obtain ⟨b₁, hb₁, b₂, hb₂, hsum⟩ := Submodule.mem_sup.mp hav'
  subst hsum
  have hb₁K : b₁ ∈ (I₁ ⊔ I₂).ideal U := by
    rw [congrFun (Scheme.IdealSheafData.ideal_sup (I := I₁) (J := I₂)) U, Pi.sup_apply]
    exact Submodule.mem_sup_left hb₁
  have hb₂K : b₂ ∈ (I₁ ⊔ I₂).ideal U := by
    rw [congrFun (Scheme.IdealSheafData.ideal_sup (I := I₁) (J := I₂)) U, Pi.sup_apply]
    exact Submodule.mem_sup_right hb₂
  rw [show reesX ((I₁ ⊔ I₂).ideal U) (b₁ + b₂) hav =
    reesX ((I₁ ⊔ I₂).ideal U) b₁ hb₁K + reesX ((I₁ ⊔ I₂).ideal U) b₂ hb₂K from
    reesX_add _ hb₁K hb₂K] at hy
  have hy' : y ∈ Proj.basicOpen (reesGrading ((I₁ ⊔ I₂).ideal U))
        (reesX ((I₁ ⊔ I₂).ideal U) b₁ hb₁K) ∨
      y ∈ Proj.basicOpen (reesGrading ((I₁ ⊔ I₂).ideal U))
        (reesX ((I₁ ⊔ I₂).ideal U) b₂ hb₂K) := by
    by_contra h
    rw [not_or] at h
    obtain ⟨hn₁, hn₂⟩ := h
    rw [Proj.mem_basicOpen, not_not] at hn₁ hn₂
    rw [Proj.mem_basicOpen] at hy
    exact hy (add_mem hn₁ hn₂)
  rcases hy' with h | h
  · rw [← AffineBlowup.opensRange_chart ((I₁ ⊔ I₂).ideal U)
      (reesX ((I₁ ⊔ I₂).ideal U) b₁ hb₁K) (reesX_mem _ b₁ hb₁K)] at h
    obtain ⟨z, rfl⟩ := h
    exact ⟨U, b₁, hb₁K, Or.inl hb₁, ⟨z, (Scheme.Hom.comp_apply _ _ _).symm⟩⟩
  · rw [← AffineBlowup.opensRange_chart ((I₁ ⊔ I₂).ideal U)
      (reesX ((I₁ ⊔ I₂).ideal U) b₂ hb₂K) (reesX_mem _ b₂ hb₂K)] at h
    obtain ⟨z, rfl⟩ := h
    exact ⟨U, b₂, hb₂K, Or.inr hb₂, ⟨z, (Scheme.Hom.comp_apply _ _ _).symm⟩⟩

/-- **The strict transform of a center misses the affine probes at its own sections**:
let `J ≤ K` be ideal sheaves and let `c : Spec S ⟶ Bl_K(X)` be a morphism lying over an
affine probe `Spec.map φ ≫ fromSpec : Spec S ⟶ X` on which the extension of `K` is
generated by the image of a section `b` of `J`. Then the strict transform of `V(J)`
along the blow-up of `K` is disjoint from the image of `c`: at a point of
`V(J) ×_X Bl_K(X)` over the complement of the support of `K`, the extension of `K` is
the unit ideal while `b` vanishes, so the open locus misses the probe; the strict
transform is the closure of the open locus and the probe is open. In the application
`c` is a blow-up chart at the degree-one element attached to `b` and `S` is the chart
ring. -/
lemma Scheme.IdealSheafData.disjoint_range_strictTransformMap_of_probe
    {X : Scheme.{u}} (K J : X.IdealSheafData) (U : X.affineOpens)
    (b : Γ(X, U.1)) (hbJ : b ∈ J.ideal U) {S : CommRingCat.{u}} (φ : Γ(X, U.1) ⟶ S)
    (hpre : (⊤ : (Spec S).Opens) ≤ (Spec.map φ ≫ U.2.fromSpec) ⁻¹ᵁ U.1)
    (hspan : (K.ideal U).map φ.hom = Ideal.span {φ.hom b})
    (c : Spec S ⟶ K.blowup) [IsOpenImmersion c]
    (hcomp : c ≫ K.blowupMap = Spec.map φ ≫ U.2.fromSpec)
    [QuasiCompact (strictTransformOpen J.subschemeι K.blowupMap K.support.compl).ι] :
    Disjoint
      (Set.range (strictTransformMap J.subschemeι K.blowupMap K.support.compl))
      (Set.range c) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, rfl⟩ hxc
  -- the image point in the fibre product lies in the closure of the open locus
  have hwcl : _root_.AlgebraicGeometry.strictTransformι J.subschemeι K.blowupMap
      K.support.compl t ∈ closure ((strictTransformOpen J.subschemeι K.blowupMap
        K.support.compl : Set _)) := by
    have hmem : _root_.AlgebraicGeometry.strictTransformι J.subschemeι K.blowupMap
        K.support.compl t ∈ Set.range (_root_.AlgebraicGeometry.strictTransformι
          J.subschemeι K.blowupMap K.support.compl) := ⟨t, rfl⟩
    have hrange : Set.range (_root_.AlgebraicGeometry.strictTransformι J.subschemeι
        K.blowupMap K.support.compl) =
        ((((strictTransformOpen J.subschemeι K.blowupMap
          K.support.compl).ι).ker.support : Set _)) :=
      Scheme.IdealSheafData.range_subschemeι _
    rw [hrange, Scheme.Hom.support_ker, Scheme.Opens.range_ι] at hmem
    exact hmem
  -- pick a point of the open locus mapping into the probe
  have hopen : IsOpen (pullback.snd J.subschemeι K.blowupMap ⁻¹' (Set.range c)) := by
    have hoc : IsOpen (Set.range c) := by
      rw [← Scheme.Hom.coe_opensRange]
      exact c.opensRange.isOpen
    exact hoc.preimage (pullback.snd J.subschemeι K.blowupMap).continuous
  have hwmem : _root_.AlgebraicGeometry.strictTransformι J.subschemeι K.blowupMap
      K.support.compl t ∈ pullback.snd J.subschemeι K.blowupMap ⁻¹' (Set.range c) := by
    rw [Set.mem_preimage]
    have heq : pullback.snd J.subschemeι K.blowupMap
        (_root_.AlgebraicGeometry.strictTransformι J.subschemeι K.blowupMap
          K.support.compl t) =
        strictTransformMap J.subschemeι K.blowupMap K.support.compl t :=
      (Scheme.Hom.comp_apply _ _ _).symm
    rwa [heq]
  obtain ⟨w', hw'⟩ := mem_closure_iff.mp hwcl _ hopen hwmem
  obtain ⟨hw'o, hw'W⟩ := hw'
  obtain ⟨y', hy'⟩ := Set.mem_preimage.mp hw'o
  -- the base point of `w'` lies in the support of `J` but not in the support of `K`
  have hz1 : K.blowupMap (pullback.snd J.subschemeι K.blowupMap w') =
      (Spec.map φ ≫ U.2.fromSpec) y' := by
    rw [← hy', ← Scheme.Hom.comp_apply, hcomp]
  have hz2 : J.subschemeι (pullback.fst J.subschemeι K.blowupMap w') =
      K.blowupMap (pullback.snd J.subschemeι K.blowupMap w') := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hzJ : K.blowupMap (pullback.snd J.subschemeι K.blowupMap w') ∈
      (J.support : Set X) := by
    rw [← hz2, ← Scheme.IdealSheafData.range_subschemeι J]
    exact ⟨_, rfl⟩
  have hzK : K.blowupMap (pullback.snd J.subschemeι K.blowupMap w') ∉
      (K.support : Set X) := hw'W
  -- transfer both statements to the affine probe
  have hy'J : y' ∈ ((J.comap (Spec.map φ ≫ U.2.fromSpec)).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    exact Set.mem_preimage.mpr (hz1 ▸ hzJ)
  have hy'K : y' ∉ ((K.comap (Spec.map φ ≫ U.2.fromSpec)).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
    exact fun hmem ↦ hzK (hz1 ▸ Set.mem_preimage.mp hmem)
  -- the pulled-back center is contained in the pulled-back ideal of `J`
  have hle : K.comap (Spec.map φ ≫ U.2.fromSpec) ≤ J.comap (Spec.map φ ≫ U.2.fromSpec) := by
    refine Scheme.IdealSheafData.le_of_isAffine ?_
    rw [Scheme.IdealSheafData.ideal_comap_specMap_fromSpec K U φ hpre,
      Scheme.IdealSheafData.ideal_comap_specMap_fromSpec J U φ hpre,
      appLE_specMap_comp_fromSpec U φ hpre, CommRingCat.hom_comp, ← Ideal.map_map,
      ← Ideal.map_map, hspan, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hbJ)
  exact hy'K (Scheme.IdealSheafData.support_antitone hle hy'J)

/-- **Quasi-compactness of the inclusion of the open locus of a strict transform** over
the complement of the support of a finite-type center on a qcqs scheme: the fibre
product is quasi-separated over `X`, and the open locus is the preimage of the
quasi-compact open `X ∖ supp K` under a quasi-compact morphism. -/
lemma Scheme.IdealSheafData.quasiCompact_strictTransformOpen_ι {X : Scheme.{u}}
    [QuasiSeparatedSpace X] {K : X.IdealSheafData} (hK : K.FiniteType)
    (hU₀ : IsCompact ((K.support.compl : X.Opens) : Set X)) (J : X.IdealSheafData) :
    QuasiCompact (strictTransformOpen J.subschemeι K.blowupMap K.support.compl).ι := by
  have hπqc : QuasiCompact K.blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap hK
  have hproper : IsProper K.blowupMap := K.isProper_blowupMap hK
  have hfstQS : QuasiSeparated (pullback.fst J.subschemeι K.blowupMap) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hPqs : QuasiSeparatedSpace ↥(Limits.pullback J.subschemeι K.blowupMap) :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst J.subschemeι K.blowupMap ≫ J.subschemeι)
  have hfstQC : QuasiCompact (pullback.fst J.subschemeι K.blowupMap) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  refine Scheme.Opens.quasiCompact_ι _ ?_
  rw [strictTransformOpen_eq_preimage]
  exact QuasiCompact.isCompact_preimage
    (f := pullback.fst J.subschemeι K.blowupMap ≫ J.subschemeι) _
    (K.support.compl).isOpen hU₀

set_option maxHeartbeats 1600000 in
-- The chart rings of the blow-up are large `HomogeneousLocalization` types; unifying
-- them exceeds the default heartbeat limit (as in
-- `Scheme.IdealSheafData.extendedToBlowup_isEffectiveCartier`).
/-- **Boundary separation** (Stacks Project Tag 0F3V; revised blueprint
`lemma:nagata-separate-closed-subschemes`): after blowing up the sum of the ideals of
two finite-type centers whose common support is disjoint from `U`, the strict
transforms of the two centers are disjoint.

The proof is the chart argument of the revised blueprint: the charts of
`Bl_{I₁ ⊔ I₂}(X)` at degree-one elements coming from local sections of `I₁` or of `I₂`
cover the blow-up (`exists_mem_range_chart_sup`), and the strict transform of `V(Iᵢ)`
misses every `Iᵢ`-chart, because on such a chart the extension of the center is
generated by a section of `Iᵢ` (`disjoint_range_strictTransformMap_of_probe`); so the
two strict transforms have no common point. -/
theorem separationBlowup_disjoint_strictTransforms [CompactSpace X]
    [QuasiSeparatedSpace X] (I₁ I₂ : X.IdealSheafData)
    (h₁ : I₁.FiniteType) (h₂ : I₂.FiniteType)
    (hdisj : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X))) :
    Disjoint
      (Set.range ((separationBlowup I₁ I₂ h₁ h₂ hdisj).strictTransformMap I₁.subschemeι))
      (Set.range ((separationBlowup I₁ I₂ h₁ h₂ hdisj).strictTransformMap
        I₂.subschemeι)) := by
  have hKft : (I₁ ⊔ I₂).FiniteType := fun V ↦ by
    have hV := congrFun (Scheme.IdealSheafData.ideal_sup (I := I₁) (J := I₂)) V
    rw [Pi.sup_apply] at hV
    rw [hV]
    exact Submodule.FG.sup (h₁ V) (h₂ V)
  have hU₀ : IsCompact (((I₁ ⊔ I₂).support.compl : X.Opens) : Set X) :=
    Scheme.IdealSheafData.isCompact_coe_compl_support hKft
  have := Scheme.IdealSheafData.quasiCompact_strictTransformOpen_ι hKft hU₀ I₁
  have := Scheme.IdealSheafData.quasiCompact_strictTransformOpen_ι hKft hU₀ I₂
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  obtain ⟨U', b, hbK, hb12, hxc⟩ :=
    Scheme.IdealSheafData.exists_mem_range_chart_sup I₁ I₂ x
  have hpre : (⊤ : (Spec (.of (HomogeneousLocalization.Away
      (reesGrading ((I₁ ⊔ I₂).ideal U')) (reesX ((I₁ ⊔ I₂).ideal U') b hbK)))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap ((I₁ ⊔ I₂).ideal U')
        (reesX ((I₁ ⊔ I₂).ideal U') b hbK))) ≫ U'.2.fromSpec) ⁻¹ᵁ U'.1 := by
    rw [Scheme.Hom.comp_preimage, U'.2.fromSpec_preimage_self]
    exact fun y _ ↦ trivial
  have hspan : ((I₁ ⊔ I₂).ideal U').map (CommRingCat.ofHom
      (AffineBlowup.awayAlgebraMap ((I₁ ⊔ I₂).ideal U')
        (reesX ((I₁ ⊔ I₂).ideal U') b hbK))).hom =
      Ideal.span {(CommRingCat.ofHom (AffineBlowup.awayAlgebraMap ((I₁ ⊔ I₂).ideal U')
        (reesX ((I₁ ⊔ I₂).ideal U') b hbK))).hom b} := by
    rw [CommRingCat.hom_ofHom]
    exact AffineBlowup.map_awayAlgebraMap_eq_span ((I₁ ⊔ I₂).ideal U') b hbK
  have hcomp := chart_blowupι_comp_blowupMap (I₁ ⊔ I₂) U' b hbK
  rcases hb12 with hb | hb
  · exact Set.disjoint_left.mp
      (Scheme.IdealSheafData.disjoint_range_strictTransformMap_of_probe
        (I₁ ⊔ I₂) I₁ U' b hb _ hpre hspan _ hcomp) hx₁ hxc
  · exact Set.disjoint_left.mp
      (Scheme.IdealSheafData.disjoint_range_strictTransformMap_of_probe
        (I₁ ⊔ I₂) I₂ U' b hb _ hpre hspan _ hcomp) hx₂ hxc

end BoundarySeparation

end AlgebraicGeometry
