/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Exceptional
public import WeilConjectures.Compactification.StrictTransform

/-!

# Admissible blow-ups and boundary separation

This file records the admissible blow-up vocabulary and the boundary-separation
interface of the proof of Nagata's compactification theorem, following the *revised*
blueprint (`blueprint/src/macros/nagata_new revised(1).tex`). The revised blueprint
replaces the flattening route of the original blueprint (Stacks Tags 0815/081R and
081P/081L) by the boundary-separation route: the two-open compactification theorem
uses blow-ups of sums of ideals to separate boundary pieces (Stacks Tag 0F3V), common
modifications, and the dense-source valuative criterion — no module flattening is
needed. Accordingly, the flattening statements previously recorded here
(`exists_admissibleBlowup_flatStrictTransform`, `exists_flatteningIdeal_openStrictTransform`,
`flatStrictTransform_isOpenImmersion`, `flat_denseOpen_dimensionPackage`) have been
removed: they are not part of the revised proof.

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
- `AlgebraicGeometry.exists_admissibleBlowup_cartierBoundary` and its fully proved
  locally Noetherian instance
  `exists_admissibleBlowup_cartierBoundary_of_locallyNoetherian`: preparation of a
  Cartier boundary (`lemma:nagata-cartier-boundary-preparation`, Stacks Tag 080Y);
- `AlgebraicGeometry.separationBlowup` together with its `U`-admissibility
  (`coe_support_sup_subset`).

## Remaining inputs (Stacks citations of the revised blueprint)

The revised blueprint invokes the following Stacks Project results through its choice
notation (`def:nagata-choice-notation`); they remain `sorry` here:

- `Scheme.exists_finiteType_ideal_zeroLocus_compl_qcOpen`: a quasi-compact open of a
  qcqs scheme is the complement of the vanishing locus of a finite-type ideal
  (`def:nagata-qc-open-complement-ideal`, Stacks Tag 01PH);
- `Scheme.exists_finiteType_ideal_extension`: finite-type ideals extend from
  quasi-compact opens (`def:nagata-finite-type-ideal-extension`, Stacks Tag 01PF);
- `AdmissibleBlowup.exists_comp`: a composite of admissible blow-ups is an admissible
  blow-up (`lemma:nagata-admissible-blowup-comp`, Stacks Tag 080L; the revised
  blueprint derives it from `thm:nagata-composition-of-blowups`, which awaits the
  blow-up universal-property chapter);
- `separationBlowup_disjoint_strictTransforms`: disjointness of strict transforms
  after the separation blow-up (`lemma:nagata-separate-closed-subschemes`, Stacks
  Tag 0F3V). Unlike the others this one has a complete chart-level proof in the
  revised blueprint, using exactly the chart machinery of
  `WeilConjectures.Blowup.Exceptional`; it is the natural next formalization target.

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

/-- A `U`-admissible blow-up is an isomorphism over `U`. This transports the blow-up
complement theorem (`thm:nagata-global-blowup-complement`) across the chosen
identification with the blow-up of the center.
(Blueprint: `lemma:nagata-admissible-blowup-over-open`.) -/
theorem isIso_π_restrict : IsIso (B.π ∣_ U) := by
  rw [← B.iso_π, morphismRestrict_comp]
  haveI h1 : IsIso (B.iso.hom ∣_ B.I.blowupMap ⁻¹ᵁ U) := inferInstance
  haveI h2 : IsIso (B.I.blowupMap ∣_ U) :=
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

/-- **Composition of admissible blow-ups** (Stacks Project Tag 080L): for `X` qcqs
with `U` a quasi-compact open, the composite of a `U`-admissible blow-up of `X` with a
`π⁻¹(U)`-admissible blow-up of its total space is, up to isomorphism over `X`, again a
`U`-admissible blow-up of `X`.
(Blueprint: `lemma:nagata-admissible-blowup-comp`.) -/
theorem exists_comp [CompactSpace X] [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X))
    (B₁ : AdmissibleBlowup X U) (B₂ : AdmissibleBlowup B₁.X' (B₁.π ⁻¹ᵁ U)) :
    ∃ (B : AdmissibleBlowup X U) (e : B.X' ≅ B₂.X'), e.hom ≫ B₂.π ≫ B₁.π = B.π := by
  -- TODO (blueprint): `thm:nagata-composition-of-blowups` writes the composite as the
  -- blow-up of a single finite-type center supported away from `U`.
  sorry

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
  -- TODO (blueprint): finite-type approximation of `Scheme.IdealSheafData.vanishingIdeal`
  -- via `lemma:nagata-finite-type-ideal-extension-exists`.
  sorry

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

/-- **Preparation of a Cartier boundary** (Stacks Project Tag 080Y): on a
quasi-compact quasi-separated scheme `X` with a quasi-compact open `U`, there is a
`U`-admissible blow-up whose boundary — the complement of the preimage of `U` — is the
support of an effective Cartier ideal.
(Blueprint: `lemma:nagata-cartier-boundary-preparation`; proof order item 24.) -/
theorem exists_admissibleBlowup_cartierBoundary [CompactSpace X] [QuasiSeparatedSpace X]
    (hU : IsCompact (U : Set X)) :
    ∃ (B : AdmissibleBlowup X U) (J : B.X'.IdealSheafData), J.IsEffectiveCartier ∧
      (J.support : Set B.X') = ((B.π ⁻¹ᵁ U) : Set B.X')ᶜ := by
  obtain ⟨I, hft, hsupp⟩ := X.exists_finiteType_ideal_zeroLocus_compl_qcOpen U hU
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

/-- **Preparation of a Cartier boundary, locally Noetherian case**: on a locally
Noetherian scheme every open has a `U`-admissible blow-up with effective Cartier
boundary. In contrast to `exists_admissibleBlowup_cartierBoundary` this is fully
proved: the finite-type boundary ideal is the vanishing ideal of the reduced boundary.
This is the instance needed for the Noetherian compactification theorem
(`thm:nagata-noetherian`).
(Blueprint: `lemma:nagata-cartier-boundary-preparation`; proof order item 24.) -/
theorem exists_admissibleBlowup_cartierBoundary_of_locallyNoetherian
    [IsLocallyNoetherian X] :
    ∃ (B : AdmissibleBlowup X U) (J : B.X'.IdealSheafData), J.IsEffectiveCartier ∧
      (J.support : Set B.X') = ((B.π ⁻¹ᵁ U) : Set B.X')ᶜ := by
  obtain ⟨I, hft, hsupp⟩ := X.exists_finiteType_ideal_zeroLocus_compl_of_locallyNoetherian U
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

/-- **Extension of finite-type ideals from a quasi-compact open** (Stacks Project
Tag 01PF): on a qcqs scheme, a finite-type quasi-coherent ideal on a quasi-compact
open extends to a finite-type quasi-coherent ideal on the whole scheme. The revised
blueprint uses this to extend blow-up centers from opens
(`def:nagata-finite-type-ideal-extension`, `lemma:nagata-extend-finite-type-ideal`). -/
theorem _root_.AlgebraicGeometry.Scheme.exists_finiteType_ideal_extension
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (W : X.Opens)
    (hW : IsCompact (W : Set X)) (J : W.toScheme.IdealSheafData) (hJ : J.FiniteType) :
    ∃ I : X.IdealSheafData, I.FiniteType ∧ I.comap W.ι = J := by
  -- TODO (blueprint): Stacks Project Tag 01PF, by extending finitely generated pieces
  -- over a finite affine cover with quasi-compact overlaps.
  sorry

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

/-- **Boundary separation** (Stacks Project Tag 0F3V; revised blueprint
`lemma:nagata-separate-closed-subschemes`): after blowing up the sum of the ideals of
two finite-type centers whose common support is disjoint from `U`, the strict
transforms of the two centers are disjoint. -/
theorem separationBlowup_disjoint_strictTransforms (I₁ I₂ : X.IdealSheafData)
    (h₁ : I₁.FiniteType) (h₂ : I₂.FiniteType)
    (hdisj : Disjoint (U : Set X) ((I₁.support : Set X) ∩ (I₂.support : Set X))) :
    Disjoint
      (Set.range ((separationBlowup I₁ I₂ h₁ h₂ hdisj).strictTransformMap I₁.subschemeι))
      (Set.range ((separationBlowup I₁ I₂ h₁ h₂ hdisj).strictTransformMap
        I₂.subschemeι)) := by
  -- TODO (revised blueprint): the charts of `Bl_{I₁ ⊔ I₂}` at degree-one elements
  -- coming from local sections of `I₁` (resp. `I₂`) cover the blow-up. On a chart at
  -- `a ∈ I₁(V)`, the pullback of `a` to `Z₁ ×_X Bl` vanishes while the extended ideal
  -- is generated by `a` (`AffineBlowup.map_awayAlgebraMap_eq_span`), so the locus of
  -- `Z₁ ×_X Bl` over the complement of the center misses the chart; since the strict
  -- transform is the closure of that locus and closure commutes with restriction to
  -- opens, the strict transform of `Z₁` misses every `I₁`-chart, and symmetrically for
  -- `Z₂`. The two strict transforms therefore live over complementary charts.
  sorry

end BoundarySeparation

end AlgebraicGeometry
