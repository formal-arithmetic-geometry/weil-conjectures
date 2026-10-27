/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.TensorSectionAffineOpen
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints

/-! # Finite invariant norm pencils from orbit-separated pairs

Source: Stacks Project, Constructions, Tag 01NE and Definition 01NF; Morphisms, Tag 01WN;
Modules, Tags 01CA and 01CD.
(blueprint: lem-sfb-proper-orbit-pair-finite-norm)

The orbit tensor and its pure tensor section are the existing pencil constructions.
The permutation relation records actual composites of associators and braidings, with
labelled factors. Thus the comparison in the statement is the canonical reindexing map,
rather than an unspecified isomorphism preserving just two sections.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The existing tensor of translates, expressed as a compatible global section.
This only applies the existing section/Hom equivalence to `pencilTranslateSection`.
Source: Stacks Modules, Tags 01CA, 01CD.
(blueprint: lem-sfb-proper-orbit-pair-finite-norm) -/
noncomputable def orbitTensorNormSection {Y : Scheme.{u}} {G : Type v} [Finite G]
    (ρ : G → Aut Y) (M : Y.Modules) (a : M.sections) :
    (pencilOrbitBundle ρ M).sections :=
  SheafOfModules.unitHomEquiv _ (homOfGlobalSection _
    (pencilTranslateSection ρ M a (pencilGroupElements G)))

/-- Canonical labelled factor permutations: precisely composites of tensor identities,
associators, and the symmetric braiding. The source and target lists track every factor,
even when the action is not faithful. Symmetric monoidal coherence makes the resulting map
independent of the chosen permutation expression.
Source: Stacks Modules, Tag 01CA, finite tensor permutations.
(blueprint: lem-sfb-proper-orbit-pair-finite-norm) -/
inductive PencilTensorPermutation {Y : Scheme.{u}} {G : Type v}
    (ρ : G → Aut Y) (M : Y.Modules) :
    {l l' : List G} → (pencilTranslateTensor ρ M l ≅ pencilTranslateTensor ρ M l') → Prop
  | nil : PencilTensorPermutation ρ M (l := []) (l' := [])
      (Iso.refl (pencilTranslateTensor ρ M []))
  | cons (g : G) {l l' : List G}
      {e : pencilTranslateTensor ρ M l ≅ pencilTranslateTensor ρ M l'}
      (he : PencilTensorPermutation ρ M e) :
      PencilTensorPermutation ρ M (l := g :: l) (l' := g :: l')
        (Iso.refl ((tensorPullback (ρ g).hom).obj M) ⊗ᵢ e)
  | swap (g k : G) (l : List G) :
      PencilTensorPermutation ρ M (l := g :: k :: l) (l' := k :: g :: l)
        ((α_ ((tensorPullback (ρ g).hom).obj M) ((tensorPullback (ρ k).hom).obj M)
          (pencilTranslateTensor ρ M l)).symm ≪≫
          ((β_ ((tensorPullback (ρ g).hom).obj M) ((tensorPullback (ρ k).hom).obj M))
            ⊗ᵢ Iso.refl (pencilTranslateTensor ρ M l)) ≪≫
          (α_ ((tensorPullback (ρ k).hom).obj M) ((tensorPullback (ρ g).hom).obj M)
            (pencilTranslateTensor ρ M l)))
  | trans {l l' l'' : List G}
      {e : pencilTranslateTensor ρ M l ≅ pencilTranslateTensor ρ M l'}
      {e' : pencilTranslateTensor ρ M l' ≅ pencilTranslateTensor ρ M l''}
      (he : PencilTensorPermutation ρ M e) (he' : PencilTensorPermutation ρ M e') :
      PencilTensorPermutation ρ M (e ≪≫ e')

/-- Distribute pullback across the actual translated tensor, then use pullback composition
and the action law to replace the factor `h* g* M` by `(g h)* M`. No permutation or arbitrary
choice is hidden here; the remaining reordering is recorded by `PencilTensorPermutation`.
Source: Stacks Modules, Tag 01CD; Sheaves, Tag 0097.
(blueprint: lem-sfb-proper-orbit-pair-finite-norm) -/
noncomputable def orbitTensorPullbackReindexIso {Y : Scheme.{u}} {G : Type v} [Group G]
    (ρ : G →* Aut Y) (M : Y.Modules) (h : G) :
    (l : List G) →
      (tensorPullback (ρ h).hom).obj (pencilTranslateTensor (fun g ↦ ρ g) M l) ≅
        pencilTranslateTensor (fun g ↦ ρ g) M (l.map (fun g ↦ g * h))
  | [] => (boundaryPullbackComparison (ρ h).hom).app _ ≪≫ pullbackObjUnitIso (ρ h).hom
  | g :: l =>
    boundaryPullbackTensorIso (ρ h).hom ((tensorPullback (ρ g).hom).obj M)
      (pencilTranslateTensor (fun k ↦ ρ k) M l) ≪≫
      (((tensorPullbackSectionComp (ρ h).hom (ρ g).hom).symm.app M ≪≫
        eqToIso (congrArg (fun f : Y ⟶ Y ↦ (tensorPullback f).obj M)
          (congrArg Iso.hom (ρ.map_mul g h)).symm)) ⊗ᵢ
        orbitTensorPullbackReindexIso ρ M h l)

/-- An orbit-separated pair on a proper scheme with affine nonvanishing opens defines finite
ordinary and invariant norm coordinate morphisms, with their chart and section identities.

Source: Stacks Constructions, Tag 01NE and Definition 01NF; Morphisms, Tags 01S8, 01W6,
01WN; Modules, Tags 01CA, 01CD, 01CT, 01CY; Properties, Tag 01PV.
(blueprint: lem-sfb-proper-orbit-pair-finite-norm)

Proof, following the node's seven steps:
1. Invertibility is preserved by pullback and finite tensor products, by
[lem-weil-pbc-invertible-pullback-tensor]. Residue-field nonvanishing commutes with pullback
by [lem-sc-nonvanishing-tensor-pullback], and a pure tensor of vectors over a field is nonzero
exactly when every factor is nonzero. Apply [lem-sc-tensor-section-affine-open] to obtain
the two norm zero-locus formulas and affineness of their complements: the identity factor
has affine nonvanishing locus U or V. Unit tails and parentheses are removed by unitors.
2. Orbit separation implies the norm sections have no common zero. The identity translate
also makes a,b have no common zero. Apply
[lem-weil-pbc-invertible-generating-sections-fibre] to both pairs to get the two epimorphisms.
3. Form their coordinate maps using
[def-weil-pbc-morphism-to-projective-space-by-sections]. Apply
[lem-weil-pbc-projective-morphism-chart-preimage] and step 1 for the four chart equalities.
Equality of opens identifies their restricted structure sheaves and hence open subschemes.
4. By [lem-weil-pbc-projective-space-standard-charts], the two standard target charts form
an affine cover. Their inverse images are affine by the hypotheses and step 1. Hence
[pqf-lem-affine-local-target] makes both maps affine.
5. Projective space is proper, hence separated, over the field by
[lemma-nagata-projective-space-base-change-proper]. Both maps are over the field, so
[lem-weil-pbc-proper-over-separated] makes them proper. Apply
[lem-sfb-affine-proper-finite] to the affine proper maps.
6. Distribute h* over the tensor, use pullback composition and (gh)(y)=g(h(y)), and permute
labels g to gh, using [lem-weil-pbc-invertible-pullback-tensor] and
[lem-weil-pbc-module-tensor-symmetric-monoidal]. Right multiplication is bijective, so this
permutation is generated by the displayed adjacent swaps. The pure tensor section formulas
send h*A to A and h*D to D. Repeated automorphisms retain their separate labels.
7. Pullback naturality and equivalence of generating pairs in
[lem-weil-pbc-projective-space-functor-of-points] identify the integral coordinate maps.
Their base components agree because the action is over the field. Fibre-product uniqueness
in [def-weil-pbc-morphism-to-projective-space-by-sections] gives h ≫ f_N = f_N, as scheme
morphisms, including on nonreduced schemes.
-/
theorem proper_orbit_pair_finite_norm
    (F : Type u) [Field F] (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of F))
    [IsProper p] (G : Type v) [Group G] [Finite G] (ρ : G →* Aut Y)
    (hρ : ∀ g : G, (ρ g).hom ≫ p = p) (M : Y.Modules) [M.IsInvertible]
    (a b : M.sections) (U V : Y.Opens)
    (hU : (U : Set Y) = nonvanishingLocus M (a.val (op ⊤)))
    (hV : (V : Set Y) = nonvanishingLocus M (b.val (op ⊤)))
    (haffU : IsAffineOpen U) (haffV : IsAffineOpen V)
    (hsep : Disjoint
      (⋃ g : G, (ρ g).hom ⁻¹' (nonvanishingLocus M (a.val (op ⊤)))ᶜ)
      (⋃ g : G, (ρ g).hom ⁻¹' (nonvanishingLocus M (b.val (op ⊤)))ᶜ)) :
    ∃ (hC : (pencilOrbitBundle (fun g ↦ ρ g) M).IsInvertible)
      (hab : Epi (M.freeHomEquiv.symm (pencilSectionPair M a b)))
      (hAD : Epi ((pencilOrbitBundle (fun g ↦ ρ g) M).freeHomEquiv.symm
        (pencilSectionPair _ (orbitTensorNormSection (fun g ↦ ρ g) M a)
          (orbitTensorNormSection (fun g ↦ ρ g) M b)))),
      (nonvanishingLocus _
        ((orbitTensorNormSection (fun g ↦ ρ g) M a).val (op ⊤)))ᶜ =
        ⋃ g : G, (ρ g).hom ⁻¹' (nonvanishingLocus M (a.val (op ⊤)))ᶜ ∧
      (nonvanishingLocus _
        ((orbitTensorNormSection (fun g ↦ ρ g) M b).val (op ⊤)))ᶜ =
        ⋃ g : G, (ρ g).hom ⁻¹' (nonvanishingLocus M (b.val (op ⊤)))ᶜ ∧
      IsFinite (pencilCoordinateMorphism p M inferInstance a b hab) ∧
      IsFinite (pencilCoordinateMorphism p _ hC
        (orbitTensorNormSection (fun g ↦ ρ g) M a)
        (orbitTensorNormSection (fun g ↦ ρ g) M b) hAD) ∧
      (pencilCoordinateMorphism p M inferInstance a b hab ⁻¹ᵁ
        ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (CommRingCat.of F)) ⟨0⟩) = U ∧
      (pencilCoordinateMorphism p M inferInstance a b hab ⁻¹ᵁ
        ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (CommRingCat.of F)) ⟨1⟩) = V ∧
      (∀ i : ULift.{u} (Fin 2),
        pencilCoordinateMorphism p _ hC
          (orbitTensorNormSection (fun g ↦ ρ g) M a)
          (orbitTensorNormSection (fun g ↦ ρ g) M b) hAD ⁻¹ᵁ
            ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (CommRingCat.of F)) i =
          ⨅ g : G, (ρ g).hom ⁻¹ᵁ (if i.down = 0 then U else V)) ∧
      (∀ i : ULift.{u} (Fin 2),
        IsAffineOpen (pencilCoordinateMorphism p M inferInstance a b hab ⁻¹ᵁ
          ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (CommRingCat.of F)) i) ∧
        IsAffineOpen (pencilCoordinateMorphism p _ hC
          (orbitTensorNormSection (fun g ↦ ρ g) M a)
          (orbitTensorNormSection (fun g ↦ ρ g) M b) hAD ⁻¹ᵁ
            ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (CommRingCat.of F)) i)) ∧
      (∀ h : G, ∃ e :
        pencilTranslateTensor (fun g ↦ ρ g) M
          ((pencilGroupElements G).map (fun g ↦ g * h)) ≅ pencilOrbitBundle (fun g ↦ ρ g) M,
        PencilTensorPermutation (fun g ↦ ρ g) M e ∧
        ((orbitTensorPullbackReindexIso ρ M h (pencilGroupElements G)) ≪≫ e).hom.app ⊤
          (((tensorPullbackSectionAdjunction (ρ h).hom).unit.app
            (pencilOrbitBundle (fun g ↦ ρ g) M)).app ⊤
              ((orbitTensorNormSection (fun g ↦ ρ g) M a).val (op ⊤))) =
          (orbitTensorNormSection (fun g ↦ ρ g) M a).val (op ⊤) ∧
        ((orbitTensorPullbackReindexIso ρ M h (pencilGroupElements G)) ≪≫ e).hom.app ⊤
          (((tensorPullbackSectionAdjunction (ρ h).hom).unit.app
            (pencilOrbitBundle (fun g ↦ ρ g) M)).app ⊤
              ((orbitTensorNormSection (fun g ↦ ρ g) M b).val (op ⊤))) =
          (orbitTensorNormSection (fun g ↦ ρ g) M b).val (op ⊤) ∧
        (ρ h).hom ≫ pencilCoordinateMorphism p _ hC
          (orbitTensorNormSection (fun g ↦ ρ g) M a)
          (orbitTensorNormSection (fun g ↦ ρ g) M b) hAD =
          pencilCoordinateMorphism p _ hC
            (orbitTensorNormSection (fun g ↦ ρ g) M a)
            (orbitTensorNormSection (fun g ↦ ρ g) M b) hAD) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
