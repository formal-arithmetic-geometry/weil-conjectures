/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Orbit-separated pencils from an ample power on a curve

Source: de Jong, Families of curves and alterations (1997), §3.4(b), p.606;
Stacks Project, Properties, Tag 09NV, and Modules, Tags 01CA, 01CD.
(blueprint: lem-sfb-ample-curve-two-section-pencil)

The auxiliary constructions implement the bundle and norm section already introduced in
this node. A finite enumeration fixes parentheses, and the existing pullback-power and
symmetric tensor-power comparisons put the norm in the actual power of the orbit bundle.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Enumerate a finite group once, solely to parenthesize its tensor product.
Source: de Jong §3.4(b), the product of translates.
(blueprint: lem-sfb-ample-curve-two-section-pencil) -/
noncomputable def pencilGroupElements (G : Type v) [Finite G] : List G :=
  letI := Fintype.ofFinite G
  List.ofFn (Fintype.equivFin G).symm

/-- Right-associated tensor product of the indicated translated modules, with unit tail.
Source: Stacks Modules, Tags 01CA and 01CD; de Jong §3.4(b).
(blueprint: lem-sfb-ample-curve-two-section-pencil) -/
noncomputable def pencilTranslateTensor {Y : Scheme.{u}} {G : Type v}
    (ρ : G → Aut Y) (L : Y.Modules) : List G → Y.Modules
  | [] => 𝟙_ Y.Modules
  | g :: gs => (tensorPullback (ρ g).hom).obj L ⊗ pencilTranslateTensor ρ L gs

/-- The bundle `B = ⨂ g, g* L` in a fixed finite enumeration.
Source: de Jong §3.4(b), the product of translates; Stacks Modules, Tag 01CA.
(blueprint: lem-sfb-ample-curve-two-section-pencil) -/
noncomputable def pencilOrbitBundle {Y : Scheme.{u}} {G : Type v} [Finite G]
    (ρ : G → Aut Y) (L : Y.Modules) : Y.Modules :=
  pencilTranslateTensor ρ L (pencilGroupElements G)

/-- Remove the unit factors in a tensor power of the unit, using only the unitors.
Source: Stacks Modules, Tag 01CA.
(blueprint: lem-sfb-ample-curve-two-section-pencil) -/
noncomputable def pencilUnitPowerIso (Y : Scheme.{u}) :
    ∀ d : ℕ, (𝟙_ Y.Modules).tensorPow d ≅ 𝟙_ Y.Modules
  | 0 => Iso.refl _
  | d + 1 => (Iso.refl _ ⊗ᵢ pencilUnitPowerIso Y d) ≪≫ (λ_ _)

/-- The canonical permutation from the tensor of translated powers to the power of the
translated tensor: first pullback-power comparison, then symmetric distribution of powers.
Source: Stacks Modules, Tags 01CA and 01CD.
(blueprint: lem-sfb-ample-curve-two-section-pencil) -/
noncomputable def pencilTranslatePowerIso {Y : Scheme.{u}} {G : Type v}
    (ρ : G → Aut Y) (L : Y.Modules) (d : ℕ) :
    ∀ gs : List G, pencilTranslateTensor ρ (L.tensorPow d) gs ≅
      (pencilTranslateTensor ρ L gs).tensorPow d
  | [] => (pencilUnitPowerIso Y d).symm
  | g :: gs =>
    (boundaryPullbackPowIso (ρ g).hom L d ⊗ᵢ pencilTranslatePowerIso ρ L d gs) ≪≫
      (tensorPowTensorObjIso ((tensorPullback (ρ g).hom).obj L)
        (pencilTranslateTensor ρ L gs) d).symm

/-- Tensor the pullbacks of a section, terminating with the unit section `1`.
The adjunction unit is the canonical `s ↦ 1 ⊗ s`; restriction to the top open is explicit.
Source: Stacks Sheaves, Tag 0096; Modules, Tag 01CD; de Jong §3.4(b).
(blueprint: lem-sfb-ample-curve-two-section-pencil) -/
noncomputable def pencilTranslateSection {Y : Scheme.{u}} {G : Type v}
    (ρ : G → Aut Y) (M : Y.Modules) (s : M.sections) :
    ∀ gs : List G, Γ(pencilTranslateTensor ρ M gs, ⊤)
  | [] => unitSectionsEquiv ⊤ 1
  | g :: gs => tmulSection
      (((tensorPullback (ρ g).hom).obj M).presheaf.map
        (homOfLE (Scheme.Hom.preimage_top (ρ g).hom).ge).op
        (((tensorPullbackSectionAdjunction (ρ g).hom).unit.app M).app ⊤
          (s.val (op ⊤))))
      (pencilTranslateSection ρ M s gs)

/-- The norm `N_G(s) = ⨂ g, g* s`, transported by the canonical permutation into `B^d`.
Global sections are encoded as compatible families, using the existing section/Hom equivalence.
Source: de Jong §3.4(b), and Stacks Modules, Tags 01CA and 01CD.
(blueprint: lem-sfb-ample-curve-two-section-pencil) -/
noncomputable def pencilNormSection {Y : Scheme.{u}} {G : Type v} [Finite G]
    (ρ : G → Aut Y) (L : Y.Modules) (d : ℕ) (s : (L.tensorPow d).sections) :
    ((pencilOrbitBundle ρ L).tensorPow d).sections :=
  SheafOfModules.unitHomEquiv _ (homOfGlobalSection _
    ((pencilTranslatePowerIso ρ L d (pencilGroupElements G)).hom.app ⊤
      (pencilTranslateSection ρ (L.tensorPow d) s (pencilGroupElements G))))

/-- The two-entry family, in the coefficient universe used by the existing free-sheaf API.
Source: Stacks Constructions, Tag 01NE.
(blueprint: lem-sfb-ample-curve-two-section-pencil) -/
noncomputable def pencilSectionPair {Y : Scheme.{u}} (M : Y.Modules) (a b : M.sections) :
    ULift.{u} (Fin 2) → M.sections :=
  fun i ↦ if i.down = 0 then a else b

/-- The coordinate morphism of a generating pair, with the invertibility proof explicit.
This is exactly the existing projective-coordinate construction, without a new chosen map.
Source: Stacks Constructions, Tag 01NE and Definition 01NF.
(blueprint: lem-sfb-ample-curve-two-section-pencil) -/
noncomputable def pencilCoordinateMorphism {Y S : Scheme.{u}} (f : Y ⟶ S)
    (M : Y.Modules) (hM : M.IsInvertible) (a b : M.sections)
    (h : Epi (M.freeHomEquiv.symm (pencilSectionPair M a b))) :
    Y ⟶ ℙ(ULift.{u} (Fin 2); S) :=
  letI := hM
  ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin 2)) f M
    (pencilSectionPair M a b) h

/-- On a nonempty projective scheme of dimension at most one over any field, some positive
ample power admits an orbit-separated pair; the ordinary and norm pairs generate and give
finite coordinate morphisms, the norm morphism being invariant as a scheme morphism.

Source: de Jong, Families of curves and alterations, §3.4(b), p.606, with the orbit-separation
argument of this node; Stacks Properties, Tag 09NV; Modules, Tags 01CA, 01CD, 01CY;
Constructions, Tag 01NE; Morphisms, Tags 01S8, 01WC and 01WN.
(blueprint: lem-sfb-ample-curve-two-section-pencil)

Proof, following the node's ten steps:
1. Finite type over a field makes Y Noetherian. Its finitely many irreducible components have
unique generic points; collect them in the finite nonempty set E. Use
[lem-weil-pbc-finite-type-over-noetherian], [lem-sc-noetherian-closed-subset-finite-components]
and [lem-weil-pbc-scheme-sober].
2. Apply [lem-sc-ample-finite-principal-affine] (09NV) to E inside Y. Obtain p > 0 and a section
u of L^p with affine nonvanishing open U containing all generic points.
3. Z = Y \ U contains no component generic point. A chain A ⊊ D in Z would extend to
A ⊊ D ⊊ C_i in Y, contradicting dim Y ≤ 1. Thus dim Z ≤ 0, and
[lem-sc-zero-dim-noetherian-closed-finite] makes Z a finite set of closed points. The needed
Noetherian-space and T0 properties follow from
[lem-weil-pbc-noetherian-scheme-closed-subsets-minimal] and sobriety.
4. The finite set T = ⋃ g, g⁻¹ Z is G-stable. Apply the same 09NV lemma to E ∪ T to obtain
q > 0 and v in L^q with affine nonvanishing open V containing E ∪ T.
5. Set d = pq, a = u^q and b = v^p. The tensor-fibre formulas of
[lem-weil-pbc-invertible-pullback-tensor] identify their nonvanishing opens with U and V.
6. Since b is nonzero on the G-stable T, the two orbit zero unions are disjoint. The identity
element gives disjoint ordinary zero sets, so the fibre criterion
[lem-weil-pbc-invertible-generating-sections-fibre] makes a,b generating.
7. Pullbacks and finite tensors preserve invertibility. The canonical tensor permutation
places the norm sections in B^d; their zero sets are exactly the two orbit unions by the
residue-fibre formulas. The same fibre criterion makes the norm pair generating.
8. The generating pairs define coordinate morphisms by
[def-weil-pbc-morphism-to-projective-space-by-sections] and
[lem-weil-pbc-projective-space-functor-of-points]. Their inverse images of the two standard
charts [lem-weil-pbc-projective-space-standard-charts] are U,V and their translated
intersections, respectively, by the residue pullback formula.
9. Y is proper and separated over F by [lem-kun-projective-implies-proper]. The finite
intersections are affine by [lem-weil-pbc-separated-affine-open-intersection], so both maps
are affine by [pqf-lem-affine-local-target]. Projective space is proper, hence separated,
by [lemma-nagata-projective-space-base-change-proper]. Both maps are proper by
[lem-weil-pbc-proper-over-separated], and finite by [lem-sfb-affine-proper-finite].
10. For h in G the permutation g ↦ gh identifies h*(B^d) with B^d and carries both pulled
norm sections to the original ones. Pullback compatibility and pair equivalence in 01NE,
followed by uniqueness of the coordinate morphism, give h ≫ f_N = f_N as scheme morphisms.
This includes nilpotents and nonfaithful actions and does not use rational parameter points.
-/
theorem exists_ample_curve_two_section_pencil
    (F : Type u) [Field F] (Y : Scheme.{u}) [Nonempty Y]
    (f : Y ⟶ Spec (CommRingCat.of F)) [IsHProjective f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim Y ≤ 1) (L : Y.Modules) [L.IsInvertible]
    (hL : IsAmple Y L) (G : Type v) [Group G] [Finite G]
    (ρ : G →* Aut Y) (hρ : ∀ g : G, (ρ g).hom ≫ f = f) :
    ∃ d : ℕ, 0 < d ∧ ∃ a b : (L.tensorPow d).sections,
      Disjoint
        (⋃ g : G, (ρ g).hom ⁻¹'
          (nonvanishingLocus (L.tensorPow d) (a.val (op ⊤)))ᶜ)
        (⋃ g : G, (ρ g).hom ⁻¹'
          (nonvanishingLocus (L.tensorPow d) (b.val (op ⊤)))ᶜ) ∧
      ∃ (hB : ((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow d).IsInvertible)
        (ha : Epi ((L.tensorPow d).freeHomEquiv.symm
          (pencilSectionPair (L.tensorPow d) a b)))
        (hN : Epi (((pencilOrbitBundle (fun g ↦ ρ g) L).tensorPow d).freeHomEquiv.symm
          (pencilSectionPair _ (pencilNormSection (fun g ↦ ρ g) L d a)
            (pencilNormSection (fun g ↦ ρ g) L d b)))),
        IsFinite (pencilCoordinateMorphism f (L.tensorPow d) inferInstance a b ha) ∧
        IsFinite (pencilCoordinateMorphism f _ hB
          (pencilNormSection (fun g ↦ ρ g) L d a)
          (pencilNormSection (fun g ↦ ρ g) L d b) hN) ∧
        ∀ g : G, (ρ g).hom ≫ pencilCoordinateMorphism f _ hB
          (pencilNormSection (fun g ↦ ρ g) L d a)
          (pencilNormSection (fun g ↦ ρ g) L d b) hN =
          pencilCoordinateMorphism f _ hB
            (pencilNormSection (fun g ↦ ρ g) L d a)
            (pencilNormSection (fun g ↦ ρ g) L d b) hN := by
  sorry

end AlgebraicGeometry.Scheme.Modules
