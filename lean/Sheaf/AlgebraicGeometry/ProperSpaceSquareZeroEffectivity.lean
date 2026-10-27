/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Category.Preorder
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Effectivity of proper algebraic spaces over square-zero ring towers

Source: Stacks Project, quot.tex, Tag 0D3X, proof of lemma-spaces-defo-thy,
from the inverse system of rings through the final deformation-property argument
(blueprint: lem-sfb-proper-space-square-zero-effectivity).

The common ambient base is the terminal scheme, equivalently Spec Z. Index `n : ℕ`
represents the source's index `n + 1`. Cartesian transition arrows encode the specified
base-change isomorphisms; functoriality encodes their identity and cocycle conditions.
The limit ring is Mathlib's subring of compatible sequences, with coordinate projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The existing spectrum and representable algebraic-space constructions, packaged
functorially over the terminal scheme. No atlas, new space, or map is chosen.
Source: Stacks, Spaces, Tags 025Y and 03I4, used in quot.tex, Tag 0D3X
(blueprint: lem-sfb-proper-space-square-zero-effectivity). -/
def effectivitySpectrum : CommRingCat.{u}ᵒᵖ ⥤ AlgebraicSpace (⊤_ Scheme.{u}) :=
  ObjectProperty.lift IsAlgebraicSpace
    (Scheme.Spec ⋙ (Over.equivalenceOfIsTerminal terminalIsTerminal).inverse ⋙
      (Scheme.fppfTopology.over (⊤_ Scheme.{u})).yoneda)
    (fun A ↦ schemeSheaf_isAlgebraicSpace
      ((Over.equivalenceOfIsTerminal terminalIsTerminal).inverse.obj (Spec A.unop)))

/-- Commutativity of the existing compatible-sequence subring comes from its ambient
product of commutative rings; this supplies only an instance, not new ring data.
Source: Stacks, quot.tex, Tag 0D3X, inverse-limit ring in the proof
(blueprint: lem-sfb-proper-space-square-zero-effectivity). -/
instance effectivitySectionsCommRing (R : ℕᵒᵖ ⥤ CommRingCat.{u}) :
    CommRing (RingCat.sectionsSubring (R ⋙ forget₂ CommRingCat RingCat)) :=
  @Subring.toCommRing (∀ i : ℕᵒᵖ, R.obj i) inferInstance
    (RingCat.sectionsSubring (R ⋙ forget₂ CommRingCat RingCat))

/-- The concrete inverse-limit ring: compatible sequences, with coordinatewise operations.
This is the existing `RingCat.sectionsSubring`, specialized to the given ring tower.
Source: Stacks, quot.tex, Tag 0D3X, inverse-limit ring in the proof
(blueprint: lem-sfb-proper-space-square-zero-effectivity). -/
abbrev effectivityRing (R : ℕᵒᵖ ⥤ CommRingCat.{u}) : CommRingCat.{u} :=
  .of (RingCat.sectionsSubring (R ⋙ forget₂ CommRingCat RingCat))

/-- Evaluation of a compatible sequence at its specified coordinate.
Source: Stacks, quot.tex, Tag 0D3X, projections of the inverse-limit ring
(blueprint: lem-sfb-proper-space-square-zero-effectivity). -/
def effectivityRingProjection (R : ℕᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ) :
    effectivityRing R ⟶ R.obj (op n) :=
  CommRingCat.ofHom ((Pi.evalRingHom (fun i : ℕᵒᵖ ↦ R.obj i) (op n)).comp
    (RingCat.sectionsSubring (R ⋙ forget₂ CommRingCat RingCat)).subtype)

/-- Compatible flat proper finitely presented spaces over a surjective square-zero
ring tower are effective over the concrete inverse-limit ring, with all specified
transition identifications retained. A pullback square is the isomorphism to the
base change together with its structural projections; naturality of `a` is exactly
compatibility with every transition identification.

Source: Stacks, quot.tex, Tag 0D3X, proof of lemma-spaces-defo-thy
(blueprint: lem-sfb-proper-space-square-zero-effectivity).

Proof:
1. Set I_n = ker(R_n to R_1) and I = lim I_n. All I_n have square zero, since the
   hypothesis covers every transition. Recursive lifting proves surjectivity of the
   projections R to R_n and I to I_n. Coordinatewise multiplication proves I^2 = 0
   and identifies I with ker(R to R_1).
2. The given cartesian squares make X_1 a first-order thickening in each X_n.
   By lem-sfb-space-first-order-ringed-description and the forward implication of
   lem-sfb-space-square-zero-flatness-criterion, their ring sheaves on X_1,et form
   extensions with kernels F_n = O_X_1 tensor I_n. Free presentations show the
   kernels are quasi-coherent (def-pur-sheaf-tensor-product and
   def-trf-space-quasi-coherent-module). Their transition maps are surjective.
3. Take sectionwise limits E = lim O_X_n and G = lim F_n. On every affine etale
   chart, lem-sfb-space-surjective-qcoh-limit gives H^1(F_n) = 0 and surjective
   maps of kernel sections. Lift a section recursively, correcting each lift by
   a lifted kernel section. Thus 0 to G to E to O_X_1 to 0 is exact, with G^2 = 0.
4. Put F = O_X_1 tensor I. The canonical u : F to G induces bijections on derived
   Hom from every complex with quasi-coherent cohomology by
   lem-sfb-proper-flat-space-pullback-limit, using properness, flatness and finite
   presentation of X_1. This does not identify the ordinary sheaves F and G.
5. Apply lem-sfb-space-square-zero-extension-transfer, with base-ideal map
   i mapping to 1 tensor i. X_1 is qcqs. The preceding derived-Hom bijections
   give a ring-sheaf extension E' by F whose pushout along u is E, and hence an
   R-algebra map E' to E inducing the identity on the quotient and u on ideals.
6. Realize E' as a first-order thickening X_1 in X by
   lem-sfb-space-first-order-ringed-description. Its base-ideal map is the identity.
   The reverse implication of lem-sfb-space-square-zero-flatness-criterion gives
   flatness of X over R and the cartesian reduction X times_R R_1 = X_1.
7. The maps E' to E to O_X_n give X_n to X. By
   lem-trf-space-fibre-products-etale-covers they induce X_n to X times_R R_n.
   Their reduction to X_1 is the identity. The isomorphism clause of
   lem-sfb-space-flat-deformation-properties applies because X_n is flat over R_n,
   so these maps are isomorphisms. Uniqueness of the ringed realization and the
   fibre-product universal property give compatibility with every transition.
8. Finally lem-sfb-space-flat-deformation-properties, applied over the square-zero
   extension R to R_1, lifts properness and finite presentation from X_1 to X.
   This gives all the asserted properties and compatible cartesian squares. -/
theorem exists_properSpace_squareZero_effective
    (R : ℕᵒᵖ ⥤ CommRingCat.{u})
    (hSurj : ∀ (i j : ℕᵒᵖ) (b : i ⟶ j), Function.Surjective (R.map b))
    (hSq : ∀ (i j : ℕᵒᵖ) (b : i ⟶ j), RingHom.ker (R.map b).hom ^ 2 = ⊥)
    (X : ℕ ⥤ AlgebraicSpace (⊤_ Scheme.{u}))
    (f : ∀ n : ℕ, X.obj n ⟶ (R.rightOp ⋙ effectivitySpectrum).obj n)
    (hFlat : ∀ n : ℕ, MapIsFlat (f n))
    (hProper : ∀ n : ℕ, MapIsProper (f n))
    (hQC : ∀ n : ℕ, MapIsQuasiCompact (f n).hom.hom)
    (hQS : ∀ n : ℕ, MapIsQuasiCompact (pullback.diagonal (f n).hom.hom))
    (hLFP : ∀ n : ℕ, MapIsLocallyOfFinitePresentation (f n))
    (hCart : ∀ (n m : ℕ) (b : n ⟶ m),
      IsPullback (X.map b).hom (f n).hom (f m).hom
        ((R.rightOp ⋙ effectivitySpectrum).map b).hom) :
    ∃ (Y : AlgebraicSpace (⊤_ Scheme.{u}))
      (g : Y ⟶ effectivitySpectrum.obj (op (effectivityRing R)))
      (a : X ⟶ (Functor.const ℕ).obj Y),
      MapIsFlat g ∧ MapIsProper g ∧ MapIsQuasiCompact g.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal g.hom.hom) ∧
      MapIsLocallyOfFinitePresentation g ∧
      ∀ n : ℕ, IsPullback (a.app n).hom (f n).hom g.hom
        (effectivitySpectrum.map (effectivityRingProjection R n).op).hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
