/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres
public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.FieldTheory.FieldTower
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.GDelta.Basic
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.FiniteEquivariantQuasiSplitNodalFibres
import Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace

/-! # Invariant boundary control for marked nodal curves

Source: de Jong, Families of curves and alterations (1997), Remark 2.5, p. 603,
§§3.3, 5.5--5.7 and the proof of Theorem 5.9, p. 617
(blueprint: lem-sfb-marked-nodal-boundary-control).

The explicit exceptional set includes the images of the nonsmooth locus and the
vertical boundary components, followed by all translates under the finite group.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The explicit exceptional boundary: translate the nonsmooth image and the images of
all boundary components whose images are not dense in the base. Components are taken
in the subspace `Z`, then mapped into `V` by `Subtype.val`.
Source: de Jong (1997), Remark 2.5 and Theorem 5.9 proof, pp. 603, 617;
the explicit construction in Step 4
(blueprint: lem-sfb-marked-nodal-boundary-control). -/
def markedNodalBoundary {V B : Scheme.{u}} (v : V ⟶ B)
    [LocallyOfFinitePresentation v] (Z : Set V)
    (G : Type w) [Group G] (σB : G →* Aut B) : Set B :=
  ⋃ g : G, (σB g).hom ''
    (v '' (v.smoothLocus : Set V)ᶜ ∪
      ⋃ (C : Set Z) (_ : C ∈ irreducibleComponents Z)
        (_ : ¬ Dense (v '' (Subtype.val '' C))), v '' (Subtype.val '' C))

/-- A marked quasi-split nodal curve has the specified invariant exceptional boundary,
and its family, markings, section equations and boundary control persist under every
base change, including the empty base and maps supported in the exceptional set.

Source: de Jong (1997), Remark 2.5, p. 603, §§3.3, 5.5--5.7 and Theorem 5.9 proof,
p. 617 (blueprint: lem-sfb-marked-nodal-boundary-control).

Proof:
1. Finite presentation and the H-projective embedding give projectivity and properness
   (def-pc-projective-morphism, lem-pc-projective-proper). Finite type over the Noetherian
   field spectrum makes B and V Noetherian (lem-weil-pbc-finite-type-over-noetherian).
   The boundary has finitely many closed irreducible components
   (lem-sc-noetherian-closed-subset-finite-components). Sections are closed immersions
   (lem-weil-pbc-section-separated-closed-immersion), so their finite union M is closed.
2. The generic point of a component dominating B maps to the unique generic point of B
   (lem-sc-scheme-sober). The generic boundary condition puts that point in M, hence its
   closure, the whole component, lies in M. Images of the other components are proper
   closed subsets of B, because v is proper.
3. The relative smooth locus is open and commutes with base change for the flat finitely
   presented family (lem-sfb-flat-space-smooth-locus). Smoothness of the generic fibre
   implies that the closed nonsmooth locus has image avoiding the generic point.
4. Take the union of that image, all vertical component images, and all their G-translates.
   It is closed and misses the generic point, hence nowhere dense. Translating permutes
   its terms, so it is invariant. The component dichotomy gives the boundary inclusion;
   over its complement v is smooth (lem-pc-proper-base-change, smoothness clause).
5. If B has dimension zero, a point different from its generic point would give a strict
   irreducible closed chain of length one (def-kun-topological-krull-dimension). Thus B
   has only its generic point and the constructed boundary is empty.
6. Under any base change flatness persists (lem-sfb-pointwise-flatness-base-change),
   as do finite presentation (lem-weil-pbc-qcqs-morphism-permanence) and projectivity
   (lem-pc-projective-base-change). A geometric fibre of the pullback is the original
   geometric fibre over the same algebraically closed field (def-pc-fibre-product,
   def-trf-nodal-geometric-fibres). Section disjointness follows by projection, and the
   smooth-locus base-change identity preserves the smoothness of their images.
7. Quasi-splitting persists by the standalone arbitrary-base-change clause of
   lem-sfb-nodal-finite-quasi-splitting: rational nodes and their two rational branches
   remain rational over the new base residue field.
8. The fibre-product universal property gives both equations for the pulled-back sections.
   A point lying over a section factors through its closed immersion on its residue-field
   spectrum (def-weil-closed-immersion, Stacks 01QO). The universal property then gives
   equality of its inverse image with the new section image. Pulling back the boundary
   inclusion gives the asserted containment; smoothness over the inverse open follows
   from smooth base change (lem-pc-proper-base-change). No density of the new boundary
   or generic smoothness over the new base is asserted.
-/
theorem exists_markedNodalBoundary_control
    (k : Type u) [Field k] (V B : Scheme.{u})
    (pB : B ⟶ Spec (.of k)) [IsIntegral B]
    [LocallyOfFiniteType pB] [QuasiCompact pB]
    (v : V ⟶ B) [IsHProjective v] [Flat v] [LocallyOfFinitePresentation v]
    (hnodal : HasNodalGeometricFibres v)
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ B),
      IsReduced (pullback v t) ∧ (pullback v t).IsPureDimension 1)
    [Smooth (v.fiberToSpecResidueField (genericPoint B))]
    [GeometricallyIntegral (v.fiberToSpecResidueField (genericPoint B))]
    (hquasi : HasQuasiSplitNodalFibres v)
    (n : ℕ) (s : Fin n → (B ⟶ V)) (hs : ∀ i, s i ≫ v = 𝟙 B)
    (hdisjoint : Pairwise (fun i j : Fin n ↦
      Disjoint (Set.range (s i)) (Set.range (s j))))
    (hsmooth : ∀ i : Fin n, Set.range (s i) ⊆ (v.smoothLocus : Set V))
    (G : Type w) [Group G] [Finite G]
    (σk : G →* (k ≃+* k)) (σV : G →* Aut V) (σB : G →* Aut B)
    (hsemilinear : ∀ g : G, (σB g).hom ≫ pB =
      pB ≫ Spec.map (CommRingCat.ofHom (σk g⁻¹).toRingHom))
    (hequiv : ∀ g : G, (σV g).hom ≫ v = v ≫ (σB g).hom)
    (hmarkings : ∀ g : G, (σV g).hom '' (⋃ i : Fin n, Set.range (s i)) =
      ⋃ i : Fin n, Set.range (s i))
    (Z : Closeds V) (hstable : ∀ g : G, (σV g).hom '' (Z : Set V) = (Z : Set V))
    (hgeneric : (Z : Set V) ∩ v ⁻¹' {genericPoint B} ⊆
      ⋃ i : Fin n, {s i (genericPoint B)}) :
    ∃ D : Closeds B,
      (D : Set B) = markedNodalBoundary v (Z : Set V) G σB ∧
      IsNowhereDense (D : Set B) ∧
      (∀ g : G, (σB g).hom '' (D : Set B) = (D : Set B)) ∧
      Smooth (v ∣_ D.compl) ∧
      (Z : Set V) ⊆ v ⁻¹' (D : Set B) ∪ ⋃ i : Fin n, Set.range (s i) ∧
      (∀ C : Set (Z : Set V), C ∈ irreducibleComponents (Z : Set V) →
        Dense (v '' (Subtype.val '' C)) →
        Subtype.val '' C ⊆ ⋃ i : Fin n, Set.range (s i)) ∧
      (topologicalKrullDim B = 0 → (D : Set B) = ∅) ∧
      ∀ (B' : Scheme.{u}) (b : B' ⟶ B),
        IsHProjective (pullback.snd v b) ∧ Flat (pullback.snd v b) ∧
        QuasiCompact (pullback.snd v b) ∧ QuasiSeparated (pullback.snd v b) ∧
        ∃ hfp' : LocallyOfFinitePresentation (pullback.snd v b),
          HasNodalGeometricFibres (pullback.snd v b) ∧
          (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ B'),
            IsReduced (pullback (pullback.snd v b) t) ∧
            (pullback (pullback.snd v b) t).IsPureDimension 1) ∧
          HasQuasiSplitNodalFibres (pullback.snd v b) ∧
          (∀ i : Fin n, v.baseChangeSection (s i) (hs i) b ≫ pullback.snd v b = 𝟙 B') ∧
          (∀ i : Fin n, v.baseChangeSection (s i) (hs i) b ≫ pullback.fst v b = b ≫ s i) ∧
          Pairwise (fun i j : Fin n ↦
            Disjoint (Set.range (v.baseChangeSection (s i) (hs i) b))
              (Set.range (v.baseChangeSection (s j) (hs j) b))) ∧
          (∀ i : Fin n, Set.range (v.baseChangeSection (s i) (hs i) b) ⊆
            ((pullback.snd v b).smoothLocus : Set (pullback (C := Scheme.{u}) v b))) ∧
          (pullback.fst v b) ⁻¹' (⋃ i : Fin n, Set.range (s i)) =
            ⋃ i : Fin n, Set.range (v.baseChangeSection (s i) (hs i) b) ∧
          (pullback.fst v b) ⁻¹' (Z : Set V) ⊆
            (pullback.snd v b) ⁻¹' (b ⁻¹' (D : Set B)) ∪
              ⋃ i : Fin n, Set.range (v.baseChangeSection (s i) (hs i) b) ∧
          Smooth ((pullback.snd v b) ∣_ (b ⁻¹ᵁ D.compl)) := by
  sorry

end AlgebraicGeometry
