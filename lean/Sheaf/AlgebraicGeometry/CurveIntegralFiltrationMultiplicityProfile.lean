/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk
import WeilConjectures.Algebra.Homology.ModuleStalkExact

/-! # Integral-ideal filtrations and generic multiplicities on proper curves

Source: Stacks Project, coherent.tex, Tag 01YF (lemma-coherent-filter);
algebra.tex, Tag 00IV (lemma-length-additive); varieties.tex, multiplicity paragraph
preceding Tag 0AYW (lemma-degree-in-terms-of-components)
(blueprint: lem-trf-curve-integral-filtration-multiplicity-profile).

The clauses are stated separately: Noetherianity and component enumeration, reduced
component geometry, existence of filtrations, classification of all integral factors,
generic quotient stalks and counts, structure-module multiplicities, and the zero cases.
All subobjects, quotient cokernels, ideals, pushforwards and stalks are the existing APIs.

## Main statements

* `curve_integral_filtration_components`: Noetherianity, coherence and the component list.
* `curve_integral_filtration_component_geometry`: reduced components and generic local rings.
* `curve_integral_filtration_exists`: the finite coherent integral-ideal filtration.
* `curve_integral_filtration_factor_geometry`: point or component classification.
* `curve_integral_filtration_stalk_count`: quotient stalks and the count for every filtration.
* `curve_integral_filtration_multiplicity`: positive integer structure multiplicities.
* `curve_integral_filtration_zero_cases`: length-zero filtrations and the empty scheme.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Noetherianity, structure-module coherence and a finite list of the one-dimensional
components without repetitions. Source: Stacks, Tags 01XZ, 01T6, 0BA8, and the paragraph
preceding 0AYW (blueprint: lem-trf-curve-integral-filtration-multiplicity-profile).
Proof: the structure module is invertible, so apply
lem-trf-proper-field-invertible-coherent to it. Noetherian spaces have finitely many
irreducible components (lem-weil-pbc-noetherian-finitely-many-components). Select the
one-dimensional members and enumerate this finite set without repetitions. -/
theorem curve_integral_filtration_components
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) :
    IsNoetherian X ∧
      RingedSpace.IsCoherent X.toRingedSpace (SheafOfModules.unit X.ringCatSheaf) ∧
      ∃ (t : ℕ) (T : Fin t → Closeds X),
        Function.Injective T ∧
        Set.range (fun i ↦ (T i : Set X)) =
          {S : Set X | S ∈ irreducibleComponents X ∧ topologicalKrullDim S = 1} := by
  sorry

/-- Geometry of each reduced one-dimensional component, including its affine prime ideal
and its generic residue-field quotient. Source: Stacks, Tags 01J3, 01IS, 00ES and the
multiplicity paragraph preceding 0AYW
(blueprint: lem-trf-curve-integral-filtration-multiplicity-profile).
Proof: use lem-weil-pbc-reduced-induced-closed-subscheme on the closed component T.
Reducedness and irreducibility give integrality, and the closed embedding preserves
dimension. Properness follows by composing a closed immersion with f. Sobriety gives
existence and uniqueness of the generic point. Every affine open meeting T has an
irreducible nonempty intersection, hence a prime defining ideal by
lem-weil-pbc-spec-irreducible-closed-subsets-primes. The generic local ring of the integral
component is a field (lem-weil-pbc-integral-scheme-ideal-generic-stalk). The closed
immersion induces a surjective local stalk map; its kernel is the maximal ideal since
the target is a field. Therefore its target identifies with the ambient residue field,
compatibly with the canonical residue map. -/
theorem curve_integral_filtration_component_geometry
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (T : Closeds X)
    (hT : (T : Set X) ∈ irreducibleComponents X)
    (hTdim : topologicalKrullDim (T : Set X) = 1) :
    IsIntegral (IdealSheafData.vanishingIdeal T).subscheme ∧
      IsProper ((IdealSheafData.vanishingIdeal T).subschemeι ≫ f) ∧
      topologicalKrullDim (IdealSheafData.vanishingIdeal T).subscheme = 1 ∧
      (∃! ξ : (IdealSheafData.vanishingIdeal T).subscheme,
        IsGenericPoint ξ Set.univ) ∧
      (∀ U : X.affineOpens, (U.1 : Set X) ∩ (T : Set X) ≠ ∅ →
        ((IdealSheafData.vanishingIdeal T).ideal U).IsPrime ∧
        PrimeSpectrum.zeroLocus
          ((IdealSheafData.vanishingIdeal T).ideal U : Set Γ(X, U)) =
            U.2.fromSpec ⁻¹' (T : Set X)) ∧
      ∀ ξ : (IdealSheafData.vanishingIdeal T).subscheme,
        IsGenericPoint ξ Set.univ →
        closure ({(IdealSheafData.vanishingIdeal T).subschemeι ξ} : Set X) = (T : Set X) ∧
        Function.Surjective ((IdealSheafData.vanishingIdeal T).subschemeι.stalkMap ξ) ∧
        ∃ e : (IdealSheafData.vanishingIdeal T).subscheme.presheaf.stalk ξ ≃+*
            X.residueField ((IdealSheafData.vanishingIdeal T).subschemeι ξ),
          ∀ r : X.presheaf.stalk ((IdealSheafData.vanishingIdeal T).subschemeι ξ),
            e ((IdealSheafData.vanishingIdeal T).subschemeι.stalkMap ξ r) =
              X.residue ((IdealSheafData.vanishingIdeal T).subschemeι ξ) r := by
  sorry

/-- Existence of the finite coherent integral-ideal filtration, using the existing
predicate verbatim. Source: Stacks, Tag 01YF
(blueprint: lem-trf-curve-integral-filtration-multiplicity-profile).
Proof: Step 1 gives Noetherianity. Apply
lem-weil-pbc-coherent-filtration-integral-subschemes to F. Its predicate uses a monotone
chain c indexed by Fin (s+1), with bottom and top endpoints, coherent terms and quotient
cokernels isomorphic to closed pushforwards of nonzero coherent ideals. -/
theorem curve_integral_filtration_exists
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    HasCoherentIntegralFiltration F := by
  sorry

/-- Every integral closed factor is proper and Noetherian, and is either a single closed
point or the reduced scheme of exactly one one-dimensional component. Source: Stacks,
Tags 01W3, 01W5, 01J3, and the geometry preceding 0AYW
(blueprint: lem-trf-curve-integral-filtration-multiplicity-profile).
Proof: properness is stable under composition with a closed immersion and implies
Noetherianity over the field. The nonempty irreducible closed image has dimension zero
or one. In dimension zero the closure of every point is the whole image, and sobriety
makes it a singleton. In dimension one a proper inclusion in another irreducible closed
set would yield a chain of length two in X. Thus the image is a component. Its reduced
structure is unique by lem-weil-pbc-reduced-induced-closed-subscheme; the isomorphism over
X is unique because closed immersions are monomorphisms. -/
theorem curve_integral_filtration_factor_geometry
    {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (h : Z ⟶ X) [IsClosedImmersion h] [IsIntegral Z] :
    IsProper (h ≫ f) ∧ IsNoetherian Z ∧
      ((topologicalKrullDim Z = 0 ∧ ∃ z : Z, ∀ w : Z, w = z) ∧
          (∀ z : Z, IsClosed ({h z} : Set X)) ∨
        (topologicalKrullDim Z = 1 ∧
          ∃! T : Closeds X,
            (T : Set X) ∈ irreducibleComponents X ∧
            topologicalKrullDim (T : Set X) = 1 ∧ Set.range h = (T : Set X) ∧
            ∃! e : Z ≅ (IdealSheafData.vanishingIdeal T).subscheme,
              e.hom ≫ (IdealSheafData.vanishingIdeal T).subschemeι = h)) := by
  sorry

/-- Quotient stalks and the multiplicity count for every filtration of the specified
form. The residue field carries the canonical restricted scalar action from the ambient
local ring. Source: Stacks, Tags 01YF, 00AE, 08KS, 01AG, 00IV, and the multiplicity
calculation preceding 0AYW
(blueprint: lem-trf-curve-integral-filtration-multiplicity-profile).
Proof: fix any such filtration. By component maximality, a factor image contains ξ iff
it equals T. Off that image lem-weil-pbc-closed-pushforward-stalks gives zero. On T,
identify its reduced integral scheme with the component. Its nonzero ideal has the whole
generic field as stalk by lem-weil-pbc-integral-scheme-ideal-generic-stalk, using
pqf-lem-coherent-ft-locnoeth for quasi-coherence. The closed-pushforward stalk comparison
respects the ambient scalar action. The surjective local map to this field identifies
it with κ(ξ). The residue field has only zero and whole submodules, since any nonzero
vector generates it under the surjective scalar action, so this quotient has length one.
Take stalks of each subobject inclusion and quotient by lem-weil-pbc-module-stalk-exact.
Apply lem-weil-pbc-length-additive-short-exact, inducting along c from its zero bottom.
Each step adds one exactly for an image equal to T, and zero otherwise. At the top the
length is the displayed finite cardinal. This argument applies to every filtration,
rather than just the filtration furnished by the existence theorem. -/
theorem curve_integral_filtration_stalk_count
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (s : ℕ) (c : Fin (s + 1) → Subobject F) (hc : Monotone c)
    (hbot : c 0 = ⊥) (htop : c (Fin.last s) = ⊤)
    (hcoh : ∀ a : Fin (s + 1), RingedSpace.IsCoherent X.toRingedSpace (c a : X.Modules))
    (Z : Fin s → Scheme.{u}) (h : ∀ a : Fin s, Z a ⟶ X)
    (hclosed : ∀ a : Fin s, IsClosedImmersion (h a))
    (hintegral : ∀ a : Fin s, IsIntegral (Z a))
    (I : ∀ a : Fin s, (Z a).IdealSheafData)
    (hnonzero : ∀ a : Fin s, I a ≠ ⊥)
    (hIcoh : ∀ a : Fin s, RingedSpace.IsCoherent (Z a).toRingedSpace (I a).toModules)
    (hquot : ∀ a : Fin s,
      Nonempty (cokernel (Subobject.ofLE (c a.castSucc) (c a.succ)
        (hc a.castSucc_le_succ)) ≅ (pushforward (h a)).obj (I a).toModules))
    (T : Closeds X) (hT : (T : Set X) ∈ irreducibleComponents X)
    (hTdim : topologicalKrullDim (T : Set X) = 1)
    (ξ : X) (hξ : IsGenericPoint ξ (T : Set X)) :
    (∀ a : Fin s,
      (Set.range (h a) ≠ (T : Set X) →
        Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj
          (cokernel (Subobject.ofLE (c a.castSucc) (c a.succ)
            (hc a.castSucc_le_succ))))) ∧
      (Set.range (h a) = (T : Set X) →
        Nonempty (((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj
          (cokernel (Subobject.ofLE (c a.castSucc) (c a.succ)
            (hc a.castSucc_le_succ)))) ≅
          (ModuleCat.restrictScalars (X.residue ξ).hom).obj
            (ModuleCat.of (X.residueField ξ) (X.residueField ξ))) ∧
        Module.length (X.presheaf.stalk ξ)
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj
            (cokernel (Subobject.ofLE (c a.castSucc) (c a.succ)
              (hc a.castSucc_le_succ)))) = 1)) ∧
    Module.length (X.presheaf.stalk ξ)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj F) =
        (Nat.card {a : Fin s // Set.range (h a) = (T : Set X)} : ℕ∞) ∧
    Module.length (X.presheaf.stalk ξ)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj F) < ⊤ ∧
    (F = SheafOfModules.unit X.ringCatSheaf →
      Module.length (X.presheaf.stalk ξ) (X.presheaf.stalk ξ) =
        (Nat.card {a : Fin s // Set.range (h a) = (T : Set X)} : ℕ∞)) := by
  sorry

/-- The structure-module generic multiplicity is a positive integer. Its equality with
the number of factors is the preceding theorem applied to the structure module.
Source: Stacks, multiplicity paragraph preceding 0AYW
(blueprint: lem-trf-curve-integral-filtration-multiplicity-profile).
Proof: the structure module is coherent, so existence and the stalk count give finite
length of the local ring. This ring surjects onto its nonzero residue field and is
therefore nonzero. The strict submodule chain 0 < R proves positivity of its length. -/
theorem curve_integral_filtration_multiplicity
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (T : Closeds X) (hT : (T : Set X) ∈ irreducibleComponents X)
    (hTdim : topologicalKrullDim (T : Set X) = 1)
    (ξ : X) (hξ : IsGenericPoint ξ (T : Set X)) :
    ∃ m : ℕ, 0 < m ∧ Module.length (X.presheaf.stalk ξ) (X.presheaf.stalk ξ) = m := by
  sorry

/-- The zero module admits the length-zero filtration, and an empty scheme has zero
structure module and no one-dimensional components. Source: Stacks, Tag 01YF, zero case,
and the empty case of the component conventions preceding 0AYW
(blueprint: lem-trf-curve-integral-filtration-multiplicity-profile).
Proof: for an IsZero module take the sole subobject to be bottom, which is also top.
There are no factors. On the empty scheme sheaf locality gives zero structure module,
and no irreducible subset is nonempty, so there are no irreducible components. -/
theorem curve_integral_filtration_zero_cases
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) :
    (∀ F : X.Modules, IsZero F →
      ∃ c : Fin (0 + 1) → Subobject F,
        Monotone c ∧ c 0 = ⊥ ∧ c (Fin.last 0) = ⊤ ∧
        ∀ a : Fin (0 + 1), RingedSpace.IsCoherent X.toRingedSpace (c a : X.Modules)) ∧
    (IsEmpty X → IsZero (SheafOfModules.unit X.ringCatSheaf) ∧
      {S : Set X | S ∈ irreducibleComponents X ∧ topologicalKrullDim S = 1} = ∅) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
