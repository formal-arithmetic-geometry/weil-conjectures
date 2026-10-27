/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.AlgebraicGeometry.RationalFunctionsGenericStalks
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Proper

/-! # Cartier blowups of reduced irreducible components

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, 2.3 Step 1,
printed p.150; Stacks Project, Tags 02ND and 02OS
(blueprint: lem-sfb-component-cartier-blowup).

The ideal of each marking is the vanishing ideal of its inverse image as a closed set;
its associated closed subscheme therefore has the reduced induced structure. The
function-field isomorphism is required to be the map on generic stalks induced by the
blowup. When a marking is empty, `IsIso` identifies the blowup map with the identity
under this canonical identification of its source and target.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The reduced components of a nonempty reduced proper scheme over a field admit
integral proper Cartier blowups of the marking, with the canonical birational and
function-field identifications.

Source: Illusie--Laszlo--Orgogozo, Expose X, 2.3 Step 1, printed p.150;
Stacks Project, Tags 02ND and 02OS (blueprint: lem-sfb-component-cartier-blowup).

Proof:
1. A field is Noetherian, so finite type over its spectrum makes T Noetherian
   (lem-weil-pbc-finite-type-over-noetherian, pqf-def-locnoeth,
   def-weil-pbc-noetherian-ring). Its irreducible components form a finite set
   (lem-weil-pbc-noetherian-finite-components) and cover T
   (lem-sc-irreducible-components-cover). Nonemptiness makes the enumeration nonempty.
2. Give each component its reduced induced closed structure, using
   lem-weil-pbc-reduced-induced-closed-subscheme. Reducedness and irreducibility
   give integrality (def-pc-integral-scheme). Closed immersions into the proper T
   are proper over the field (lem-weil-pbc-closed-immersion-proper), hence finite
   type and Noetherian. The reduced marking is given by its vanishing ideal.
3. The complement of all the other components is a nonempty open in each fixed
   component: otherwise irreducibility forces containment in another component.
   Nowhere density of C therefore prevents C from containing a component. Each
   complement U is nonempty and, by irreducibility, dense.
4. Opens of a Noetherian scheme are quasi-compact
   (lem-weil-pbc-noetherian-open-subscheme-noetherian). Every affine ideal is finitely
   generated, so the marking ideal is finite type
   (lem-weil-pbc-quasi-coherent-finite-type-affine). It is nonzero since its zero
   set is the proper closed marking (lem-weil-pbc-quasi-coherent-ideal-zero-set-affine).
5. The ordinary blowup is integral by lem-sfb-integral-blowup-projective-geometry,
   proper by thm-nagata-global-blowup-proper, and an isomorphism over U by
   thm-nagata-global-blowup-complement. The inverse image of U is a nonempty open
   of an integral scheme and hence dense.
6. Properness makes the image closed. It contains the dense U, so the blowup is
   surjective. Proper composition (lem-weil-pbc-proper-composition) gives properness
   over the field; properness includes finite type.
7. The dense open isomorphism identifies the unique generic points
   (lem-sc-scheme-sober) and their stalks. Restriction to an open neighbourhood
   preserves stalks. These are the function fields by def-sc-function-field and
   lem-sc-rational-functions-generic-stalks, and the resulting isomorphism is the
   blowup's own stalk map, transported along its equality on generic points.
8. The extended ideal is Cartier by thm-nagata-blowup-principalizes-center. By
   def-nagata-extended-ideal and lem-pc-closed-subscheme-base-change-ideal-image it
   cuts out the inverse image of the marking. On affine charts a prime contains
   the extended ideal JB exactly when its inverse image contains J; thus its
   support is precisely the inverse image of C_i
   (lem-weil-pbc-quasi-coherent-ideal-zero-set-affine).
9. If C_i is empty its vanishing ideal is the unit ideal. Then U is the entire
   component, so the complement isomorphism is the whole blowup map. Under that
   canonical isomorphism the map is the identity. -/
theorem exists_component_cartier_blowups
    (e : Type u) [Field e] (T : Scheme.{u}) (p : T ⟶ Spec (.of e))
    [Nonempty T] [IsReduced T] [IsProper p]
    (C : Closeds T) (hC : interior (C : Set T) = ∅) :
    ∃ (s : ℕ) (_ : 0 < s)
      (components : Fin s ≃ {Z : Set T // Z ∈ irreducibleComponents T})
      (Ti : Fin s → Scheme.{u}) (ι : ∀ i : Fin s, Ti i ⟶ T)
      (I : ∀ i : Fin s, (Ti i).IdealSheafData) (U : ∀ i : Fin s, (Ti i).Opens),
      ∀ i : Fin s,
        IsClosedImmersion (ι i) ∧ Set.range (ι i) = (components i).val ∧
        I i = IdealSheafData.vanishingIdeal (C.preimage (ι i).continuous) ∧
        U i = (C.preimage (ι i).continuous).compl ∧
        (∀ V : (Ti i).affineOpens, ((I i).ideal V).FG) ∧
        Nonempty (U i) ∧ IsCompact (U i : Set (Ti i)) ∧ Dense (U i : Set (Ti i)) ∧
        IsProper (ι i ≫ p) ∧
        IsProper (I i).blowupMap ∧ Surjective (I i).blowupMap ∧
        IsProper ((I i).blowupMap ≫ ι i ≫ p) ∧
        LocallyOfFiniteType ((I i).blowupMap ≫ ι i ≫ p) ∧
        QuasiCompact ((I i).blowupMap ≫ ι i ≫ p) ∧
        IsIso ((I i).blowupMap ∣_ U i) ∧
        Dense ((I i).blowupMap ⁻¹' (U i : Set (Ti i))) ∧
        ((I i).comap (I i).blowupMap).IsInvertible ∧
        ((I i).comap (I i).blowupMap).support =
          (C.preimage (ι i).continuous).preimage (I i).blowupMap.continuous ∧
        ((C.preimage (ι i).continuous : Closeds (Ti i)) = ⊥ →
          I i = ⊤ ∧ IsIso (I i).blowupMap) ∧
        ∃ (hTi : IsIntegral (Ti i)) (hS : IsIntegral (I i).blowup)
          (hη : (I i).blowupMap
            (@genericPoint (I i).blowup _ inferInstance (@irreducibleSpace_of_isIntegral _ hS)) =
              @genericPoint (Ti i) _ inferInstance (@irreducibleSpace_of_isIntegral _ hTi))
          (K : @Scheme.functionField (Ti i) (@irreducibleSpace_of_isIntegral _ hTi) ≅
            @Scheme.functionField (I i).blowup (@irreducibleSpace_of_isIntegral _ hS)),
          K.hom = ((Ti i).presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom ≫
            (I i).blowupMap.stalkMap
              (@genericPoint (I i).blowup _ inferInstance
                (@irreducibleSpace_of_isIntegral _ hS)) := by
  sorry

end AlgebraicGeometry.Scheme
