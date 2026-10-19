/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Category.Ring.FinitePresentation
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import WeilConjectures.RingTheory.LocalizationColimitPrincipalLocalizations

/-!
# Clopen refinements of pointed étale neighbourhoods

Source: Stacks Project, Tags 0EZV, 09AY and 03PN, with the finite-presentation/clopen
refinement argument recorded in the DAG
(blueprint: lem-weil-pbc-clopen-etale-neighbourhood-cofinality).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Clopen pointed neighbourhoods refine and equalize all pointed étale neighbourhoods.
The initial subsystem is expressed as the full subcategory of pointed neighbourhoods whose
structural map is an open immersion with closed image. Each such object is canonically
isomorphic over the base to its image open subscheme, and its marking is the unique lift.

Source: Stacks Project, Tags 0EZV (finite-product presentation), 09AY and 03PN; the explicit
finite-presentation argument in the DAG
(blueprint: lem-weil-pbc-clopen-etale-neighbourhood-cofinality).

Proof:
1. By lem-weil-pbc-spec-clopen-idempotent, a clopen is D(e) for an idempotent e.
   By lem-weil-pbc-affine-open-section-vanishing-prime its open scheme is Spec C_e.
   Open immersions are étale (lem-weil-pbc-open-immersion-etale).
2. The map C → Ω extends uniquely to γ : C_z → Ω by the localization universal
   property (lem-weil-pbc-ring-localization-universal-property). The structural
   isomorphism K → C_z identifies γ with an embedding K → Ω and factors the marking
   through Spec K. In particular γ is injective.
3. Apply lem-exc-etale-lift-separably-closed-factorization to descend the given marked
   lift to Spec K. Shrink its target to an affine open around the marked image using
   lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink. The affine étale ring
   criterion (lem-weil-pbc-etale-ring-map-iff-etale-affine) gives a finitely presented
   C-algebra B and a C-algebra map B → C_z defining this lift.
4. Express C_z as the filtered colimit of C_s for s outside z using
   lem-weil-pbc-localization-colimit-principal-localizations. By
   lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit the map B → C_z
   factors through C_s. The induced map D(s) → V preserves the marking, since both
   composites B → Ω are γ composed with B → C_z.
5. Refine D(s) by a clopen containing z, using the assumed basis, and restrict the
   scheme map (def-weil-open-immersion). This proves pointed refinement.
6. For two pointed maps, first shrink their common domain to a clopen W₀ whose images
   lie in one affine open Spec B of V containing the common marked image. Write
   W₀ = D(e). The two resulting C-algebra maps B → C_e agree after mapping to Ω.
7. For each of finitely many generators of B their difference a/e^r is zero in C_z,
   since γ is injective. Fraction equality (def-weil-pbc-localization-at-prime)
   supplies t outside z annihilating a. Multiply these finitely many t's, with empty
   product 1. Refine W₀ ∩ D(t) by a clopen W₃. Restriction makes all generator
   differences zero, so the maps agree by the affine correspondence
   (def-weil-affine-spectrum).
8. In each comma category for the clopen inclusion, step 5 gives an object and step 7
   joins any two objects by W₁ ← W₃ → W₂. Hence it is nonempty and connected, exactly
   Functor.Initial (lem-weil-pbc-initial-functor-limit). Step 1 also covers the
   empty clopen with e = 0 and the whole spectrum with e = 1. -/
theorem clopen_etale_neighbourhood_cofinality
    (K : Type v) (C : Type u) [Field K] [IsSepClosed K] [CommRing C] [Algebra K C]
    (hlocal : ∀ p : PrimeSpectrum C,
      Function.Bijective (algebraMap K (Localization.AtPrime p.asIdeal)))
    (hbasis : ∀ (U : (Spec (.of C)).Opens) (x : Spec (.of C)), x ∈ U →
      ∃ W : (Spec (.of C)).Opens, IsClosed (W : Set (Spec (.of C))) ∧ x ∈ W ∧ W ≤ U)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (z : PrimeSpectrum C) (zbar : Spec (.of Ω) ⟶ Spec (.of C))
    (hz : zbar default = z) :
    (∀ V : (Scheme.pointSmallEtale zbar).fiber.Elements,
      ∃ W : (Spec (.of C)).Opens, IsClosed (W : Set (Spec (.of C))) ∧ z ∈ W ∧
        ∃ (w : Spec (.of Ω) ⟶ W.toScheme) (b : W.toScheme ⟶ V.1.left),
          w ≫ W.ι = zbar ∧ b ≫ V.1.hom = W.ι ∧ w ≫ b = V.2.left) ∧
    (∀ (V : (Scheme.pointSmallEtale zbar).fiber.Elements)
      (W₁ W₂ : (Spec (.of C)).Opens),
      IsClosed (W₁ : Set (Spec (.of C))) → IsClosed (W₂ : Set (Spec (.of C))) →
      z ∈ W₁ → z ∈ W₂ →
      ∀ (w₁ : Spec (.of Ω) ⟶ W₁.toScheme) (w₂ : Spec (.of Ω) ⟶ W₂.toScheme)
        (b₁ : W₁.toScheme ⟶ V.1.left) (b₂ : W₂.toScheme ⟶ V.1.left),
        w₁ ≫ W₁.ι = zbar → w₂ ≫ W₂.ι = zbar →
        b₁ ≫ V.1.hom = W₁.ι → b₂ ≫ V.1.hom = W₂.ι →
        w₁ ≫ b₁ = V.2.left → w₂ ≫ b₂ = V.2.left →
        ∃ W₃ : (Spec (.of C)).Opens, IsClosed (W₃ : Set (Spec (.of C))) ∧ z ∈ W₃ ∧
          ∃ (h₃₁ : W₃ ≤ W₁) (h₃₂ : W₃ ≤ W₂),
            (Spec (.of C)).homOfLE h₃₁ ≫ b₁ = (Spec (.of C)).homOfLE h₃₂ ≫ b₂) ∧
    (ObjectProperty.ι (fun V : (Scheme.pointSmallEtale zbar).fiber.Elements ↦
      IsOpenImmersion V.1.hom ∧ IsClosed (Set.range V.1.hom))).Initial ∧
    (∀ W : (Spec (.of C)).Opens, IsClosed (W : Set (Spec (.of C))) →
      ∃ e : C, IsIdempotentElem e ∧
        (W : Set (Spec (.of C))) = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum C)) ∧
        ∃ i : W.toScheme ≅ Spec (.of (Localization.Away e)),
          i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away e))) = W.ι) := by
  sorry

end AlgebraicGeometry
