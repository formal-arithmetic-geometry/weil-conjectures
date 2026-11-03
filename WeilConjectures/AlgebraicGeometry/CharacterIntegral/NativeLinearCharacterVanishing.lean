/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CharacterIntegral.CharacterIntegralTrace
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier

/-! # Native compact vanishing of a nonzero linear character

Source: the finite-level vanishing and coefficient-passage paragraphs of
lem-fd-character-integral in the latest blueprint
(blueprint: lem-fd-native-linear-character-vanishing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CharacterIntegral
open DiagonalCoefficients RationalP1

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))

/-- The nonzero calculation before applying derived coefficient sections.

Source: latest blueprint, sec-fourier-transform/sk-lem-wft-character-integral/
lem-fd-character-integral.proof.md, the nonzero-form calculation and the
coefficient-passage paragraph
(blueprint: lem-fd-native-linear-character-vanishing).

Proof:
1. Classify the nontrivial degree-q character as a nontrivial prime-field
character composed with a nonzero multiple of the field trace. All its values
are integral units. The degree-q projector and its image have integral models,
whose reductions are the same character-projector images over the finite rings.
2. Over Spec k at finite coefficients, identify compact support of the prime
Artin--Schreier pushforward with compact support of its total affine line. Translation preserves
the normalized top trace, hence acts as the identity on this compact cohomology.
The nontrivial character sum is zero in the integral domain of coefficients,
and therefore in every finite quotient. Thus the projector induces zero on
compact cohomology. Since its image is a retract, the image has zero cohomology;
this uses no cancellation of a nonunit in a finite coefficient ring.
3. The trace-polynomial comparison and nonzero scaling of the line coordinate
identify the actual degree-q character line with this prime calculation. At this
stage only the line is needed. Higher dimension will use the existing native
Kunneth theorem after coefficient passage, as prescribed by the blueprint unit.
4. For the same affine-line compactification use exact open-extension comparison,
proper direct-image comparison, and the ordinary/internal module equivalence.
Their naturality identifies the actual native finite projector-image reductions
with the zero objects just computed.
5. The integral rank-one character-line model over k has finite Tor amplitude.
Compact support preserves bounded constructibility and finite Tor amplitude,
so its compact-support object is derived complete. The actual scalar mates identify its
compatible reduction
tower with the zero tower. Applying derived inverse limit gives integral
vanishing. The rationalization and finite-subextension scalar comparisons carry
this zero object to E and to the finite-subextension-valued algebraic closure.
6. Work first over k, a finite ground field, and apply the existing native Kunneth
isomorphism to the standard coordinate character and the unit on the other
factors. Compact-support composition identifies the ordered word, and the line
factor is zero. Apply arbitrary-base condensed compact-support exchange to
Spec Omega -> Spec k. Its original schemes and compactification are Noetherian,
and its theorem requires no finite-type condition on the new base. The actual
pullback and compactification comparisons therefore give standard-coordinate
vanishing over Omega. For general nonzero a choose i with a i nonzero. The
coordinates lambda and the other coordinates are an isomorphism, with inverse
x_i = (a i)^(-1) times (lambda minus the sum of the other a_j x_j). Pullback
compatibility of the actual character projector and compact-support composition
transport the standard-coordinate zero object along this isomorphism.
The finite-ground-field Kunneth interface is never applied directly over Omega.
The consumer treats rank zero, where a nonzero vector is impossible.
-/
theorem nativeLinearCharacter_isZero (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (k Ω : Type u) [Field k] [Fintype k] [CharP k p] [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω]
    (hroots : match c with
      | some E => ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ),
          ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1
      | none => True)
    (ψ : AddChar k (MonObj.Γ (coefficient ℓ c).X)) (hψ : ψ ≠ 1)
    (r : ℕ) (a : Fin (r + 1) → Ω) (ha : a ≠ 0) :
    letI : (affineTraceTower (Spec (.of Ω)) (r + 1)).Over (Spec (.of k)) :=
      ⟨affineTraceProjection (Spec (.of Ω)) (r + 1) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k Ω))⟩
    IsZero ((compact ℓ c (Spec (.of Ω)) (r + 1)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (condensedArtinSchreierSheafOf (coefficient ℓ c).X k _ ψ
          (∑ i : Fin (r + 1), (affineTraceProjection (Spec (.of Ω)) (r + 1)).appTop
            ((Scheme.ΓSpecIso (.of Ω)).inv.hom (a i)) *
              affineTraceCoordinate (Spec (.of Ω)) (r + 1) i)))) := by
  sorry

end AlgebraicGeometry.ProEtale.CharacterIntegral
