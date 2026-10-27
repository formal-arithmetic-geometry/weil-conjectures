module

public import Sheaf.AlgebraicGeometry.TorusFixedLocalIdealJets
public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary

/-! # Dense-subgroup fixed local ideals and rational finite jets

Source: Milne, Algebraic Groups (2017), Propositions 1.10 and 1.13, pp.9--10,
Lemma 13.4, p.255, proof of Lemma 13.6, p.256, and Section 4(d), pp.86--87.
(blueprint: lem-sfb-dense-fixed-local-ideal-jets)

Affine coordinates write X = Spec B and F = Spec(B/K). The coaction rho describes
pullback by the right action (z,g) ↦ g⁻¹z associated to the given left action.
The coordinate Hopf algebra is the one induced by the specified group scheme G.
Convolution points and their prime kernels identify H and its Zariski density.
All local rings, jets, evaluation maps and jet ideals reuse TorusFixedJets:
those constructions are general in their coordinate algebra despite the namespace.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct
open AlgebraicGeometry.TorusFixedJets

namespace AlgebraicGeometry.DenseFixedJets

/-- A dense subgroup's fixed local ring is the difference-ideal quotient, and the
finite local jets carry the induced rational algebra coactions and cotangent reduction.

Source: Milne, Propositions 1.10 and 1.13, pp.9--10; Lemma 13.4, p.255;
proof of Lemma 13.6, p.256; Section 4(d), pp.86--87.
(blueprint: lem-sfb-dense-fixed-local-ideal-jets).

Proof:
1. Smoothness makes G reduced (sbc-lem-smooth-geometrically-reduced and
   def-pc-reduced-scheme). A coordinate function vanishing on H has zero locus
   containing a dense set, hence is nilpotent by
   lem-weil-pbc-zero-locus-eq-iff-radical-eq, and is therefore zero.
2. The affine product/tensor pushout and coordinate Hopf structure identify the
   inverse action with rho and its counit and coassociativity identities
   (lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-algebra-tensor-pushout-universal-property,
   lem-sfb-affine-group-coordinate-hopf, def-weil-pbc-module-tensor-product).
3. For b in B the coordinate function (x tensor 1)rho(b)-x(b) vanishes on H.
   Step 1 makes it zero. Evaluation at every algebra-valued point proves
   scheme-theoretic fixedness, including nonreduced test algebras.
4. Let I be the ideal of global H-differences. Testing the fixed-subfunctor
   condition at B/I and B/K gives K=I, without taking radicals
   (def-weil-closed-immersion and def-weil-pbc-algebra-hom-quotient).
5. Localize at p=ker x. H preserves p. Subtracting the scalar x(b) shows
   IA is contained in J. The fraction identity
   gamma(b/s)-b/s = (s(gamma(b)-b)-b(gamma(s)-s))/(s gamma(s))
   proves the reverse inclusion. Quotient-localization identifies the immersion
   stalk map with A to A/J (lem-weil-pbc-spec-map-stalk-localization,
   def-weil-pbc-localization-at-prime,
   lem-weil-pbc-localization-at-prime-of-quotient).
6. Subtract the values at x from finitely many generators of B. Their monomials
   of degree below N span B/p^N. Denominators outside p have inverses given by
   a finite geometric series modulo p^N, identifying B/p^N with A/m^N
   (lem-pc-affine-finite-type-algebra, def-weil-finite-dimensional-subspace).
7. Fixedness gives rho(p) contained in p tensor k[G]: split B=k direct-sum p
   using x. Multiplicativity preserves p^N. Descend rho to B/p^N and transport
   along Step 6. The two coaction laws descend, as does evaluation at H.
8. The same splitting makes m/m^N a subcomodule. Reduction to m/m^2 is
   surjective and commutes with the coactions on coordinate generators.
9. The rational-representation/comodule dictionary identifies these coactions
   with rational representations and their reduction with an equivariant map
   (lem-sfb-rational-representation-comodule-dictionary). No smoothness of X
   or linear reductivity is used. -/
theorem dense_fixed_local_ideal_jets
    {k B : Type u} [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B]
    (G : Scheme.{u}) [G.Over (Spec (.of k))]
    [GrpObj (G.asOver (Spec (.of k)))] [IsAffine G]
    [Smooth (G ↘ Spec (.of k))]
    [LocallyOfFiniteType (G ↘ Spec (.of k))] [QuasiCompact (G ↘ Spec (.of k))]
    (ρ : HopfAction.AlgebraCoaction k (Γ(G, ⊤)) B)
    (H : Subgroup (WithConv (Γ(G, ⊤) →ₐ[k] k)))
    (hdense : DenseRange (fun γ : H ↦ pointPrime γ.val.ofConv))
    (K : Ideal B)
    (hfixed : ∀ (D : Type u) [CommRing D] [Algebra k D] (q : B →ₐ[k] D),
      K ≤ RingHom.ker q ↔ ∀ γ : H,
        evaluate ρ.map q ((Algebra.ofId k D).comp γ.val.ofConv) = q)
    (x : (B ⧸ K) →ₐ[k] k) :
    (∀ (D : Type u) [CommRing D] [Algebra k D] (g : Γ(G, ⊤) →ₐ[k] D),
      evaluate ρ.map ((Algebra.ofId k D).comp (quotientPoint K x)) g =
        (Algebra.ofId k D).comp (quotientPoint K x)) ∧
    ∃ τ : H →
        (LocalRing (quotientPoint K x) ≃ₐ[k] LocalRing (quotientPoint K x)),
      (∀ (t : H) (b : B),
        τ t (algebraMap B (LocalRing (quotientPoint K x)) b) =
          algebraMap B (LocalRing (quotientPoint K x))
            (evaluate ρ.map (AlgHom.id k B) ((Algebra.ofId k B).comp t.val.ofConv) b)) ∧
      (∃ e : IsLocalRing.ResidueField (LocalRing (quotientPoint K x)) ≃ₐ[k] k,
        ∀ b : B,
          e (IsLocalRing.residue _ (algebraMap B (LocalRing (quotientPoint K x)) b)) =
            quotientPoint K x b) ∧
      (∃ J : Ideal (LocalRing (quotientPoint K x)),
        J = Ideal.span {a | ∃ (γ : H)
          (f : IsLocalRing.maximalIdeal (LocalRing (quotientPoint K x))), a = τ γ f - f} ∧
      (∃ e : (LocalRing (quotientPoint K x) ⧸ J) ≃ₐ[k] LocalRing x,
        ∀ b : B,
          e (Ideal.Quotient.mk _ (algebraMap B (LocalRing (quotientPoint K x)) b)) =
            algebraMap (B ⧸ K) (LocalRing x) (Ideal.Quotient.mk K b)) ∧
      ∃ c : (N : ℕ) → HopfAction.AlgebraCoaction k (Γ(G, ⊤))
          (Jet (quotientPoint K x) N),
        ∀ n : ℕ, 1 ≤ n →
          FiniteDimensional k (Jet (quotientPoint K x) (n + 1)) ∧
          (∀ (t : H) (a : LocalRing (quotientPoint K x)),
            evaluate (c (n + 1)).map (AlgHom.id k _) ((Algebra.ofId k _).comp t.val.ofConv)
                (jetMap (quotientPoint K x) (n + 1) a) =
              jetMap (quotientPoint K x) (n + 1) (τ t a)) ∧
          (∃ d : JetIdeal (quotientPoint K x) (n + 1) →ₗ[k]
              JetIdeal (quotientPoint K x) (n + 1) ⊗[k] Γ(G, ⊤),
            HopfAction.Counital k (Γ(G, ⊤)) _ d ∧
            HopfAction.Coassociative k (Γ(G, ⊤)) _ d ∧
            (JetIdeal (quotientPoint K x) (n + 1)).subtype.rTensor (Γ(G, ⊤)) ∘ₗ d =
              (c (n + 1)).map.toLinearMap ∘ₗ
                (JetIdeal (quotientPoint K x) (n + 1)).subtype ∧
            ∃ (d₂ : JetIdeal (quotientPoint K x) 2 →ₗ[k]
                JetIdeal (quotientPoint K x) 2 ⊗[k] Γ(G, ⊤))
              (p : JetIdeal (quotientPoint K x) (n + 1) →ₗ[k]
                JetIdeal (quotientPoint K x) 2),
              HopfAction.Counital k (Γ(G, ⊤)) _ d₂ ∧
              HopfAction.Coassociative k (Γ(G, ⊤)) _ d₂ ∧
              (JetIdeal (quotientPoint K x) 2).subtype.rTensor (Γ(G, ⊤)) ∘ₗ d₂ =
                (c 2).map.toLinearMap ∘ₗ (JetIdeal (quotientPoint K x) 2).subtype ∧
              (∀ a : IsLocalRing.maximalIdeal (LocalRing (quotientPoint K x)),
                (p ⟨jetMap (quotientPoint K x) (n + 1) a,
                  Ideal.mem_map_of_mem _ a.property⟩ : Jet (quotientPoint K x) 2) =
                  jetMap (quotientPoint K x) 2 a) ∧
              Function.Surjective p ∧ p.rTensor (Γ(G, ⊤)) ∘ₗ d = d₂ ∘ₗ p)) := by
  sorry

end AlgebraicGeometry.DenseFixedJets
