/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Dimension.Free
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.AffinePuncturedLineAlgebra
import WeilConjectures.AlgebraicGeometry.Sites.Gm
import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# Kummer computations on the affine and punctured lines

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/thm-pur-kummer-affine-line,
Degrees 0 and 1 and Coefficients; Stacks Project, Tags 03PK, 03PL, 03SC and 01FT
(blueprint: thm-pur-kummer-affine-line).

The Boolean index is false for Spec k[t] and true for Spec k[t,t⁻¹]. The residue ring
is lifted to the coefficient universe; this changes neither its modules nor its scalars.
All cohomology is the existing abelian étale sheaf cohomology, with its unique residue-ring
action. The restriction map is characterized on the coefficient tensors, which generate
by the asserted coefficient comparison. Thus its characterization determines the actual
restriction map uniquely, including for the zero module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.KummerLine

/-- The two affine schemes in the computation.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def curve (k : Type u) [Field k] : Bool → Scheme.{u}
  | false => Spec (CommRingCat.of (Polynomial k))
  | true => Spec (CommRingCat.of (LaurentPolynomial k))

/-- The structure morphisms of the two lines over k.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def structureMap (k : Type u) [Field k] : (b : Bool) → curve k b ⟶ Spec (CommRingCat.of k)
  | false => Spec.map (CommRingCat.ofHom Polynomial.C)
  | true => Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

/-- The canonical open inclusion, induced by k[t] → k[t,t⁻¹].
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def inclusion (k : Type u) [Field k] : curve k true ⟶ curve k false :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

/-- Pullback of a scalar to global functions on either line.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def scalar (k : Type u) [Field k] (b : Bool) : k →+* Γ(curve k b, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (structureMap k b).appTop).hom

/-- The global unit t on the punctured line.
Source: blueprint sk-prop-a1-kummer (blueprint: thm-pur-kummer-affine-line). -/
def coordinateUnit (k : Type u) [Field k] : Γ(curve k true, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom.toMonoidHom
    (LaurentPolynomial.isUnit_T (R := k) 1).unit

/-- The Kummer generator is the actual connecting homomorphism applied to t.
Source: blueprint sk-prop-a1-kummer, Degrees 0 and 1
(blueprint: thm-pur-kummer-affine-line). -/
def generator (k : Type u) [Field k] (m : ℕ) (hm : IsUnit (m : Γ(curve k true, ⊤))) :
    Sheaf.H ((curve k true).rootsOfUnitySheaf m) 1 :=
  (curve k true).kummerδ₀ m hm (Additive.ofMul (coordinateUnit k))

/-- Restriction on root-sheaf cohomology, using the canonical pullback comparison.
Source: Stacks, Tag 03PK (blueprint: thm-pur-kummer-affine-line). -/
def rootRestriction (k : Type u) [Field k] (m q : ℕ) :
    Sheaf.H ((curve k false).rootsOfUnitySheaf m) q →+
      Sheaf.H ((curve k true).rootsOfUnitySheaf m) q :=
  (Sheaf.H.map (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf m (inclusion k)) q).comp
    (Etale.cohomologyMap (inclusion k) ((curve k false).rootsOfUnitySheaf m) q)

/-- Kummer computations with all finite free module coefficients, their canonical degree-zero
sections and degree-one generator, naturality, and finite free coefficient extension.
Source: blueprint thm-pur-kummer-affine-line; Stacks, Tags 03PK, 03PL, 03SC and 01FT
(blueprint: thm-pur-kummer-affine-line).

Proof: (1) Both schemes are smooth affine connected curves [def-sc-curves]. Apply
 [lem-sc-affine-cohomological-dimension] to the m-torsion roots sheaf to kill degrees above one.
(2) The exact Kummer sequence and its cohomology sequence identify H⁰ with the kernel
 of the power map on units and H¹ with its cokernel, since the Picard groups vanish.
 Use [lem-sc-kummer-exact], [def-sc-kummer-sequence], [def-weil-pbc-sites-and-cohomology],
 [lem-weil-pbc-derived-functor-long-exact], [lem-sc-h1-gm-pic], and
 [lem-pur-affine-punctured-line-algebra].
(3) The units are kˣ on the line and kˣ times t^Z on the punctured line. Both kernels are
 μ_m(k); the primitive root identifies them with R, compatibly with restriction.
 Use [lem-pur-affine-punctured-line-algebra] and [lem-sc-primitive-root].
(4) Divisibility of kˣ kills the first cokernel; the second is Z/m, with inverse sending
 1 to δ(t). The Laurent exponent computes this quotient and fixes the sign of the generator.
 These are the unit quotients of [lem-pur-affine-punctured-line-algebra].
(5) A finite basis of A identifies its twist with a finite sum of μ_m. Finite sums preserve
 injective resolutions, global sections and homology, proving the coefficient comparison.
 Its pure-tensor formula is basis independent and natural because i_a followed by a
 coefficient map f equals i_(f a). This includes the empty basis. Use
 [def-pur-sheaf-tensor-product], [def-weil-pbc-sites-and-cohomology], and
 [def-sp-injective-resolutions].
(6) Tensor the root computation with A. The surviving groups are A and hence finite;
 H¹ on the punctured line is free of the same rank as A. Root restriction and coefficient
 comparison determine restriction on coefficients, so its degree-zero map is the identity.
 Finally apply coefficient comparison to A and A ⊗ S and tensor associativity. Its formula
 on x ⊗ a ⊗ s gives the displayed scalar-extension compatibility and the Kummer formula. -/
theorem kummer_affine_line (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k)) (hN : 1 ≤ N)
    (ζ : kˣ) (hζ : IsPrimitiveRoot ζ (ℓ ^ N)) :
    ∃ (hm : IsUnit ((ℓ ^ N : ℕ) : Γ(curve k true, ⊤)))
      (z : (b : Bool) → Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) 0),
      (∀ b : Bool,
        (kernel.ι (ℓ ^ N • 𝟙 (curve k b).gmSheaf)).hom.app
            (op (Scheme.Etale.mk (𝟙 (curve k b))))
            (Sheaf.H.equiv₀ _ (MorphismProperty.Over.mkIdTerminal @Etale (curve k b)) (z b)) =
          ULift.up (Additive.ofMul (Units.map (scalar k b).toMonoidHom ζ))) ∧
      rootRestriction k (ℓ ^ N) 0 (z false) = z true ∧
      (∀ (b : Bool) (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ N)))),
        Module.Free (ULift.{u + 1} (ZMod (ℓ ^ N))) A →
        Module.Finite (ULift.{u + 1} (ZMod (ℓ ^ N))) A →
        (∃ e : A ≃ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
            Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj A) 0,
          ∀ a : A, e a = Sheaf.H.map
            (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N) A a) 0 (z b)) ∧
        (∀ q : ℕ, (if b then 1 else 0) < q →
          Subsingleton (Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj A) q)) ∧
        (∀ q : ℕ, Finite
          (Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj A) q)) ∧
        (∀ q : ℕ, ∃ e :
            (Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q ⊗[ULift.{u + 1} (ZMod (ℓ ^ N))]
              A) ≃ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
                Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj A) q,
          ∀ (x : Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q) (a : A),
            e (x ⊗ₜ a) = Sheaf.H.map
              (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N) A a) q x) ∧
        (∀ (B : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ N))))
            [Module.Free (ULift.{u + 1} (ZMod (ℓ ^ N))) B]
            [Module.Finite (ULift.{u + 1} (ZMod (ℓ ^ N))) B]
            (f : A →ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))] B)
            (q : ℕ) (x : Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q) (a : A),
          Sheaf.H.map ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).map
              (ModuleCat.ofHom f)) q
              (Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N) A a) q x) =
            Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N) B (f a)) q x) ∧
        (∀ (S : Type (u + 1)) [CommRing S] [Algebra (ULift.{u + 1} (ZMod (ℓ ^ N))) S]
            [Module.Free (ULift.{u + 1} (ZMod (ℓ ^ N))) S]
            [Module.Finite (ULift.{u + 1} (ZMod (ℓ ^ N))) S] (q : ℕ),
          ∃ e : (Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj A) q
              ⊗[ULift.{u + 1} (ZMod (ℓ ^ N))] S) ≃ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
            Sheaf.H ((Scheme.kummerAbelianTwist (curve k b) (ℓ ^ N)).obj
              (ModuleCat.of _ (A ⊗[ULift.{u + 1} (ZMod (ℓ ^ N))] S))) q,
          ∀ (x : Sheaf.H ((curve k b).rootsOfUnitySheaf (ℓ ^ N)) q) (a : A) (s : S),
            e ((Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N) A a)
              q x) ⊗ₜ s) = Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k b) (ℓ ^ N)
                (ModuleCat.of _ (A ⊗[ULift.{u + 1} (ZMod (ℓ ^ N))] S)) (a ⊗ₜ s)) q x)) ∧
      (∀ (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ N))))
          [Module.Free (ULift.{u + 1} (ZMod (ℓ ^ N))) A]
          [Module.Finite (ULift.{u + 1} (ZMod (ℓ ^ N))) A],
        (∃ e : A ≃ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
            Sheaf.H ((Scheme.kummerAbelianTwist (curve k true) (ℓ ^ N)).obj A) 1,
          ∀ a : A, e a = Sheaf.H.map
            (Scheme.kummerCoefficientInsertion (curve k true) (ℓ ^ N) A a) 1
            (generator k (ℓ ^ N) hm)) ∧
        ∃! res : Sheaf.H ((Scheme.kummerAbelianTwist (curve k false) (ℓ ^ N)).obj A) 0
            →ₗ[ULift.{u + 1} (ZMod (ℓ ^ N))]
              Sheaf.H ((Scheme.kummerAbelianTwist (curve k true) (ℓ ^ N)).obj A) 0,
          (∀ (x : Sheaf.H ((curve k false).rootsOfUnitySheaf (ℓ ^ N)) 0) (a : A),
            res (Sheaf.H.map
              (Scheme.kummerCoefficientInsertion (curve k false) (ℓ ^ N) A a) 0 x) =
            Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) (ℓ ^ N) A a) 0
              (rootRestriction k (ℓ ^ N) 0 x)) ∧
          (∀ a : A, res (Sheaf.H.map
              (Scheme.kummerCoefficientInsertion (curve k false) (ℓ ^ N) A a) 0 (z false)) =
            Sheaf.H.map (Scheme.kummerCoefficientInsertion (curve k true) (ℓ ^ N) A a)
              0 (z true))) := by
  sorry

end AlgebraicGeometry.KummerLine
