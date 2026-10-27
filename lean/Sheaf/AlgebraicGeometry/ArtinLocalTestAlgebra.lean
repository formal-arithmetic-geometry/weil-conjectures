module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Jacobson.Ring

/-! # Algebra of Artinian deformation tests

Source: Stacks Project, formal-defos.tex, Tags 06GH (lemma-fiber-product-CLambda)
and 06GE (lemma-factor-small-extension); artin.tex, Tag 07T4
(equation-predeformation-category), localization at the image point
(blueprint: lem-sfb-artin-local-test-algebra).

The localization clause is stated on marked structures and their maps: it extends
structures uniquely without changing any underlying ring, residue marking, or map.
Thus it applies to both Artinian tests and complete Noetherian local algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {R k : Type u} [CommRing R] [hR : IsNoetherianRing R] [Field k] [Algebra R k]
  [hk : Algebra.FiniteType R k]

include hR hk

/-- Nilpotence, literal fibre products, and canonical kernels of Artinian tests.
Source: Stacks, Tags 06GH, 00J8 and 00JB
(blueprint: lem-sfb-artin-local-test-algebra).

Proof: Step 1 applies the Artinian-local nilpotence criterion. Steps 2 and 4
identify the common residue of a compatible pair and its maximal kernel; a pair
with nonzero residue has coordinatewise inverse. Surjectivity of the second leg
lifts each first coordinate. Step 5 filters its kernel by simple ideals using
lem-weil-pbc-artinian-ideal-length-one-filtration. Nilpotence kills the maximal
ideal on every simple factor, making it a one-dimensional residue module. These
are also simple modules for the fibre product. Length additivity in the kernel
sequence, and finite self-length of the Artinian quotient, give finite self-length
of the fibre product, hence Artinianness. Step 6 identifies the projection kernel
by the second coordinate, with inverse j ↦ (0,j). For a small second leg this
kernel is nonzero principal and annihilated by the maximal ideal, hence small.
-/
theorem artin_local_test_algebra :
    (∀ B : TestCategory R k,
      ∃ N : ℕ, 0 < N ∧ IsLocalRing.maximalIdeal (ring B) ^ N = ⊥) ∧
    (∀ (A₁ A₂ A : TestCategory R k) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
      (hs : Function.Surjective (map f₂)),
      IsTestAlgebra R k (A := CommAlgCat.of R (fibreProductAlgebra f₁ f₂))
          (fibreProductResidue f₁ f₂) ∧
      Function.Surjective (map (fibreProductFst f₁ f₂ hs)) ∧
      (IsSmallExtension f₂ →
        IsSmallExtension (fibreProductFst f₁ f₂ hs) ∧
        ∃ e : RingHom.ker (map (fibreProductFst f₁ f₂ hs)).toRingHom ≃+
            RingHom.ker (map f₂).toRingHom,
          ∀ x, (e x).val = x.val.val.2)) := sorry

/-- Every surjection factors into small extensions followed by an isomorphism;
a nonzero kernel permits a positive chain ending at the target itself.
Source: Stacks, Tag 06GE (blueprint: lem-sfb-artin-local-test-algebra).

Proof: Steps 1--3 of the node first filter the kernel J by simple ideals.
Nilpotence of the maximal ideal makes each simple factor a one-dimensional
k-vector space. Quotients by the filtration ideals remain Artinian local marked
R-algebras. Their consecutive surjections have nonzero principal kernels killed
by the maximal ideal, so they are small. Their composite is the quotient by J,
followed by the canonical marked isomorphism to C. If J is nonzero, absorb that
last isomorphism into the last small extension. If J is zero, retain the given
isomorphism as the final arrow of a zero-length chain. Conversely a positive
chain of small extensions has nonzero kernel. In particular a nonidentity
automorphism is represented by the final isomorphism, not an empty composite.
-/
theorem exists_small_extension_factorization {B C : TestCategory R k} (f : B ⟶ C)
    (hf : Function.Surjective (map f)) :
    (∃ (n : ℕ) (T : ComposableArrows (TestCategory R k) n)
      (hB : T.left = B) (eC : T.right ≅ C),
      (∀ i : Fin n, IsSmallExtension (T.map (homOfLE (Fin.castSucc_le_succ i)))) ∧
      eqToHom hB.symm ≫ T.hom ≫ eC.hom = f ∧ (n = 0 ↔ IsIso f)) ∧
    (RingHom.ker (map f).toRingHom ≠ ⊥ →
      ∃ (n : ℕ) (T : ComposableArrows (TestCategory R k) n)
        (hB : T.left = B) (hC : T.right = C),
        0 < n ∧
        (∀ i : Fin n, IsSmallExtension (T.map (homOfLE (Fin.castSucc_le_succ i)))) ∧
        eqToHom hB.symm ≫ T.hom ≫ eqToHom hC = f) := sorry

/-- Localization at the kernel of R → k is Noetherian local, makes k module-finite,
and uniquely extends marked structures and preserves precisely the same arrows.
Here Λ is any model of the specified localization, not an additional base ring.
Source: Stacks, Artin Tag 07T4 (equation-predeformation-category); Algebra Tags
00CP, 00FN and 00FV (blueprint: lem-sfb-artin-local-test-algebra).

Proof: Step 7 sets p = ker(R → k). It is prime since k is a field. Localization
is Noetherian and local. For every marked local algebra, every element outside p
has nonzero residue and hence is a unit. The localization universal property
therefore extends its R-structure uniquely by r/s ↦ r_B / s_B. Compatibility with
the fixed residue map follows by the same universal property. Any R-map between
such algebras commutes with their extended structures by uniqueness. Restriction
and extension thus identify objects and arrows of the two test categories.
The identical argument applies to complete Noetherian marked local algebras:
underlying rings, maximal ideals, quotient towers and their limit maps do not
change, so completeness and Noetherianness do not change. Step 8 factors Λ → k
through its residue field k₀. The finite R-algebra generators generate k as a
k₀-algebra. Zariski's lemma makes k finite-dimensional over k₀, so a k₀-basis
also generates k over Λ. No maximality of p in R is asserted or used.
-/
theorem localization_marked_structures (Λ : Type u) [CommRing Λ] [Algebra R Λ]
    [IsLocalization
      (@Ideal.primeCompl R _ (RingHom.ker (algebraMap R k))
        (RingHom.ker_isPrime (algebraMap R k))) Λ] :
    IsNoetherianRing Λ ∧ IsLocalRing Λ ∧
    ∃! q : Λ →+* k,
      q.comp (algebraMap R Λ) = algebraMap R k ∧
      q.Finite ∧
      (∀ A : TestCategory R k,
        ∃! a : Λ →+* ring A,
          a.comp (algebraMap R Λ) = algebraMap R (ring A) ∧
          (residue A).toRingHom.comp a = q) ∧
      (∀ C : CompleteLocalAlgebra R k,
        ∃! a : Λ →+* C.ring,
          a.comp (algebraMap R Λ) = algebraMap R C.ring ∧
          (C.residueEquiv.toRingHom.comp (IsLocalRing.residue C.ring)).comp a = q) ∧
      (∀ (A B : TestCategory R k) (a : Λ →+* ring A) (b : Λ →+* ring B),
        a.comp (algebraMap R Λ) = algebraMap R (ring A) →
        b.comp (algebraMap R Λ) = algebraMap R (ring B) →
        ∀ f : A ⟶ B, (map f).toRingHom.comp a = b) ∧
      (∀ (C D : CompleteLocalAlgebra R k) (a : Λ →+* C.ring) (b : Λ →+* D.ring),
        a.comp (algebraMap R Λ) = algebraMap R C.ring →
        b.comp (algebraMap R Λ) = algebraMap R D.ring →
        ∀ f : C.ring →ₐ[R] D.ring, IsLocalHom f →
          (D.residueEquiv.toRingHom.comp (IsLocalRing.residue D.ring)).comp f.toRingHom =
            C.residueEquiv.toRingHom.comp (IsLocalRing.residue C.ring) →
          f.toRingHom.comp a = b) := sorry

end AlgebraicGeometry.ArtinDeformation
