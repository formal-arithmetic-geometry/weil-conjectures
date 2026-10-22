module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct
import WeilConjectures.RingTheory.FiniteProductNormal
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed

/-!
# Normality and properness of an existing finite geometric quotient

Source: ILO, Travaux de Gabber, Expose X 2.3, Steps 2--3, printed pp. 151--152;
Stacks Project, Tags 00IS, 09MQ(4), and 03GN.
(blueprint: lem-sfb-finite-quotient-normal-proper)

The action is given by scheme automorphisms over the field. Invariant sections are
expressed using `Scheme.Hom.appLE`, without choosing an identification of equal opens.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- An existing finite geometric and categorical quotient of a normal proper scheme
by a finite group is normal, proper, of finite type, and Noetherian.

Source: ILO, Expose X 2.3, Steps 2--3, printed pp. 151--152; Stacks Tags 00IS,
09MQ(4), and 03GN. (blueprint: lem-sfb-finite-quotient-normal-proper)

Proof:
1. The field is Noetherian. Finite type makes X Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Quasi-compactness descends along the
   surjection q, so Z has a finite affine cover, including the empty cover if Z is empty.
2. Over a chart Spec A of Z the inverse image is Spec B, with B finite over A by
   def-weil-finite-integral-morphism. By lem-weil-pbc-lft-affine-pairs, B is finite type
   over k. The invariant-section condition identifies A with the k-subalgebra B^H.
   Apply lem-sfb-artin-tate-subalgebra-finite-type (Stacks 00IS), then
   lem-weil-pbc-finite-type-algebra-noetherian. These charts prove finite type and
   Noetherianity of Z, using def-weil-finite-type-morphism.
3. Apply lem-sbc-normal-sections-finite-product to the quasi-compact affine inverse
   image in the locally Noetherian normal X: B is a finite product of normal domains.
4. Automorphisms permute the primitive nonzero idempotents of that product, hence
   its factors. Restrictions to the factors give compatible ring isomorphisms.
5. Projecting to one representative per orbit identifies B^H with the product of
   the representative factors fixed by their stabilizers. Conversely, transport a
   fixed representative coordinate along the factor isomorphisms. Stabilizer
   invariance makes this independent of the transporter, and the action law makes
   the resulting tuple invariant. The constructions are inverse ring maps.
6. A stabilizer-fixed subring C of a normal domain D is a normal domain: a fraction
   c/d integral over C is integral over D and lies in D. Applying a stabilizer element
   to d*y=c and cancelling nonzero d shows y is fixed. No averaging is required.
7. For a prime of C, clear the finitely many denominators of a monic equation for y
   over its localization by s outside the prime. Then s*y is integral over C, hence
   in C by step 6; thus y lies in the localization (def-weil-pbc-normal-ring).
8. Use lem-weil-pbc-finite-product-normal and the isomorphism of step 5, then
   lem-weil-pbc-affine-open-stalk-localization to obtain normal stalks on Z.
   The zero ring has no primes, so the empty product is covered.
9. By lem-weil-pbc-finite-proper, q is proper, hence universally closed. Apply
   lem-weil-pbc-surjective-universally-closed-separated to q over Spec k, and
   lem-weil-pbc-image-universally-closed to its composition with b. Together with
   finite type from step 2, these give properness (def-weil-proper-morphism).
   The geometric-orbit and categorical hypotheses are retained although this
   proof only needs the finite surjection and invariant sections. -/
theorem finiteQuotient_normal_proper
    (k : Type u) [Field k] {X Z : Scheme.{u}}
    (a : X ⟶ Spec (CommRingCat.of k)) (b : Z ⟶ Spec (CommRingCat.of k))
    [IsProper a]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (H : Type v) [Group H] [Finite H] (α : H →* Aut X)
    (hα : ∀ h : H, (α h).hom ≫ a = a)
    (q : X ⟶ Z) (hq : q ≫ b = a)
    (hinv : ∀ h : H, (α h).hom ≫ q = q)
    [IsFinite q] [Surjective q]
    (horbits : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x y : Spec (CommRingCat.of Ω) ⟶ X),
      x ≫ q = y ≫ q ↔ ∃ h : H, x ≫ (α h).hom = y)
    (hsections : ∀ U : Z.Opens, Function.Injective (q.app U) ∧
      ∀ s : Γ(X, q ⁻¹ᵁ U),
        (∃ t : Γ(Z, U), q.app U t = s) ↔
          ∀ (h : H) (e : q ⁻¹ᵁ U ≤ (α h).hom ⁻¹ᵁ (q ⁻¹ᵁ U)),
            (α h).hom.appLE (q ⁻¹ᵁ U) (q ⁻¹ᵁ U) e s = s)
    (hcategorical : ∀ (W : Scheme.{u}) (c : W ⟶ Spec (CommRingCat.of k))
      (f : X ⟶ W), f ≫ c = a → (∀ h : H, (α h).hom ≫ f = f) →
      ∃! g : Z ⟶ W, g ≫ c = b ∧ q ≫ g = f) :
    (∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z)) ∧
    IsProper b ∧ (LocallyOfFiniteType b ∧ QuasiCompact b) ∧ IsNoetherian Z := by
  sorry

end AlgebraicGeometry
