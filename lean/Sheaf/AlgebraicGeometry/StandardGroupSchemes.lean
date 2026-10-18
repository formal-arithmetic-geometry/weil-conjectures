/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

import Mathlib.Algebra.CharP.Frobenius
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-!
# Multiplicative, additive, roots-of-unity and Frobenius-kernel group schemes

Source: the Weil conjectures blueprint, `sec-smooth-purity/sk-prop-an/def-sc-gm-ga`
(blueprint: def-sc-gm-ga); Stacks Project, Tags 022U, 022V, 040M and 0CC9.

The underlying affine schemes and all coordinate maps are explicit. Group structures
are selected from unique-existence theorems fixing all three structure maps, so no
unspecified data is introduced. Only verification of these maps is postponed.

## Main definitions

- `StandardGroupSchemes.multiplicative`: Spec k[t,t⁻¹], with its Laurent Hopf group law.
- `StandardGroupSchemes.additive`: Spec k[y], with its additive group law.
- `StandardGroupSchemes.roots`: Spec k[t]/(t^n-1), with `rootsInclusion` into Gₘ.
- `StandardGroupSchemes.alpha`: Spec k[y]/(y^p), with `alphaInclusion` into Gₐ.
- `StandardGroupSchemes.frobenius`: the coefficient-fixing map induced by z ↦ y^p.

## Main statements

The two inclusion theorems assert the closed subgroup properties;
`StandardGroupSchemes.alpha_isFrobeniusKernel` identifies the latter subgroup
with the scheme-theoretic kernel, respecting its inclusion.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry
namespace StandardGroupSchemes

variable (k : Type u) [Field k]

/-- Spec of a coordinate algebra over the field (Stacks, Tag 01I1;
(blueprint: def-sc-gm-ga)). -/
noncomputable def affine (A : Type u) [CommRing A] [Algebra k A] :
    Over (Spec (.of k)) :=
  (algSpec (.of k)).obj (op (CommAlgCat.of k A))

/-- Contravariant Spec of a coordinate algebra map (Stacks, Tag 01I1;
(blueprint: def-sc-gm-ga)). -/
noncomputable def map {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) : affine k B ⟶ affine k A :=
  (algSpec (.of k)).map (CommAlgCat.ofHom f).op

/-- Multiplication from comultiplication, using the canonical affine-product
identification (Stacks, Tags 022U, 022V, 01I4; (blueprint: def-sc-gm-ga)). -/
noncomputable def multiplication {A : Type u} [CommRing A] [Algebra k A]
    (d : A →ₐ[k] A ⊗[k] A) : affine k A ⊗ affine k A ⟶ affine k A :=
  letI := braidedAlgSpec (R := .of k)
  Functor.LaxMonoidal.μ (algSpec (.of k)) (op (CommAlgCat.of k A))
    (op (CommAlgCat.of k A)) ≫ map k d

/-- Identity section from the counit, using Spec k as tensor unit (Stacks,
Tags 022U, 022V; (blueprint: def-sc-gm-ga)). -/
noncomputable def identitySection {A : Type u} [CommRing A] [Algebra k A]
    (e : A →ₐ[k] k) : 𝟙_ (Over (Spec (.of k))) ⟶ affine k A :=
  letI := braidedAlgSpec (R := .of k)
  Functor.LaxMonoidal.ε (algSpec (.of k)) ≫ map k e

/-- The multiplicative group Spec k[t,t⁻¹], with Mathlib's canonical Laurent
Hopf algebra (Stacks, Tag 022U; (blueprint: def-sc-gm-ga)). -/
noncomputable def multiplicative : Over (Spec (.of k)) := affine k (LaurentPolynomial k)

/-- The canonical multiplicative group structure from the Laurent Hopf algebra:
t maps to t⊗t, 1 and t⁻¹ (Stacks, Tag 022U; (blueprint: def-sc-gm-ga)). -/
noncomputable instance multiplicativeGroup : GrpObj (multiplicative k) :=
  inferInstanceAs (GrpObj ((Spec (.of (LaurentPolynomial k))).asOver (Spec (.of k))))

/-- The additive group Spec k[y] (Stacks, Tag 022V; (blueprint: def-sc-gm-ga)). -/
noncomputable def additive : Over (Spec (.of k)) := affine k (Polynomial k)

/-- Additive comultiplication y ↦ y⊗1+1⊗y (Stacks, Tag 022V;
(blueprint: def-sc-gm-ga)). -/
noncomputable def additiveComul : Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k :=
  Polynomial.aeval (Polynomial.X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Polynomial.X)

/-- Additive counit y ↦ 0 (Stacks, Tag 022V; (blueprint: def-sc-gm-ga)). -/
noncomputable def additiveCounit : Polynomial k →ₐ[k] k := Polynomial.aeval 0

/-- Additive antipode y ↦ -y (Stacks, Tag 022V; (blueprint: def-sc-gm-ga)). -/
noncomputable def additiveAntipode : Polynomial k →ₐ[k] Polynomial k :=
  Polynomial.aeval (-Polynomial.X)

/-- The three displayed coordinate maps give a unique group structure on the
additive affine line (Stacks, Tag 022V; (blueprint: def-sc-gm-ga)).
Proof: substitute y in the two triple comultiplications to obtain
 y⊗1⊗1+1⊗y⊗1+1⊗1⊗y; both counit composites fix y, and the inverse
composites send y to -y+y=0=y-y. Algebra maps are determined by y; the
fully faithful affine Spec functor gives the group diagrams. All three
structure maps have been fixed, so the structure is unique by proof irrelevance. -/
theorem additiveGroup_existsUnique :
    ∃! h : GrpObj (additive k),
      h.one = identitySection k (additiveCounit k) ∧
      h.mul = multiplication k (additiveComul k) ∧
      h.inv = map k (additiveAntipode k) := by
  sorry

/-- The uniquely specified additive group structure (Stacks, Tag 022V;
(blueprint: def-sc-gm-ga)). -/
noncomputable instance additiveGroup : GrpObj (additive k) :=
  (additiveGroup_existsUnique k).exists.choose

/-- The defining ideal for the roots of unity (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)). -/
noncomputable def rootsIdeal (n : ℕ) : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X ^ n - 1} : Set (Polynomial k))

/-- The coordinate algebra of the roots of unity (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)). -/
abbrev rootsAlgebra (n : ℕ) := Polynomial k ⧸ rootsIdeal k n

/-- The residue class of the coordinate (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)). -/
noncomputable def rootsCoordinate (n : ℕ) : rootsAlgebra k n :=
  Ideal.Quotient.mkₐ k (rootsIdeal k n) Polynomial.X

/-- The affine roots of unity scheme (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)). -/
noncomputable def roots (n : ℕ) : Over (Spec (.of k)) :=
  affine k (rootsAlgebra k n)

/-- The coordinate substitutions kill the defining ideal (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)).
Proof: the quotient coordinate satisfies its defining relation. For roots of
unity, its n-th power is 1, so its tensor square and inverse also have n-th
power 1. For alpha, characteristic p makes the p-th power additive, so the
p-th power of the tensor sum is zero; zero and the negative also satisfy the
relation. Each substitution is an algebra map and hence kills the generated ideal. -/
theorem rootsRelations (n : ℕ) [NeZero n] :
    (∀ f ∈ rootsIdeal k n,
      Polynomial.aeval (rootsCoordinate k n ⊗ₜ[k] rootsCoordinate k n) f = 0) ∧
    (∀ f ∈ rootsIdeal k n,
      (Polynomial.aeval (1 : k)) f = 0) ∧
    (∀ f ∈ rootsIdeal k n,
      Polynomial.aeval (rootsCoordinate k n ^ (n - 1)) f = 0) := by
  sorry

/-- The descended comultiplication (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)). -/
noncomputable def rootsComul (n : ℕ) [NeZero n] :
    rootsAlgebra k n →ₐ[k] rootsAlgebra k n ⊗[k] rootsAlgebra k n :=
  Ideal.Quotient.liftₐ (rootsIdeal k n)
    (Polynomial.aeval (rootsCoordinate k n ⊗ₜ[k] rootsCoordinate k n))
    (rootsRelations k n).1

/-- The descended counit (Stacks, Tag 040M; (blueprint: def-sc-gm-ga)). -/
noncomputable def rootsCounit (n : ℕ) [NeZero n] : rootsAlgebra k n →ₐ[k] k :=
  Ideal.Quotient.liftₐ (rootsIdeal k n) (Polynomial.aeval 1)
    (rootsRelations k n).2.1

/-- The descended antipode (Stacks, Tag 040M; (blueprint: def-sc-gm-ga)). -/
noncomputable def rootsAntipode (n : ℕ) [NeZero n] :
    rootsAlgebra k n →ₐ[k] rootsAlgebra k n :=
  Ideal.Quotient.liftₐ (rootsIdeal k n)
    (Polynomial.aeval (rootsCoordinate k n ^ (n - 1)))
    (rootsRelations k n).2.2

/-- The displayed maps uniquely specify the roots of unity group structure
(Stacks, Tag 040M; (blueprint: def-sc-gm-ga)).
Proof: check all diagrams on the quotient coordinate. In the roots case the
iterated comultiplications are x⊗x⊗x, the counits fix x, and multiplication
with the inverse gives x^n=1. In the alpha case the iterated sums agree,
the counits fix x, and x+(-x)=0=(-x)+x. Quotient algebra maps are determined
by the coordinate, and faithful Spec turns these into the group diagrams.
All three structure maps are fixed, giving uniqueness by proof irrelevance. -/
theorem rootsGroup_existsUnique (n : ℕ) [NeZero n] :
    ∃! h : GrpObj (roots k n),
      h.one = identitySection k (rootsCounit k n) ∧
      h.mul = multiplication k (rootsComul k n) ∧
      h.inv = map k (rootsAntipode k n) := by
  sorry

/-- The unique roots of unity group structure with the displayed coordinates
(Stacks, Tag 040M; (blueprint: def-sc-gm-ga)). -/
noncomputable instance rootsGroup (n : ℕ) [NeZero n] : GrpObj (roots k n) :=
  (rootsGroup_existsUnique k n).exists.choose

/-- The defining ideal for the Frobenius kernel (Stacks, Tag 0CC9;
(blueprint: def-sc-gm-ga)). -/
noncomputable def alphaIdeal (p : ℕ) : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X ^ p} : Set (Polynomial k))

/-- The coordinate algebra of the Frobenius kernel (Stacks, Tag 0CC9;
(blueprint: def-sc-gm-ga)). -/
abbrev alphaAlgebra (p : ℕ) := Polynomial k ⧸ alphaIdeal k p

/-- The residue class of the coordinate (Stacks, Tag 0CC9;
(blueprint: def-sc-gm-ga)). -/
noncomputable def alphaCoordinate (p : ℕ) : alphaAlgebra k p :=
  Ideal.Quotient.mkₐ k (alphaIdeal k p) Polynomial.X

/-- The affine Frobenius kernel scheme (Stacks, Tag 0CC9;
(blueprint: def-sc-gm-ga)). -/
noncomputable def alpha (p : ℕ) : Over (Spec (.of k)) :=
  affine k (alphaAlgebra k p)

/-- The coordinate substitutions kill the defining ideal (Stacks, Tag 0CC9;
(blueprint: def-sc-gm-ga)).
Proof: the quotient coordinate satisfies its defining relation. For roots of
unity, its n-th power is 1, so its tensor square and inverse also have n-th
power 1. For alpha, characteristic p makes the p-th power additive, so the
p-th power of the tensor sum is zero; zero and the negative also satisfy the
relation. Each substitution is an algebra map and hence kills the generated ideal. -/
theorem alphaRelations (p : ℕ) [NeZero p] [CharP k p] :
    (∀ f ∈ alphaIdeal k p,
      Polynomial.aeval (alphaCoordinate k p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] alphaCoordinate k p) f = 0) ∧
    (∀ f ∈ alphaIdeal k p,
      (Polynomial.aeval (0 : k)) f = 0) ∧
    (∀ f ∈ alphaIdeal k p,
      Polynomial.aeval (-alphaCoordinate k p) f = 0) := by
  sorry

/-- The descended comultiplication (Stacks, Tag 0CC9;
(blueprint: def-sc-gm-ga)). -/
noncomputable def alphaComul (p : ℕ) [NeZero p] [CharP k p] :
    alphaAlgebra k p →ₐ[k] alphaAlgebra k p ⊗[k] alphaAlgebra k p :=
  Ideal.Quotient.liftₐ (alphaIdeal k p)
    (Polynomial.aeval (alphaCoordinate k p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] alphaCoordinate k p))
    (alphaRelations k p).1

/-- The descended counit (Stacks, Tag 0CC9; (blueprint: def-sc-gm-ga)). -/
noncomputable def alphaCounit (p : ℕ) [NeZero p] [CharP k p] : alphaAlgebra k p →ₐ[k] k :=
  Ideal.Quotient.liftₐ (alphaIdeal k p) (Polynomial.aeval 0)
    (alphaRelations k p).2.1

/-- The descended antipode (Stacks, Tag 0CC9; (blueprint: def-sc-gm-ga)). -/
noncomputable def alphaAntipode (p : ℕ) [NeZero p] [CharP k p] :
    alphaAlgebra k p →ₐ[k] alphaAlgebra k p :=
  Ideal.Quotient.liftₐ (alphaIdeal k p)
    (Polynomial.aeval (-alphaCoordinate k p))
    (alphaRelations k p).2.2

/-- The displayed maps uniquely specify the Frobenius kernel group structure
(Stacks, Tag 0CC9; (blueprint: def-sc-gm-ga)).
Proof: check all diagrams on the quotient coordinate. In the roots case the
iterated comultiplications are x⊗x⊗x, the counits fix x, and multiplication
with the inverse gives x^n=1. In the alpha case the iterated sums agree,
the counits fix x, and x+(-x)=0=(-x)+x. Quotient algebra maps are determined
by the coordinate, and faithful Spec turns these into the group diagrams.
All three structure maps are fixed, giving uniqueness by proof irrelevance. -/
theorem alphaGroup_existsUnique (p : ℕ) [NeZero p] [CharP k p] :
    ∃! h : GrpObj (alpha k p),
      h.one = identitySection k (alphaCounit k p) ∧
      h.mul = multiplication k (alphaComul k p) ∧
      h.inv = map k (alphaAntipode k p) := by
  sorry

/-- The unique Frobenius kernel group structure with the displayed coordinates
(Stacks, Tag 0CC9; (blueprint: def-sc-gm-ga)). -/
noncomputable instance alphaGroup (p : ℕ) [NeZero p] [CharP k p] : GrpObj (alpha k p) :=
  (alphaGroup_existsUnique k p).exists.choose

/-- The coordinate of μₙ is a unit, with inverse x^(n-1) (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)).
Proof: the relation x^n=1 and n≥1 give x*x^(n-1)=1=x^(n-1)*x. -/
theorem rootsCoordinate_inverse (n : ℕ) [NeZero n] :
    rootsCoordinate k n * rootsCoordinate k n ^ (n - 1) = 1 ∧
      rootsCoordinate k n ^ (n - 1) * rootsCoordinate k n = 1 := by
  sorry

/-- The explicit unit defining the Laurent quotient map (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)). -/
noncomputable def rootsCoordinateUnit (n : ℕ) [NeZero n] : (rootsAlgebra k n)ˣ where
  val := rootsCoordinate k n
  inv := rootsCoordinate k n ^ (n - 1)
  val_inv := (rootsCoordinate_inverse k n).1
  inv_val := (rootsCoordinate_inverse k n).2

/-- Laurent substitution fixes all coefficients (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)).
Proof: a constant Laurent polynomial evaluates to its coefficient under the
coefficient algebra map. This is exactly compatibility with the k-algebra structure. -/
theorem rootsLaurent_commutes (n : ℕ) [NeZero n] (c : k) :
    LaurentPolynomial.eval₂ (algebraMap k (rootsAlgebra k n)) (rootsCoordinateUnit k n)
      (algebraMap k (LaurentPolynomial k) c) = algebraMap k (rootsAlgebra k n) c := by
  sorry

/-- The displayed quotient surjection k[t,t⁻¹] → k[t]/(t^n-1), sending
t to its residue class and t⁻¹ to its (n-1)-st power (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)). -/
noncomputable def rootsQuotient (n : ℕ) [NeZero n] :
    LaurentPolynomial k →ₐ[k] rootsAlgebra k n :=
  { LaurentPolynomial.eval₂ (algebraMap k (rootsAlgebra k n)) (rootsCoordinateUnit k n) with
    commutes' := rootsLaurent_commutes k n }

/-- The closed subgroup inclusion μₙ → Gₘ induced by the quotient map
(Stacks, Tag 040M; (blueprint: def-sc-gm-ga)). -/
noncomputable def rootsInclusion (n : ℕ) [NeZero n] : roots k n ⟶ multiplicative k :=
  map k (rootsQuotient k n)

/-- The quotient k[y] → k[y]/(y^p) (Stacks, Tag 0CC9;
(blueprint: def-sc-gm-ga)). -/
noncomputable def alphaQuotient (p : ℕ) : Polynomial k →ₐ[k] alphaAlgebra k p :=
  Ideal.Quotient.mkₐ k (alphaIdeal k p)

/-- The closed subgroup inclusion αₚ → Gₐ induced by the quotient map
(Stacks, Tag 0CC9; (blueprint: def-sc-gm-ga)). -/
noncomputable def alphaInclusion (p : ℕ) : alpha k p ⟶ additive k :=
  map k (alphaQuotient k p)

/-- Both defining coordinate maps are surjective (Stacks, Tags 040M, 0CC9;
(blueprint: def-sc-gm-ga)).
Proof: every quotient class is represented by a polynomial. For roots of
unity use the same polynomial as a Laurent polynomial; the Laurent substitution
restricts to the polynomial quotient map. For alpha use surjectivity of the quotient map. -/
theorem quotient_surjective (n p : ℕ) [NeZero n] :
    Function.Surjective (rootsQuotient k n) ∧
      Function.Surjective (alphaQuotient k p) := by
  sorry

/-- μₙ is a closed subgroup of Gₘ (Stacks, Tag 040M;
(blueprint: def-sc-gm-ga)).
Proof: the Laurent quotient is surjective, hence Spec gives a closed immersion
and is injective on points. Its coordinate generator respects all three
structure maps, so it is a group homomorphism and a closed subgroup scheme. -/
theorem roots_isClosedSubgroupScheme (n : ℕ) [NeZero n] :
    IsClosedSubgroupScheme (rootsInclusion k n) := by
  sorry

/-- αₚ is a closed subgroup of Gₐ in positive characteristic p (Stacks, Tag 0CC9;
(blueprint: def-sc-gm-ga)).
Proof: the polynomial quotient is surjective, giving a closed immersion and
injectivity on points. Its coordinate respects addition, zero and negation;
these formulas descend because p-th powers are additive in characteristic p. -/
theorem alpha_isClosedSubgroupScheme (p : ℕ) [NeZero p] [CharP k p] :
    IsClosedSubgroupScheme (alphaInclusion k p) := by
  sorry

/-- The k-linear Frobenius coordinate map z ↦ y^p. Coefficients are fixed:
this is the relative Frobenius after identifying the twist by its coordinate,
not the absolute Frobenius of k[y] (Stacks, Tag 0CC9; (blueprint: def-sc-gm-ga)). -/
noncomputable def frobeniusCoordinates (p : ℕ) : Polynomial k →ₐ[k] Polynomial k :=
  Polynomial.aeval (Polynomial.X ^ p)

/-- Frobenius on Gₐ, induced by z ↦ y^p fixing k (Stacks, Tag 0CC9;
(blueprint: def-sc-gm-ga)). -/
noncomputable def frobenius (p : ℕ) : additive k ⟶ additive k :=
  map k (frobeniusCoordinates k p)

/-- The relative Frobenius is a group homomorphism (Stacks, Tag 0CC9;
(blueprint: def-sc-gm-ga)).
Proof: in positive field characteristic p, p is prime and (a+b)^p=a^p+b^p.
This verifies compatibility with the additive comultiplication on the generator;
zero and negation are preserved as well. Faithful Spec gives the group identity. -/
theorem frobenius_isMonHom (p : ℕ) [NeZero p] [CharP k p] :
    IsMonHom (frobenius k p) := by
  sorry

/-- The quotient αₚ is the scheme-theoretic Frobenius kernel, compatibly
with its specified inclusion (Stacks, Tag 0CC9; (blueprint: def-sc-gm-ga)).
Proof: the kernel fibre product has coordinate algebra k[y]⊗_{k[z]}k,
where z maps to y^p and to zero. The map f⊗c ↦ c*f modulo (y^p)
has inverse induced by y ↦ y⊗1, since y^p⊗1=1⊗0=0. The two
composites fix k and y, so they are inverse; Spec gives the required
isomorphism and compatibility with the kernel inclusion. This calculation
uses no perfectness or reducedness hypothesis. To check the relative Frobenius
identification, its twist algebra is k[y]⊗_{k,F_k}k. The coefficient-fixing
isomorphism to k[z] sends a*y^i⊗b to a^p*b*z^i; its inverse sends z to y⊗1
and b to 1⊗b. The balancing relation a*c⊗b=a⊗c^p*b proves that these
maps are inverse. They preserve the additive comultiplication and zero counit.
The relative Frobenius map f⊗b ↦ f^p*b therefore becomes precisely the
coefficient-fixing substitution z ↦ y^p used here. -/
theorem alpha_isFrobeniusKernel (p : ℕ) [NeZero p] [CharP k p] :
    ∃ e : alpha k p ≅ GrpObj.ker (frobenius k p),
      e.hom ≫ GrpObj.kerι (frobenius k p) = alphaInclusion k p := by
  sorry

end StandardGroupSchemes
end AlgebraicGeometry
