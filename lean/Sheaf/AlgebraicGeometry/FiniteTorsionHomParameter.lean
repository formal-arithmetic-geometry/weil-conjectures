module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import WeilConjectures.AlgebraicGeometry.SchemeClopenIdempotent
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Finite constant parameter scheme for torus-torsion homomorphisms

Source: Milne, Algebraic Groups (2017), Lemmas 12.4 and 12.35, Theorem 12.9(a),
printed pp.232--233, 243 (blueprint: lem-sfb-finite-torsion-hom-parameter).

Products and coproducts are taken in schemes over Spec k. The test-algebra
condition uses the recorded group laws on roots of unity and the multiplicative group.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

open StandardGroupSchemes

/-- The constant scheme on s-by-r matrices modulo n, with its map to Spec k.
Source: Milne, Lemma 12.35 and character labels in Lemma 12.4
(blueprint: lem-sfb-finite-torsion-hom-parameter). -/
def finiteTorsionParameterScheme (k : Type u) [Field k] (n r s : ℕ) [NeZero n] :
    Over (Spec (.of k)) :=
  ∐ fun _ : Fin s → Fin r → ZMod n ↦ Over.mk (𝟙 (Spec (.of k)))

/-- Evaluate a family's j-th coordinate on an algebra-valued parameter and a tuple of roots.
Source: Milne, Theorem 12.36, family condition, p.243
(blueprint: lem-sfb-finite-torsion-hom-parameter). -/
def finiteTorsionFamilyValue {k : Type u} [Field k] {n r s : ℕ} [NeZero n]
    {X : Over (Spec (.of k))}
    (φ : X ⨯ (∏ᶜ fun _ : Fin r ↦ roots k n) ⟶
      ∏ᶜ fun _ : Fin s ↦ multiplicative k)
    {A : Type u} [CommRing A] [Algebra k A] (x : affine k A ⟶ X)
    (h : Fin r → (affine k A ⟶ roots k n)) (j : Fin s) :
    affine k A ⟶ multiplicative k :=
  prod.lift x (Pi.lift h) ≫ φ ≫ Pi.π (fun _ : Fin s ↦ multiplicative k) j

/-- The family is a homomorphism in the roots-of-unity variable over every test algebra.
Naturality in the algebra is built into evaluation by composition of scheme morphisms.
Source: Milne, Lemma 12.35 and Theorem 12.36, p.243
(blueprint: lem-sfb-finite-torsion-hom-parameter). -/
def IsFiniteTorsionFamily {k : Type u} [Field k] {n r s : ℕ} [NeZero n]
    {X : Over (Spec (.of k))}
    (φ : X ⨯ (∏ᶜ fun _ : Fin r ↦ roots k n) ⟶
      ∏ᶜ fun _ : Fin s ↦ multiplicative k) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] (x : affine k A ⟶ X) (j : Fin s),
    finiteTorsionFamilyValue φ x 1 j = 1 ∧
      ∀ h h' : Fin r → (affine k A ⟶ roots k n),
        finiteTorsionFamilyValue φ x (h * h') j =
          finiteTorsionFamilyValue φ x h j * finiteTorsionFamilyValue φ x h' j

/-- The natural bijection between maps to the finite constant parameter scheme and families
of homomorphisms from μₙ^r to Gₘ^s, normalized by every integer lift of the matrix label.
Source: Milne, Lemma 12.35, p.243; Lemma 12.4 and Theorem 12.9(a), pp.232--233
(blueprint: lem-sfb-finite-torsion-hom-parameter).

Proof: On an affine U = Spec A in X, identify U × μₙ^r with Spec A[N],
N = (Z/n)^r, by sending each torsion coordinate to its basis monomial. The Hopf maps
send e^v to e^v ⊗ e^v and to 1. Pull the target coordinates back to units u_j.
The identity and multiplication equations on universal algebra-valued points give
ε(u_j) = 1 and Δ(u_j) = u_j ⊗ u_j. Comparing coefficients gives orthogonal
idempotents a_{jv} with sum 1, without reducedness or domain hypotheses on A.
The products b_m = ∏_j a_{j,m_j} give a disjoint clopen partition indexed by matrices;
on its m-th part the coordinates are e^{m_j}. Use the coproduct-copies/clopen lemma
to get U → C. Coefficients and idempotents commute with restriction, so these maps
agree on affine covers of overlaps and glue over X. Conversely the indicator sections
of a clopen partition give the units ∑_m c_m ∏_i h_i^{m_ji}; their inverses use
negative exponents. The affine-target adjunction gives the family, and the torsion
relations make it independent of integer lifts and a homomorphism on every algebra.
Coefficient uniqueness shows the constructions are inverse. Pullback of indicator
sections proves naturality for every X' → X. Empty products handle r = 0 and s = 0;
n = 1 gives only the identity character, and both maps from the empty scheme are unique.
The affine-product, tensor-pushout, open-base-change, and idempotent/clopen lemmas
are exactly the proof dependencies recorded in the DAG. -/
theorem finite_torsion_hom_parameter (k : Type u) [Field k] (n r s : ℕ) [NeZero n] :
    ∃ e : ∀ X : Over (Spec (.of k)),
      (X ⟶ finiteTorsionParameterScheme k n r s) ≃
        {φ : X ⨯ (∏ᶜ fun _ : Fin r ↦ roots k n) ⟶
          ∏ᶜ fun _ : Fin s ↦ multiplicative k // IsFiniteTorsionFamily φ},
      (∀ (X X' : Over (Spec (.of k))) (g : X' ⟶ X)
        (f : X ⟶ finiteTorsionParameterScheme k n r s),
        (e X' (g ≫ f)).val = prod.map g (𝟙 _) ≫ (e X f).val) ∧
      (∀ (X : Over (Spec (.of k))) (f : X ⟶ finiteTorsionParameterScheme k n r s)
        (A : Type u) [CommRing A] [Algebra k A] (x : affine k A ⟶ X)
        (m : Fin s → Fin r → ZMod n),
        x ≫ f = (Over.homMk (affine k A).hom) ≫
          Sigma.ι (fun _ : Fin s → Fin r → ZMod n ↦ Over.mk (𝟙 (Spec (.of k)))) m →
        ∀ (a : Fin s → Fin r → ℤ), (∀ j i, (a j i : ZMod n) = m j i) →
        ∀ (h : Fin r → (affine k A ⟶ roots k n)) (j : Fin s),
          finiteTorsionFamilyValue (e X f).val x h j =
            (List.ofFn (fun i : Fin r ↦ (h i ≫ rootsInclusion k n) ^ (a j i))).prod) := by
  sorry

end AlgebraicGeometry
