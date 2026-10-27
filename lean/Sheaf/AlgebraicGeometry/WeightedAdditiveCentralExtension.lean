module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Sheaf.AlgebraicGeometry.WeightedAdditiveExtension

/-! # Equivariant splitting of weight-two additive central extensions

Source: Conrad, Reductive group schemes, Proposition 4.3.1 and Lemma 4.3.2,
printed pp.127–128 (blueprint: lem-sfb-weighted-additive-central-extension).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

set_option autoImplicit false

/-- A central fppf extension of the additive group, with trivial kernel action and quotient
weight `2` or `-2`, is commutative and has a unique equivariant homomorphic section.
Every invariant homomorphism from the additive group to the kernel is trivial.

Source: Conrad, Proposition 4.3.1, additive commutator paragraph, and Lemma 4.3.2,
printed pp.127–128 (blueprint: lem-sfb-weighted-additive-central-extension).

Proof:
1. Lift two additive sections fppf-locally. Their commutator is a unique kernel section.
Centrality makes it independent of the lifts; sheaf gluing defines the commutator pairing.
2. Expanding commutators with central values shows that this pairing is biadditive.
The action fixes the kernel, so the pairing is invariant under simultaneous weight scaling.
3. By lem-sfb-unit-power-fppf-surjective, every unit is fppf-locally a square (or an inverse
square), so invariance holds for simultaneous scaling by any unit `a`. Equivalently,
`c(a*u,v) = c(u,a⁻¹*v)`.
4. On an affine test scheme use lem-sfb-monic-principal-open-fppf with
`P(t) = t*(t+1)*(t^2+t+1)`. Then `t`, `t+1`, and
`delta = (t+1)⁻¹-t⁻¹-1` are units. Biadditivity and step 3 give `c(u,delta*v) = 1`.
Replace `v` by `delta⁻¹*v` and descend, first along the fppf cover and then along affine
opens. Thus all commutators vanish and the middle sheaf is commutative.
5. For an invariant homomorphism to the kernel, use the same avoidance lemma with
`P(t) = t*(t^2-1)`. Both signs of the weight give an invertible `a = t^k-1`.
Invariance and the homomorphism law give `f(a*u) = 1`. Substitute `a⁻¹*u` and descend.
6. On this cover, for a lift `x` of `u`, put `d(u) = action(t,x)/x`.
Changing the lift by a kernel section leaves `d(u)` unchanged, so it glues naturally.
Commutativity shows that `d` is a homomorphism and `q(d(u)) = a*u`.
Set `j(u) = d(a⁻¹*u)` to obtain a homomorphic section.
7. The actions of any two units commute. Applying this to the formula for `d` shows
that `j` is equivariant for every local unit.
8. The quotient of two equivariant homomorphic sections is an invariant homomorphism
into the kernel, hence is trivial by step 5. This uniqueness glues the locally constructed
sections across the fppf and affine covers, and ensures naturality on every test scheme. -/
theorem weightedAdditiveCentralExtension_splits (S : Scheme.{u}) (Z : Over S)
    [GrpObj Z] [IsCommMonObj Z] [IsSeparated Z.hom]
    (k : ℤ) (hk : k = 2 ∨ k = -2) (E : WeightedAdditiveExtension.{u, v} S Z k) :
    (∀ (T : Over S) (x y : E.F.obj (op T)), x * y = y * x) ∧
    (∃! j : fppfAdditiveGroup.{u, v} S ⟶ E.F,
      j ≫ E.q = 𝟙 (fppfAdditiveGroup.{u, v} S) ∧
      ∀ (T : Over S) (t : Γ(T.left, ⊤)ˣ) (a : (fppfAdditiveGroup.{u, v} S).obj (op T)),
        j.app (op T) (fppfAdditiveWeight S k T t a) = E.action T t (j.app (op T) a)) ∧
    (∀ f : fppfAdditiveGroup.{u, v} S ⟶ yonedaGrpObj Z ⋙ GrpCat.uliftFunctor.{v, u},
      (∀ (T : Over S) (t : Γ(T.left, ⊤)ˣ) (a : (fppfAdditiveGroup.{u, v} S).obj (op T)),
        f.app (op T) (fppfAdditiveWeight S k T t a) = f.app (op T) a) →
      ∀ (T : Over S) (a : (fppfAdditiveGroup.{u, v} S).obj (op T)),
        f.app (op T) a = 1) := by
  sorry

end AlgebraicGeometry
