module

public import Mathlib.RepresentationTheory.Induced
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Induced characters and conjugacy classes

Source: the auxiliary quotient-basis calculation attached to the latest blueprint,
lem-per-artin-gabber-affine-curve, inherited representation input under Step 3.
ILO, Exposé X, Proposition 1.2, printed p.138, is motivation only; Serre,
Linear Representations of Finite Groups, Part I, Chapter 7, is the wanted reference.
(blueprint: lem-per-induced-character-conjugacy-formula)

Mathlib's `IndV` uses diagonal coinvariants and right inverse translation. The symbol
`[x,w]` of the node means `Representation.IndV.mk H.subtype ρ x⁻¹ w`.
The diagonal coinvariant relation identifies `[xh,w]` with `[x,ρ h w]`, and
`Representation.ind_mk` sends `[x,w]` to `[a*x,w]` under `a`. Conversely, send
Mathlib's generator at `y` with coefficient `w` to `[y⁻¹,w]`; the same relation
makes this inverse well defined. Thus no new induction construction is needed.
-/

@[expose] public section

universe u v

namespace Representation

/-- Both induced-character formulas, for the quotient with left translation.
Source: the auxiliary calculation under latest blueprint lem-per-artin-gabber-affine-curve,
Step 3; ILO X, Proposition 1.2, p.138 (motivation); Serre, Part I, Chapter 7 (wanted).

Proof:
1. Tensor generators and quotient surjectivity show that the classes `[x,w]` span.
   The relation `[xh,w]=[x,ρ h w]` is preserved by left translation; its inverse
   is translation by the inverse group element (tensor and quotient definition nodes).
2. By lem-weil-pbc-vector-space-free choose a basis `(b_i)` of W. A finite spanning
   family and the union of its basis supports show that the basis is finite
   (def-weil-finite-dimensional-subspace). Choose finite left-coset representatives S;
   each x has a unique expression s*h with s in S and h in H.
3. Map the direct sum of copies of W indexed by S to the quotient by summing `[s,w_s]`.
   Its inverse sends `[s*h,w]` to the s-coordinate `ρ h w`. Bilinearity gives a tensor
   map, and the action law kills every defining relation, so it descends to the quotient
   (def-weil-pbc-direct-sum-modules, tensor and quotient definition nodes).
4. The two maps are inverse on spanning generators. The coordinate vectors `[s,b_i]`
   are therefore a finite basis of the quotient, proving finite-dimensionality.
5. Write g*s=t*h. Translation sends `[s,b_i]` to `[t,ρ h b_i]`; a diagonal block
   contributes only when t=s, equivalently s⁻¹*g*s lies in H. That block's trace is
   the trace of ρ(s⁻¹*g*s). Sum diagonal entries (def-weil-endomorphism-trace).
6. For x=s*h, its conjugate is h⁻¹*(s⁻¹*g*s)*h. Membership in H is unchanged and
   trace is invariant under conjugation. The bijection S × H → G thus replaces the
   coset sum by the all-elements sum divided by |H|. This denominator is nonzero
   in ℂ, since H contains 1 (def-weil-endomorphism-trace).
7. For k=x₀⁻¹*g*x₀, the fibre of x ↦ x⁻¹*g*x over k is in bijection with C_G(g)
   by c ↦ c*x₀, with inverse x ↦ x*x₀⁻¹. Regroup the first sum by these fibres;
   each has |C_G(g)| elements. This proves the second equality.
8. An empty basis makes both sides zero when W=0. For H=G the representative set
   is {1}, giving χ_W(g). For H={1}, the value is zero unless g=1, when it is
   |G| dim W. This also covers the trivial group.

The finite sums are `finsum` over finite subtypes, so no choice of enumeration or
extra decidability hypothesis is imposed. The class `conjugatesOf g` is the set
of x⁻¹*g*x as x varies, since inversion permutes G. Both cardinal ratios lie in ℂ.
(blueprint: lem-per-induced-character-conjugacy-formula) -/
theorem induced_character_conjugacy_formula
    (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (W : Type v) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H W) (g : G) :
    LinearMap.trace ℂ (IndV H.subtype ρ) (ind H.subtype ρ g) =
        (1 / (Nat.card H : ℂ)) *
          ∑ᶠ x : {x : G // x⁻¹ * g * x ∈ H},
            LinearMap.trace ℂ W (ρ ⟨x.val⁻¹ * g * x.val, x.property⟩) ∧
      (1 / (Nat.card H : ℂ)) *
          (∑ᶠ x : {x : G // x⁻¹ * g * x ∈ H},
            LinearMap.trace ℂ W (ρ ⟨x.val⁻¹ * g * x.val, x.property⟩)) =
        ((Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) / (Nat.card H : ℂ)) *
          ∑ᶠ h : {h : H // (h : G) ∈ conjugatesOf g}, LinearMap.trace ℂ W (ρ h.val) := by
  sorry

end Representation
