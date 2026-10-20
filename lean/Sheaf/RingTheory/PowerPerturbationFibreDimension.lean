module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.AffineLimitFibreDimensionBound
import Sheaf.AlgebraicGeometry.CompositeFibreDimensionInequality
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds
import Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.GenericOpenFibreDensity
import Sheaf.AlgebraicGeometry.NowhereDenseDimensionDrop
import WeilConjectures.RingTheory.LimitModuleFinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# High-power perturbations preserve a fibre-dimension bound

Source: Stacks Project, More on Morphisms, Tag 0GTF, lemma-sum-is-ok
(blueprint: lem-trf-power-perturbation-fibre-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

/-- The morphism from `Spec S` to the affine line over `Spec R` associated to
an element of `S`, by evaluation of the unique polynomial variable at that element.
Source: Stacks Project, More on Morphisms, Tag 0GTF, lemma-sum-is-ok
(blueprint: lem-trf-power-perturbation-fibre-dimension). -/
noncomputable def powerPerturbationMap {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (c : S) :
    Spec (.of S) ⟶ Spec (.of (MvPolynomial (Fin 1) R)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom φ (fun _ : Fin 1 ↦ c)))

/-- For a finite-type ring map, sufficiently high perturbations `a ^ n + b`
preserve a uniform upper bound on the Krull dimensions of all scheme-theoretic
fibres. Empty fibres are included, since their topological Krull dimension is
`⊥`.
Source: Stacks Project, More on Morphisms, Tag 0GTF, lemma-sum-is-ok
(blueprint: lem-trf-power-perturbation-fibre-dimension).

Proof (the node's steps).
1. Each coordinate morphism `f_c` is of finite type (the generators of `S` over
   `R` generate it over `R[t]`), and its fibre over `Q` is
   `Spec (S ⊗_{R[t]} κ(Q))`.
2. Write `S = R[A, B, x₁, …, xₘ] / J` with `A, B ↦ a, b`; the quotients by the
   finitely generated subideals `J_λ ⊆ J` form a directed system with
   surjective transition maps and colimit `S`. By the affine limit
   fibre-dimension bound some stage `S_λ`, finitely presented over `R`, has
   all `a_λ`-fibres of dimension `≤ d`; the fibres for `a ^ n + b` are
   quotients of the stage fibres, so a stage threshold works for `S`.
3. For `R → S` finitely presented, Noetherian approximation gives a directed
   system `R_i → S_i` of finite-type `ℤ`-algebras with `S ≅ S_i ⊗_{R_i} R`;
   with representatives `a_i, b_i` the maps `R_i[t] → S_i` form a system with
   colimit `R[t] → S`, so the affine limit bound gives a stage with bound `d`.
4. Each `t ↦ a ^ n + b` is the base change of `t ↦ a_i ^ n + b_i`; fibre
   dimension is preserved by base change and is the supremum of the local
   dimensions, so a threshold at the stage passes to `R → S`. Hence assume `R`
   and `S` of finite type over `ℤ`.
5. Induct strongly on `dim R`, finite since `R` is a quotient of a polynomial
   ring over `ℤ`; `R = 0` or `S = 0` gives empty fibres.
6. `S` is Noetherian with finitely many minimal primes `P_i`; each `S / P_i`
   satisfies the hypothesis, every fibre chain lies in one closed piece, and
   the maximum of the thresholds works: assume `S` is a domain.
7. Replace `R` by its image in `S`: fibres over primes not containing the
   kernel are empty, the others are unchanged; if the dimension dropped use
   the induction hypothesis. Assume `R ⊆ S` domains.
8. `dim_z 𝔸ʳ_k = r` for `r = 1, 2`; the composite fibre inequality for
   `X → 𝔸¹_R → Spec R` gives `dim X_p ≤ d + 1` for every `p`.
9. Let `φ : X → 𝔸²_R` be `x ↦ a, y ↦ b` and `π_n` send the coordinate to
   `x ^ n + y`, so `f_{a ^ n + b} = π_n ∘ φ`. If `R[x, y] → S` is injective,
   generic flatness gives a nonempty open `U = D(H(a, b)) ⊆ X` with `φ|_U`
   flat, and generic density gives a nonempty open `V ⊆ Spec R` with `U_p`
   dense in `X_p` for `p ∈ V`.
10. The flat additivity of fibre dimension, applied after `𝔸²_R → Spec R` and
    after `π_n` (whose fibre is `κ(q)[x]`), gives `dim_u U_q = e + 1` and
    `e + 2 ≤ d + 1`, so `dim U_q ≤ d` for all `n`.
11. For `p ∈ V` the closed complement `Z_p` is nowhere dense, so
    `dim Z_p ≤ d` and its coordinate fibres have dimension `≤ d`; as
    `U_q ⊔ Z_q → X_q` is surjective, the image bound gives `dim X_q ≤ d`:
    the dominant case holds over `V` with `n₀ = 0`.
12. Otherwise take a nonzero `g(x, y)` in the kernel with leading coefficient
    `c` (top `y`-degree `s`, then top `x`-degree `t`) and `M` its largest
    `x`-degree; for `n > M` and every `τ` in a residue field where `c ≠ 0`,
    `g(x, τ - x ^ n)` has unique top term `(-1) ^ s c x ^ (t + s n)`.
13. Factor `X_{D(c)} → Y = Spec (R_c[x, y] / (g)) → 𝔸¹_{R_c}`: the fibres of
    the second map are zero-dimensional or empty, those of the first have
    dimension `≤ d`, so the composite fibre inequality bounds the fibres of
    `f_{a ^ n + b}` over `V = D(c)` by `d` for `n > M`.
14. Choose `f ≠ 0` with `D(f) ⊆ V`. If `f` is not a unit, `R / f R` has smaller
    dimension, its `a`-fibres are original fibres, and the induction
    hypothesis gives a threshold `n₁`; in dimension zero `f` is a unit.
15. `N = max(n₀, n₁)` works: a prime `Q` of `R[t]` lies over `D(f)` (fibres
    unchanged by inverting `f`) or over `V(f)` (fibres those of `S / f S`).
    Steps 6–7 and 2–4 then give the threshold for every finite-type `R → S`;
    empty fibres satisfy the bound throughout. -/
theorem power_perturbation_fibre_dimension
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : RingHom.FiniteType φ) (a b : S) (d : ℕ)
    (h : ∀ y : Spec (.of (MvPolynomial (Fin 1) R)),
      topologicalKrullDim ((powerPerturbationMap φ a).fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ y : Spec (.of (MvPolynomial (Fin 1) R)),
        topologicalKrullDim ((powerPerturbationMap φ (a ^ n + b)).fiber y) ≤
          (d : WithBot ℕ∞) := by
  sorry
