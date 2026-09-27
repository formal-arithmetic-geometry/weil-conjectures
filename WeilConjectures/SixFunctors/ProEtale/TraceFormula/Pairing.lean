/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence

/-!
# The Lefschetz-Verdier pairing, trace classes and local terms

For an opposite pair of correspondences `(C, c, u)` from `(X, K)` to `(Y, L)` and
`(D, d, v)` back, the Kuenneth-Verdier comparison turns the two coefficient maps into
sections over the intersection `E(C, D) = C ×_{Y × X} D`, and their contraction is the
Lefschetz-Verdier pairing `⟨u, v⟩_LV : A_E ⟶ ω_E`, a Borel-Moore section. Pairing against
the diagonal identity gives the *trace class* of an endocorrespondence, a Borel-Moore
section on the fixed scheme, and integrating over a clopen piece gives a *local term*.

## Main definitions

- `AlgebraicGeometry.ProEtale.GeometricOperations.supportedPairing`: the Lefschetz-Verdier
  pairing `⟨u, v⟩_LV`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.traceClass`: the trace class `Tr_c(u)`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm`: the local term `LT_B(α)`.

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.integral_traceClass_eq_trace`: the point
  normalisation of the pairing.
- `AlgebraicGeometry.ProEtale.GeometricOperations.integral_eq_sum_localTerm`: the
  decomposition of an integral into local terms.

## Implementation notes

`supportedPairing`, `traceClass` and `localTerm` are composites of the Kuenneth-Verdier
comparison and the other maps that the package
`AlgebraicGeometry.ProEtale.GeometricOperations` only postulates, so this project cannot
build them. They are `opaque` for the reason explained in
`WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence`: their types carry the
content, no `sorryAx` enters, and they stay dependent on all their arguments.

Perfectness is rendered as dualizability, `HasRightDual`, and `tr_A` is
`CategoryTheory.MonoidalCategory.trace`, taken in `D(s, A)`, whose unit endomorphism ring
is the coefficient ring. Its braiding is an instance hypothesis: this project installs a
monoidal structure on a derived category but not yet a braiding.
-/

@[expose] public section

universe u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}

namespace GeometricOperations

variable (G : GeometricOperations A s)

/-- The *Lefschetz-Verdier pairing* of an opposite pair of correspondences: the inverse
Kuenneth-Verdier maps turn the supported classes of `u` and `v` into

`ũ : Rc_! A_C ⟶ L ⊠ D_X K` and `ṽ : Rd̄_! A_D ⟶ D_Y L ⊠ K`

on `Z = Y × X`; the projection formula and `!`-base change identify `Re_! A_E` with
`Rc_! A_C ⊗ᴸ Rd̄_! A_D` for `e : E(C, D) ⟶ Z`, and composing with `ũ ⊗ ṽ`, the two Verdier
evaluations and `ω_Y ⊠ ω_X ≃ ω_Z` and taking the exceptional adjoint gives a Borel-Moore
section `⟨u, v⟩_LV : A_E ⟶ ω_E` (blueprint: `sk-d-pairing`). -/
noncomputable opaque supportedPairing (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K) : G.borelMooreSections (c.intersectionStr d) := 0

/-- The *trace class* `Tr_c(u) : A_F ⟶ ω_F` of an endocorrespondence `(C, c, u)` on
`(X, K)`, a Borel-Moore section on the fixed scheme `F = Fix(c)`: the mate of `u` followed
by the trace map of external duality. It agrees on the nose with the supported pairing
`⟨u, 𝟙 K⟩_LV` against the diagonal identity, the intersection of `c` with the diagonal
identity being `F` (blueprint: `sk-d-trace-class`). -/
noncomputable opaque traceClass (c : Correspondence aX aX K K) :
    G.borelMooreSections c.fixStr := 0

/-- The *local term* `LT_B(α) ∈ A` of a Borel-Moore section `α : A_E ⟶ ω_E` along a clopen
immersion `j_B : B ⟶ E` with `B` proper over `s`: restrict `α` along `j_B`, identify
`j_B^* A_E ≃ A_B` and `j_B^* ω_E ≃ ω_B` by open purity and dualizing composition, and
integrate over `B`. The ambient support `E` need not be proper; at a Frobenius fixed point
`LT_x̄` means the local term on its reduced clopen point component
(blueprint: `sk-d-local-term`). -/
noncomputable opaque localTerm {E B : Scheme.{u}} (aE : E ⟶ s) (jB : B ⟶ E)
    [IsOpenImmersion jB] (hB : IsClosed (Set.range jB.base))
    [HasCompactification (jB ≫ aE)] [IsProper (jB ≫ aE)] (α : G.borelMooreSections aE) :
    End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))) := 0

/-- Point normalization of the pairing: for a perfect `A`-complex `P` on the base point `s`
and an endomorphism `v : P ⟶ P`, regarded as an endocorrespondence with support `s` and
identity legs, the supported pairing against the diagonal identity is the ordinary
categorical trace, `⟨v, 𝟙 P⟩_LV = tr_A(v ∣ P)`.

The same adjunction calculation identifies the trace class of an endocorrespondence on an
arbitrary `X`, which is what the proper compatibility theorem uses
(blueprint: `sk-p-pairing`). -/
theorem integral_traceClass_eq_trace
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))]
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology s) A)) [HasRightDual P] (v : P ⟶ P) :
    G.integral (Correspondence.ofEnd (𝟙 s) P v).fixStr
        (G.traceClass (Correspondence.ofEnd (𝟙 s) P v)) =
      MonoidalCategory.trace v :=
  sorry

/-- Decomposition into local terms: if the support of a Borel-Moore section is a finite
disjoint union `E = ∐_{β ∈ B} β` of clopen subschemes, each proper over `s`, then the
integral of the section is the sum of its local terms, `∫_E α = ∑_β LT_β(α)`. In particular
this applies to the Lefschetz-Verdier pairing `α = ⟨u, v⟩_LV`; the empty support gives the
empty sum `0` (blueprint: `sk-p-local`). -/
theorem integral_eq_sum_localTerm {E : Scheme.{u}} (aE : E ⟶ s) [HasCompactification aE]
    [IsProper aE] {ι : Type u} [Fintype ι] {B : ι → Scheme.{u}} (j : ∀ i, B i ⟶ E)
    [∀ i, IsOpenImmersion (j i)] [∀ i, HasCompactification (j i ≫ aE)]
    [∀ i, IsProper (j i ≫ aE)] (hclosed : ∀ i, IsClosed (Set.range (j i).base))
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).base) (Set.range (j i').base))
    (hcover : ⋃ i, Set.range (j i).base = Set.univ)
    (α : G.borelMooreSections aE) :
    G.integral aE α = ∑ i, G.localTerm aE (j i) (hclosed i) α :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
