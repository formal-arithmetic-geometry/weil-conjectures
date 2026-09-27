/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
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

- `AlgebraicGeometry.ProEtale.GeometricOperations.supportedPairing` (blueprint
  `sk-d-pairing`)
- `AlgebraicGeometry.ProEtale.Correspondence.traceClass` (blueprint `sk-d-trace-class`)
- `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm` (blueprint `sk-d-local-term`)

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.integral_traceClass_eq_trace` (blueprint
  `sk-p-pairing`)
- `AlgebraicGeometry.ProEtale.GeometricOperations.integral_eq_sum_localTerm` (blueprint
  `sk-p-local`)
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}

namespace Correspondence

/-- The support map `c = (c₁, c₂) : C ⟶ Y × X` of a correspondence. -/
noncomputable def toProd (c : Correspondence aX aY K L) : c.supp ⟶ pullback aY aX :=
  pullback.lift c.fst c.snd (c.fst_comp.trans c.snd_comp.symm)

/-- The support map `d̄ = τ d : D ⟶ Y × X` of an opposite correspondence, obtained from
`d = (d₁, d₂) : D ⟶ X × Y` by the exchange of factors. -/
noncomputable def toProdSwap (d : Correspondence aY aX L K) : d.supp ⟶ pullback aY aX :=
  pullback.lift d.snd d.fst (d.snd_comp.trans d.fst_comp.symm)

/-- The intersection support `E(C, D) = C ×_{Y × X} D` of an opposite pair. -/
noncomputable def intersection (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K) : Scheme.{u} :=
  pullback c.toProd d.toProdSwap

/-- The structure morphism `E(C, D) ⟶ s` of the intersection support. -/
noncomputable def intersectionStr (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K) : c.intersection d ⟶ s :=
  pullback.fst c.toProd d.toProdSwap ≫ c.str

/-- The endocorrespondence on `(X, K)` with support `X`, support map the diagonal `Δ_X`,
identity legs, and a prescribed coefficient map `v : K ⟶ K`. For `v = 𝟙 K` this is the
blueprint's *diagonal identity*. The coefficient field is `v` read through the comparisons
`L(𝟙)^* K ≃ K ≃ 𝟙^! K`, which the package does not provide, so it carries a `sorry`. -/
noncomputable def ofEnd (aX : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    Correspondence aX aX K K where
  supp := X
  str := aX
  fst := 𝟙 X
  snd := 𝟙 X
  fst_comp := Category.id_comp aX
  snd_comp := Category.id_comp aX
  coeff := sorry

end Correspondence

namespace GeometricOperations

variable (G : GeometricOperations A s)

/-- Blueprint `sk-d-pairing`: The supported pairing recipe.

For an opposite pair of correspondences, the inverse Kuenneth-Verdier maps turn the
supported classes of `u` and `v` into

`ũ : Rc_! A_C ⟶ L ⊠ D_X K` and `ṽ : Rd̄_! A_D ⟶ D_Y L ⊠ K`

on `Z = Y × X`. The projection formula and `!`-base change identify `Re_! A_E` with
`Rc_! A_C ⊗ᴸ Rd̄_! A_D` for `e : E(C, D) ⟶ Z`; composing with `ũ ⊗ ṽ`, the two Verdier
evaluations and `ω_Y ⊠ ω_X ≃ ω_Z`, and taking the exceptional adjoint, gives the
Lefschetz-Verdier pairing, a Borel-Moore section `⟨u, v⟩_LV : A_E ⟶ ω_E`.

The composite uses the Kuenneth-Verdier comparison, which belongs to the six operations
chapter and is not available here, so the definition is stated and left with a `sorry`
body; its type is the Borel-Moore section it produces. -/
noncomputable def supportedPairing (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K) :
    𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology (c.intersection d)) A)) ⟶
      G.dualizing (c.intersectionStr d) :=
  sorry

/-- Blueprint `sk-d-trace-class`: Diagonal trace class.

The intersection of an endocorrespondence `(C, c, u)` on `(X, K)` with the diagonal
identity is the fixed scheme `F = Fix(c)`, and its *trace class* `Tr_c(u) : A_F ⟶ ω_F` is
the Verdier trace class: the mate of `u` followed by the trace map of external duality. It
agrees on the nose with the supported pairing `⟨u, 𝟙 K⟩_LV` against the diagonal identity.

This is a Borel-Moore section on the fixed scheme; integration is a separate operation.
The construction is left with a `sorry` body, its type carrying the content. -/
noncomputable def traceClass (c : Correspondence aX aX K K) :
    𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology c.fix) A)) ⟶ G.dualizing c.fixStr :=
  sorry

/-- Blueprint `sk-d-local-term`: Local terms.

Let `α : A_E ⟶ ω_E` be a Borel-Moore section on a geometric scheme `E` — in the blueprint
either the pairing `⟨u, v⟩_LV` of an opposite pair or the trace class `Tr_c(u)` of an
endocorrespondence — and let `j_B : B ⟶ E` be open and closed with `B` proper over `s`.
Restricting `α` along `j_B`, using open purity and dualizing composition to identify
`j_B^* A_E ≃ A_B` and `j_B^* ω_E ≃ ω_B`, and integrating over `B` gives the local term
`LT_B(α) ∈ A`. The restricted section is defined even when `B` is not proper; properness
is what makes the scalar integral defined.

The ambient support `E` need not be proper. At a Frobenius fixed point, `LT_x̄` means the
local term on its reduced clopen point component. The definition is left with a `sorry`
body. -/
noncomputable def localTerm {E B : Scheme.{u}} (aE : E ⟶ s) (jB : B ⟶ E)
    [IsOpenImmersion jB] (_hB : IsClosed (Set.range jB.base))
    [HasCompactification (jB ≫ aE)] [IsProper (jB ≫ aE)]
    (_α : 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology E) A)) ⟶ G.dualizing aE) :
    End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))) :=
  sorry

/-- Blueprint `sk-p-pairing`: Pairing and its point normalization.

For a perfect `A`-complex `P` on the base point `s` and an endomorphism `v : P ⟶ P`,
regarded as an endocorrespondence with support `s` and identity legs, the supported
pairing against the diagonal identity is the ordinary categorical trace:
`⟨v, 𝟙 P⟩_LV = tr_A(v ∣ P)`.

Perfectness is rendered as dualizability, `HasRightDual P`, and `tr_A` is
`CategoryTheory.MonoidalCategory.trace`, taken in `D(s, A)`, whose unit endomorphism ring
is `A`. The symmetry of `D(s, A)` is an instance hypothesis: this project installs a
monoidal structure on a derived category but not yet a braiding.

The same adjunction calculation identifies the
trace class of `sk-d-trace-class` on an arbitrary `X`, which is what the proper
compatibility theorem uses. -/
theorem integral_traceClass_eq_trace
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))]
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology s) A)) [HasRightDual P] (v : P ⟶ P)
    [HasCompactification (Correspondence.ofEnd (𝟙 s) P v).fixStr]
    [IsProper (Correspondence.ofEnd (𝟙 s) P v).fixStr] :
    G.integral (Correspondence.ofEnd (𝟙 s) P v).fixStr
        (G.traceClass (Correspondence.ofEnd (𝟙 s) P v)) =
      MonoidalCategory.trace v :=
  sorry

/-- Blueprint `sk-p-local`: Decomposition into local terms.

If the intersection support of an opposite pair is a finite disjoint union
`E = ∐_{β ∈ B} β` of clopen subschemes, each proper over `s`, then the integral of any
Borel-Moore section on `E` is the sum of its local terms,
`∫_E α = ∑_β LT_β(α)`. In particular this applies to the Lefschetz-Verdier pairing
`α = ⟨u, v⟩_LV`; the empty support gives the empty sum `0`. -/
theorem integral_eq_sum_localTerm {E : Scheme.{u}} (aE : E ⟶ s) [HasCompactification aE]
    [IsProper aE] {ι : Type u} [Fintype ι] {B : ι → Scheme.{u}} (j : ∀ i, B i ⟶ E)
    [∀ i, IsOpenImmersion (j i)] [∀ i, HasCompactification (j i ≫ aE)]
    [∀ i, IsProper (j i ≫ aE)] (hclosed : ∀ i, IsClosed (Set.range (j i).base))
    (_hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).base) (Set.range (j i').base))
    (_hcover : ⋃ i, Set.range (j i).base = Set.univ)
    (α : 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology E) A)) ⟶ G.dualizing aE) :
    G.integral aE α = ∑ i, G.localTerm aE (j i) (hclosed i) α :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
