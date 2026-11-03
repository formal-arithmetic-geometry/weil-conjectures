/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.TraceWeilComplex.TraceWeilComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.FrobeniusRationalPointFixed
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius

/-! # Trace formula for a Frobenius correspondence

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-the-trace-formula-with-finite-coefficients/sk-thm-tf-coefficient-morphism-formula/
_section.md (blueprint: sk-thm-tf-coefficient-morphism-formula).

The iterates `ψ_m`, the global operator `T_{c_m}(ψ_m)` and the local operators `ψ_{m,x̄}` are
exactly those of sk-d-weil (`Sheaf.Paper.TraceWeilComplex`):
`FrobeniusCorrespondence.operator` and `WeilComplex.stalkEndomorphism` of
`FrobeniusCorrespondence.toWeilComplex`.  As there, the coefficient ring `A` is realized as the
condensed ring `Λ ≅ C(-,A)` (hypothesis `hΛ`, the same finite `ℓ`-primary branch as
sk-lem-tf-compact-trace, `compactTrace_perfect`), and `RΓ_c(X,K) = Ra_{X!}K` is the compact
support of the given operation package of sk-d-six.
* `pointFibre`: `Fib_s`, terminal-point coefficient sections at `s = Spec k`, with values in
  `D(Γ Λ)` (`Γ Λ = A`), as in def-weil-ordinary-compact-cohomology
  (`RΓ_c(Y,K) = Fib_s(Ra_!K)`), so that `RΓ_c(X,K)` and `K_x̄ = Fib_s(x̄^*K)` are complexes
  of `A`-modules;
* `fixedGeometricPoint`: the geometric point `x̄ : s → X` over `s` of `x ∈ X₀(F_{q^m})`
  (`localExtensionPoint`), with `Φ_X^m x̄ = x̄` (`fixedGeometricPoint_fixed`, from
  thm-trf-frobenius-fixed-points);
* `CoefficientMorphismTraceFormula`: both complexes are perfect and the displayed identity of
  categorical traces (`DerivedCategory.perfectCategoricalTrace`, sk-d-trace) holds in `A`;
* `coefficientMorphism_traceFormula`: the theorem, for every `m ≥ 1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.TraceCoefficientMorphismFormula

open WeilConjectures.TraceWeilComplex

variable (D : FiniteFieldDatum.{u})

/-- The power `Φ_X^m` of the model Frobenius has underlying morphism the `m`-fold iterate of
the scalar-extended `q`-power scheme Frobenius.
Source: "Denote by `Φ_X : X → X` the base change of the `q`-power scheme Frobenius of `X₀`"
and "Put `Φ_m = Φ₁^m`" (blueprint: sk-d-weil); def-trf-scheme-frobenius.
Proof: induction on `m`; both sides are identities at `0`, and at `m + 1` both are
`Φ_X^m ≫ Φ_X`, since `(modelFrobenius D X₀).left` is `relativeFrobenius D X₀` by definition. -/
theorem frobeniusPower_modelFrobenius_left (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) :
    (frobeniusPower (modelFrobenius D X₀) m).left = D.schemeFrobeniusIterate X₀ m := by
  induction m with
  | zero =>
    simp only [frobeniusPower, FiniteFieldDatum.schemeFrobeniusIterate, pow_zero,
      Over.id_left, End.one_def]
  | succ m ih =>
    simp only [frobeniusPower, Over.comp_left, ih, FiniteFieldDatum.schemeFrobeniusIterate,
      pow_succ', End.mul_def]
    rfl

/-- The geometric point `x̄ : s → X`, as a point over `s = Spec k`, of a point
`x ∈ X₀(F_{q^m})`: the fibre-product lift `localExtensionPoint` of
`Spec k → Spec F_{q^m} → X₀` and `id_s`.
Source: "`∑_{x ∈ X₀(F_{q^m})} tr_A(ψ_{m,x̄} | K_x̄)`"
(blueprint: sk-thm-tf-coefficient-morphism-formula); def-weil-local-frobenius-trace, `x̄`. -/
def fixedGeometricPoint (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) (hm : 1 ≤ m)
    (x : D.extensionPoints X₀ m hm) :
    TraceOperations.base (Spec (CommRingCat.of D.k)) ⟶ D.geometricFiber X₀ :=
  Over.homMk (localExtensionPoint D X₀ m hm x)
    (by simp [localExtensionPoint, FiniteFieldDatum.geometricFiber])

/-- The geometric point of `x ∈ X₀(F_{q^m})` is fixed by `Φ_X^m`, so the stalk endomorphism
`ψ_{m,x̄}` of sk-d-weil is defined at it.
Source: "For `y ∈ X₀(F_{q^m})` with geometric point `ȳ` one has `Φ^m ȳ = ȳ`"
(blueprint: thm-trf-coefficient-morphism-trace-formula); thm-trf-frobenius-fixed-points.
Proof: on underlying morphisms this is `rationalPoint_schemeFrobenius_fixed`, after
`frobeniusPower_modelFrobenius_left`. -/
theorem fixedGeometricPoint_fixed (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) (hm : 1 ≤ m)
    (x : D.extensionPoints X₀ m hm) :
    fixedGeometricPoint D X₀ m hm x ≫ frobeniusPower (modelFrobenius D X₀) m =
      fixedGeometricPoint D X₀ m hm x := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, frobeniusPower_modelFrobenius_left]
  exact rationalPoint_schemeFrobenius_fixed D X₀ m hm x

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The derived category of `Γ Λ`-modules with morphisms in the module universe, the
Grothendieck-abelian model required by `DerivedCategory.perfectCategoricalTrace` (as in
`local_frobenius_conjugacy` and `ConstantStalkTrace`).
Source: "both sides being categorical traces of endomorphisms of perfect complexes"
(blueprint: sk-thm-tf-coefficient-morphism-formula); def-trf-categorical-trace. -/
abbrev coefficientDerivedCategory :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ Λ)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

attribute [local instance] coefficientDerivedCategory

/-- `Fib_s`: the derived terminal-point coefficient sections at `s = Spec k`, from `D(s,A)` to
the derived category of `Γ Λ`-modules (`Γ Λ = A`). It computes
`RΓ_c(X,K) = Fib_s(Ra_{X!}K)` and the stalk `K_x̄ = Fib_s(x̄^*K)` as complexes of `A`-modules.
Source: "`tr_A(T_{c_m}(ψ_m) | RΓ_c(X_proét, K))`", "`tr_A(ψ_{m,x̄} | K_x̄)`"
(blueprint: sk-thm-tf-coefficient-morphism-formula); def-weil-ordinary-compact-cohomology,
`RΓ_c(Y,K) = Fib_s(Ra_!K)`. -/
abbrev pointFibre :
    TraceOperations.D Λ (Spec (CommRingCat.of D.k)) ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ Λ)) :=
  (CondensedRing.condensedRingCoefficientSections Λ
    (Spec (CommRingCat.of D.k))).rightDerivedFunctor

/-- The trace formula for a Frobenius correspondence `ψ : Φ_X^*K → K` at `m`: the complexes
`RΓ_c(X,K)` and `K_x̄` (`x ∈ X₀(F_{q^m})`) are perfect `A`-complexes, and
`tr_A(T_{c_m}(ψ_m) | RΓ_c(X,K)) = ∑_{x ∈ X₀(F_{q^m})} tr_A(ψ_{m,x̄} | K_x̄)` in `A`,
both sides being categorical traces of endomorphisms of perfect complexes.
Source: "For every `m ≥ 1`, in `A`, `tr_A(T_{c_m}(ψ_m) | RΓ_c(X_proét, K)) =
∑_{x ∈ X₀(F_{q^m})} tr_A(ψ_{m,x̄} | K_x̄)`. Both sides are traces of endomorphisms of perfect
complexes." (blueprint: sk-thm-tf-coefficient-morphism-formula). -/
def CoefficientMorphismTraceFormula (O : TraceOperations.Given Λ (Spec (CommRingCat.of D.k)))
    (P : TraceOperations.GeometricOperations O) (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [HasCompactification (D.geometricFiber X₀).hom]
    (K : ConstantModelConstructibleFiniteTor Λ (D.geometricFiber X₀).left)
    (ψ : FrobeniusCorrespondence D Λ X₀ K) (m : ℕ) (hm : 1 ≤ m) : Prop :=
  ∃ (hc : _root_.DerivedCategory.IsPerfectRingComplex
      ((pointFibre D Λ).obj
        ((TraceOperations.Comparisons.compactlySupported O (D.geometricFiber X₀)).obj K.obj)))
    (hx : ∀ x : D.extensionPoints X₀ m hm, _root_.DerivedCategory.IsPerfectRingComplex
      ((pointFibre D Λ).obj
        ((TraceOperations.star Λ (fixedGeometricPoint D X₀ m hm x).left).obj K.obj))),
    _root_.DerivedCategory.perfectCategoricalTrace
        ((pointFibre D Λ).obj
          ((TraceOperations.Comparisons.compactlySupported O (D.geometricFiber X₀)).obj K.obj)) hc
        ((pointFibre D Λ).map (FrobeniusCorrespondence.operator D O P ψ m)) =
      ∑ᶠ x : D.extensionPoints X₀ m hm,
        _root_.DerivedCategory.perfectCategoricalTrace
          ((pointFibre D Λ).obj
            ((TraceOperations.star Λ (fixedGeometricPoint D X₀ m hm x).left).obj K.obj)) (hx x)
          ((pointFibre D Λ).map
            ((FrobeniusCorrespondence.toWeilComplex D ψ).stalkEndomorphism m
              (fixedGeometricPoint D X₀ m hm x) (fixedGeometricPoint_fixed D X₀ m hm x)))

/-- **Trace formula for a Frobenius correspondence.** Let `X₀/F_q` be separated of finite
type, `X = X₀ ×_{F_q} k`, `A` any finite commutative `ℓ`-primary ring (`ℓ ≠ p`, realized as
`Λ ≅ C(-,A)`), `K ∈ D^b_ctf(X,A)` and `ψ : Φ_X^*K → K` any Frobenius correspondence (any
morphism in `D_ctf(X,A)`, not necessarily invertible). Then for every `m ≥ 1`, in `A`,
`tr_A(T_{c_m}(ψ_m) | RΓ_c(X_proét, K)) = ∑_{x ∈ X₀(F_{q^m})} tr_A(ψ_{m,x̄} | K_x̄)`,
both sides being traces of endomorphisms of perfect complexes.
Source: "Let `X₀/F_q` be separated and of finite type, put `X = X₀ ×_{F_q} k`, let `A` be any
finite commutative `ℓ`-primary ring and `K ∈ D^b_ctf(X,A)`, and let `ψ : Φ_X^*K → K` be any
Frobenius correspondence on `K`. For every `m ≥ 1`, in `A`, ..." and "The iterates `ψ_m`, the
global operators `T_{c_m}(ψ_m)` and the local operators `ψ_{m,x̄}` of a Frobenius
correspondence are those of [sk-d-weil]" (blueprint: sk-thm-tf-coefficient-morphism-formula).
Proof (the node's steps):
1. sk-lem-tf-compact-trace makes `RΓ_c(X,K)` and every geometric stalk perfect; argue at
   once for every finite field, scheme, coefficient ring, correspondence and `m ≥ 1`, so that
   `F_q` may be replaced by `F_{q^m}` on a rational fibre.
2. Finite `S₀`: by sk-i-topology `RΓ_c(S,K) = ⊕_{s̄ ∈ S(k)} K_{s̄}`; by prop-trf-graph-operator
   the operator is the block matrix with blocks `ψ_{m,s̄} : K_{Φ^m(s̄)} → K_{s̄}`; with
   finite-free stalk models (fix-lem-finite-tor-perfect) only diagonal blocks contribute
   (lem-trf-chain-supertrace, prop-trf-trace-formal-laws (1)), and the diagonal points are
   `S₀(F_{q^m})` (thm-trf-frobenius-fixed-points).
3. `A¹_F`: via `j : A¹ ⊂ P¹` (sk-d-lines), extend `ψ_m` to `j_!K`
   (lem-trf-compactification-graph-operator), conjugate to the proper graph operator on
   `RΓ(P¹, j_!K)` (lem-trf-compactification-cohomology), then sk-p-proper and sk-p-frob on the
   finitely many fixed points; the stalk at `∞` is zero.
4. Closed `S₀ ⊂ A¹_F`: `I = 0` is step 3, otherwise `S₀` is finite and step 2 applies.
5. Closed `S₀ ⊂ A^d_F`: induction on `d` along `f₀ : S₀ → A^{d-1}_F`, with `Rf_!K` in `Dctf`
   (sk-thm-sf-ctf-stability) and the induced correspondence, operators and fibres of
   sk-i-relative-frob (2)-(4); the fibres are closed in `A¹_{F_{q^m}}` (step 4).
6. General `S₀`: stratify a finite affine open cover into affine locally closed pieces and add
   traces and point sums by sk-i-global-additivity. -/
theorem coefficientMorphism_traceFormula (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (hΛ : ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A)))
    (O : TraceOperations.Given Λ (Spec (CommRingCat.of D.k)))
    (P : TraceOperations.GeometricOperations O) (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [HasCompactification (D.geometricFiber X₀).hom]
    (K : ConstantModelConstructibleFiniteTor Λ (D.geometricFiber X₀).left)
    (ψ : FrobeniusCorrespondence D Λ X₀ K) (m : ℕ) (hm : 1 ≤ m) :
    CoefficientMorphismTraceFormula D Λ O P X₀ K ψ m hm := by
  sorry

end WeilConjectures.TraceCoefficientMorphismFormula
