/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule
public import WeilConjectures.ZetaSeries

/-!
# The provisional interface of `ℓ`-adic Weil sheaves

The blueprint develops `ℓ`-adic Weil sheaves, their weights, their Fourier transform and the
six operations in the blocks `sec-purity-real-sheaves`, `sec-fourier-transform`,
`sec-six-functors`, `sec-trace-formula` and `sec-poincare-duality`. None of that is available
yet: the repository has the constructible bounded derived category of étale sheaves
(`AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible`) and the derived complete
categories with `𝒪_E`- and `E`-coefficients (`DerivedCategoryDerivedCompleteRational`), but no
Frobenius structure on them, hence no notion of weight.

This file collects the notions the blocks downstream of that formalism *use* but do not own, as
opaque declarations with `sorry` bodies, each carrying a `TODO(unify)` comment naming the
blueprint node that owns it. They are placeholders to be replaced, not definitions: nothing is
proved about them anywhere. They are gathered here, rather than inside the directory of the
first block that needs them, so that there is one copy to replace and the blocks that share
them share one vocabulary.

What is *not* provisional is the weight formalism they are phrased against:
`FrobeniusModule` (`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule`) is an honest
finite-dimensional vector space with an automorphism, and purity and upper weight bounds are
honest conditions on the eigenvalues of that automorphism under an embedding `ι : ℚ̄_ℓ →+* ℂ`.

## Conventions

Throughout, `k₀` is a finite field with `q = Nat.card k₀` elements and `l` is a prime different
from the characteristic of `k₀`, carried as `[Fact (ringChar k₀ ≠ l)]`; both hypotheses are
arguments of `AlgebraicGeometry.WeilSheaf` itself, so every statement about Weil sheaves
carries them. The embedding `ι : ℚ̄_ℓ →+* ℂ` is an explicit argument rather than a choice: no
such embedding is constructed anywhere in mathlib. A lisse Weil sheaf is punctually pure of
weight `w` if every eigenvalue `α` of the local Frobenius at a closed point `x` satisfies
`|ι α| = q_x ^ (w / 2)`, with `q_x = q ^ deg x` the residue cardinality
`AlgebraicGeometry.Scheme.Hom.residueCard`; replacing equality by `≤` gives
`AlgebraicGeometry.WeilSheaf.HasWeightsAtMost`. Weights of cohomology are taken relative to `q`
instead, which `FrobeniusModule.IsPureOfWeightOver` names.

## Main declarations

- `AlgebraicGeometry.WeilSheaf` and `AlgebraicGeometry.WeilComplex`: the abelian category of
  constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme and its bounded derived category.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight`,
  `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost` and `AlgebraicGeometry.WeilSheaf.IsReal`: the
  weight conditions and the reality condition.
- `AlgebraicGeometry.WeilSheaf.higherLowerShriek` and
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`: the higher direct images with compact
  support `Rʳf₀!` and the total derived one `Rf₀!`.
- `AlgebraicGeometry.WeilSheaf.directImage`, `AlgebraicGeometry.WeilSheaf.extensionByZero` and
  `AlgebraicGeometry.WeilSheaf.extensionByZeroToDirectImage`: the two extensions along an open
  immersion and the canonical map between them.
- `AlgebraicGeometry.artinSchreier` and `AlgebraicGeometry.fourierTransform`: the
  Artin–Schreier sheaves and the Fourier–Deligne transform of the affine line.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

section Sheaves

-- The binders of the next two declarations are spelled out rather than taken from a `variable`
-- block: their bodies are placeholders, so `l` and the two `Fact` hypotheses do not occur in
-- the type and would not be included.

-- TODO(unify): sk-d-real-weil
/-- The abelian category of constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme `X`.
Placeholder for the category built in the blueprint block `sec-purity-real-sheaves`; see the
module docstring. -/
def WeilSheaf (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    Type u := sorry

-- TODO(unify): sk-d-real-weil
/-- The bounded derived category of constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme `X`.
Placeholder; see the module docstring. -/
def WeilComplex (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    Type u := sorry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-d-real-weil
noncomputable instance : Category.{u} (WeilSheaf k₀ l X) := sorry

-- TODO(unify): sk-d-real-weil
noncomputable instance : Abelian (WeilSheaf k₀ l X) := sorry

-- TODO(unify): sk-d-real-weil
noncomputable instance : Category.{u} (WeilComplex k₀ l X) := sorry

-- TODO(unify): sk-d-real-weil
noncomputable instance : Preadditive (WeilComplex k₀ l X) := sorry

-- TODO(unify): sk-d-real-weil
noncomputable instance : HasShift (WeilComplex k₀ l X) ℤ := sorry

namespace WeilSheaf

-- TODO(unify): sk-d-real-weil
/-- A Weil sheaf, viewed as a Weil complex concentrated in degree zero. -/
noncomputable def toComplex : WeilSheaf k₀ l X ⥤ WeilComplex k₀ l X := sorry

-- TODO(unify): sk-d-real-weil
instance : (toComplex (k₀ := k₀) (l := l) (X := X)).Additive := sorry

-- TODO(unify): sk-d-real-weil
/-- `F` is lisse, i.e. finite locally constant for the étale topology. -/
def IsLisse (F : WeilSheaf k₀ l X) : Prop := sorry

-- TODO(unify): sk-d-real-weil
/-- The support of a Weil sheaf: the set of points with nonzero stalk. -/
def support (F : WeilSheaf k₀ l X) : Set X := sorry

-- TODO(unify): sk-d-real-weil
/-- The geometric stalk of `F` at a closed point `x`, with its local geometric Frobenius
`Fₓ`, which acts on the stalk at a geometric point above `x`. -/
noncomputable def stalk (F : WeilSheaf k₀ l X) (x : X) :
    FrobeniusModule.{u, 0} (PadicAlgCl l) := sorry

-- TODO(unify): sk-def-trace
/-- The trace function `t_{F,n}` of a Weil sheaf: the trace of the Frobenius relative to
`𝔽_{qⁿ}` on the stalk at an `𝔽_{qⁿ}`-rational point. -/
noncomputable def traceFunction (F : WeilSheaf k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    PadicAlgCl l := sorry

/-- `F` is punctually `ι`-pure of weight `w`: at every closed point `x`, every eigenvalue `α`
of the local Frobenius `Fₓ` satisfies `|ι α| = q_x ^ (w / 2)`, with `q_x` the residue
cardinality at `x`. -/
def IsPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) →
    (F.stalk x).IsPureOfWeight ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x) w

/-- `F` has weights at most `w`: at every closed point `x`, every eigenvalue `α` of the local
Frobenius `Fₓ` satisfies `|ι α| ≤ q_x ^ (w / 2)`. -/
def HasWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) →
    (F.stalk x).HasWeightsAtMost ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x) w

/-- A punctually pure sheaf has weights at most its weight. -/
theorem IsPunctuallyPureOfWeight.hasWeightsAtMost {ι : PadicAlgCl l →+* ℂ}
    {F : WeilSheaf k₀ l X} {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) :
    F.HasWeightsAtMost ι w :=
  fun x hx ↦ (h x hx).hasWeightsAtMost

-- TODO(unify): sk-d-real-weights
/-- `F` is `ι`-*real* if the realization under `ι` of the local Frobenius characteristic
polynomial `P_x(F, T) = det(1 - T Fₓ | F_x̄)` has real coefficients at every closed point `x`;
equivalently, if every complex local eigenvalue multiset is stable under complex conjugation.
Placeholder; see the module docstring. -/
def IsReal (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : Prop := sorry

-- TODO(unify): sk-d-real-operations
/-- The dual `F ↦ F ∨` of a lisse Weil sheaf. -/
noncomputable def dual (F : WeilSheaf k₀ l X) : WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-d-real-operations
/-- The coinvariants `V_{π₁(X ⊗ k)}` of the generic geometric representation of a lisse Weil
sheaf, with the Frobenius induced from the Weil structure: the maximal geometrically constant
quotient of `F`. -/
noncomputable def geometricCoinvariants (F : WeilSheaf k₀ l X) :
    FrobeniusModule.{u, 0} (PadicAlgCl l) := sorry

end WeilSheaf

namespace WeilComplex

-- TODO(unify): sk-d-real-weil
/-- The `a`-th ordinary cohomology sheaf `𝓗ᵃK` of a Weil complex. -/
noncomputable def homologySheaf (a : ℤ) :
    WeilComplex k₀ l X ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-d-real-weil
instance (a : ℤ) : (homologySheaf (k₀ := k₀) (l := l) (X := X) a).Additive := sorry

-- TODO(unify): sk-thm-sf-global-duality
/-- The compactly supported cohomology `H_c^r(X ⊗ k, K)` of a Weil complex, with its geometric
Frobenius. -/
noncomputable def compactlySupportedCohomology (r : ℤ) (K : WeilComplex k₀ l X) :
    FrobeniusModule.{u, 0} (PadicAlgCl l) := sorry

end WeilComplex

/-- The compactly supported cohomology `H_c^r(X ⊗ k, F)` of a Weil sheaf. -/
noncomputable def WeilSheaf.compactlySupportedCohomology (r : ℤ) (F : WeilSheaf k₀ l X) :
    FrobeniusModule.{u, 0} (PadicAlgCl l) :=
  (WeilSheaf.toComplex.obj F).compactlySupportedCohomology r

end Sheaves

/-! ### Direct images with compact support

The repository already has the étale compact-support formalism: `Rf_!` is
`AlgebraicGeometry.Etale.rightDerivedLowerShriek` and `H_c` is
`AlgebraicGeometry.Etale.compactlySupportedCohomology`, both available for every separated
quasi-compact morphism locally of finite type, the `HasCompactification` hypothesis being
discharged by the Nagata instance. What is missing is their Frobenius-equivariant form on Weil
sheaves and Weil complexes, which is what the two placeholders below stand for. Their
hypotheses are exactly the triple that makes the étale `Rf_!` available.
-/

section LowerShriek

-- The binders of the next two declarations are spelled out rather than taken from a `variable`
-- block: their bodies are placeholders, so `l` and the two `Fact` hypotheses do not occur in the
-- type and would not be included.

-- TODO(unify): sk-thm-sf-package
/-- The `r`-th higher direct image with compact support `Rʳf₀!` along a separated quasi-compact
morphism of `k₀`-schemes locally of finite type. Placeholder; see the module docstring. -/
noncomputable def WeilSheaf.higherLowerShriek (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ)
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (r : ℕ) : WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y := sorry

-- TODO(unify): sk-thm-sf-package
/-- The total derived direct image with compact support `Rf₀!` along a separated quasi-compact
morphism of `k₀`-schemes locally of finite type. Placeholder; see the module docstring. -/
noncomputable def WeilComplex.derivedLowerShriek (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ)
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] : WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y := sorry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-thm-sf-package
instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (r : ℕ) :
    (WeilSheaf.higherLowerShriek k₀ l f r).Additive := sorry

-- TODO(unify): sk-thm-sf-package
instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    (WeilComplex.derivedLowerShriek k₀ l f).Additive := sorry

end LowerShriek

/-! ### Direct images along an open immersion -/

section OpenImmersion

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

-- TODO(unify): sk-d-real-boundary
/-- The *ordinary* sheaf direct image `j_*` along an open immersion `j`; its stalks at the
missing points are the inertia invariants. -/
noncomputable def directImage (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-d-real-boundary
/-- The higher direct image `Rⁱj_*` along an open immersion `j`. -/
noncomputable def higherDirectImage (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (i : ℕ) :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
/-- Extension by zero `j_!` along an open immersion `j`. -/
noncomputable def extensionByZero (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
instance (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    (directImage (k₀ := k₀) (l := l) j).Additive := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
instance (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    (extensionByZero (k₀ := k₀) (l := l) j).Additive := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
/--
The canonical map `j_! ⟶ j_*`, whose cokernel is the boundary sheaf `B` supported on the
complement of `U`:

```
  j_! F ──────▶ j_* F ──────▶ B ──────▶ 0
    │             │
    │ j_! α       │ j_* α
    ▼             ▼
  j_! G ──────▶ j_* G
```
-/
noncomputable def extensionByZeroToDirectImage (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    extensionByZero (k₀ := k₀) (l := l) j ⟶ directImage j := sorry

end WeilSheaf

end OpenImmersion

/-! ### Artin–Schreier sheaves and the Fourier transform -/

section Fourier

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

-- TODO(unify): sk-def-as
/-- The Artin–Schreier sheaf `ℒ_{ψ(a x)}` on the affine line: the `ψ`-isotypic part of the
pushforward of the constant sheaf along the Artin–Schreier cover `u^q - u = a x`, which is
Galois over the line with group `k₀`, so that its isotypic components are indexed by the
additive characters of `k₀`. It is lisse of rank one and of weight zero. -/
noncomputable def artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    WeilSheaf k₀ l (affineLine k₀) := sorry

-- TODO(unify): sk-def-ft
/-- The Fourier–Deligne transform `FT_ψ` from the bounded derived category of Weil complexes
on the affine line to that of the dual affine line, with Laumon's shift by the relative
dimension one. -/
noncomputable def fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilComplex k₀ l (affineLine k₀) ⥤ WeilComplex k₀ l (affineLine k₀) := sorry

-- TODO(unify): sk-def-ft
instance (ψ : AddChar k₀ (PadicAlgCl l)) : (fourierTransform (l := l) ψ).Additive := sorry

-- TODO(unify): sk-thm-inversion
/-- Fourier inversion: for a nontrivial additive character the Fourier–Deligne transform is an
equivalence of the bounded derived categories of the two dual lines. Owned by the blueprint
block `sec-fourier-transform`; see the module docstring. -/
theorem isEquivalence_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    (fourierTransform (l := l) ψ).IsEquivalence := sorry

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-d-real-operations
/-- `F.HasLinearArtinSchreierConstituent ψ a` says that the restriction to `U` of the geometric
linear Artin–Schreier sheaf `ℒ_{ψ(a x)}`, for `a` in the algebraic closure of `k₀`, is an
irreducible constituent of the pullback of `F` to `U ⊗_{k₀} k`. The geometric sheaf is defined
over the finite subextension `k₀(a)`, where it is `AlgebraicGeometry.artinSchreier` for the
character `ψ ∘ Tr`; only its pullback to the geometric affine line is used here. -/
def WeilSheaf.HasLinearArtinSchreierConstituent (F : WeilSheaf k₀ l U)
    (ψ : AddChar k₀ (PadicAlgCl l)) (a : AlgebraicClosure k₀) : Prop := sorry

end Fourier

end AlgebraicGeometry
