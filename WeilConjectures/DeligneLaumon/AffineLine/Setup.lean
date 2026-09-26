/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.ZetaSeries
public import Weil.Definitions

/-!
# Weil sheaves on the affine line: conventions

This file fixes the conventions in which the Deligne–Laumon affine-line estimate
(`WeilConjectures.DeligneLaumon.AffineLine.Upper`) and its auxiliary statements are phrased,
and provides the interface of `ℓ`-adic Weil sheaves that they are phrased against.

## The interface, and why it is provisional

The blueprint develops `ℓ`-adic Weil sheaves, their weights, their Fourier transform and the
six operations in the blocks `sec-purity-real-sheaves`, `sec-fourier-transform`,
`sec-six-functors` and `sec-poincare-duality`. None of that is available yet: the repository
has the constructible bounded derived category of étale sheaves
(`AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible`) and the derived complete
categories with `𝒪_E`- and `E`-coefficients
(`DerivedCategoryDerivedCompleteRational`), but no Frobenius structure on them, hence no
notion of weight.

So the objects that the affine-line block *uses* but does not own are introduced here as
opaque declarations with `sorry` bodies, each carrying a `TODO(unify)` comment naming the
blueprint node that owns it. They are placeholders to be replaced, not definitions: nothing
in this directory proves anything about them. The declarations that the affine-line block
*does* own — `AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant`,
`AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity`, and the perverse subcategories of
`WeilConjectures.DeligneLaumon.AffineLine.Perverse` — carry a blueprint docstring instead.

What *is* genuine mathematics here is the weight formalism: a `Frobenius module` is an honest
finite-dimensional `ℚ̄_ℓ`-vector space with an automorphism, and purity and upper weight
bounds for it are honest conditions on the eigenvalues of that automorphism. All the weight
statements of the block are conditions of this kind.

## Conventions, following `sk-d-dl-a1-setup`

Throughout, `k₀` is a finite field with `q = Nat.card k₀` elements, `l` is a prime different
from the characteristic of `k₀`, and `ι : ℚ̄_ℓ →+* ℂ` is a fixed embedding, carried as an
explicit argument rather than chosen: no such embedding is constructed anywhere in mathlib.
The affine line `A₀ = 𝔸¹_{k₀}` is `AlgebraicGeometry.affineLine k₀`, and the dual affine line
is another copy of it. A lisse Weil sheaf is pure of weight `w` if every eigenvalue `α` of the
local Frobenius at a closed point `x` satisfies `|ι α| = q_x ^ (w / 2)`, with `q_x = q ^ deg x`;
replacing equality by `≤` gives the upper bound
`AlgebraicGeometry.WeilSheaf.HasWeightsAtMost`. The Tate twist `(-1)` raises weights by two.

## Main declarations

- `AlgebraicGeometry.FrobeniusModule`: a finite-dimensional `ℚ̄_ℓ`-vector space with a
  geometric Frobenius automorphism, with `FrobeniusModule.IsPureOfWeight` and
  `FrobeniusModule.HasWeightsAtMost`.
- `AlgebraicGeometry.WeilSheaf` and `AlgebraicGeometry.WeilComplex`: the abelian category of
  constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme and its bounded derived category.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight`,
  `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost`: the weight conditions.
- `AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant`,
  `AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity`: the two conditions on a lisse Weil
  sheaf on a dense open of the affine line that `sk-d-dl-a1-setup` introduces.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-! ### Frobenius modules and their weights -/

/-- A *Frobenius module* over `ℚ̄_ℓ`: a finite-dimensional `ℚ̄_ℓ`-vector space together with an
automorphism, the geometric Frobenius. This is the target of every cohomological construction
below: a stalk with its local Frobenius, or a compactly supported cohomology group with the
global geometric Frobenius. -/
structure FrobeniusModule (l : ℕ) [Fact l.Prime] : Type (u + 1) where
  /-- The underlying `ℚ̄_ℓ`-vector space. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module (PadicAlgCl l) carrier]
  [finiteDimensional : FiniteDimensional (PadicAlgCl l) carrier]
  /-- The geometric Frobenius automorphism. -/
  frobenius : carrier ≃ₗ[PadicAlgCl l] carrier

namespace FrobeniusModule

attribute [instance] addCommGroup module finiteDimensional

variable {l : ℕ} [Fact l.Prime]

/-- The geometric Frobenius of a Frobenius module, as an endomorphism. -/
noncomputable def frobeniusEnd (M : FrobeniusModule.{u} l) :
    Module.End (PadicAlgCl l) M.carrier :=
  M.frobenius.toLinearMap

/-- `M` is *`ι`-pure of weight `w` relative to `qₓ`* if every eigenvalue `α` of its geometric
Frobenius satisfies `|ι α| = qₓ ^ (w / 2)`. -/
def IsPureOfWeight (ι : PadicAlgCl l →+* ℂ) (qx : ℕ) (M : FrobeniusModule.{u} l) (w : ℝ) :
    Prop :=
  ∀ α : PadicAlgCl l, M.frobeniusEnd.HasEigenvalue α → ‖ι α‖ = (qx : ℝ) ^ (w / 2)

/-- `M` *has weights at most `w` relative to `qₓ`* if every eigenvalue `α` of its geometric
Frobenius satisfies `|ι α| ≤ qₓ ^ (w / 2)`. -/
def HasWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (qx : ℕ) (M : FrobeniusModule.{u} l) (w : ℝ) :
    Prop :=
  ∀ α : PadicAlgCl l, M.frobeniusEnd.HasEigenvalue α → ‖ι α‖ ≤ (qx : ℝ) ^ (w / 2)

theorem HasWeightsAtMost.of_isPureOfWeight {ι : PadicAlgCl l →+* ℂ} {qx : ℕ}
    {M : FrobeniusModule.{u} l} {w : ℝ} (h : M.IsPureOfWeight ι qx w) :
    M.HasWeightsAtMost ι qx w :=
  fun α hα ↦ (h α hα).le

end FrobeniusModule

/-! ### The affine line -/

/-- The affine line `𝔸¹_{k₀}` over a commutative ring `k₀`, the one-dimensional affine space.
The *dual* affine line `A'₀` of the Fourier transform is another copy of it. -/
noncomputable abbrev affineLine (k₀ : Type u) [CommRing k₀] : Scheme.{u} :=
  𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀))

/-! ### Weil sheaves and Weil complexes -/

section WeilSheaf

variable (k₀ : Type u) [Field k₀] (l : ℕ) [Fact l.Prime]

-- TODO(unify): sk-d-real-weil
/-- The abelian category of constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme `X`.
Placeholder for the category built in the blueprint block `sec-purity-real-sheaves`; see the
module docstring. -/
def WeilSheaf (k₀ : Type u) [Field k₀] (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] : Type u := sorry

-- TODO(unify): sk-d-real-weil
/-- The bounded derived category of constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme `X`.
Placeholder; see the module docstring. -/
def WeilComplex (k₀ : Type u) [Field k₀] (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] : Type u := sorry

variable {k₀ l}
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

-- TODO(unify): sk-d-real-weil
/-- A Weil sheaf, viewed as a Weil complex concentrated in degree zero. -/
noncomputable def WeilSheaf.toComplex : WeilSheaf k₀ l X ⥤ WeilComplex k₀ l X := sorry

-- TODO(unify): sk-d-real-weil
/-- The `a`-th ordinary cohomology sheaf `𝓗ᵃK` of a Weil complex. -/
noncomputable def WeilComplex.homologySheaf (a : ℤ) :
    WeilComplex k₀ l X ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-d-real-weil
noncomputable instance : (WeilSheaf.toComplex (k₀ := k₀) (l := l) (X := X)).Additive := sorry

-- TODO(unify): sk-d-real-weil
noncomputable instance (a : ℤ) :
    (WeilComplex.homologySheaf (k₀ := k₀) (l := l) (X := X) a).Additive := sorry

namespace WeilSheaf

-- TODO(unify): sk-d-real-weil
/-- `F` is lisse, i.e. finite locally constant for the étale topology. -/
def IsLisse (F : WeilSheaf k₀ l X) : Prop := sorry

-- TODO(unify): sk-d-real-weil
/-- The rank of a lisse Weil sheaf. -/
noncomputable def rank (F : WeilSheaf k₀ l X) : ℕ := sorry

-- TODO(unify): sk-d-real-weil
/-- The support of a Weil sheaf: the set of points with nonzero stalk. -/
def support (F : WeilSheaf k₀ l X) : Set X := sorry

-- TODO(unify): sk-d-real-weil
/-- The geometric stalk of `F` at a closed point `x`, with its local geometric Frobenius
`Fₓ`, which acts on the stalk at a geometric point above `x`. -/
noncomputable def stalk (F : WeilSheaf k₀ l X) (x : X) : FrobeniusModule.{u} l := sorry

-- TODO(unify): sk-def-trace
/-- The trace function `t_{F,n}` of a Weil sheaf: the trace of the Frobenius relative to
`𝔽_{qⁿ}` on the stalk at an `𝔽_{qⁿ}`-rational point. -/
noncomputable def traceFunction (F : WeilSheaf k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    PadicAlgCl l := sorry

/-- The local cardinality `q_x = q ^ [κ(x) : k₀]` at a point `x` of a `k₀`-scheme. -/
noncomputable def localCard (k₀ : Type u) [Field k₀] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (x : X) : ℕ :=
  Nat.card k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x

/-- `F` is punctually `ι`-pure of weight `w`: at every closed point `x`, every eigenvalue `α`
of the local Frobenius `Fₓ` satisfies `|ι α| = q_x ^ (w / 2)`. -/
def IsPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → (F.stalk x).IsPureOfWeight ι (localCard k₀ X x) w

/-- `F` has weights at most `w`: at every closed point `x`, every eigenvalue `α` of the local
Frobenius `Fₓ` satisfies `|ι α| ≤ q_x ^ (w / 2)`. -/
def HasWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → (F.stalk x).HasWeightsAtMost ι (localCard k₀ X x) w

-- TODO(unify): sk-d-real-operations
/-- The dual `F ↦ F ∨` of a lisse Weil sheaf. -/
noncomputable def dual (F : WeilSheaf k₀ l X) : WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-d-real-operations
/-- The Tate twist `F(n)`, tensoring with the constant Weil line on which the geometric
Frobenius acts by `q ^ (-n)`. -/
noncomputable def tateTwist (F : WeilSheaf k₀ l X) (n : ℤ) : WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-d-real-operations
/-- The coinvariants `V_{π₁(X ⊗ k)}` of the generic geometric representation of a lisse Weil
sheaf, with the Frobenius induced from the Weil structure: the maximal geometrically constant
quotient of `F`. -/
noncomputable def geometricCoinvariants (F : WeilSheaf k₀ l X) : FrobeniusModule.{u} l := sorry

end WeilSheaf

-- TODO(unify): sk-def-trace
/-- The alternating trace function `t_{K,n}` of a Weil complex. -/
noncomputable def WeilComplex.traceFunction (K : WeilComplex k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    PadicAlgCl l := sorry

-- TODO(unify): sk-thm-sf-global-duality
/-- The compactly supported cohomology `H_c^r(X ⊗ k, K)` of a Weil complex, with its geometric
Frobenius. -/
noncomputable def WeilComplex.compactlySupportedCohomology (r : ℤ) (K : WeilComplex k₀ l X) :
    FrobeniusModule.{u} l := sorry

/-- The compactly supported cohomology `H_c^r(X ⊗ k, F)` of a Weil sheaf. -/
noncomputable def WeilSheaf.compactlySupportedCohomology (r : ℤ) (F : WeilSheaf k₀ l X) :
    FrobeniusModule.{u} l :=
  (WeilSheaf.toComplex.obj F).compactlySupportedCohomology r

end WeilSheaf

/-! ### Direct images along an open immersion -/

section OpenImmersion

variable {k₀ : Type u} [Field k₀] {l : ℕ} [Fact l.Prime]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-d-real-boundary
/-- The *ordinary* sheaf direct image `j_*` along an open immersion `j`; its stalks at the
missing points are the inertia invariants. -/
noncomputable def WeilSheaf.directImage (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-d-real-boundary
/-- The higher direct image `Rⁱj_*` along an open immersion `j`. -/
noncomputable def WeilSheaf.higherDirectImage (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (i : ℕ) :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
/-- Extension by zero `j_!` along an open immersion `j`. -/
noncomputable def WeilSheaf.extensionByZero (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
noncomputable instance (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    (WeilSheaf.directImage (k₀ := k₀) (l := l) j).Additive := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
noncomputable instance (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    (WeilSheaf.extensionByZero (k₀ := k₀) (l := l) j).Additive := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
/-- The canonical map `j_! → j_*`, whose cokernel is the boundary sheaf `B` supported on the
complement of `U`. -/
noncomputable def WeilSheaf.extensionByZeroToDirectImage (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf.extensionByZero (k₀ := k₀) (l := l) j ⟶ WeilSheaf.directImage j := sorry

end OpenImmersion

/-! ### Artin–Schreier sheaves and the Fourier transform -/

section Fourier

variable {k₀ : Type u} [Field k₀] {l : ℕ} [Fact l.Prime]

-- TODO(unify): sk-def-as
/-- The Artin–Schreier sheaf `ℒ_{ψ(a x)}` on the affine line: the `ψ`-isotypic part of the
pushforward of the constant sheaf along the Artin–Schreier cover `uᵖ - u = a x`. It is lisse
of rank one and of weight zero. -/
noncomputable def artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    WeilSheaf k₀ l (affineLine k₀) := sorry

-- TODO(unify): sk-def-ft
/-- The Fourier–Deligne transform `FT_ψ` from the bounded derived category of Weil complexes
on the affine line to that of the dual affine line, with Laumon's shift by the relative
dimension one. -/
noncomputable def fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilComplex k₀ l (affineLine k₀) ⥤ WeilComplex k₀ l (affineLine k₀) := sorry

-- TODO(unify): sk-def-ft
noncomputable instance (ψ : AddChar k₀ (PadicAlgCl l)) :
    (fourierTransform (l := l) ψ).Additive := sorry

end Fourier

/-! ### Constancy and ramification at infinity -/

section Infinity

variable {k₀ : Type u} [Field k₀] {l : ℕ} [Fact l.Prime]
variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `sk-d-dl-a1-setup`: Affine-line and weight conventions. A Weil sheaf is
*geometrically constant* if the geometric fundamental group `π₁(U ⊗ k)` acts trivially on it;
its Frobenius module may still be nontrivial. -/
def WeilSheaf.IsGeometricallyConstant (F : WeilSheaf k₀ l U) : Prop := sorry

/-- Blueprint `sk-d-dl-a1-setup`: Affine-line and weight conventions. A lisse Weil sheaf on an
open `U₀` of the affine line is *unramified at infinity* if the inertia group at
`∞ ∈ ℙ¹` acts trivially on its geometric generic fibre; equivalently, if it extends to a lisse
Weil sheaf on an open neighbourhood of `∞` in `ℙ¹`. -/
def WeilSheaf.IsUnramifiedAtInfinity (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U) : Prop := sorry

-- TODO(unify): sk-d-real-operations
/-- `F.HasLinearArtinSchreierConstituent ψ k a` says that the restriction of the geometric
linear Artin–Schreier sheaf `ℒ_{ψ(a x)}` to `U` is an irreducible constituent of the pullback
of `F` to `U ⊗_{k₀} k`, for `a` in an algebraically closed extension `k` of `k₀`. -/
def WeilSheaf.HasLinearArtinSchreierConstituent (ψ : AddChar k₀ (PadicAlgCl l))
    (F : WeilSheaf k₀ l U) (k : Type u) [Field k] [Algebra k₀ k] (a : k) : Prop := sorry

end Infinity

/-! ### Lisse Weil sheaves on a dense open of the affine line -/

/-- The standing situation of the affine-line estimate: a dense open immersion
`j : U₀ ↪ 𝔸¹_{k₀}` together with a lisse Weil `ℚ̄_ℓ`-sheaf on `U₀`. Bundling the data avoids
carrying six instance arguments through every statement, and makes the existential statements
of the block — which produce a new dense open of the dual line — readable. -/
structure LisseOnDenseOpen (k₀ : Type u) [Field k₀] (l : ℕ) [Fact l.Prime] where
  /-- The dense open subscheme `U₀`. -/
  U : Scheme.{u}
  [overBase : U.Over (Spec (CommRingCat.of k₀))]
  /-- The open immersion `j : U₀ ↪ 𝔸¹_{k₀}`. -/
  j : U ⟶ affineLine k₀
  [isOpenImmersion : IsOpenImmersion j]
  [isOver : j.IsOver (Spec (CommRingCat.of k₀))]
  [isDominant : IsDominant j]
  /-- The lisse Weil sheaf on `U₀`. -/
  sheaf : WeilSheaf k₀ l U
  /-- The sheaf is lisse. -/
  lisse : sheaf.IsLisse

namespace LisseOnDenseOpen

attribute [instance] overBase isOpenImmersion isOver isDominant

variable {k₀ : Type u} [Field k₀] {l : ℕ} [Fact l.Prime] (D : LisseOnDenseOpen k₀ l)

/-- The ordinary direct image `j_*M` of the datum, a Weil sheaf on the whole affine line. -/
noncomputable def directImage : WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.directImage D.j).obj D.sheaf

/-- The extension by zero `j_!M` of the datum. -/
noncomputable def extensionByZero : WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.extensionByZero D.j).obj D.sheaf

/-- The curve perverse middle extension `j_{!*}(M[1]) = (j_*M)[1]` of the datum. -/
noncomputable def middleExtension : WeilComplex k₀ l (affineLine k₀) :=
  (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧

/-- The boundary sheaf `B = j_*M / j_!M`: the cokernel of the canonical map `j_!M → j_*M`, a
punctual sheaf supported on the finite complement of `U₀`. -/
noncomputable def boundarySheaf : WeilSheaf k₀ l (affineLine k₀) :=
  Limits.cokernel ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf)

/-- The shifted zero extension `j_!M[1]`, a curve perverse sheaf. -/
noncomputable def shiftedExtensionByZero : WeilComplex k₀ l (affineLine k₀) :=
  (WeilSheaf.toComplex.obj D.extensionByZero)⟦(1 : ℤ)⟧

end LisseOnDenseOpen

end AlgebraicGeometry
