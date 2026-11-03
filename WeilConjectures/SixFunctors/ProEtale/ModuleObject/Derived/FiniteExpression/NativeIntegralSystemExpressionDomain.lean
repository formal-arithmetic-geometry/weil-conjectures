/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.CategoryTheory.Pi.Basic

/-! # Finite condensed-coefficient expressions and their intermediate constructible domains

Source: latest blueprint `fix-prop-coherence`, proof sentences beginning “The maps used here
are tensor reassociation, evaluation, and adjunction units and counits” and final sentence
“Thus coherence is inherited from the individual maps on the stated domains”.
(blueprint: def-sf-integral-system-expression-domain).

This file records the finite syntax, its native condensed-module evaluation, the finite list of
all evaluated subexpressions (including the hidden open-extension value in a compactification),
and the full subcategory on which all those objects have common bounded constructible and Tor
amplitude bounds. The public domain declaration is `FiniteExpression.domain`; its recorded
signature is copied verbatim into the DAG lean record. No preservation or comparison theorem is
asserted here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Functor CategoryTheory.Obj MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ambient category `C_T = D(T_proet, Λ_T)` of a scheme `T`: the ordinary derived category
of module objects over the pulled-back coefficient ring `Λ_T = p_T^* Λ`.
Source: latest blueprint `fix-prop-coherence`, the categories of the stated domains
(blueprint: def-sf-integral-system-expression-domain). -/
abbrev ModuleDerivedCategory (T : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))

/-- A finite typed expression over a base scheme. Every constructor is indexed by its output
scheme; morphisms are morphisms in `Over B`, so all arrows are over `B`.
Source: latest blueprint `fix-prop-coherence`, finite-expression syntax
(blueprint: def-sf-integral-system-expression-domain). -/
inductive FiniteExpression (B : Scheme.{u}) (I : Type u) [Fintype I]
    (X : I → Over B) : Over B → Type (u + 1) where
  | var (i : I) : FiniteExpression B I X (X i)
  | pullback {U V : Over B} (f : U ⟶ V)
      (e : FiniteExpression B I X V) : FiniteExpression B I X U
  | properPushforward {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : FiniteExpression B I X U) : FiniteExpression B I X V
  | openExtension {U V : Over B} (j : U ⟶ V) (hj : IsOpenImmersion j.left)
      (hqc : QuasiCompact j.left)
      (e : FiniteExpression B I X U) : FiniteExpression B I X V
  | tensor {W : Over B} (e e' : FiniteExpression B I X W) : FiniteExpression B I X W
  | compactSupport {U V : Over B} (f : U ⟶ V) (c : Compactification f.left)
      (e : FiniteExpression B I X U) : FiniteExpression B I X V

/-- The native condensed derived category object attached to a finite expression.
Source: latest blueprint `fix-prop-coherence`, evaluation recursion
(blueprint: def-sf-integral-system-expression-domain). -/
noncomputable def FiniteExpression.evaluate {B : Scheme.{u}} {I : Type u} [Fintype I]
    {X : I → Over B} {W : Over B} (e : FiniteExpression B I X W) :
    (∀ i, ModuleDerivedCategory Λ (X i).left) ⥤ ModuleDerivedCategory Λ W.left := by
  induction e with
  | var i => exact Pi.eval _ i
  | pullback f e ih => exact ih ⋙ moduleObjectDerivedPullback Λ f.left
  | properPushforward f hf e ih => exact ih ⋙ moduleObjectDerivedPushforward Λ f.left
  | openExtension j hj hqc e ih =>
      exact ih ⋙ (openImmersionLowerShriek Λ j.left).mapDerivedCategory
  | tensor e e' ihe ihe' =>
      exact (ihe.prod' ihe') ⋙ Functor.uncurry.obj (derivedTensor Λ _)
  | compactSupport f c e ih =>
      exact ih ⋙ rightDerivedLowerShriekOfCompactification Λ c

/-- An object of the ambient category of some scheme: the members of the intermediate lists.
Source: latest blueprint `fix-prop-coherence`, intermediate-object recursion
(blueprint: def-sf-integral-system-expression-domain). -/
abbrev ExpressionObject := Σ T : Scheme.{u}, ModuleDerivedCategory Λ T

/-- The finite list of evaluated subexpressions. At a compact-support vertex it also records
`j_! M` on the compactification before the proper pushforward.
Source: latest blueprint `fix-prop-coherence`, intermediate-object recursion
(blueprint: def-sf-integral-system-expression-domain). -/
noncomputable def FiniteExpression.intermediates
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {B : Scheme.{u}} {I : Type u} [Fintype I]
    {X : I → Over B} {W : Over B} (e : FiniteExpression B I X W)
    (K : ∀ i, ModuleDerivedCategory Λ (X i).left) : List (ExpressionObject Λ) :=
  match e with
  | .var i => [⟨(X i).left, K i⟩]
  | .pullback f e =>
      FiniteExpression.intermediates Λ e K ++
        [⟨_, ((FiniteExpression.pullback f e).evaluate Λ).obj K⟩]
  | .properPushforward f hf e =>
      FiniteExpression.intermediates Λ e K ++
        [⟨_, ((FiniteExpression.properPushforward f hf e).evaluate Λ).obj K⟩]
  | .openExtension j hj hqc e =>
      FiniteExpression.intermediates Λ e K ++
        [⟨_, ((FiniteExpression.openExtension j hj hqc e).evaluate Λ).obj K⟩]
  | .tensor e e' =>
      FiniteExpression.intermediates Λ e K ++ FiniteExpression.intermediates Λ e' K ++
        [⟨_, ((FiniteExpression.tensor e e').evaluate Λ).obj K⟩]
  | .compactSupport f c e =>
      FiniteExpression.intermediates Λ e K ++
        [⟨c.Z, ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj
            ((e.evaluate Λ).obj K))⟩,
          ⟨_, ((FiniteExpression.compactSupport f c e).evaluate Λ).obj K⟩]

/-- The object property of input families whose inputs and every intermediate expression have
constructible cohomology and common cohomological and Tor intervals. The full domain evaluation
is the ambient evaluation restricted along this property.
Source: latest blueprint `fix-prop-coherence`, realization-domain paragraph
(blueprint: def-sf-integral-system-expression-domain).

Construction, following the node's proof:
1. The typed syntax `FiniteExpression` has the six constructors; `FiniteExpression.evaluate`
   takes the projection at a variable, composes the child functor with the native pullback,
   proper pushforward or open extension at a unary vertex, and pairs the two child functors
   followed by the derived tensor bifunctor at a tensor vertex.
2. At a compact-support vertex with compactification `c = (i, g)` the evaluation is the child
   followed by `i_!` and `Rg_*`, i.e. `rightDerivedLowerShriekOfCompactification`.
   `FiniteExpression.intermediates` appends the child list, `i_!` of the child value and its
   `Rg_*` image; an ordinary unary vertex appends its output, a tensor vertex concatenates both
   child lists and appends the tensor output, a variable gives its singleton list.
3. The predicate below asks the bounded constructibility, cohomology interval and Tor
   amplitude conditions of `det-def-sfb-constructible-tor-amplitude` on every input and every
   intermediate, with the two integer intervals quantified existentially; no theorem that an
   operation preserves constructibility or a bound is used. `domainEvaluation` restricts the
   evaluation along the full inclusion, keeping all ambient morphisms. -/
noncomputable def FiniteExpression.domain {B : Scheme.{u}} {I : Type u} [Fintype I]
    {X : I → Over B} {W : Over B} (e : FiniteExpression B I X W) :
    ObjectProperty (∀ i, ModuleDerivedCategory Λ (X i).left) := fun K ↦
  ∃ a b c d : ℤ, a ≤ b ∧ c ≤ d ∧
    (∀ i, constantModelBoundedConstructible Λ (X i).left (K i) ∧
      DerivedCategory.homologyConcentratedIn a b (K i) ∧
      DerivedCategory.torAmplitudeIn _ c d (K i)) ∧
    ∀ M, M ∈ FiniteExpression.intermediates Λ e K →
      constantModelBoundedConstructible Λ M.1 M.2 ∧
      DerivedCategory.homologyConcentratedIn a b M.2 ∧
      DerivedCategory.torAmplitudeIn _ c d M.2

/-- The domain evaluation functor, retaining all morphisms of the full input subcategory.
Source: latest blueprint `fix-prop-coherence`, realization-domain paragraph
(blueprint: def-sf-integral-system-expression-domain). -/
noncomputable def FiniteExpression.domainEvaluation {B : Scheme.{u}} {I : Type u} [Fintype I]
    {X : I → Over B} {W : Over B} (e : FiniteExpression B I X W) :
    (e.domain Λ).FullSubcategory ⥤ ModuleDerivedCategory Λ W.left :=
  (e.domain Λ).ι ⋙ e.evaluate Λ

end AlgebraicGeometry.ProEtale.CondensedRing
