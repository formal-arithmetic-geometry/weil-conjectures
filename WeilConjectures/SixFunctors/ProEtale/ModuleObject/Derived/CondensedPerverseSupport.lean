/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.DeligneLaumon.Sheaf.DeligneLaumon.CondensedStructuralExceptionalDual

/-!
# Support conditions for ordinary condensed algebraic ell-adic complexes

Source: the latest blueprint, `sec-deligne-laumon-a1/sk-lem-wft-curve-heart/`
`def-per-support-condition.md`, order 4191 (blueprint: def-per-support-condition).
The module-object stalk has the same underlying abelian group as its module stalk.
We use the specified geometric point given by an algebraic closure of the residue field.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Closed support of a module sheaf: closure of the nonzero geometric-stalk locus.
The stalk is the pointed-neighbourhood colimit of its underlying abelian sheaf; forgetting
module scalars does not change whether this stalk is zero.
Source: latest blueprint, order 4191 (blueprint: def-per-support-condition). -/
def condensedModuleSupport {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) : Set X :=
  closure {x | ¬ IsZero (Scheme.proEtaleGeometricStalk (X.algClosurePoint x) M.X)}

/-- The support inequality in every degree, with empty support of dimension minus infinity.
The nonempty guard makes the condition vacuous for empty support; otherwise an integer bound
is equivalent to its nonnegativity together with the bound in `WithBot ℕ∞`.
Source: latest blueprint, order 4191 (blueprint: def-per-support-condition). -/
def CondensedAmbientSupportCondition {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) : Prop :=
  ∀ i : ℤ, (condensedModuleSupport R ((DerivedCategory.homologyFunctor _ (-i)).obj K)).Nonempty →
    0 ≤ i ∧ topologicalKrullDim
      (condensedModuleSupport R ((DerivedCategory.homologyFunctor _ (-i)).obj K)) ≤
        (i.toNat : ℕ∞)

/-- `SuppCon` on the actual ordinary bounded constructible condensed `Qbar_ℓ` category.

Construction, following the node's steps. First, the coefficient ring is the pull-back
`Ω_X = p_X^* Qbar_ℓ` of the finite-subextension-valued condensed ring, `K` lies in the bounded
constructible category over it, `H^r(K)` is the standard derived cohomology sheaf, and the
support of a module sheaf is the closure of its nonzero geometric-stalk locus, so it is closed by
definition. Second (used only by `CondensedCosupportCondition`), the exceptional dual is the
derived internal Hom into `Ra_X^! Ω_s[0]` for a compactification of `X → Spec k`. Third, for every
integer `i` the topological Krull dimension of `Supp H^{-i}(K)` is at most `i`, empty support
having dimension `-∞`; the conjunction over all `i` is `SuppCon(K)`.
Source: latest blueprint, order 4191 (blueprint: def-per-support-condition). -/
def CondensedSupportCondition (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}}
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) : Prop :=
  CondensedAmbientSupportCondition (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) K.obj

/-- The actual relative derived internal Hom into the exceptional image of the coefficient
unit, for a chosen compactification. Choices are extracted only from a restriction of the
specified compact-support functor, its right adjoint, and an object isomorphic to the unit;
these universal properties determine the resulting dual up to isomorphism.
Source: Bhatt--Scholze, Lemmas 6.7.13 and 6.7.19, Remark 6.8.15; latest blueprint,
order 4191 (blueprint: def-per-support-condition). -/
def condensedPerverseDual (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Invertible (ℓ : k)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom)
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) :=
  let h := Sheaf.DeligneLaumon.condensedStructuralExceptionalDual ℓ X
  let U := h.choose
  let hF := h.choose_spec.2 c
  let hG := hF.choose_spec
  let G := hG.choose
  ⟨((derivedHom (Profinite.padicAlgClRingObj ℓ) X.left).obj (op K.obj)).obj
      (G.obj U).obj, hG.choose_spec.2.2 K⟩

/-- `CosuppCon(K)` is precisely `SuppCon(D_X K)` for the constructible condensed exceptional
Verdier dual, with no characteristic or cohomological-dimension restriction on the base field.

Construction, following the node's steps. First, the ambient category, cohomology sheaves and
closed supports are those of `CondensedSupportCondition`. Second, the structure morphism is
separated of finite type, so a compactification `c` is given; the constructible exceptional
adjoint of `condensedStructuralExceptionalDual` applied to the coefficient unit is `ω_X`, and the
actual relative derived internal Hom `RHom(K, ω_X)` is bounded constructible by the same theorem;
this is `condensedPerverseDual`. Third, the support predicate is applied to this dual.
Source: latest blueprint, order 4191 (blueprint: def-per-support-condition). -/
def CondensedCosupportCondition (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Invertible (ℓ : k)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom)
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) : Prop :=
  CondensedSupportCondition ℓ (condensedPerverseDual ℓ X c K)

end AlgebraicGeometry.ProEtale.CondensedRing
