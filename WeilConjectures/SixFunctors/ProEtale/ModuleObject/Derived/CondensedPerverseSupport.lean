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
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

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

/-- A finite field, or an algebraic closure of a finite field, has finite `ℓ`-cohomological
dimension: `cd_ℓ ≤ 1` for a finite field and `cd_ℓ = 0` for an algebraically closed field.
This is the hypothesis of the constructible exceptional adjoint of det-def-sf-operations.
Source: blueprint sk-def-cd (blueprint: def-per-support-condition). -/
theorem baseFieldFiniteCD_of_finite_or_closure (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x) :
    BaseFieldFiniteCD ℓ k :=
  hk.1.elim (fun h ↦ by have := h; exact BaseFieldFiniteCD.of_finite ℓ k)
    (fun h ↦ by have := h; exact BaseFieldFiniteCD.of_isAlgClosed ℓ k)

/-- The dualizing complex `ω_X = Ra_X^! Ω_s[0]` of a separated finite-type scheme over a finite
field or an algebraic closure of a finite field, as an object of the ambient derived category of
`Ω_X`-modules: the constructible exceptional inverse image of det-def-sf-operations along
`a_X : X → Spec k`, applied to the coefficient unit of `Spec k` (which lies in `D_ctf` by
lem-per-condensed-coefficient-unit). This is the dualizing complex of def-trf-dualizing-complex
with coefficients `Ω = Qbar_ℓ`, and the one used by sk-thm-pd-verdier-duality.
Source: latest blueprint, order 4191 (blueprint: def-per-support-condition). -/
def condensedDualizingObject (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :=
  letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))
  letI : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
  letI : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))
  ((ctfExceptionalInverseImage (Profinite.padicAlgClRingObj ℓ) ℓ k
      (baseFieldFiniteCD_of_finite_or_closure ℓ hk) (Over.mkIdTerminal.from X)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))))).obj
    ⟨𝟙_ _, condensedCoefficientUnit_mem (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))⟩).obj

/-- The Verdier dual `D_X K = RHom_{Ω_X}(K, ω_X)`, the actual relative derived internal Hom into
the dualizing complex `condensedDualizingObject`.
Source: latest blueprint, order 4191 (blueprint: def-per-support-condition). -/
def condensedPerverseDual (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :=
  ((derivedHom (Profinite.padicAlgClRingObj ℓ) X.left).obj (op K.obj)).obj
    (condensedDualizingObject ℓ hk X)

/-- `CosuppCon(K)` is precisely `SuppCon(D_X K)` for the Verdier dual into the dualizing
complex `Ra_X^! Ω_s[0]`, over a finite field or an algebraic closure of a finite field.

Construction, following the node's steps. First, the ambient category, cohomology sheaves and
closed supports are those of `CondensedSupportCondition`. Second, the dualizing complex is the
constructible exceptional inverse image of the coefficient unit along `a_X`
(`condensedDualizingObject`, det-def-sf-operations), and `D_X K` is the actual relative derived
internal Hom into it (`condensedPerverseDual`). Third, the support predicate is applied to `D_X K`.
Source: latest blueprint, order 4191 (blueprint: def-per-support-condition). -/
def CondensedCosupportCondition (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : (Finite k ∨ IsAlgClosed k) ∧ ∀ x : k, x ≠ 0 → IsOfFinOrder x)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) : Prop :=
  CondensedAmbientSupportCondition (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
    (condensedPerverseDual ℓ hk X K)

end AlgebraicGeometry.ProEtale.CondensedRing
