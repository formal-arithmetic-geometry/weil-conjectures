/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Basic


/-! # The precise proper integral adjoint obligation for general-field consumers

Source: current blueprint, `sk-thm-existence`,
`lem-sfb-dc-proper-pushforward-left-adjoint-oe.md` and its proof companion;
the proof order follows Wei Yang #1412. Houyi DM #1449 requires general-field
consumers to use the exact named obligation, rather than an arbitrary-field instance.
(blueprint: lem-sfb-dc-proper-pushforward-left-adjoint-oe-general-field)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

/-- Over a field of positive characteristic different from `ell`, proper derived pushforward
on bounded constructible `𝒪̲_E`-complexes
has a right adjoint, denoted `Rp^!`.

Source: current blueprint, `sk-thm-existence`,
`lem-sfb-dc-proper-pushforward-left-adjoint-oe.md` and its proof companion;
expert resolution Wei Yang #1412, item 1, and Houyi DM #1449: a general-field
consumer uses a named theorem for the required adjoint, never an arbitrary-field instance.
(blueprint: lem-sfb-dc-proper-pushforward-left-adjoint-oe-general-field)

Proof:
1. Set `O = 𝒪_E` and `A_n = O/ell^n`, cofinal with the uniformizer quotients.
Finite proper derived pushforward `F_n` on ordinary etale module sheaves
preserves arbitrary coproducts (`lem-sfb-finite-proper-derived-coproducts`).
The module-sheaf category is Grothendieck abelian and right derived pushforward
is triangulated, so derived Brown representability gives `F_n ⊣ G_n`.
2. Independently, `lem-sfb-finite-proper-exceptional-quotient` proves that `G_n`
preserves bounded constructible finite-Tor complexes. Its proper scalar
comparisons and counit mates are compatible with units and composition by
their defining counit equations, not just after reduction.
3. The coherent-tower theorem assembles the `G_n K_n` into a normalized tower.
Normalization identifies reduction to `A_1` with `G_1 K_1`. Filtering `A_n`
and its modules by powers of `ell` gives `A_1`-module subquotients, hence
uniform Tor and cohomological bounds. The schemes are Noetherian, so
`sk-lem-sp-tower` realizes the tower as a functorial bounded constructible
complex `G_O K = R lim_n G_n K_n`.
The general-field case is the precise existence obligation used by the abstract
compactification constructions. It makes no assertion that arbitrary base fields have
finite absolute cohomological dimension. The finite torsion-level construction and the
relative bounds must be proved without such an assertion.
4. Proper integral pushforward is constructible and derived complete.
The completion unit writes `K` as `R lim K_n`. Global derived Hom commutes
with this limit; derived coefficient adjunction and the coherent finite
adjunctions identify `RHom_Y(Rp_* M,K)` with
`R lim_n RHom_{A_n}(M_n,G_n K_n)`, and then with `RHom_Z(M,G_O K)`.
Taking degree-zero cohomology gives natural Hom bijections; the
natural-bijection criterion gives the adjunction for the actual restricted
pushforward below. This precedes purity, exchange and biduality.
-/
theorem properPushforwardLeftAdjointOE_general
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ell)] [Algebra ℚ_[ell] E]
    [IsScalarTower ℚ_[ell] E (PadicAlgCl ell)] [FiniteDimensional ℚ_[ell] E]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] :
    (boundedConstructibleLowerStar ell E p).IsLeftAdjoint := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
