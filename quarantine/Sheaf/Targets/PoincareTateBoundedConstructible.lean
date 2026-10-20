/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import Sheaf.Paper.ProEtaleTateTwists
import Sheaf.Paper.CompletedCondensedCoefficients
import Sheaf.Paper.CondensedZlReduction
import Sheaf.Paper.PurTwistSheafLocallyFree
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Paper.CondensedConstantConstructibility
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Bounded constructibility of shifted condensed Tate twists

Source: archived upstream `WeilConjectures/PoincareDuality/Poincare.lean`,
`boundedConstructible_tateTwistDerived`, with the invertibility hypothesis of the current
blueprint `sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md`
(blueprint: nt-target-poincare-tate-bc).

The conclusion uses the ordinary unbounded derived category of internal modules over the
finite-subextension-valued condensed coefficient ring. Constructibility is the upstream
finite-stratification predicate, without any finiteness assumption on the scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Every integer shift of the actual condensed Tate twist is bounded constructible when
ell is invertible on the scheme. Source: archived upstream Poincare.lean, the lemma
`boundedConstructible_tateTwistDerived`, and current blueprint `sk-def-sp-tate-twist`
(blueprint: nt-target-poincare-tate-bc).

Proof plan (the six steps of the node):
1. Put R_X = p_X^* Z_ell and A_r = (Z/ell^r)_X. The integral coefficient comparison
   `sk-prop-sfb-qlbar-colimit-x` at E = Q_ell identifies R_X with the inverse limit of A_r.
   The ring-and-module isomorphism of `lem-pur-condensed-zl-reduction-mod-ell-power`
   identifies R_X/ell^r with A_r; its compatibility clause identifies successive quotient
   maps with residue reduction. These inputs impose no further hypothesis on X.
2. The actual level F_r of `def-pur-condensed-tate-twists` is R_X tensor_Z mu_(ell^r).
   Since ell^r annihilates the roots sheaf, balancing factors through A_r. Multiplication
   a tensor z ↦ az and z ↦ 1 tensor z are inverse R_X-linear maps. Locally an element of
   the constant residue sheaf has an integer representative k, and
   1 tensor az = 1 tensor kz = k tensor z = a tensor z. For successive transitions both
   composites are z^(k*ell), so these isomorphisms identify the whole inverse systems.
   At r = 0 the roots sheaf mu_1 is zero. A cone on the positive levels extends uniquely
   to this zero level. The universal property of the limit therefore identifies the
   actual tateModule with the positive-level inverse limit Z_X of roots of unity.
3. Clause 2 of `lem-pur-twist-sheaf-locally-free`, with E = Q_ell, supplies a pro-etale
   covering on which Z_X is the completed constant integral coefficient line. It requires
   exactly the displayed residue-field invertibility hypothesis. Step 1 identifies this
   coefficient ring with R_X. Restriction to the covering slice preserves the sectionwise
   tensor and its sheafification. Thus the actual scalar extension tateTwistOne becomes
   B tensor_R R, identified with B by multiplication and b ↦ b tensor 1. The coefficient
   comparisons of `sk-prop-sfb-qlbar-colimit-x` identify the restricted coefficient rings.
4. On this same cover the zero power is B and positive powers are B tensor_B B = B,
   with inverse b ↦ b tensor 1. A negative power is the internal Hom from its positive
   opposite power into B. By `def-pur-sheaf-hom`, evaluation at 1 identifies this with B;
   its inverse sends b to multiplication by b. These maps commute with restrictions.
   Consequently every signed tateTwist is locally free of rank one on that cover.
5. Use the single stratum id_X, whose image is the constructible whole space. The scalar
   model P = B(*) has the rank-one finite presentation with zero relations; its scalar
   extension is B. This meets `det-def-sfb-constructible-local-model` and
   `sk-def-sfb-constructible`. For the exact predicate `def-sfb-constructible-module`,
   inverse image along a covering object is restriction to its slice: the base-change
   functor has as left adjoint the functor forgetting the map to the covering object,
   so its sheafified left Kan extension is that restriction
   (`def-sfb-finite-upper-star`). The local trivializations are therefore finite free
   presentations in `def-sfb-finitely-presented-module`, proving
   `def-sfb-locally-finitely-presented` and the required constructibility on the single
   stratum. The cover need not be finite. The zero module has the rank-zero presentation.
6. The complex tateTwistDerived is the single complex in degree zero. Its shift by n has
   tateTwist in degree -n and zero elsewhere, with zero differentials. Computing kernels
   and images gives H^(-n) = tateTwist and H^i = 0 otherwise. Step 5 makes all these
   modules constructible, and [-n,-n] bounds the cohomology. This is exactly
   `def-sfb-bounded-constructible-complexes` and `sk-def-sfb-bounded-constructible`.
   The empty scheme gives zero sheaves and the same argument applies.
-/
theorem boundedConstructible_tateTwistDerived_of_invertible
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (d n : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((shiftFunctor _ n).obj (tateTwistDerived X ℓ d)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
