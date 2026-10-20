/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ExchangeFunctoriality
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.FiniteCoefficientAdjointComparisons

/-! # Invertibility of compact-support exchange for geometric Frobenius

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md,
Proof paragraph 1: Frobenius comparison and its inverse
(blueprint: lem-coef-frobenius-exchange-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange

/-- The compact-support exchange for geometric Frobenius is invertible on every raw
rational constructible object.  The exchange is the canonical localized exchange
attached to the base-changed compactification, and no Weil structure is supplied.
Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md,
Proof paragraph 1: Frobenius comparison and its inverse
(blueprint: lem-coef-frobenius-exchange-equivalence).
Proof, following the seven steps of the node:
1. Write h_T = g_T inverse. For every integer r give the same underlying scheme T
   the structure a_T g_T^r. Then g_T and h_T become k-isomorphisms between the
   adjacent twists. The vertical maps are conjugate to f and remain separated
   finite type. Both Frobenius squares are Cartesian: the lift of (u,v) through
   the g-square is h_X u. The pro-etale sites and all coefficient constructions
   use the underlying scheme maps, so the twists do not change those operations.
2. By lem-weil-isomorphism-derived-pullback and
   lem-weil-proetale-isomorphism-inverse-image the integral pullbacks along g and
   h are exact termwise inverse-image equivalences. Cancellation on sections
   supplies their inverse comparisons and triangle identities. Exact inverse
   image preserves the products used in the one shifted-cone-of-1-s reduction
   diagram of def-pur-integral-derived-operations, so these same identities hold
   for the completed operations, including their reduction maps.
3. Raw rationalization keeps every integral object and extends integral Hom maps
   linearly. It therefore extends the cancellation comparisons and identities.
   Put P = Lg_Y*, Q = Lh_Y*, S = Lg_X*, R = Lh_X*, F = Rf! and write
   u : QP isomorphic to id, v : PQ isomorphic to id,
   x : RS isomorphic to id, y : SR isomorphic to id.
   Their triangle equations are Pu = vP and Sx = yS.
   By lem-sf-integral-compact-support-constructible and
   def-weil-integral-rational-qbar-compact-support, all four composites with F
   are defined on every raw rational constructible object.
4. Use lem-sf-proetale-constructible-origin to choose bounded constructible etale
   origins for every finite reduction of an integral representative, also after
   either inverse pullback. Compute all reductions from one flat-term K-flat
   representative P. Its reductions are K-flat over the quotient rings. Their
   normalization maps send (p tensor b) tensor a to p tensor ba; associativity
   gives the quotient cocycle. The uniformizer-power quotients have the finite
   free two-term resolutions. Thus lem-weil-pbc-normalized-etale-origin-witnesses
   supplies compatible witnesses, without any extra input-object hypothesis.
5. Let a : PF to FS be the specified exchange and b : QF to FR its inverse-square
   exchange. Naturality, identity and horizontal pasting from fix-lem-exchanges
   apply on these witnessed domains. They give
   (bS)(Qa) = (F x inverse)(uF) and
   (aR)(Pb) = (F y inverse)(vF).
   Use twist indices 0,1,0 and 1,0,1 for the two pastings; the repeated underlying
   operations agree by step 1. Only compact-support coherence is used here.
6. Define c : FS to PF by (PFx)(PbS)(v inverse FS). Naturality of v at a and
   the first pasting equation give
   ca = P((Fx)(bS)(Qa))(v inverse PF) = (PuF)(v inverse PF) = id,
   using Pu = vP. These are the actual canonical pullback comparisons.
7. Naturality of a at x gives a(PFx) = (FSx)(aRS). Evaluate the second pasting
   equation on SK to obtain (aRS)(PbS) = (F y inverse S)(vFS). Hence
   ac = (FSx)(F y inverse S)(vFS)(v inverse FS) = id, using Sx = yS.
   Every factor of c is natural, so c is a natural inverse on the whole raw
   rational category. At no point is a Weil structure on K required. -/
theorem compactSupportFrobeniusExchange_isIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c₀ : Compactification f₀.left) :
    IsIso (frobeniusRational D l hl E f₀
      (frobeniusCompactModel D f₀ c₀)) := by
  sorry

end WeilConjectures.FrobeniusExchange
