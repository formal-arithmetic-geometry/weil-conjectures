/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.RingTheory.RegularRingNormal
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Etale.Weakly
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
import WeilConjectures.RingTheory.EtaleNormalRing
import WeilConjectures.RingTheory.FilteredColimitNormalRing
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.LocalProperties.Basic

/-! # Normal charts on the full SNC parameter-root limit

Source: ILO, Travaux de Gabber, Expose IX, Proposition 2.1 proof, printed p.133;
Bhatt--Scholze, Theorem 2.3.4; Stacks Tags 097Z, 033C, 037D, 033G.
(blueprint: lem-sfb-snc-root-limit-normal-charts).

The existing `tameRootAlgebra` presents the displayed colimit by adjoining every root
and imposing precisely the divisibility transition equations. No root choice is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Every weakly etale chart of the full simultaneous prime-to-p parameter-root limit
is normal, and the image of the boundary product acts injectively on its ring.
Source: ILO IX, Proposition 2.1 proof, p.133; Bhatt--Scholze Theorem 2.3.4;
Stacks Tags 097Z, 033C, 037D, 033G.
(blueprint: lem-sfb-snc-root-limit-normal-charts).

Proof:
1. For each positive n prime to p, the finite simultaneous root algebra A_n over A
   is regular Noetherian by `lem-sfb-snc-finite-root-regular-ring`: Bezout makes n
   invertible in A. The SNC empty intersection supplies regularity of the chart.
   `lem-weil-pbc-regular-ring-normal` gives normality of A_n.
2. The polynomial quotient universal property identifies A_n tensor_A R with R_n:
   the two inverse maps fix all coefficients and all roots. Thus A_n -> R_n is
   weakly etale by `lem-exc-weakly-etale-ring-base-change-composition`, using
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`.
3. `lem-weil-pbc-existing-weakly-etale-indetale-refinement` gives a faithfully flat
   refinement R_n -> T_n with A_n -> T_n ind-etale. Its finite-presentation etale
   stages are normal by `lem-weil-pbc-etale-over-normal-ring-normal`; apply
   `lem-weil-pbc-filtered-colimit-normal-ring` and then
   `lem-sfb-faithfully-flat-normal-ring-descent` to obtain normality of R_n.
4. The positive orders prime to p are directed by divisibility (use the product
   as upper bound). Their prescribed power maps respect the equations and compose.
   The quotient presentation `tameRootAlgebra` is their colimit. Apply
   `lem-weil-pbc-filtered-colimit-normal-ring` to obtain normality of S.
5. Apply the same ind-etale refinement, etale normality, filtered-colimit normality,
   and faithfully flat descent to S -> Q. This gives the asserted prime-local form.
6. Each maximal localization of A is a domain by `lem-sc-regular-local-domain`.
   A branch equation cannot vanish there: its generic prime would lie on that
   branch with local dimension zero, contradicting the SNC codimension-one clause.
   Thus t_d y = 0 implies y vanishes at every maximal localization, and hence y = 0
   by `lem-weil-pbc-ideal-membership-at-maximal-localizations`. Composing gives
   injectivity of multiplication by the product on A.
7. Flatness of A -> R preserves this injection. Each R_n is free over R on monomials
   with each exponent less than n, by `lem-weil-pbc-monic-quotient-free`; uniqueness
   of coefficients therefore gives injectivity of multiplication by the product.
8. Represent a kernel element at a finite stage and its zero equality at a common
   later stage by `lem-pc-filtered-colimit-commrings-elementwise`. Step 7 kills it
   there, proving injectivity on S. Flatness of S -> Q preserves the injection.
9. A zero ring has no prime ideals and multiplication on its singleton set is
   injective. For r = 0 all stages and their colimit are canonically R, the product
   is 1, and multiplication is the identity. The argument includes n = 1.
-/
theorem sncRootLimit_normal_charts
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k)) [LocallyOfFiniteType y] [QuasiCompact y]
    [IsSeparated y] (hY : IsRegularScheme Y)
    (A : Type u) [CommRing A] (b : Spec (.of A) ⟶ Y) [Etale b]
    (r : ℕ) (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hproduct : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv (∏ i, t i)}))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (R : Type v) [CommRing R] (a : A →+* R) (ha : a.WeaklyEtale)
    (Q : Type w) [CommRing Q] [Algebra (tameRootAlgebra p (fun i ↦ a (t i))) Q]
    [Algebra.WeaklyEtale (tameRootAlgebra p (fun i ↦ a (t i))) Q] :
    (∀ (q : Ideal Q) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) ∧
    Function.Injective (fun z : Q ↦
      algebraMap (tameRootAlgebra p (fun i ↦ a (t i))) Q
        (algebraMap R (tameRootAlgebra p (fun i ↦ a (t i))) (a (∏ i, t i))) * z) := by
  sorry

end AlgebraicGeometry.ProEtale
