/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.Paper.BoundaryFiniteSiteData

/-! # Evaluation transport on the finite-Tor boundary comparison

Source: boundary-duality discharge, second proof paragraph
(blueprint: lem-weil-boundary-finite-evaluation-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.BoundaryFiniteSite
open BoundaryComparison BoundaryComparisonOfCoefficients

/-- Boundary Hom, projection, evaluation and biduality comparison at finite coefficients.
Source: boundary finite-site realization, steps 2 and 5--8, and the second paragraph
of boundary-duality discharge (blueprint: lem-weil-boundary-finite-evaluation-realization).

Proof: the closed immersion is proper. The existing boundary projection comparison gives
Hom bijectivity, canonical mate invertibility, and counit/projection normalization.
Etale exceptional preservation supplies its constructibility hypothesis. The identity-open
compactification in boundary_etale_adjunction_restriction gives Noetherianity and a finite
dimension bound. The finite-coefficient proper projection formula makes its components
invertible, and the comparison square transfers the inverse.
Use boundary_finite_tor_comparison for both schemes to obtain representatives and interval
comparison. Then lift bounded etale objects to D+. Applying C_Z G to the invertible comparison
unit gives theta with hom the specified raw origin map. The pullback square gives psi.
The comparison equivalences and etale preservation transfer preservation to the two
specified pro-etale functors. The coefficient unit is finite-Tor constructible; dual
preservation and the closed monoidal unit isomorphism put omega_T there. Exceptional
preservation puts G omega_T there. The composition isomorphisms identify its realization
with omega_Z,p, compatibly with theta by the pasted-counit normalization.
Apply finite_duality_site_comparison to these dualizing objects and all finite-Tor
inputs, including restrictions and iterated duals. It gives the evaluation-normalized
chi and the four ambient duality pairings. Transfer dual preservation along etale
representatives. These projection comparisons and finite coefficient projection
formula give ep and pp. Transpose the projection inverse followed by the ordinary
exceptional counit through the bijective exceptional Hom transport to define qp;
naturality of each factor gives its naturality. boundary_proetale_q_compatibility
identifies this qp on etale representatives with assembleProQ and comparedEtaleQ.
Transpose these pairing equalities through tensor-Hom. Evaluation and symmetry
compatibility give the stated alpha and beta squares, in their displayed factor orders.
Apply C_Z to CompositeIdentity and replace the evaluation, double-dual and alpha/beta
factors using these squares; cancel the comparison isomorphisms. Applying C_Z to inverses
and conjugating proves invertibility on comparison inputs. Naturality and the finite-Tor
etale representatives extend invertibility to every pro-etale input. No pro-etale ambient
exceptional adjunction is used. -/
theorem boundary_finite_evaluation_realization (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z T : Scheme.{u}} (i : Z ⟶ T)
    [Z.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))] [IsSeparated (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))] [IsSeparated (T ↘ Spec (.of D.k))]
    [i.IsOver (Spec (.of D.k))] [IsClosedImmersion i] :
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of D.k))
  let A := Padic.coefficientExtensionRing l E n
  let C := BoundaryComparison.coefficients A
  let a := T ↘ Spec (.of D.k)
  let G := BoundaryComparisonOfCoefficients.etaleExceptional (ULift.{u + 1, u} A) i
  let W := Etale.dualizingComplex C a
  letI : BraidedCategory (DerivedCategory (Sheaf T.smallEtaleTopology C)) :=
    DerivedCategory.braidedCategory' _
  letI : BraidedCategory (DerivedCategory (Sheaf Z.smallEtaleTopology C)) :=
    DerivedCategory.braidedCategory' _
  EtaleHypotheses ((Etale.upperStar C i).leftDerivedFunctor) G W (G.obj W)
      (WeilConjectures.finiteTorConstructibleEtale l E n hn T)
      (WeilConjectures.finiteTorConstructibleEtale l E n hn Z) →
  BasicRemainder A i a
    (WeilConjectures.finiteTorConstructibleEtale l E n hn T)
    (WeilConjectures.finiteTorConstructibleEtale l E n hn Z)
    (WeilConjectures.finiteTorConstructibleProEtaleModule l E n hn T)
    (WeilConjectures.finiteTorConstructibleProEtaleModule l E n hn Z) ∧
  EvaluationAt A i a
    (WeilConjectures.finiteTorConstructibleEtale l E n hn T)
    (WeilConjectures.finiteTorConstructibleEtale l E n hn Z)
    (WeilConjectures.finiteTorConstructibleProEtaleModule l E n hn T)
    (WeilConjectures.finiteTorConstructibleProEtaleModule l E n hn Z) := by
  sorry

end AlgebraicGeometry.ProEtale.BoundaryFiniteSite
