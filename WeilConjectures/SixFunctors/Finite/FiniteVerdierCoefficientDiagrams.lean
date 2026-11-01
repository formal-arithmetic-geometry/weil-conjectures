/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData

/-! # Finite Verdier coefficient diagrams without numerical bounds

Source: current blueprint cor-coef-finite-verdier.proof.md, the Hom comparison,
evaluation, double-dual and quotient cocycle sentences.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- The normalized coefficient diagrams on both sites, without a numerical Tor bound.
The two constant-true interval predicates deliberately assert no quantitative bound.
This is the morphism part of finite Verdier change; it does not imply its Tor estimates.

Source: current blueprint cor-coef-finite-verdier.proof.md, sentences 1--4;
DAG cor-coef-finite-verdier, steps 1--3 and the diagram part of step 5.
(blueprint: lem-coef-finite-verdier-coefficient-diagrams).

Proof:
1. The coefficient unit has interval [0,0]. Applying Verdier preservation to it
identifies its dual with omega and proves omega finite-Tor constructible. The same
preservation theorem gives closure of the finite-Tor domain under D. Flat-model
scalar extension preserves this domain on the etale site.
2. On any finite range of positive levels, form the target family omega with the
counit-defined transition isomorphisms of lem-coef-finite-dualizing. Their unit and
cocycle are exactly the hypotheses of lem-coef-finite-target-change-coherence.
Apply its etale clause to obtain d = Hom(1,u) after the canonical reduced-evaluation
transpose. The construction is defined on all ambient objects and is natural there;
only its invertibility and the displayed equations are restricted to finite-Tor inputs.
Since the formula is independent of the finite range, its laws hold on all levels.
3. Normalize the tensor comparisons by lem-coef-finite-hom-domain-calculus. The
published ordinary scalar adjunction and its cochain representative are definitionally
the finiteVerdier ones. Its tensor normalization therefore supplies the witness in
FiniteVerdierSiteComparison. The normalized pairing gives the specified evaluations.
Evaluation compatibility at K and DK, together with lem-coef-finite-bidual-transpose,
gives the double-dual square. Uniqueness of the adjoint transpose identifies these
pairings and transposes with finiteVerdierEtaleEvaluationAt and BidualityAt.
4. For the pro-etale site, lem-coef-finite-hom-site-descent represents each input by
an etale finite-Tor input. Apply lem-coef-finite-site-hom-transport to the target family.
Its scalar/site square transports u, evaluations, double-dual squares and cocycles.
The fixed-ModuleCat realization equivalence transports the intrinsic closed and scalar
data to the published pro-etale tensor, Hom and pbcFixedScalarExtension. The uniqueness
of the normalized tensor comparison and of the evaluation transpose identifies the
result with the specified fixed-module structures. In particular the transported target
map is pbcComparisonReduction.hom followed by comparison pullback of u, as required.
This proves all pro-etale clauses, including the identity at exponent one. No numerical
interval is used in these equations; the two dummy interval clauses are True. -/
theorem finiteVerdier_coefficient_diagrams
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
  @FiniteVerdierTwoSitesComparison X (finiteDualizingCoeff l E)
    (fun _n ↦ inferInstance) (fun {_ _} h ↦ finiteDualizingQuotient l E h)
    (finiteDualizingQuotient_id l E) (fun {_ _ _} h g ↦ finiteDualizingQuotient_comp l E h g)
    (finiteDualizingEtaleTerm l E D X)
    (fun n ↦ finiteTorConstructibleEtale l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X)
    (fun n ↦ finiteTorConstructibleProEtaleModule l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X)
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun {_ _} h ↦ finiteDualizingEtaleComparison l E D X h) 0 := by
  sorry

end WeilConjectures
