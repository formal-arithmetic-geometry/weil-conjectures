/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.Paper.BoundaryFiniteSiteData
import Sheaf.Paper.BoundaryFiniteTorComparison
import Sheaf.Paper.BoundaryFiniteEvaluationRealization

/-! # Finite-stage realization of boundary evaluation

Source: blueprint boundary-duality discharge, second proof paragraph
(blueprint: lem-weil-boundary-finite-site-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.BoundaryFiniteSite
open BoundaryComparison BoundaryComparisonOfCoefficients

attribute [local irreducible] EvaluationConclusion EvaluationTransport


/-- Finite-stage boundary evaluation is realized by the specified pro-etale functors.
Source: blueprint `cor-weil-boundary-duality-discharge`, second proof paragraph
(blueprint: lem-weil-boundary-finite-site-realization).

Proof:
1. Constructible origin and comparison of every Tor interval restrict the comparison
   equivalence to D^b_ctf and give bounded finite-Tor constructible representatives.
2. The comparison unit is invertible on D+. Applying C_Z G gives theta. The ordinary
   pullback comparison gives psi. The assumed etale preservation and representatives
   prove preservation by the specified pro-etale functors.
3. The closed immersion is proper. Its identity-open compactification has source Z,
   which is Noetherian and has finite dimension over k, including bound zero when empty.
   Restrict the etale adjunction to D+ and apply fully faithful exceptional Hom transport.
4. The canonical direct-image mate is invertible on D+. Its counit normalization gives
   the displayed exceptional counit formula. The ordinary projection comparison gives
   its square. Finite compact-support projection makes both maps invertible, and
   multiplying the square by the inverses gives their asserted inverse comparison.
5. The coefficient unit is constructible of Tor interval [0,0]. Dual preservation gives
   omega_T in D^b_ctf; exceptional preservation gives G omega_T there. Dualizing
   composition identifies this with the structure-map dualizing object on Z.
6. Finite-duality site comparison gives w, chi and compatibility with evaluation and
   delta. Apply it also to restrictions and iterated duals, which satisfy the assumed
   preservation hypotheses. The composition identification is normalized by counits.
7. Boundary q compatibility identifies the ordinary projection-inverse/counit transpose.
   Tensor-Hom transposition then identifies the specified alpha and beta pairings.
8. Apply comparison to the two etale composites, use functoriality and these squares,
   and cancel the comparison isomorphisms. This transfers their equality and their
   invertibility. Every pro-etale input has an etale representative, so the assertion
   covers all finite-Tor constructible inputs.
-/
theorem boundary_finite_site_realization
    (D : WeilConjectures.FiniteFieldDatum.{u})
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
    FiniteStatement D l hl E n hn i := by
  classical
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of D.k))
  let A := Padic.coefficientExtensionRing l E n
  let C := coefficients A
  let PeT := WeilConjectures.finiteTorConstructibleEtale l E n hn T
  let PeZ := WeilConjectures.finiteTorConstructibleEtale l E n hn Z
  let PpT := WeilConjectures.finiteTorConstructibleProEtaleModule l E n hn T
  let PpZ := WeilConjectures.finiteTorConstructibleProEtaleModule l E n hn Z
  intro h
  have hT := boundary_finite_tor_comparison D l hl E n hn T
  have hZ := boundary_finite_tor_comparison D l hl E n hn Z
  have hremaining := boundary_finite_evaluation_realization D l hl E n hn i h
  exact ⟨⟨hT.1, hZ.1, hT.2.1, hZ.2.1, hT.2.2, hZ.2.2, hremaining.1⟩,
    hremaining.2⟩

end AlgebraicGeometry.ProEtale.BoundaryFiniteSite
