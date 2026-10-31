/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerGeometricTransportData
public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerFiniteEvaluationExistence
/-! # Geometric transport for normalized finite evaluation -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- Geometric transport for a finite evaluation with the canonical proper/open
support normalization. Source: Zheng Construction 4.1, Lemma 4.10, Construction 5.15,
Lemmas 5.16 and 5.22; Stacks 099R and 099W.
(blueprint: lem-route-brown-tower-geometric-transport-core-exists).

Proof: Construct the ordinary and universal derived system images of the actual
etale/pro-etale comparison at X, Z and Y. Use N.data.realizationX and
N.data.realizationY on the etale side and N.support.middle at Z. Realize the pro-etale
levels by the exact constant-ring module equivalence. The representative transpose
equations give inverse/direct finite comparison squares and their counit equation.
Exact inverse image and its derived right adjoint preserve each lower bound. These
are the site records, with the required realization equalities by construction.

The evaluated system unit is the finite site unit and is invertible by finite site
full faithfulness on bounded-below inputs. Joint detection by exact evaluations gives
the system unit. For Origin objects the evaluated counits are invertible; derived
system comparison gives the system counit without choosing compatible level witnesses.
The exact faithful site inverse image reflects cohomology vanishing and lower bounds.

Construct open extension on pro-etale strict systems componentwise, retaining its
adjunction transpose. It is exact; localize it on complexes and compose with universal
derived proper direct image to obtain ProCompact. Its evaluation squares give
compactEvaluation. Construct compactComparison by pasting the open inverse-image
left mate with the proper inverse-image right mate. Representative transpose equations
identify each evaluation with that same proper/open mate word. N.support fixes the
ordinary direct-image maps on sections and their universal derived-unit comparisons;
the open comparison is their prescribed inverse mate. Thus this mate word agrees with
the inverse canonical compact-support site comparison, with the finite comparison
N.support.comparison inserted. Rewriting by N.lower_eq gives exactly
compactComparison_evaluation with N.data.lower. This step uses the normalization;
an arbitrary finite evaluation with a twisted lower comparison is not permitted.
For bounded-below K, finite compact-support site comparison makes every evaluation
invertible, and joint detection proves compact_iso.

For the bound field, use finite evaluation of the Brown right adjoint and the finite
site adjunction to identify the evaluations of its site inverse image with
finiteExceptional. Exact constant realization reflects the given common bound;
joint cohomological detection and exact faithful site inverse image reflect it to the
etale Brown object as well. Transpose the actual transition equation of N.data through
the site counits. The etale/pro-etale coefficient-compatibility equation identifies
its quotient mates with the specified pro-etale finite exceptional mates. On the ctf
class these are invertible; normalization of C then gives normalization of the output.
All uses of finite comparison retain the same N.support choices. Zero objects and empty
schemes use the same mate and conservativity arguments. -/
theorem brownTowerGeometricTransport_core_exists
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (_hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (t : Padic.coefficientExtensionIntegers l E)
    (_ht : Ideal.span ({t} : Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E) t c)
    (G : EtaleTowerBrownAdjunction S)
    (N : CanonicalFiniteEvaluation S G) :
    Nonempty (GeometricTransportCore S G N.data) := by
  sorry

end BrownTowerComparison
end AlgebraicGeometry
