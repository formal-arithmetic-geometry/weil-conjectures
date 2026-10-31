/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerBoundedTransport

/-! # Geometric comparisons before transporting the Brown adjunction

Source: Zheng Lemmas 4.10, 5.16 and 5.22 and the integral-adjunction Hom display
(blueprint: lem-pur-brown-tower-geometric-transport).

This package omits the transported counit and Hom equivalence. Those are constructed
from the specified geometric transformations and Brown adjunction in the consumer.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- The geometric part of bounded transport, before constructing a counit or Hom bijection.
Source: Zheng Lemmas 4.10, 5.16 and 5.22, and the compact-support site comparison;
Steps 1--10 of lem-pur-brown-tower-finite-site-comparison. The finite evaluation
package is chosen simultaneously with the geometry, so its finite support comparison
has the canonical normalization needed by compactComparison_evaluation.
(blueprint: lem-pur-brown-tower-geometric-transport). -/
structure GeometricTransport (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S) (H : FiniteEvaluation S G) where
  [finite : ∀ n : ℕ, Finite (Ring O t n)]
  siteX : Site X O t S.PX
  siteY : Site Y O t S.PY
  compact : ProCompact S siteX siteY
  compactComparison : S.functor ⋙ siteY.inverse ⟶ siteX.inverse ⋙ compact.functor
  compactEvaluation : ∀ n,
    compact.functor ⋙ siteY.proEvaluation.evaluation n ⋙ (siteY.realization n).derived ≅
    siteX.proEvaluation.evaluation n ⋙ (siteX.realization n).derived ⋙
      FiniteCoefficientAdjoints.lower (Ring O t n) c
  realizationX : ∀ n, siteX.etaleRealization n = H.realizationX n
  realizationY : ∀ n, siteY.etaleRealization n = H.realizationY n
  compactComparison_evaluation : ∀ n K
      (hK : DerivedCategory.TStructure.t.plus
        ((H.realizationX n).derived.obj ((S.PX.evaluation n).obj K))),
    (siteY.realization n).derived.map
      ((siteY.proEvaluation.evaluation n).map (compactComparison.app K)) ≫
      (compactEvaluation n).hom.app (siteX.inverse.obj K) ≫
      (FiniteCoefficientAdjoints.lower (Ring O t n) c).map
        ((siteX.realization n).derived.map
          ((siteX.comparison.evaluation.inverseEvaluation n).hom.app K) ≫
          (siteX.inverseLevel n).hom.app ((S.PX.evaluation n).obj K)) =
    (siteY.realization n).derived.map
      ((siteY.comparison.evaluation.inverseEvaluation n).hom.app (S.functor.obj K)) ≫
      (siteY.inverseLevel n).hom.app ((S.PY.evaluation n).obj (S.functor.obj K)) ≫
      (FiniteCoefficientAdjoints.nu (Ring O t n) Y).map
        (eqToHom (congrArg
          (fun R ↦ R.derived.obj ((S.PY.evaluation n).obj (S.functor.obj K)))
          (realizationY n)) ≫
        (H.realizationY n).derived.map ((S.evaluation n).hom.app K) ≫
          (H.lower n).hom.app ((S.PX.evaluation n).obj K)) ≫
      (ProEtale.compactSupportSiteComparison (Ring O t n) c).inv.app
        ⟨(H.realizationX n).derived.obj ((S.PX.evaluation n).obj K), hK⟩ ≫
      (FiniteCoefficientAdjoints.lower (Ring O t n) c).map
        ((FiniteCoefficientAdjoints.nu (Ring O t n) X).map
          (eqToHom (congrArg
            (fun R ↦ R.derived.obj ((S.PX.evaluation n).obj K))
            (realizationX n).symm)))
  compact_iso : ∀ K, (∃ a : ℤ, K.IsGE a) → IsIso (compactComparison.app K)
  unit_iso_X : ∀ K, (∃ a : ℤ, K.IsGE a) → IsIso (siteX.adjunction.unit.app K)
  unit_iso_Y : ∀ K, (∃ a : ℤ, K.IsGE a) → IsIso (siteY.adjunction.unit.app K)
  counit_iso_X : ∀ K, siteX.Origin K → IsIso (siteX.adjunction.counit.app K)
  counit_iso_Y : ∀ K, siteY.Origin K → IsIso (siteY.adjunction.counit.app K)
  bound : ∀ (C : DerivedCategory (ProSystem Y O t)), siteY.Origin C →
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y) O t siteY.proEvaluation C →
    (∀ n, FiniteCoefficientAdjoints.ctf (Ring O t n) Y
      ((siteY.realization n).derived.obj ((siteY.proEvaluation.evaluation n).obj C))) →
    ∀ a : ℤ,
    (∀ n, ((finiteExceptional S G H siteX siteY n).obj
      ((siteY.proEvaluation.evaluation n).obj C)).IsGE a) →
    (G.right.obj (siteY.direct.obj C)).IsGE a ∧
    (siteX.inverse.obj (G.right.obj (siteY.direct.obj C))).IsGE a ∧
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology X) O t siteX.proEvaluation
      (siteX.inverse.obj (G.right.obj (siteY.direct.obj C)))
/-- The site comparison, common-bound reflection, normalized exceptional images,
and actual compact-support comparison before adjoining the transported counit.
Source: Zheng Lemmas 4.10 and 5.22 and the canonical compact-support site comparison.

Proof: At each finite level construct the constant-ring module realization and the
ordinary exceptional right adjoint. Transpose the inverse of the evaluated support
comparison along derived extension from one level. Below that level its evaluations
are the proper scalar counit mates followed by open scalar comparison, and above it
both sides vanish. Unbounded scalar coherence and joint conservativity make this
extension comparison invertible. Conjugate it under the composite extension/Brown
and finite-support/extension adjunctions to obtain evaluation of the Brown right
adjoint. The conjugation counit equation and the defining transpose yield the finite
counit equation by the extension triangle identity. Transpose this equation along
the actual system transitions to get the coefficient mates; identity and composition
follow from the unit and associativity of derived scalar change and mate pasting.
Choose these finite comparisons together, retaining the canonical support comparison.
Construct the site inverse/direct images using the strict-system comparison
and identify their finite evaluations through constant-ring realization. Finite site
full faithfulness makes the evaluated units invertible; conservativity gives the
system units. The counit is invertible on bounded-below objects of levelwise origin.
Reflect common lower bounds through exact, conservative finite inverse image and
then through the exact evaluations. The finite adjoint comparison identifies the
exceptional quotient mates with the chosen finite counit transposes. Coefficient
compatibility on constructible finite-Tor inputs makes these mates invertible, so
normalized inputs give normalized exceptional systems. Finally paste the proper
site mate and termwise open-extension comparison into a transformation on whole
systems. Its finite evaluations are the named compact-support site isomorphisms;
conservativity proves invertibility on bounded-below inputs. Exact open extension
and right-derived proper image give its bound. No transported counit or Hom
equivalence is chosen in this construction: those
are obtained afterwards by inverting this compact-support comparison at the bounded
exceptional image and by composing the three adjunction Hom bijections.
(blueprint: lem-pur-brown-tower-geometric-transport). -/
theorem brownTowerGeometricTransport_exists
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
    (G : EtaleTowerBrownAdjunction S) :
    ∃ H : FiniteEvaluation S G, Nonempty (GeometricTransport S G H) := by
  sorry

end BrownTowerComparison
end AlgebraicGeometry
