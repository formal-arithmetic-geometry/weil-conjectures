/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTowerData.FinitePullbackStrictTowerData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerScalarComparison
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerQuotientComparison
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerKoszulAugmentation

/-! # Balanced finite-tower comparison with fixed generators

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL, with the
strict-tower refinement in proof steps 1--8
(blueprint: lem-a1-balanced-finite-tower-generator-comparison).
The index n : ℕ denotes positive exponent n+1. Ordinary pullback is not assumed exact.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.FinitePullbackStrictTowerData
open WeilConjectures.CompletedPullbackUniverseTransportData

namespace WeilConjectures.BalancedFiniteTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The normalized comparisons exist for all unbounded complexes and satisfy the
augmentation square before localization. Both Koszul generators are retained.

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; sites-cohomology.tex,
Tag 07A4 (blueprint: lem-a1-balanced-finite-tower-generator-comparison).

Proof:
1. The completed uniformizer has the constant residues. The coefficient ring map
preserves these residues and hence the uniformizer. The completed coefficient free
resolution identifies its specified projection with the principal sheaf quotient.
Exact inverse image preserves this cokernel, giving the actual ideal-image square.
2. The normalized inverse-image tensor comparison identifies the finite target with
(g^-1 P tensor g^-1 S_n) tensor S'_n, retaining the adjunction-unit generators.
3. Apply lem-pur-strict-coefficient-comparison-calculus to the completed and finite
coefficient rows. Both sides of lambda identify with g^-1 P tensor S'_n by
(x tensor b) tensor a ↦ x tensor pi(b)*a and (x tensor z) tensor a ↦ x tensor c_n(z)*a.
Their inverses insert 1. Balancing is precisely the coefficient projection square.
4. Apply lem-pur-ideal-quotient-tower-scalar-associator to the actual principal
quotients from step 1. Compose its scalar associator with lambda to obtain C.
On a pulled quotient-unit generator its value is the finite generator times pi(b).
Quotient residues lift locally; no surjectivity on sections of every object is used.
5. Both maps commute with transitions since q pi_(n+1)=pi_n. A chain map replaces
x by f(x); restriction restricts all factors. These equations give natural strict maps.
6. Cochain tensor pullback coherence and the action unitor give theta. The two
Koszul basis vectors are sent to the corresponding basis vectors, with no interchange
of homogeneous factors. Both total differential summands and the (-1)^degree sign stay.
7. Evaluate the augmentation square on e_0: both sides give the finite generator
multiplied by pi(b). On e_-1 both vanish. Pure tensor sections determine the sheaf
maps, so the equality holds as strict chain maps, natural in every P.
8. Localize this equality. For good P the pulled-Koszul comparison makes the middle
augmentation a quasi-isomorphism. The ordinary finite evaluation comparison has the
same source, target and quotient-unit formula; the uniqueness clause of
lem-weil-pbc-ordinary-finite-evaluation-transition identifies it with C termwise.
The final clause states this identification itself, after the uniquely tensor-normalized
source comparison r from P tensor S_n to ordinary reduction. At independent universes it
asserts unique existence together with sectionwise conjugation to the published
completedReductionOrdinaryComparison, using actual additive universe transports.
Thus the localized zigzag retains the prescribed representative maps and generators
of def-a1-integral-completed-pullback-interfaces, without any assumption on c_g. -/
theorem balanced_finite_tower_generator_comparison
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ (lambda : G l E g ⋙ reductions l E X ≅ finite l E g)
      (c : reductions l E Y ⋙ diagramPull l E g ≅ finite l E g)
      (theta : koszuls l E Y ⋙ diagramPull l E g ≅ G l E g ⋙ koszuls l E X),
      (∀ P : CochainComplex (Modules l E Y) ℤ,
        BalancedNormalization l E g P (lambda.app P)) ∧
      QuotientUnitNormalization l E g c ∧
      (∀ P : CochainComplex (Modules l E Y) ℤ,
        KoszulNormalization l E g P (theta.app P)) ∧
      (∀ P : CochainComplex (Modules l E Y) ℤ,
        (theta.hom.app P) ≫ augmentation l E X ((G l E g).obj P) ≫ lambda.hom.app P =
          (diagramPull l E g).map (augmentation l E Y P) ≫ c.hom.app P) ∧
      (∀ n : ℕ, ∃! e : ordinaryReduction l E Y n ⋙ pull l E g ≅ ordinaryFinite l E g n,
        OrdinaryNormalization l E g n e ∧ PublishedCompatibility l E g n e ∧
        ∀ (P : CochainComplex (Modules l E Y) ℤ),
        integralOperationsGoodComplex l E Y P →
          ∃ r : tensorReduction l E Y P ≅ ((reductionComplex l E Y).obj P).asFunctor,
            ReductionNormalization l E Y P r ∧ ∀ i : ℤ,
              (((c.hom.app P).app (op n)).f i) =
                (pull l E g).map (((r.hom.app (op n)).f i)) ≫
                  (e.hom.app (P.X i))) := by
  exact (balanced_scalar_comparison l E g).elim fun lambda hlambda ↦
    (quotient_comparison_with_ordinary_evaluations l E g).elim fun c hc ↦
      (koszul_augmentation_compatibility l E g lambda c hlambda hc.1).elim fun theta ht ↦
        ⟨lambda, c, theta, hlambda, hc.1, ht.1, ht.2, hc.2⟩

end WeilConjectures.BalancedFiniteTower
