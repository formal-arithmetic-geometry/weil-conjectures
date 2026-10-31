/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerComparisonData
import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerShifts
import WeilConjectures.DeligneLaumon.FiniteReductionTower.FiniteReductionTowerResolvingModel
import WeilConjectures.DeligneLaumon.PulledKoszulTowerChainComparison
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerGeneratorComparison
import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerRepresentativeConstruction

/-! # Natural finite pullback comparison of strict reduction towers

Source: Stacks Project, Tags 099N(5), 0G7E, 06XN, 03EL and 0FNH.
(blueprint: lem-a1-finite-pullback-strict-tower-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.FinitePullbackStrictTower
attribute [local implicit_reducible] asIso
attribute [local implicit_reducible] H tensorReduction augmentation G diagramPull
  finiteComplex pulledReduction transpose PrincipalQuotientCompletion.transpose
  koszulTowerComplex HomologicalComplex.asFunctor
  PrincipalKoszulStrictReplacement.sourceTower PrincipalKoszulStrictReplacement.targetTower
  FinitePullbackStrictTowerData.G FinitePullbackStrictTowerData.koszuls
  FinitePullbackStrictTowerData.reductions FinitePullbackStrictTowerData.diagramPull
  FinitePullbackStrictTowerData.finite FinitePullbackStrictTowerData.augmentation
  CompletedTowerIndependent.towerPull koszulTowerComplexMap
  PrincipalKoszulStrictReplacement.tensorWith
  PrincipalKoszulStrictReplacement.sourceTowerMap PrincipalKoszulStrictReplacement.targetTowerMap
  CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.map₂HomologicalComplex
  SheafOfModules.KFlatTotalTensorModel.tensor
attribute [local irreducible] CompletedTowerIndependent.reductionPair
  CompletedTowerIndependent.derivedPull CompletedTowerIndependent.derivedCounit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

private theorem representative_comparison
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (RepresentativeComparison l E g) := by
  obtain ⟨R⟩ := FiniteReductionTower.finite_reduction_tower_resolving_model l E g hX hY
  obtain ⟨θ₀, hg⟩ := pulled_koszul_tower_chain_comparison l E g hX hY
  obtain ⟨lambda, c, θ, hlambda, hc, hθ, hsquare, heval⟩ :=
    BalancedFiniteTower.balanced_finite_tower_generator_comparison l E g hX hY
  exact representative_from_models l E g R θ lambda hθ hlambda
    (fun P hP ↦ (hg P hP).1) (fun P hP ↦ (hg P hP).2.1)
    (fun P hP ↦ (hg P hP).2.2.2.2.1) (fun P hP ↦ (hg P hP).2.2.2.2.2.1)

/-- Strict finite pullback and derived strict tower pullback have the normalized
natural comparison, including arbitrary derived arrows and every integer shift.

Source: Stacks Project, proetale.tex Tag 099N(5), sites-cohomology.tex Tags 0G7E,
06YS, 06YT, 06YY, 0G7D, 07A4, sites-modules.tex 03EK/03EL, and derived.tex 06XN.
(blueprint: lem-a1-finite-pullback-strict-tower-comparison).

Proof:
1. Apply flat-term K-flat resolutions (lem-pc-kflat-resolution), change-of-rings
   invariance (lem-pur-derived-change-of-rings), exact finite inverse image
   (prop-weil-pbc-proetale-constant-exact), and levelwise exactness of towers.
   The resolving-class theorem lem-pur-left-derived-from-kflat-class descends B^0
   with its universal counit and representative computation to B on all of D(R).
2. Use lem-a1-principal-koszul-strict-replacement to replace P tensor S by
   H(P)=P tensor Q, with transitions id tensor (t,1) and the actual augmentation.
   The diagram resolving class of def-weil-pbc-completed-pullback and
   lem-weil-pbc-diagram-kflat-replacements computes V on H(P).
3. Apply lem-weil-pbc-ringed-topoi-derived-tensor-pullback (Stacks 0G7E) to P
   and to each P tensor Q_n. Their images under G are K-flat with flat terms.
   No invertibility or flatness of the completed coefficient map is needed.
4. The ordinary comparison lem-pur-cochain-pullback-tensor-coherence and the
   action unitor identify GQ_n with Q'_n. Constants preserve t, so (t,1) maps
   to (t,1). Its total tensor map is uniquely fixed on the two Koszul generators
   by KoszulNormalization, with no sign or scalar automorphism introduced.
5. Apply principal Koszul replacement on X to GP, now known to be flat-term
   K-flat. The middle augmentation is a levelwise quasi-isomorphism. Levelwise
   abelianness makes its transposition a quasi-isomorphism of strict towers.
6. Constant coefficient transport (prop-weil-pbc-proetale-constant-ring-map)
   identifies g^-1 S_n with S'_n. The coefficient projection square commutes by
   directRingMap. Tensor association identifies both GP tensor S'_n and g_n^*P_n
   with g^-1 P tensor S'_n. The forward formula is (x tensor b) tensor a mapped
   to x tensor pi_n(b)*a; its inverse inserts 1. The balanced maps commute with
   restrictions and the differentials, giving BalancedNormalization.
7. Quotient reduction commutes with those formulas: q(pi_(n+1)(b)*a) equals
   pi_n(b)*q(a). Thus both isomorphisms and the augmentation form strict maps.
   On a pulled-back quotient-unit generator this gives pi_n(b), exactly the
   ordinary and derived finite evaluation normalizations fixed by the recorded
   completed-pullback and def-a1-integral-completed-pullback-interfaces APIs.
8. All maps are natural in chain maps. The localization equivalence of
   lem-weil-pbc-site-derived-tensor-descent uniquely extends them to all derived
   morphisms. Chain naturality also gives naturality for inverse resolving
   quasi-isomorphisms, proving independence of representatives and linearity.
9. In lem-weil-pbc-total-tensor-integer-shifts the first-variable tensor shift
   is unsigned. Termwise pullback shifts are identities on terms. Hence every
   arrow of the zigzag commutes with them on complexes. The canonical derived
   shift comparisons are their counit-normalized descents. Localize the chain
   equality to obtain sB after b(K[r]) = b(K)[r] after sV for every K and r. -/
theorem finite_pullback_strict_tower_comparison
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (Comparison l E g) := by
  obtain ⟨C⟩ := representative_comparison l E g hX hY
  obtain ⟨S⟩ := finite_pullback_strict_tower_shifts l E g C
  exact ⟨{
    B := C.B
    b := C.b
    reductionIso := C.reductionIso
    reduction_normalization := C.reduction_normalization
    koszulIso := C.koszulIso
    koszul_normalization := C.koszul_normalization
    balancedIso := C.balancedIso
    balanced_normalization := C.balanced_normalization
    pull_good := C.pull_good
    koszul_pull_good := C.koszul_pull_good
    middle_quasiIso := C.middle_quasiIso
    reductionH := C.reductionH
    reductionH_normalization := C.reductionH_normalization
    zigzag := C.zigzag
    reductionChainShift := S.reductionChainShift
    reductionChainShift_normalization := S.reductionChainShift_normalization
    reductionShift := S.reductionShift
    reductionShift_descent := S.reductionShift_descent
    towerShift := S.towerShift
    towerShift_descent := S.towerShift_descent
    finiteChainShift := S.finiteChainShift
    finiteChainShift_normalization := S.finiteChainShift_normalization
    finiteShift := S.finiteShift
    finiteShift_descent := S.finiteShift_descent
    shifts := S.shifts }⟩

end WeilConjectures.FinitePullbackStrictTower
