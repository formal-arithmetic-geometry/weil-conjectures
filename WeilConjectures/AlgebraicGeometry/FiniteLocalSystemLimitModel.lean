/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.MilnorTower
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.IndPrincipalZariski
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.AlgebraicGeometry.CompletedConstantRealizationDataSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReductionSupplement
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.ConstructibleSheaf.StalkCardinality
import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarMittagLeffler
import WeilConjectures.AlgebraicGeometry.FiniteLocalSystemLimitModelEpi
import WeilConjectures.AlgebraicGeometry.FiniteLocalSystemLimitModelLocalModel

/-! # Finite constant local models for limits of finite local systems

Source: blueprint latest, sec-zeta-weil/sk-prop-smooth-proper-purity,
prop-zl-smooth-proper-relative-purity.proof.md, Step 1, Passage to the limit
(blueprint: lem-zl-finite-local-system-limit-model).

We use the ringed-site presentation of pulled-back integral coefficients: the limit
of the positive finite constant quotient rings. The integral coefficient comparison
identifies this with p_Y^* underline(A). A localization at a covering site object is
inverse image along that object. Thus all the displayed local isomorphisms below
are isomorphisms over A restricted to that object, equivalently over A on its domain.
The natural isomorphism of diagrams expresses compatibility with every transition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit

open Scheme

/-- The scalar ring of integers, lifted to the coefficient universe of the site.
Source: blueprint Passage to the limit, coefficient convention
(blueprint: lem-zl-finite-local-system-limit-model). -/
abbrev Scalars (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :=
  ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)

/-- The uniformizer ideal in the lifted scalar ring. Source: blueprint Passage to the limit
(blueprint: lem-zl-finite-local-system-limit-model). -/
def ideal (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Ideal (Scalars l E) :=
  Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}

/-- The completed coefficient sheaf, using its finite-quotient presentation.
Source: blueprint Passage to the limit; det-prop-sfb-qlbar-colimit-x-integral-limit (3)
(blueprint: lem-zl-finite-local-system-limit-model). -/
abbrev coefficients (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{u}) :=
  Scheme.adicLisseCompletedRing Y (ideal l E)

/-- Forget completed scalars through the canonical constant-section map, keeping its
scalar action, and read the result as a fixed-scalar module-valued sheaf.
Source: blueprint Passage to the limit, A-linear transitions
(blueprint: lem-zl-finite-local-system-limit-model). -/
def scalarRestriction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{u}) :
    Scheme.proEtaleRingModules Y (coefficients l E Y) ⥤
      Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (Scalars l E)) :=
  SheafOfModules.restrictScalars ((Scheme.adicLisseForget Y).map
      (Scheme.CompletedConstantReduction.base Y (ideal l E))) ⋙
    SheafOfModules.restrictScalars
      ((constantCommuteCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (Scalars l E))).inv ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology Y) (Scalars l E)

/-- The actual tensor A_Y tensor_A N, extending the constant-section scalar action.
For a finite module annihilated by a positive uniformizer power this is its finite
constant sheaf with its residue action. Source: blueprint Passage to the limit
(blueprint: lem-zl-finite-local-system-limit-model). -/
def tensor (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{u}) :
    ModuleCat.{u + 1} (Scalars l E) ⥤
      Scheme.proEtaleRingModules Y (coefficients l E Y) :=
  Scheme.adicLisseConstantModules Y (Scalars l E) ⋙
    Scheme.completedConstantExtension Y (Scheme.CompletedConstantReduction.base Y (ideal l E))

/-- The diagram of geometric fibres, including the induced A-linear transition maps.
Source: blueprint Passage to the limit, N_n = (M_n)_y
(blueprint: lem-zl-finite-local-system-limit-model). -/
def fibres (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Scalars l E))) :
    ℕᵒᵖ ⥤ ModuleCat.{u + 1} (Scalars l E) :=
  H ⋙ (Scheme.pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} (Scalars l E))

/-- Restriction to a pro-etale object, with its restricted completed coefficient action.
Source: blueprint Passage to the limit; inverse image is localized-site restriction
(blueprint: lem-zl-finite-local-system-limit-model). -/
def localization (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) (V : Y.ProEt) :
    Scheme.proEtaleRingModules Y (coefficients l E Y) ⥤
      SheafOfModules.{u + 1} (((Scheme.adicLisseForget Y).obj (coefficients l E Y)).over V) :=
  SheafOfModules.overFunctor.{u + 1, u, u + 1, u + 1}
    ((Scheme.adicLisseForget Y).obj (coefficients l E Y)) V

private lemma finiteLocallyConstant_of_finite_fiber
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Scalars l E)))
    (hLC : Scheme.IsLocallyConstantSheaf F)
    (hfinite : Finite ((pointSmallEtale y).sheafFiber
      (A := ModuleCat.{u + 1} (Scalars l E)).obj F)) :
    Scheme.IsFiniteLocallyConstantSheaf F ∧
      ∀ x : Y, Finite ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} (Scalars l E)).obj F) := by
  let : Scheme.IsLocallyConstantSheaf F := hLC
  let : Finite ((pointSmallEtale y).sheafFiber
      (A := ModuleCat.{u + 1} (Scalars l E)) |>.obj F) := hfinite
  let x₀ : Y := y.base (IsLocalRing.closedPoint Ω)
  let F₀ := (pointSmallEtale (Y.algClosurePoint x₀)).sheafFiber
    (A := ModuleCat.{u + 1} (Scalars l E)).obj F
  let n₀ : ℕ := Nat.card F₀
  have h₀ : Finite F₀ := by
    obtain ⟨e⟩ :=
      Etale.nonempty_sheafFiber_iso_of_isLocallyConstantSheaf F y
        (Y.algClosurePoint x₀) (by rw [algClosurePoint_base])
    exact Finite.of_equiv _ e.toLinearEquiv.toEquiv
  have hn₀ : n₀ ≠ 0 := by
    apply Nat.card_ne_zero.mpr
    exact ⟨inferInstance, h₀⟩
  let S : Set Y := {x | Nat.card
    ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} (Scalars l E)).obj F) = n₀}
  have hSopen : IsOpen S := by
    exact Etale.isOpen_setOf_natCard_sheafFiber F n₀
  have hScompl : IsOpen Sᶜ := by
    have hEq : Sᶜ = ⋃ n : ℕ, {x : Y | Nat.card
        ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
          (A := ModuleCat.{u + 1} (Scalars l E)) |>.obj F) = n ∧ n ≠ n₀} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
      change Nat.card ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} (Scalars l E)) |>.obj F) ≠ n₀ ↔
        ∃ n : ℕ, Nat.card ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
          (A := ModuleCat.{u + 1} (Scalars l E)) |>.obj F) = n ∧ n ≠ n₀
      constructor
      · intro hx
        exact ⟨_, rfl, hx⟩
      · rintro ⟨n, hn, hne⟩
        exact fun heq ↦ hne (hn.symm.trans heq)
    rw [hEq]
    exact isOpen_iUnion fun n ↦ by
      by_cases hn : n = n₀
      · simp [hn]
      · rw [show {x : Y | Nat.card
          ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
            (A := ModuleCat.{u + 1} (Scalars l E)) |>.obj F) = n ∧ n ≠ n₀} =
          {x : Y | Nat.card ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
            (A := ModuleCat.{u + 1} (Scalars l E)) |>.obj F) = n} by
            ext x; simp [hn]]
        exact Etale.isOpen_setOf_natCard_sheafFiber F n
  have hSuniv : S = Set.univ := by
    apply IsClopen.eq_univ ⟨isOpen_compl_iff.mp hScompl, hSopen⟩
    refine ⟨x₀, ?_⟩
    change Nat.card F₀ = n₀
    rfl
  have hfinite_alg (x : Y) : Finite ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} (Scalars l E)) |>.obj F) := by
    have hx : x ∈ S := by rw [hSuniv]; trivial
    change Nat.card ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} (Scalars l E)) |>.obj F) = n₀ at hx
    apply Nat.finite_of_card_ne_zero
    rw [hx]
    exact hn₀
  let : Scheme.IsFiniteSheaf F := by
    constructor
    intro Ω' _ _ s
    let : Finite ((pointSmallEtale (Y.algClosurePoint
        (s.base (IsLocalRing.closedPoint Ω')))).sheafFiber
          (A := ModuleCat.{u + 1} (Scalars l E)) |>.obj F) := hfinite_alg _
    obtain ⟨e⟩ := Etale.nonempty_sheafFiber_iso_of_isLocallyConstantSheaf F s
      (Y.algClosurePoint (s.base (IsLocalRing.closedPoint Ω')))
      (by rw [algClosurePoint_base])
    let : Finite ((pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} (Scalars l E)) |>.obj F) :=
      Finite.of_equiv _ e.toLinearEquiv.toEquiv.symm
    exact (ModuleCat.isFinitelyGenerated_iff _).2 Module.Finite.of_finite
  exact ⟨{}, hfinite_alg⟩

/-- Finite locally constant towers have zero first Roos limit and a simultaneous finite
constant local model whenever the inverse limit of one geometric fibre is finite over A.
Source: blueprint latest, prop-zl-smooth-proper-relative-purity.proof.md, Step 1,
Passage to the limit (blueprint: lem-zl-finite-local-system-limit-model).

Proof: (1) For each n the private lemma finiteLocallyConstant_of_finite_fiber shows
that H_n is finite locally constant with finite stalks at every algebraically closed
point: the stalk cardinality is locally constant on the connected base, its level set
through the chosen point is clopen and nonempty, hence everything.
(2) The upstream theorem mittagLeffler_imageSubobject_of_iso_comparisonUpperStar (the
finite-image argument of cor-galois-lisse-representations transported by the exact
comparison inverse image, lem-pe-constant-left-module-inverse-image) gives the
image-subobject Mittag-Leffler condition for the scalar-restricted tower.
(3) lem-zl-finite-local-system-limit-model-epi turns it into epicity of 1-T, the
Roos vanishing clause of det-pe-milnor-sequence (2).
(4) lem-zl-finite-local-system-limit-model-local supplies the covering, the
simultaneous trivialization, the completed tensor comparison and the finite constant
ringed local model. Pair (3) and (4). -/
theorem finite_local_system_limit_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [IsNoetherian Y] [ConnectedSpace Y]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Scalars l E)))
    (_hLC : ∀ n : ℕ, Scheme.IsLocallyConstantSheaf (H.obj (op n)))
    (_hfinite : ∀ n : ℕ, Finite ((fibres l E Y Ω y H).obj (op n)))
    (_hkill : ∀ (n : ℕ) (V : Y.Etaleᵒᵖ) (x : (H.obj (op n)).obj.obj V),
      (ULift.up (Padic.coefficientExtensionUniformizer l E) : Scalars l E) ^ (n + 1) • x = 0)
    (M : ℕᵒᵖ ⥤ Scheme.proEtaleRingModules Y (coefficients l E Y))
    (_eM : M ⋙ scalarRestriction l E Y ≅
      H ⋙ comparisonUpperStar (ModuleCat.{u + 1} (Scalars l E)) Y)
    (_hN : Module.Finite (Scalars l E)
      (limit (fibres l E Y Ω y H) : ModuleCat.{u + 1} (Scalars l E))) :
    Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op)) ∧
    (∃ (V : Y.ProEt) (f : V ⟶ ⊤_ Y.ProEt),
      Sieve.generate (Presieve.singleton f) ∈ Scheme.ProEt.topology Y (⊤_ Y.ProEt) ∧
      Nonempty (M ⋙ localization l E Y V ≅
        fibres l E Y Ω y H ⋙ tensor l E Y ⋙ localization l E Y V) ∧
      Nonempty ((localization l E Y V).obj (limit M) ≅
        limit (fibres l E Y Ω y H ⋙ tensor l E Y ⋙ localization l E Y V)) ∧
      Nonempty (limit (fibres l E Y Ω y H ⋙ tensor l E Y ⋙ localization l E Y V) ≅
        (localization l E Y V).obj ((tensor l E Y).obj (limit (fibres l E Y Ω y H))))) ∧
    HasFiniteConstantRingedLocalModel Y (Padic.coefficientExtensionIntegers l E)
      (coefficients l E Y) (Scheme.CompletedConstantReduction.base Y (ideal l E))
      (limit M) := by
  have hFLC (n : ℕ) : Scheme.IsFiniteLocallyConstantSheaf (H.obj (op n)) :=
    (finiteLocallyConstant_of_finite_fiber y (H.obj (op n)) (_hLC n) (_hfinite n)).1
  let : ∀ n : ℕ, Scheme.IsFiniteLocallyConstantSheaf (H.obj (op n)) := hFLC
  have hfin (n : ℕ) (x : Y) : Finite ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} (Scalars l E)).obj (H.obj (op n))) :=
    (finiteLocallyConstant_of_finite_fiber y (H.obj (op n)) (_hLC n) (_hfinite n)).2 x
  have hML := mittagLeffler_imageSubobject_of_iso_comparisonUpperStar
    (M ⋙ scalarRestriction l E Y) (fun n ↦ H.obj (op n)) hfin
    (fun n ↦ (_eM.app (op n)).symm)
  exact ⟨finite_local_system_limit_model_epi l E Y M hML,
    finite_local_system_limit_model_local_model l E Y Ω y H hFLC _hfinite _hkill M _eM _hN⟩

end AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
