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
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.ConstructibleSheaf.StalkCardinality
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.AlgebraicGeometry.FiniteSystemCompletedTrivialization
import WeilConjectures.AlgebraicGeometry.FiniteTowerCompletedTensorLimit

/-! # A strict subargument of the finite local system limit model

The expanded scalar functors keep this proof module independent of the parent
module's convenience definitions. (blueprint: lem-zl-finite-local-system-limit-model-local) -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
open Scheme

/-- Local constancy makes the cardinality of the geometric fibre constant on a connected
base. One finite fibre therefore makes the underlying sheaf of sets finite locally constant.
The coefficient ring itself need not be finite. -/
private theorem set_flc_of_finite_fibre (Y : Scheme.{u}) [ConnectedSpace Y]
    {A : Type (u + 1)} [CommRing A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hLC : Scheme.IsLocallyConstantSheaf F)
    (hfinite : Finite (((pointSmallEtale y).sheafFiber
      (A := ModuleCat.{u + 1} A)).obj F)) : Scheme.IsSetFLC F := by
  let : Scheme.IsLocallyConstantSheaf F := hLC
  let x₀ : Y := y.base (IsLocalRing.closedPoint Ω)
  let F₀ := (pointSmallEtale (Y.algClosurePoint x₀)).sheafFiber
    (A := ModuleCat.{u + 1} A) |>.obj F
  have h₀ : Finite F₀ := by
    obtain ⟨e⟩ := Etale.nonempty_sheafFiber_iso_of_isLocallyConstantSheaf F y
      (Y.algClosurePoint x₀) (by rw [algClosurePoint_base])
    exact @Finite.of_equiv _ _ hfinite e.toLinearEquiv.toEquiv
  let card : Y → ℕ := fun x ↦ Nat.card
    ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} A) |>.obj F)
  have hc : IsLocallyConstant card := IsLocallyConstant.iff_isOpen_fiber.mpr
    (fun n ↦ Etale.isOpen_setOf_natCard_sheafFiber F n)
  have hfinite_alg (x : Y) : Finite
      ((pointSmallEtale (Y.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} A) |>.obj F) := by
    apply Nat.finite_of_card_ne_zero
    change card x ≠ 0
    rw [hc.apply_eq_of_preconnectedSpace x x₀]
    exact Nat.card_ne_zero.mpr ⟨inferInstance, h₀⟩
  have hfinite_all {K : Type u} [Field K] [IsSepClosed K]
      (s : Spec (CommRingCat.of K) ⟶ Y) : Finite
      ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A) |>.obj F) := by
    obtain ⟨e⟩ := Etale.nonempty_sheafFiber_iso_of_isLocallyConstantSheaf F s
      (Y.algClosurePoint (s.base (IsLocalRing.closedPoint K)))
      (by rw [algClosurePoint_base])
    exact @Finite.of_equiv _ _ (hfinite_alg _) e.toLinearEquiv.toEquiv.symm
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := hLC.nonempty_locallyConstantDatum
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ⟨fun K _ _ s ↦ ?_⟩⟩
  · have := h𝒰 i
    exact inferInstanceAs (((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} A))).obj
      (F.over _)).IsConstant _)
  · let e := ((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} A))).app F
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    exact @Finite.of_equiv _ _ (hfinite_all s) e.symm.toEquiv

private theorem over_preserves_limit (Y : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}) (V : Y.ProEt)
    (F : ℕᵒᵖ ⥤ SheafOfModules.{u + 1} R) :
    PreservesLimit F (SheafOfModules.overFunctor R V) where
  preserves {c} hc := ⟨by
    apply isLimitOfReflects (SheafOfModules.forget _)
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro W
    exact isLimitOfPreserves (SheafOfModules.evaluation R (op W.unop.left)) hc⟩

-- Fix the coefficient universe before elaborating scalar extension's instances.
private noncomputable def extension (Y : Scheme.{u})
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (a : R ⟶ S)
    (N : completedConstantModules Y R) : completedConstantModules Y S :=
  @SheafOfModules.changeOfRings.{u, u + 1, u + 1}
    Y.ProEt inferInstance (ProEt.topology Y) inferInstance
    (completedConstantAbLocallyBijective Y)
    (inferInstance : HasWeakSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1}) R S a N

private theorem local_model_of_singleton (Y : Scheme.{u})
    (A : Type u) [CommRing A]
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (a : proEtaleConstantRing Y A ⟶ R)
    (L : proEtaleRingModules Y R)
    (N : ModuleCat.{u + 1} (ULift.{u + 1} A))
    (hN : Module.FinitePresentation (ULift.{u + 1} A) N)
    (V : Y.ProEt) (f : V ⟶ ⊤_ Y.ProEt)
    (hf : Sieve.generate (Presieve.singleton f) ∈ Scheme.ProEt.topology Y (⊤_ Y.ProEt))
    (e : L.over V ≅
      (extension Y a (proEtaleConstantModuleSheaf Y A N)).over V) :
    HasFiniteConstantRingedLocalModel Y A R a L := by
  refine ⟨Sieve.generate (Presieve.singleton f), hf, ?_⟩
  rintro W g ⟨Z, h, k, hk, _⟩
  cases hk
  refine ⟨N, hN, ⟨?_⟩⟩
  exact ((SheafOfModules.overFunctorMap.{u + 1} ((adicLisseForget Y).obj R) h).app L).symm ≪≫
    (SheafOfModules.overMap.{u + 1} ((adicLisseForget Y).obj R) h).mapIso e ≪≫
      (SheafOfModules.overFunctorMap.{u + 1} ((adicLisseForget Y).obj R) h).app _

private theorem stalk_annihilated (Y : Scheme.{u})
    {A : Type (u + 1)} [CommRing A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (r : A) (h : ∀ (V : Y.Etaleᵒᵖ) (x : H.obj.obj V), r • x = 0)
    (x : ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} A)).obj H) :
    r • x = 0 := by
  have hz : r • 𝟙 H = (0 : H ⟶ H) := by
    ext V z
    exact h V z
  have hf := congrArg ((pointSmallEtale y).sheafFiber
    (A := ModuleCat.{u + 1} A)).map hz
  rw [GrothendieckTopology.Point.sheafFiber_map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at hf
  exact ConcreteCategory.congr_hom hf x

private theorem extension_obj (Y : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}} (a : R ⟶ S)
    (N : SheafOfModules.{u + 1} ((adicLisseForget Y).obj R)) :
    (completedConstantExtension Y a).obj N =
      extension Y a N := by
  let ab (T : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
      Abelian (completedConstantModules Y T) :=
    @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1}
      Y.ProEt inferInstance (ProEt.topology Y) ((adicLisseForget Y).obj T)
      (completedConstantAbSheafify Y) (completedConstantAbLocallyBijective Y)
  exact (@SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1,
    u + 1, u} Y.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
    (ProEt.topology Y) inferInstance (completedConstantAbLocallyBijective Y)
    (completedConstantAbSheafify Y) R S a
    (@HasDerivedCategory.standard.{u + 1, u + 2}
      (completedConstantModules Y R) inferInstance (ab R))
    (@HasDerivedCategory.standard.{u + 1, u + 2}
      (completedConstantModules Y S) inferInstance (ab S))).choose_spec.choose N

/-- A simultaneous constant covering and completed finite local model for the limit.
Source: blueprint latest, prop-zl-smooth-proper-relative-purity.proof.md, Step 1,
Passage to the limit (blueprint: lem-zl-finite-local-system-limit-model-local).

Proof: the private set_flc_of_finite_fibre shows that every H_n has finite locally
constant underlying set sheaf: the geometric fibre cardinality is locally constant,
hence constant on the connected base, and finite at y. The simultaneous completed-linear
trivialization (lem-zl-finite-system-completed-trivialization) then gives a pro-etale
object V whose singleton generates a covering sieve and a natural isomorphism e of the
localized towers M|_V and (H_y K)|_V. Annihilation by the uniformizer power passes to
the geometric fibres F = H_y because the fibre functor is linear (stalk_annihilated).
The finite-tower comparison (lem-zl-finite-tower-completed-tensor-limit) gives
t : lim(F K) iso K(lim F). Restriction over V preserves limits of module sheaves
(over_preserves_limit, checked through the forgetful functor and the jointly
reflecting evaluations); this with e and t gives the second and third displayed
isomorphisms. The coefficient ring is a DVR, hence Noetherian, so the finite module
lim F is finitely presented. extension_obj identifies the prescribed completed
extension with ordinary change of rings, and local_model_of_singleton pulls the
resulting isomorphism back along every map of the generated sieve, which gives the
finite constant ringed local model. Torsion and the zero module need no change. -/
theorem finite_local_system_limit_model_local_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [IsNoetherian Y] [ConnectedSpace Y]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (H : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} ((ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))))
    (_hLC : ∀ n : ℕ, Scheme.IsFiniteLocallyConstantSheaf (H.obj (op n)))
    (_hfinite : ∀ n : ℕ, Finite (((H ⋙ (Scheme.pointSmallEtale y).sheafFiber (A := ModuleCat.{u
    + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).obj (op n)))
    (_hkill : ∀ (n : ℕ) (V : Y.Etaleᵒᵖ) (x : (H.obj (op n)).obj.obj V),
      (ULift.up (Padic.coefficientExtensionUniformizer l E) : (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))) ^ (n + 1) • x = 0)
    (M : ℕᵒᵖ ⥤ Scheme.proEtaleRingModules Y ((Scheme.adicLisseCompletedRing Y (Ideal.span
    {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))))
    (_eM : M ⋙ (SheafOfModules.restrictScalars ((Scheme.adicLisseForget Y).map
    (Scheme.CompletedConstantReduction.base Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) ⋙ SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u +
    1})).app (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).inv ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology Y) (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))) ≅
      H ⋙ comparisonUpperStar (ModuleCat.{u + 1} ((ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))) Y)
    (_hN : Module.Finite ((ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
      (limit ((H ⋙ (Scheme.pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) : ModuleCat.{u + 1} ((ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) :
    (∃ (V : Y.ProEt) (f : V ⟶ ⊤_ Y.ProEt),
      Sieve.generate (Presieve.singleton f) ∈ Scheme.ProEt.topology Y (⊤_ Y.ProEt) ∧
      Nonempty (M ⋙ (SheafOfModules.overFunctor.{u + 1, u, u + 1, u + 1}
    ((Scheme.adicLisseForget Y).obj (Scheme.adicLisseCompletedRing Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) V) ≅
        (H ⋙ (Scheme.pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))) ⋙ (Scheme.adicLisseConstantModules Y (ULift.{u +
    1} (Padic.coefficientExtensionIntegers l E)) ⋙ Scheme.completedConstantExtension Y
    (Scheme.CompletedConstantReduction.base Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) ⋙ (SheafOfModules.overFunctor.{u + 1, u, u + 1,
    u + 1} ((Scheme.adicLisseForget Y).obj (Scheme.adicLisseCompletedRing Y (Ideal.span
    {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) V)) ∧
      Nonempty (((SheafOfModules.overFunctor.{u + 1, u, u + 1, u + 1} ((Scheme.adicLisseForget
    Y).obj (Scheme.adicLisseCompletedRing Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) V)).obj (limit M) ≅
        limit ((H ⋙ (Scheme.pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))) ⋙ (Scheme.adicLisseConstantModules Y (ULift.{u +
    1} (Padic.coefficientExtensionIntegers l E)) ⋙ Scheme.completedConstantExtension Y
    (Scheme.CompletedConstantReduction.base Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) ⋙ (SheafOfModules.overFunctor.{u + 1, u, u + 1,
    u + 1} ((Scheme.adicLisseForget Y).obj (Scheme.adicLisseCompletedRing Y (Ideal.span
    {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) V))) ∧
      Nonempty (limit ((H ⋙ (Scheme.pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))) ⋙
    (Scheme.adicLisseConstantModules Y (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
    ⋙ Scheme.completedConstantExtension Y (Scheme.CompletedConstantReduction.base Y (Ideal.span
    {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) ⋙ (SheafOfModules.overFunctor.{u + 1, u, u + 1,
    u + 1} ((Scheme.adicLisseForget Y).obj (Scheme.adicLisseCompletedRing Y (Ideal.span
    {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) V)) ≅
        ((SheafOfModules.overFunctor.{u + 1, u, u + 1, u + 1} ((Scheme.adicLisseForget Y).obj
    (Scheme.adicLisseCompletedRing Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) V)).obj (((Scheme.adicLisseConstantModules Y
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⋙ Scheme.completedConstantExtension
    Y (Scheme.CompletedConstantReduction.base Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))))).obj (limit ((H ⋙ (Scheme.pointSmallEtale
    y).sheafFiber (A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l
    E))))))))) ∧
    HasFiniteConstantRingedLocalModel Y (Padic.coefficientExtensionIntegers l E)
      ((Scheme.adicLisseCompletedRing Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) (Scheme.CompletedConstantReduction.base Y
    ((Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))))
      (limit M) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let I : Ideal A := Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}
  let R := adicLisseCompletedRing Y I
  let a := CompletedConstantReduction.base Y I
  let F := H ⋙ (pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} A)
  let K := adicLisseConstantModules Y A ⋙ completedConstantExtension Y a
  obtain ⟨V, f, hf, ⟨e⟩⟩ := finite_system_completed_trivialization
    l E Y Ω y H (fun n ↦ set_flc_of_finite_fibre Y Ω y (H.obj (op n))
      (_hLC n).toIsLocallyConstantSheaf (_hfinite n)) _hkill M _eM
  let L := SheafOfModules.overFunctor.{u + 1} ((adicLisseForget Y).obj R) V
  have hkill (n : ℕ) (x : F.obj (op n)) :
      (ULift.up (Padic.coefficientExtensionUniformizer l E) : A) ^ (n + 1) • x = 0 :=
    stalk_annihilated Y Ω y (H.obj (op n)) _ (_hkill n) x
  obtain ⟨t⟩ := finite_tower_completed_tensor_limit l E Y F _hfinite hkill _hN
  let : PreservesLimit M L := over_preserves_limit Y _ V M
  let : PreservesLimit (F ⋙ K) L := over_preserves_limit Y _ V (F ⋙ K)
  let e₂ : L.obj (limit M) ≅ limit (F ⋙ K ⋙ L) :=
    preservesLimitIso L M ≪≫ lim.mapIso e
  let e₃ : limit (F ⋙ K ⋙ L) ≅ L.obj (K.obj (limit F)) :=
    (preservesLimitIso L (F ⋙ K)).symm ≪≫ L.mapIso t
  refine ⟨⟨V, f, hf, ⟨e⟩, ⟨e₂⟩, ⟨e₃⟩⟩, ?_⟩
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  let : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) :=
    hdvr.2.2.2.2.2.2.2.1
  let : IsNoetherianRing A := isNoetherianRing_of_ringEquiv
    (Padic.coefficientExtensionIntegers l E) ULift.ringEquiv.symm
  let : Module.Finite A (limit F : ModuleCat.{u + 1} A) := _hN
  have hp : Module.FinitePresentation A (limit F : ModuleCat.{u + 1} A) :=
    Module.finitePresentation_of_finite A _
  let j : K.obj (limit F) ≅ extension Y a
      (proEtaleConstantModuleSheaf Y (Padic.coefficientExtensionIntegers l E) (limit F)) :=
    eqToIso (extension_obj Y a ((adicLisseConstantModules Y A).obj (limit F)))
  exact local_model_of_singleton Y (Padic.coefficientExtensionIntegers l E) R a
    (limit M) (limit F) hp V f hf (e₂ ≪≫ e₃ ≪≫ L.mapIso j)

end AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
