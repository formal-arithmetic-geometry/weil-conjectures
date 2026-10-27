module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Module.FinitePresentation
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicCoefficientDatum
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.Paper.ContinuousConstructibleModule
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback
public import Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension
public import Sheaf.Paper.ScalarExtensionDualTowerCore
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import all Sheaf.Algebra.Homology.LocallyFreeDerivedScalars
import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.LinearAlgebra.ScalarPresentationCokernel
import Sheaf.LinearAlgebra.RankNormalCokernel
import Sheaf.CategoryTheory.ConstantMatrixCokernelModels
import all Sheaf.CategoryTheory.ConstantScalarTowerComparison
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Field.ULift
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarDualEvaluationDescent
import all Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
import all Sheaf.CategoryTheory.SiteConstantModuleHom
import all Sheaf.Paper.PurInverseImageScalarComparison
import all Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison

import all Sheaf.Paper.LatticeCoefficientPullbackIso
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import all Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import all Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension


/-! # Rational finite free models on the original strata

Source: Bhatt--Scholze, Lemma 6.8.2, the paragraph before Definition 6.8.6,
Definition 6.8.10 and Proposition 6.8.14(2); Stacks, Tags 03EI, 03EK, 03EL and 03EP
(blueprint: lem-per-rational-stratum-finite-free-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.all false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
-- Repeated universe-polymorphic sheafification inference makes this linter expensive.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SheafOfModules
open AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ProEtale.RationalStratum

private instance stratumWeakAdd (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) AddCommGrpCat.{u + 1} := inferInstance

private instance stratumWeakRing (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) CommRingCat.{u + 1} := inferInstance

private instance stratumWeakNoncommRing (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) RingCat.{u + 1} := inferInstance

private instance stratumSheafifyAdd (S : Scheme.{u}) :
    HasSheafify (ProEt.topology S) AddCommGrpCat.{u + 1} := inferInstance

private instance stratumSheafifyRing (S : Scheme.{u}) :
    HasSheafify (ProEt.topology S) RingCat.{u + 1} := inferInstance

private instance stratumSheafifyCommRing (S : Scheme.{u}) :
    HasSheafify (ProEt.topology S) CommRingCat.{u + 1} := inferInstance

section Coefficients
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Integral scalars in the module universe. Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev A := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- Rational scalars in the module universe. Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev K := ULift.{u + 1, u} E

/-- The ordinary inclusion of coefficient rings. Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev inclusion : A l E →+* K E :=
  RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype

/-- Integral constant sections, using the existing constant-sheaf comparison.
Source: Bhatt--Scholze, Definition 6.8.10
(blueprint: lem-per-rational-stratum-finite-free-model). -/
def integralConstants (S : Scheme.{u}) :
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).obj (CommRingCat.of (A l E)) ⟶
      integralCoefficientSheaf l S E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientConstantComparison S (A l E)

/-- Rational constant sections, using the existing constant-sheaf comparison.
Source: Bhatt--Scholze, Definition 6.8.6
(blueprint: lem-per-rational-stratum-finite-free-model). -/
def rationalConstants (S : Scheme.{u}) :
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).obj (CommRingCat.of (K E)) ⟶
      rationalCoefficientSheaf l S E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientConstantComparison S (K E)

/-- Ordinary rationalization `E tensor_A N`. Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev vectorSpace (N : ModuleCat.{u + 1} (A l E)) : ModuleCat.{u + 1} (K E) :=
  (ModuleCat.extendScalars (inclusion l E)).obj N

/-- The specified integral local model, with the recorded constant module functor.
Source: Bhatt--Scholze, Definition 6.8.10
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev integralModel (S : Scheme.{u}) (N : ModuleCat.{u + 1} (A l E)) :
    Modules (integralCoefficientSheaf l S E) :=
  ConstantFiniteFreePresentationExtension.extension (ProEt.topology S) (A l E)
    (integralCoefficientSheaf l S E) (integralConstants l E S) N

/-- Scalar extension from the completed integral coefficient sheaf.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev rationalize (S : Scheme.{u}) (M : Modules (integralCoefficientSheaf l S E)) :
    Modules (rationalCoefficientSheaf l S E) :=
  changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (integralRationalCoefficientMap l E S) M

/-- The middle scalar model `E_S tensor_A N_S`.
Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.14(2)
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev directModel (S : Scheme.{u}) (N : ModuleCat.{u + 1} (A l E)) :
    Modules (rationalCoefficientSheaf l S E) :=
  ConstantFiniteFreePresentationExtension.extension (ProEt.topology S) (A l E)
    (rationalCoefficientSheaf l S E)
    (integralConstants l E S ≫ integralRationalCoefficientMap l E S) N

/-- The rational constant-module model `E_S tensor_E V_S`.
Source: Bhatt--Scholze, Definition 6.8.6 and Proposition 6.8.14(2)
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev rationalModel (S : Scheme.{u}) (V : ModuleCat.{u + 1} (K E)) :
    Modules (rationalCoefficientSheaf l S E) :=
  ConstantFiniteFreePresentationExtension.extension (ProEt.topology S) (K E)
    (rationalCoefficientSheaf l S E) (rationalConstants l E S) V

/-- The normalized first comparison is the existing balanced scalar-tower isomorphism.
Source: Stacks, Section 03EK; Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev reassociation (S : Scheme.{u}) (N : ModuleCat.{u + 1} (A l E)) :
    rationalize l E S (integralModel l E S N) ≅ directModel l E S N :=
  scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1}
    (integralConstants l E S) (integralRationalCoefficientMap l E S)
    ((constantModuleHomFunctor (ProEt.topology S) (A l E)).obj N)

/-- Integral restriction with the canonical continuous pullback of coefficient rings.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6
(blueprint: lem-per-rational-stratum-finite-free-model). -/
def integralPullback {S X : Scheme.{u}} (h : S ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (integralCoefficientSheaf l X E) ⟶ integralCoefficientSheaf l S E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (A l E) h

/-- Rational restriction with the canonical continuous pullback of coefficient rings.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6
(blueprint: lem-per-rational-stratum-finite-free-model). -/
def rationalPullback {S X : Scheme.{u}} (h : S ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l X E) ⟶ rationalCoefficientSheaf l S E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (K E) h

/-- Integral module restriction, transported along the canonical coefficient comparison.
Source: Bhatt--Scholze, Definition 6.8.10
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev restrictIntegral {S X : Scheme.{u}} (h : S ⟶ X)
    (M : Modules (integralCoefficientSheaf l X E)) :
    Modules (integralCoefficientSheaf l S E) :=
  changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (integralPullback l E h)
    ((proEtaleModuleInverseImage h (integralCoefficientSheaf l X E)).obj M)

/-- Rational module restriction, transported along the canonical coefficient comparison.
Source: Bhatt--Scholze, Definition 6.8.6
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev restrictRational {S X : Scheme.{u}} (h : S ⟶ X)
    (M : Modules (rationalCoefficientSheaf l X E)) :
    Modules (rationalCoefficientSheaf l S E) :=
  changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (rationalPullback l E h)
    ((proEtaleModuleInverseImage h (rationalCoefficientSheaf l X E)).obj M)

/-- The canonical ring map sending an ordinary rational scalar to a constant section.
Source: Bhatt--Scholze, Definition 6.8.1; Stacks 03EK
(blueprint: lem-per-rational-stratum-finite-free-model). -/
def constantSection (S : Scheme.{u}) (U : S.ProEtᵒᵖ) :
    K E →+* (rationalCoefficientSheaf l S E).obj.obj U := by
  letI := coefficientExtensionNormedField l E
  exact ContinuousMap.C

/-- The specified ordinary map from N to its rationalization, n mapped to 1 tensor n.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev vectorUnit (N : ModuleCat.{u + 1} (A l E)) (x : N) : vectorSpace l E N :=
  (ModuleCat.ExtendRestrictScalarsAdj.Unit.map.{u + 1, u + 1, u + 1} (inclusion l E)) x

/-- The finite power of the rational coefficient sheaf, including rank zero.
Source: Stacks 03EK; Bhatt--Scholze, Definition 6.8.6
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev freeModel (S : Scheme.{u}) (n : ℕ) : Modules (rationalCoefficientSheaf l S E) :=
  ConstantFiniteFreePresentationExtension.power.{u + 1, u} (ProEt.topology S)
    ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (rationalCoefficientSheaf l S E)) n

/-- Coordinates in the recorded finite power. Source: Stacks 03EK
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev coord (S : Scheme.{u}) (n : ℕ) (U : S.ProEtᵒᵖ)
    (x : (freeModel l E S n).val.obj U) (i : Fin n) :=
  ConstantFiniteFreePresentationExtension.commCoordinate.{u + 1, u} (ProEt.topology S)
    (rationalCoefficientSheaf l S E) n U x i

/-- An ordinary matrix interpreted as a morphism of finite free modules.
Source: Stacks, Algebra, Tag 00DF
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev matrixOverField {m n : ℕ} (D : Matrix (Fin n) (Fin m) (A l E)) :
    ModuleCat.of (K E) (Fin m → K E) ⟶ ModuleCat.of (K E) (Fin n → K E) :=
  ModuleCat.ofHom (Matrix.toLin' (D.map (inclusion l E)))

/-- The rectangular rank-normal matrix, with every zero-size case included.
Source: the finite-matrix calculation in Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-rational-stratum-finite-free-model). -/
def rankMatrix (m n ρ : ℕ) : Matrix (Fin n) (Fin m) (K E) :=
  fun i j ↦ if i.val = j.val ∧ i.val < ρ then 1 else 0

/-- Tail coordinates after an invertible row operation, retaining the case ρ = n.
Source: Stacks 03EK, finite cokernel calculation
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev tailIndex {n ρ : ℕ} (hρ : ρ ≤ n) (j : Fin (n - ρ)) : Fin n :=
  Fin.cast (Nat.add_sub_of_le hρ) (Fin.natAdd ρ j)

/-- Direct scalar-model maps, using the constant-module functor recorded by the dependency.
Source: Stacks 03EI and 03EK
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev directMap (S : Scheme.{u}) {N N' : ModuleCat.{u + 1} (A l E)} (f : N ⟶ N') :
    directModel l E S N ⟶ directModel l E S N' :=
  ConstantFiniteFreePresentationExtension.extensionMap (ProEt.topology S) (A l E)
    (rationalCoefficientSheaf l S E)
    (integralConstants l E S ≫ integralRationalCoefficientMap l E S) f

/-- Rational scalar-model maps. Source: Stacks 03EI and 03EK
(blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev rationalMap (S : Scheme.{u}) {V V' : ModuleCat.{u + 1} (K E)} (f : V ⟶ V') :
    rationalModel l E S V ⟶ rationalModel l E S V' :=
  ConstantFiniteFreePresentationExtension.extensionMap (ProEt.topology S) (K E)
    (rationalCoefficientSheaf l S E) (rationalConstants l E S) f

set_option backward.isDefEq.respectTransparency false in
private theorem constants_compatible (S : Scheme.{u}) (U : S.ProEtᵒᵖ) (r : A l E) :
    (scalarRingUnit (ProEt.topology S) (A l E) (rationalCoefficientSheaf l S E)
      (integralConstants l E S ≫ integralRationalCoefficientMap l E S)).app U r =
    (scalarRingUnit (ProEt.topology S) (K E) (rationalCoefficientSheaf l S E)
      (rationalConstants l E S)).app U (inclusion l E r) := by
  let := coefficientExtensionNormedField l E
  rw [scalarRingUnit_apply, scalarRingUnit_apply]
  change (integralRationalCoefficientMap l E S).hom.app U
      ((continuousCoefficientConstantComparison S (A l E)).hom.app U
        ((toSheafify (ProEt.topology S)
          ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (A l E)))).app U r)) = _
  have hA := congrArg (fun t ↦ t.app U r)
    (continuousCoefficientConstantComparison_unit S (A l E))
  have hK := congrArg (fun t ↦ t.app U (inclusion l E r))
    (continuousCoefficientConstantComparison_unit S (K E))
  change (continuousCoefficientConstantComparison S (A l E)).hom.app U
    ((toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (A l E)))).app U r) = _ at hA
  rw [hA]
  change _ = (continuousCoefficientConstantComparison S (K E)).hom.app U
    ((toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E)))).app U (inclusion l E r))
  rw [show (continuousCoefficientConstantComparison S (K E)).hom.app U
    ((toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E)))).app U (inclusion l E r)) =
    _ from hK]
  rfl


end Coefficients



section Coefficients
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] GenericScalar.scalarModelIso GenericScalar.scalarForward
  GenericScalar.scalarBackward GenericScalar.scalarForwardRaw GenericScalar.scalarBackwardRaw
  GenericScalar.backwardUnit GenericScalar.backwardLinear

/-- Both normalized scalar identifications, natural in finitely presented N.
The first is the existing scalar-tower isomorphism, not an arbitrary isomorphism.
The second is normalized on all local constant-module sections by n mapped to 1 tensor n.
Its naturality equation and the restriction of both isomorphisms to every slice retain
any chosen covering object.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2); Stacks 03EK and 0GMW
(blueprint: lem-per-rational-stratum-finite-free-model).

Proof: The first comparison is the scalar-tower isomorphism, whose pure-tensor
formula gives the first normalization. For the second comparison use the universal
property of scalar constant generators. The forward map sends a tensor n to
a tensor (1 tensor n). For the inverse, the ordinary extension/restriction adjunction
extends n mapped to 1 tensor n to a linear map from K tensor_A N on each object.
Compatibility of the constant coefficient units makes these maps balanced and
natural. The same universal properties prove the two inverse identities and
naturality in N. Applying overFunctor gives the comparisons on each specified slice.
No flatness of N is used. -/
theorem scalarModels (S : Scheme.{u}) :
    ∃ e : ∀ (N : ModuleCat.{u + 1} (A l E)) (_hN : Module.FinitePresentation (A l E) N),
        directModel l E S N ≅ rationalModel l E S (vectorSpace l E N),
      (∀ (N : ModuleCat.{u + 1} (A l E)) (_hN : Module.FinitePresentation (A l E) N)
        (U : S.ProEtᵒᵖ)
        (x : ((constantModuleHomFunctor (ProEt.topology S) (A l E)).obj N).val.obj U)
        (b : (integralCoefficientSheaf l S E).obj.obj U)
        (a : (rationalCoefficientSheaf l S E).obj.obj U),
        (reassociation l E S N).hom.val.app U
          (scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            (integralRationalCoefficientMap l E S) (integralModel l E S N) U a
            (scalarExtensionSection.{u + 1, u, u + 1, u + 1}
              (integralConstants l E S) _ U b x)) =
          scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            (integralConstants l E S ≫ integralRationalCoefficientMap l E S) _ U
            (a * (integralRationalCoefficientMap l E S).hom.app U b) x) ∧
      (∀ (N : ModuleCat.{u + 1} (A l E)) (hN : Module.FinitePresentation (A l E) N)
        (U : S.ProEtᵒᵖ) (x : N) (a : (rationalCoefficientSheaf l S E).obj.obj U),
        (e N hN).hom.val.app U
          (scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            (integralConstants l E S ≫ integralRationalCoefficientMap l E S) _ U a
            ((constantModuleHomUnit (ProEt.topology S) (A l E) N).app U x)) =
          scalarExtensionSection.{u + 1, u, u + 1, u + 1} (rationalConstants l E S) _ U a
            ((constantModuleHomUnit (ProEt.topology S) (K E) (vectorSpace l E N)).app U
              (vectorUnit l E N x))) ∧
      (∀ (N N' : ModuleCat.{u + 1} (A l E))
        (hN : Module.FinitePresentation (A l E) N)
        (hN' : Module.FinitePresentation (A l E) N') (f : N ⟶ N'),
        directMap l E S f ≫ (e N' hN').hom =
          (e N hN).hom ≫ rationalMap l E S ((ModuleCat.extendScalars (inclusion l E)).map f)) ∧
      (∀ (N : ModuleCat.{u + 1} (A l E)) (hN : Module.FinitePresentation (A l E) N)
        (U : S.ProEt),
        Nonempty ((rationalize l E S (integralModel l E S N)).over U ≅
          (rationalModel l E S (vectorSpace l E N)).over U)) := by
  obtain ⟨e, he, hn⟩ := GenericScalar.scalarModel_spec (constants_compatible l E S)
  refine ⟨fun N _ ↦ e N, ?_, ?_, ?_, ?_⟩
  · intro N _hN U x b a
    dsimp only [reassociation]
    rw [scalarExtensionTowerIso_hom.{u + 1, u, u + 1, u + 1}]
    exact scalarExtensionTowerForward_tmul.{u + 1, u, u + 1, u + 1}
      (integralConstants l E S) (integralRationalCoefficientMap l E S)
      ((constantModuleHomFunctor (ProEt.topology S) (A l E)).obj N) U a b x
  · intro N hN U x a
    exact he N U a x
  · intro N N' hN hN' f
    exact hn f
  · intro N hN U
    exact ⟨(overFunctor.{u + 1} _ U).mapIso
      (reassociation l E S N ≪≫ e N)⟩

/-- Pull a rational section back by precomposition with the base-change projection.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6
(blueprint: lem-per-rational-stratum-finite-free-model). -/
def rationalSection {S X : Scheme.{u}} (h : S ⟶ X) (V : X.ProEt)
    (a : (rationalCoefficientSheaf l X E).obj.obj (op V)) :
    (rationalCoefficientSheaf l S E).obj.obj (op ((proEtaleBaseChange h).obj V)) := by
  letI := coefficientExtensionNormedField l E
  exact (continuousCoefficientDirectMap (K E) h).hom.app (op V) a

/-- Rationalize a module morphism by the existing scalar-extension map.
Source: Stacks 03EK (blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev rationalizeMap (S : Scheme.{u})
    {M M' : Modules (integralCoefficientSheaf l S E)} (f : M ⟶ M') :
    rationalize l E S M ⟶ rationalize l E S M' :=
  changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
    (integralRationalCoefficientMap l E S) M f

/-- Restrict an integral module morphism by canonical inverse image and coefficient transport.
Source: Stacks 03D2 (blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev restrictIntegralMap {S X : Scheme.{u}} (h : S ⟶ X)
    {M M' : Modules (integralCoefficientSheaf l X E)} (f : M ⟶ M') :
    restrictIntegral l E h M ⟶ restrictIntegral l E h M' :=
  changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} (integralPullback l E h) _
    ((proEtaleModuleInverseImage h (integralCoefficientSheaf l X E)).map f)

/-- Restrict a rational module morphism by canonical inverse image and coefficient transport.
Source: Stacks 03D2 (blueprint: lem-per-rational-stratum-finite-free-model). -/
abbrev restrictRationalMap {S X : Scheme.{u}} (h : S ⟶ X)
    {M M' : Modules (rationalCoefficientSheaf l X E)} (f : M ⟶ M') :
    restrictRational l E h M ⟶ restrictRational l E h M' :=
  changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} (rationalPullback l E h) _
    ((proEtaleModuleInverseImage h (rationalCoefficientSheaf l X E)).map f)

attribute [local irreducible] Scheme.PurScalar.scalarIso proEtaleModuleInverseImage
attribute [local irreducible] scalarExtensionSection
  changeOfRingsHomOfUniverses

private theorem inverseSection_eq {S X : Scheme.{u}} (h : S ⟶ X)
    (R : Rings X) (M : Modules R) (V : X.ProEt) (x : M.val.obj (op V)) :
    purInverseImageSection h R M V x = inverseSection h M V x := by
  rfl

private theorem scalarSection_eq {S : Scheme.{u}} {R B : Rings S} (a : R ⟶ B)
    (M : Modules R) (V : S.ProEt) (b : B.obj.obj (op V)) (x : M.val.obj (op V)) :
    purScalarSection R B a M V b x =
      scalarExtensionSection.{u + 1, u, u + 1, u + 1} a M (op V) b x := by
  unfold purScalarSection scalarExtensionSection
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem inverseScalar_pure {S X : Scheme.{u}} (h : S ⟶ X)
    (R B : Rings X) (a : R ⟶ B) (M : Modules R) (V : X.ProEt)
    (b : B.obj.obj (op V)) (x : M.val.obj (op V)) :
    ((Scheme.PurScalar.scalarIso h R B a).hom.app M).val.app
      (op ((proEtaleBaseChange h).obj V))
        (purInverseImageSection h B _ V (purScalarSection R B a M V b x)) =
      purScalarSection _ _ ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a)
        ((proEtaleModuleInverseImage h R).obj M) ((proEtaleBaseChange h).obj V)
        (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app B).hom.app (op V) b)
        (purInverseImageSection h R M V x) := by
  let e : (proEtaleModuleInverseImage h B).obj
      (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M) ≅
      inverseImageScalarExtension h R B a M := (Scheme.PurScalar.scalarIso h R B a).app M
  erw [Scheme.PurScalar.scalarSection_one a M V b x,
    Scheme.PurScalar.inverseSection_smul h B _ V b
      (purScalarSection R B a M V 1 x)]
  have he := (e.hom.val.app (op ((proEtaleBaseChange h).obj V))).hom.map_smul
    ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app B).hom.app (op V)) b)
    (purInverseImageSection h B _ V (purScalarSection R B a M V 1 x))
  refine he.trans ?_
  refine (congrArg (fun z ↦
    ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app B).hom.app (op V)) b) • z)
      (Scheme.PurScalar.scalarIso_one h R B a M V x)).trans ?_
  exact (Scheme.PurScalar.scalarSection_one
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a)
    ((proEtaleModuleInverseImage h R).obj M) ((proEtaleBaseChange h).obj V) _
    (purInverseImageSection h R M V x)).symm

private theorem coefficientSquare {S X : Scheme.{u}} (h : S ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (integralRationalCoefficientMap l E X) ≫ rationalPullback l E h =
      integralPullback l E h ≫ integralRationalCoefficientMap l E S := by
  let := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback_naturality (inclusion l E)
    (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)) h

end Coefficients

section
namespace GenericTowers
variable {D : Type (u + 1)} [Category.{u} D] {J : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
private abbrev Rings := Sheaf J CommRingCat.{u + 1}
private abbrev Modules (R : Sheaf J CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
private def scalarCongrIso {R B : Sheaf J CommRingCat.{u + 1}} {a b : R ⟶ B}
    (ha : a = b) (M : Modules R) :
    changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M ≅
      changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} b M := by
  subst b
  exact Iso.refl _

private theorem scalarCongr_pure {R B : Sheaf J CommRingCat.{u + 1}} {a b : R ⟶ B}
    (ha : a = b) (M : Modules R) (U : Dᵒᵖ) (c : B.obj.obj U)
    (x : M.val.obj U) :
    (scalarCongrIso ha M).hom.val.app U
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} a M U c x) =
        scalarExtensionSection.{u + 1, u, u + 1, u + 1} b M U c x := by
  subst b
  rfl

attribute [local irreducible] scalarCongrIso

private theorem towerIso_inv {R B T : Sheaf J CommRingCat.{u + 1}} (a : R ⟶ B)
    (b : B ⟶ T) (M : Modules R) :
    (scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1} a b M).inv =
      scalarExtensionTowerReverse.{u + 1, u, u + 1, u + 1} a b M := by
  unfold scalarExtensionTowerIso
  rfl

private def towerSquare {R T C B : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ T) (b : T ⟶ B) (c : R ⟶ C) (d : C ⟶ B) (hs : a ≫ b = c ≫ d)
    (M : Modules R) :
    changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} b
      (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M) ≅
    changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} d
      (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} c M) :=
  scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1} a b M ≪≫
    scalarCongrIso hs M ≪≫
    (scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1} c d M).symm

private theorem towerSquare_all {R T C B : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ T) (b : T ⟶ B) (c : R ⟶ C) (d : C ⟶ B) (hs : a ≫ b = c ≫ d)
    (M : Modules R) (U : Dᵒᵖ) (r : B.obj.obj U) (t : T.obj.obj U) (x : M.val.obj U) :
    (towerSquare a b c d hs M).hom.val.app U
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} b _ U r
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} a M U t x)) =
      scalarExtensionSection.{u + 1, u, u + 1, u + 1} d _ U (r * b.hom.app U t)
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} c M U 1 x) := by
  dsimp only [towerSquare, Iso.trans_hom, Iso.symm_hom]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have h₁ : (scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1} a b M).hom.val.app U
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} b _ U r
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} a M U t x)) =
      scalarExtensionSection.{u + 1, u, u + 1, u + 1} (a ≫ b) M U (r * b.hom.app U t) x := by
    rw [scalarExtensionTowerIso_hom.{u + 1, u, u + 1, u + 1}
      (J := J) a b M]
    exact (scalarExtensionTowerForward_tmul.{u + 1, u, u + 1, u + 1}
      (J := J) a b M U r t x)
  let q := scalarCongrIso hs M
  let z := scalarExtensionSection.{u + 1, u, u + 1, u + 1} (a ≫ b) M U (r * b.hom.app U t) x
  refine (congrArg (fun y ↦ (scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1}
    c d M).inv.val.app U (q.hom.val.app U y)) h₁).trans ?_
  refine (congrArg (fun y ↦ (scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1}
    c d M).inv.val.app U y) (scalarCongr_pure hs M U (r * b.hom.app U t) x)).trans ?_
  rw [towerIso_inv c d M]
  exact scalarExtensionTowerReverse_tmul.{u + 1, u, u + 1, u + 1}
    (J := J) c d M U (r * b.hom.app U t) x

private theorem towerSquare_pure {R T C B : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ T) (b : T ⟶ B) (c : R ⟶ C) (d : C ⟶ B) (hs : a ≫ b = c ≫ d)
    (M : Modules R) (U : Dᵒᵖ) (t : T.obj.obj U) (x : M.val.obj U) :
    (towerSquare a b c d hs M).hom.val.app U
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} b _ U 1
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} a M U t x)) =
      scalarExtensionSection.{u + 1, u, u + 1, u + 1} d _ U (b.hom.app U t)
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} c M U 1 x) := by
  simpa only [one_mul] using towerSquare_all a b c d hs M U 1 t x

attribute [local irreducible] towerSquare

private theorem towerSquare_natural {R T C B : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ T) (b : T ⟶ B) (c : R ⟶ C) (d : C ⟶ B) (hs : a ≫ b = c ≫ d)
    {M N : Modules R} (f : M ⟶ N) :
    changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} b _
      (changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} a M f) ≫
        (towerSquare a b c d hs N).hom =
      (towerSquare a b c d hs M).hom ≫
        changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} d _
          (changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} c M f) := by
  apply scalarExtensionTower_hom_ext.{u + 1, u, u + 1, u + 1} a b M
  intro U r t x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [scalarExtension_map_tmul.{u + 1, u, u + 1, u + 1}
      (J := J) b
      (changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} a M f) U r _,
    scalarExtension_map_tmul.{u + 1, u, u + 1, u + 1}
      (J := J) a f U t x,
    towerSquare_all a b c d hs N U r t _, towerSquare_all a b c d hs M U r t x,
    scalarExtension_map_tmul.{u + 1, u, u + 1, u + 1}
      (J := J) d
      (changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} c M f) U _ _,
    scalarExtension_map_tmul.{u + 1, u, u + 1, u + 1}
      (J := J) c f U 1 x]

private def towerNatIso {R T C B : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ T) (b : T ⟶ B) (c : R ⟶ C) (d : C ⟶ B) (hs : a ≫ b = c ≫ d) :
    Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} a ⋙
      Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} b ≅
    Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} c ⋙
      Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} d :=
  NatIso.ofComponents (fun M ↦ towerSquare a b c d hs M)
    (fun f ↦ towerSquare_natural a b c d hs f)

end GenericTowers
end

section Coefficients
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] GenericTowers.towerSquare GenericTowers.scalarCongrIso
private theorem rationalPullback_unit {S X : Scheme.{u}} (h : S ⟶ X) (V : X.ProEt)
    (b : (rationalCoefficientSheaf l X E).obj.obj (op V)) :
    (rationalPullback l E h).hom.app (op ((proEtaleBaseChange h).obj V))
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app
        (rationalCoefficientSheaf l X E)).hom.app (op V) b) =
      rationalSection l E h V b := by
  let := coefficientExtensionNormedField l E
  have he := ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
    (continuousCoefficientDirectMap (K E) h)
  exact congrArg (fun d ↦ d.hom.app (op V) b) he

private def inverseSquareNatIso {S X : Scheme.{u}} (h : S ⟶ X)
    (R B : Rings X) (C D : Rings S) (a : R ⟶ B)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ⟶ C)
    (b : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj B ⟶ D) (d : C ⟶ D)
    (hs : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a ≫ b = c ≫ d)
 :
    Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} a ⋙ proEtaleModuleInverseImage h B ⋙
      Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} b ≅
    proEtaleModuleInverseImage h R ⋙ Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} c ⋙
      Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} d :=
  Functor.isoWhiskerRight (Scheme.PurScalar.scalarIso h R B a)
    (Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} b) ≪≫
  Functor.isoWhiskerLeft (proEtaleModuleInverseImage h R)
    (GenericTowers.towerNatIso
      ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a) b c d hs)

private def inverseSquareIso {S X : Scheme.{u}} (h : S ⟶ X)
    (R B : Rings X) (C D : Rings S) (a : R ⟶ B)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ⟶ C)
    (b : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj B ⟶ D) (d : C ⟶ D)
    (hs : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a ≫ b = c ≫ d)
    (M : Modules R) :
    changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} b
      ((proEtaleModuleInverseImage h B).obj
        (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M)) ≅
    changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} d
      (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} c
        ((proEtaleModuleInverseImage h R).obj M)) :=
  (inverseSquareNatIso h R B C D a c b d hs).app M

private theorem inverseSquareIso_pure {S X : Scheme.{u}} (h : S ⟶ X)
    (R B : Rings X) (C D : Rings S) (a : R ⟶ B)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ⟶ C)
    (b : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj B ⟶ D) (d : C ⟶ D)
    (hs : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a ≫ b = c ≫ d)
    (M : Modules R) (V : X.ProEt) (t : B.obj.obj (op V)) (x : M.val.obj (op V)) :
    (inverseSquareIso h R B C D a c b d hs M).hom.val.app
      (op ((proEtaleBaseChange h).obj V))
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} b _ (op ((proEtaleBaseChange h).obj V)) 1
        (purInverseImageSection h B _ V (purScalarSection R B a M V t x))) =
      scalarExtensionSection.{u + 1, u, u + 1, u + 1} d _ (op ((proEtaleBaseChange h).obj V))
        (b.hom.app (op ((proEtaleBaseChange h).obj V))
          (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app B).hom.app (op V) t))
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} c _ (op ((proEtaleBaseChange h).obj V)) 1
          (purInverseImageSection h R M V x)) := by
  let W := op ((proEtaleBaseChange h).obj V)
  let T := (proEtaleModuleInverseImage h R).obj M
  let q := GenericTowers.towerSquare ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a)
    b c d hs T
  let e : (proEtaleModuleInverseImage h B).obj
      (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M) ≅
      changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a) T :=
    (Scheme.PurScalar.scalarIso h R B a).app M
  let z := purInverseImageSection h B _ V (purScalarSection R B a M V t x)
  change q.hom.val.app W
    ((changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} b _ e.hom).val.app W
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} b _ W 1 z)) = _
  refine (congrArg (fun y ↦ q.hom.val.app W y)
    (scalarExtension_map_tmul.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology S) b e.hom W 1 z)).trans ?_
  have he := inverseScalar_pure h R B a M V t x
  refine (congrArg (fun y ↦ q.hom.val.app W
    (scalarExtensionSection.{u + 1, u, u + 1, u + 1} b _ W 1 y)) he).trans ?_
  rw [scalarSection_eq]
  exact GenericTowers.towerSquare_pure ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a)
    b c d hs T W
    ((((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app B).hom.app (op V)) t)
    (purInverseImageSection h R M V x)

private theorem inverseSquareIso_natural {S X : Scheme.{u}} (h : S ⟶ X)
    (R B : Rings X) (C D : Rings S) (a : R ⟶ B)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ⟶ C)
    (b : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj B ⟶ D) (d : C ⟶ D)
    (hs : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a ≫ b = c ≫ d)
    {M N : Modules R} (f : M ⟶ N) :
    changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} b _
      ((proEtaleModuleInverseImage h B).map
        (changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} a M f)) ≫
          (inverseSquareIso h R B C D a c b d hs N).hom =
      (inverseSquareIso h R B C D a c b d hs M).hom ≫
        changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} d _
          (changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} c _
            ((proEtaleModuleInverseImage h R).map f)) := by
  exact (inverseSquareNatIso h R B C D a c b d hs).hom.naturality f

private theorem inverseSquare_spec {S X : Scheme.{u}} (h : S ⟶ X)
    (R B : Rings X) (C D : Rings S) (a : R ⟶ B)
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ⟶ C)
    (b : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj B ⟶ D) (d : C ⟶ D)
    (hs : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map a ≫ b = c ≫ d)
 :
    ∃ e : ∀ M : Modules R,
    changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} b
      ((proEtaleModuleInverseImage h B).obj
        (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M)) ≅
    changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} d
      (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} c
        ((proEtaleModuleInverseImage h R).obj M)),
      (∀ (M : Modules R) (V : X.ProEt) (t : B.obj.obj (op V)) (x : M.val.obj (op V)),
    (e M).hom.val.app
      (op ((proEtaleBaseChange h).obj V))
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} b _ (op ((proEtaleBaseChange h).obj V)) 1
        (purInverseImageSection h B _ V (purScalarSection R B a M V t x))) =
      scalarExtensionSection.{u + 1, u, u + 1, u + 1} d _ (op ((proEtaleBaseChange h).obj V))
        (b.hom.app (op ((proEtaleBaseChange h).obj V))
          (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app B).hom.app (op V) t))
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} c _ (op ((proEtaleBaseChange h).obj V)) 1
          (purInverseImageSection h R M V x))) ∧
      (∀ {M N : Modules R} (f : M ⟶ N),
    changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} b _
      ((proEtaleModuleInverseImage h B).map
        (changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} a M f)) ≫
          (e N).hom =
      (e M).hom ≫
        changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} d _
          (changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1} c _
            ((proEtaleModuleInverseImage h R).map f))) := by
  refine ⟨inverseSquareIso h R B C D a c b d hs, ?_, ?_⟩
  · intro M V t x
    exact inverseSquareIso_pure h R B C D a c b d hs M V t x
  · intro M N f
    exact inverseSquareIso_natural h R B C D a c b d hs f

attribute [local irreducible] inverseSquareIso

/-- Rationalization commutes naturally with immersion restriction, including localization
units, with the specified formula on original pulled-back pure tensors.
Source: Bhatt--Scholze, paragraph before Definition 6.8.6; Stacks 03EL
(blueprint: lem-per-rational-stratum-finite-free-model).

Proof: The inverse-image scalar comparison is constructed by its adjunction.
Its equation on a general pure tensor follows from its equation at scalar 1 and
linearity. The coefficient pullback square commutes by naturality of continuous
coefficient maps. Two scalar-tower isomorphisms transport the inverse-image
comparison across this square. Their pure-tensor formulas and the coefficient
adjunction unit give the displayed normalization. Naturality of each comparison
gives the morphism equation. Applying overFunctor gives the specified slice. -/
theorem immersionComparison (X : Scheme.{u}) [IsNoetherian X]
    {S : Scheme.{u}} (h : S ⟶ X) [IsImmersion h] :
    ∃ e : ∀ M : Modules (integralCoefficientSheaf l X E),
        restrictRational l E h (rationalize l E X M) ≅
          rationalize l E S (restrictIntegral l E h M),
      (∀ (M : Modules (integralCoefficientSheaf l X E)) (V : X.ProEt)
        (a : (rationalCoefficientSheaf l X E).obj.obj (op V)) (x : M.val.obj (op V)),
        (e M).hom.val.app (op ((proEtaleBaseChange h).obj V))
          (scalarExtensionSection.{u + 1, u, u + 1, u + 1} (rationalPullback l E h) _
            (op ((proEtaleBaseChange h).obj V)) 1
            (inverseSection h (rationalize l E X M) V
              (scalarExtensionSection.{u + 1, u, u + 1, u + 1}
                (integralRationalCoefficientMap l E X) M (op V) a x))) =
          scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            (integralRationalCoefficientMap l E S) (restrictIntegral l E h M)
            (op ((proEtaleBaseChange h).obj V)) (rationalSection l E h V a)
            (scalarExtensionSection.{u + 1, u, u + 1, u + 1} (integralPullback l E h) _
              (op ((proEtaleBaseChange h).obj V)) 1 (inverseSection h M V x))) ∧
      (∀ (M M' : Modules (integralCoefficientSheaf l X E)) (f : M ⟶ M'),
        restrictRationalMap l E h (rationalizeMap l E X f) ≫ (e M').hom =
          (e M).hom ≫ rationalizeMap l E S (restrictIntegralMap l E h f)) ∧
      (∀ (M : Modules (integralCoefficientSheaf l X E)) (U : S.ProEt),
        Nonempty ((restrictRational l E h (rationalize l E X M)).over U ≅
          (rationalize l E S (restrictIntegral l E h M)).over U)) := by
  obtain ⟨e, he, hn⟩ := inverseSquare_spec h (integralCoefficientSheaf l X E)
    (rationalCoefficientSheaf l X E) (integralCoefficientSheaf l S E)
    (rationalCoefficientSheaf l S E) (integralRationalCoefficientMap l E X)
    (integralPullback l E h) (rationalPullback l E h)
    (integralRationalCoefficientMap l E S) (coefficientSquare l E h)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro M V a x
    have hh := he M V a x
    simp only [scalarSection_eq, inverseSection_eq] at hh
    refine hh.trans ?_
    exact congrArg (fun z ↦ scalarExtensionSection.{u + 1, u, u + 1, u + 1}
      (integralRationalCoefficientMap l E S) _ (op ((proEtaleBaseChange h).obj V)) z
      (scalarExtensionSection.{u + 1, u, u + 1, u + 1} (integralPullback l E h) _
        (op ((proEtaleBaseChange h).obj V)) 1 (inverseSection h M V x)))
      (rationalPullback_unit l E h V a)
  · intro M N f
    exact hn f
  · intro M U
    exact ⟨(overFunctor.{u + 1} _ U).mapIso (e M)⟩


end Coefficients

section Coefficients
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem rationalConstant_eq (S : Scheme.{u}) (U : S.ProEtᵒᵖ) (a : K E) :
    (rationalConstants l E S).hom.app U
      ((toSheafify (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E)))).app U a) =
      constantSection l E S U a := by
  let := coefficientExtensionNormedField l E
  exact congrArg (fun t ↦ t.app U a)
    (continuousCoefficientConstantComparison_unit S (K E))

/-- The specified finite-presentation cokernels, and their specified changes of basis.
Neither the presentation arrow nor N is assumed injective, flat or torsion-free.
Source: Bhatt--Scholze, Proposition 6.8.14(2), finite-presentation calculation;
Stacks 03EI, 03EK, 03EP and 00DF
(blueprint: lem-per-rational-stratum-finite-free-model).

Proof: Ordinary extension of scalars preserves the specified presentation cokernel
by its left adjunction. TensorProduct.piScalarRight identifies the finite powers and
pins the quotient map on the original vectors. Constant module realization preserves
finite colimits, detected on underlying additive sheaves; scalar extension preserves
them by its adjunction. Conjugation by the normalized beta isomorphisms therefore
gives the specified sheaf cokernel and the matrix entries as constant sections.
For every supplied PDQ = diag(I_rho,0), tail extraction has kernel the image of the
rank matrix and is surjective by zero padding. Transport its cokernel isomorphism
through the given invertible row and column operations, then through realization.
The same coordinate formulas give both inverse matrices and the specified tail map.
Empty matrices and rho = n use the identical finite-index formulas. Restricting the
constructed isomorphisms by overFunctor retains every specified covering object. -/
theorem presentationModels (S : Scheme.{u}) (N : ModuleCat.{u + 1} (A l E))
    [Module.FinitePresentation (A l E) N] (m n : ℕ)
    (D : Matrix (Fin n) (Fin m) (A l E))
    (q : ModuleCat.of (A l E) (Fin n → A l E) ⟶ N)
    (_exact : Function.Exact (Matrix.toLin' D) q) (_surj : Function.Surjective q) :
    ∃ (dS : freeModel l E S m ⟶ freeModel l E S n)
      (pE : ModuleCat.of (K E) (Fin n → K E) ⟶ vectorSpace l E N)
      (pS : freeModel l E S n ⟶ directModel l E S N)
      (v : vectorSpace l E N ≅ cokernel (matrixOverField l E D))
      (w : directModel l E S N ≅ cokernel dS),
      (∀ j : Fin n, pE (Pi.single j 1) = vectorUnit l E N (q (Pi.single j 1))) ∧
      pE ≫ v.hom = cokernel.π (matrixOverField l E D) ∧
      pS ≫ w.hom = cokernel.π dS ∧
      (∀ (U : S.ProEtᵒᵖ) (x : (freeModel l E S m).val.obj U) (i : Fin n),
        coord l E S n U (dS.val.app U x) i = ∑ j : Fin m,
          constantSection l E S U (inclusion l E (D i j)) * coord l E S m U x j) ∧
      (∀ (U : S.ProEtᵒᵖ) (x : Fin n → A l E),
        ∃ y : (freeModel l E S n).val.obj U,
          (∀ i : Fin n, coord l E S n U y i =
            constantSection l E S U (inclusion l E (x i))) ∧
          pS.val.app U y = scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            (integralConstants l E S ≫ integralRationalCoefficientMap l E S) _ U 1
            ((constantModuleHomUnit (ProEt.topology S) (A l E) N).app U (q x))) ∧
      (∀ (ρ : ℕ) (hρn : ρ ≤ n) (_hρm : ρ ≤ m)
        (P : Matrix.GeneralLinearGroup (Fin n) (K E))
        (Q : Matrix.GeneralLinearGroup (Fin m) (K E)),
        (P : Matrix (Fin n) (Fin n) (K E)) * D.map (inclusion l E) *
            (Q : Matrix (Fin m) (Fin m) (K E)) = rankMatrix E m n ρ →
        ∃ (p : freeModel l E S n ≅ freeModel l E S n)
          (q' : freeModel l E S m ≅ freeModel l E S m)
          (a : cokernel (matrixOverField l E D) ≅
            ModuleCat.of (K E) (Fin (n - ρ) → K E))
          (b : cokernel dS ≅ freeModel l E S (n - ρ)),
          (∀ (U : S.ProEtᵒᵖ) (x : (freeModel l E S n).val.obj U) (i : Fin n),
            coord l E S n U (p.hom.val.app U x) i = ∑ j : Fin n,
              constantSection l E S U ((P : Matrix (Fin n) (Fin n) (K E)) i j) *
                coord l E S n U x j) ∧
          (∀ (U : S.ProEtᵒᵖ) (x : (freeModel l E S n).val.obj U) (i : Fin n),
            coord l E S n U (p.inv.val.app U x) i = ∑ j : Fin n,
              constantSection l E S U ((P⁻¹ : Matrix.GeneralLinearGroup (Fin n) (K E)) i j) *
                coord l E S n U x j) ∧
          (∀ (U : S.ProEtᵒᵖ) (x : (freeModel l E S m).val.obj U) (i : Fin m),
            coord l E S m U (q'.hom.val.app U x) i = ∑ j : Fin m,
              constantSection l E S U ((Q : Matrix (Fin m) (Fin m) (K E)) i j) *
                coord l E S m U x j) ∧
          (∀ (U : S.ProEtᵒᵖ) (x : (freeModel l E S m).val.obj U) (i : Fin m),
            coord l E S m U (q'.inv.val.app U x) i = ∑ j : Fin m,
              constantSection l E S U ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) (K E)) i j) *
                coord l E S m U x j) ∧
          (∀ (x : Fin n → K E) (j : Fin (n - ρ)),
            a.hom (cokernel.π (matrixOverField l E D) x) j =
              ((P : Matrix (Fin n) (Fin n) (K E)).mulVec x) (tailIndex hρn j)) ∧
          (∀ (U : S.ProEtᵒᵖ) (x : (freeModel l E S n).val.obj U) (j : Fin (n - ρ)),
            coord l E S (n - ρ) U (b.hom.val.app U ((cokernel.π dS).val.app U x)) j =
              coord l E S n U (p.hom.val.app U x) (tailIndex hρn j)) ∧
          (∀ U : S.ProEt,
            Nonempty ((directModel l E S N).over U ≅ (freeModel l E S (n - ρ)).over U))) := by
  obtain ⟨pE, v, hpE, hv⟩ := ModuleCat.scalarPresentationCokernel
    (inclusion l E) N m n D q _exact _surj
  obtain ⟨dS, pB, wB, hwB, hdS, hgen, htail⟩ :=
    ConstantFiniteFreePresentationExtension.constantMatrixCokernelModels
      (ProEt.topology S) (K E) (rationalCoefficientSheaf l S E)
      (rationalConstants l E S) (vectorSpace l E N) m n (D.map (inclusion l E)) pE v hv
  obtain ⟨c, _, hc, _, _⟩ := scalarModels l E S
  let e := c N inferInstance
  let pS := pB ≫ e.inv
  let w := e ≪≫ wB
  refine ⟨dS, pE, pS, v, w, ?_, hv, ?_, ?_, ?_, ?_⟩
  · intro j
    have hh := hpE (Pi.single j 1)
    have hs : (fun i : Fin n ↦ inclusion l E
        ((Pi.single j 1 : Fin n → A l E) i)) = (Pi.single j 1 : Fin n → K E) := by
      funext i
      by_cases h : i = j <;> simp [Pi.single_apply, h]
    rw [hs] at hh
    exact hh
  · change (pB ≫ e.inv) ≫ e.hom ≫ wB.hom = _
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hwB
  · intro U x i
    simpa only [coord, Matrix.map_apply, rationalConstant_eq] using hdS U x i
  · intro U x
    obtain ⟨y, hy, hpy⟩ := hgen U (fun i ↦ inclusion l E (x i))
    refine ⟨y, ?_, ?_⟩
    · intro i
      exact (hy i).trans (rationalConstant_eq l E S U _)
    · have hg := hc N inferInstance U (q x) 1
      change e.hom.val.app U
        (scalarConstantGenerator (ProEt.topology S) (A l E)
          (rationalCoefficientSheaf l S E)
          (integralConstants l E S ≫ integralRationalCoefficientMap l E S) N U 1 (q x)) =
        scalarConstantGenerator (ProEt.topology S) (K E)
          (rationalCoefficientSheaf l S E) (rationalConstants l E S)
          (vectorSpace l E N) U 1 (vectorUnit l E N (q x)) at hg
      rw [hpE x] at hpy
      change e.inv.val.app U (pB.val.app U y) = _
      rw [hpy, ← hg]
      exact ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.val.app U) e.hom_inv_id) _
  · intro ρ hρn hρm P Q hnorm
    obtain ⟨a, ha⟩ := Matrix.rankNormalCokernel (D.map (inclusion l E))
      hρn hρm P Q hnorm
    obtain ⟨p, q', b, hp, hpi, hq, hqi, hb⟩ :=
      htail (n - ρ) (tailIndex hρn) P Q a ha
    refine ⟨p, q', a, b, ?_, ?_, ?_, ?_, ha, hb, ?_⟩
    · intro U x i
      simpa only [rationalConstant_eq] using hp U x i
    · intro U x i
      simpa only [rationalConstant_eq] using hpi U x i
    · intro U x i
      simpa only [rationalConstant_eq] using hq U x i
    · intro U x i
      simpa only [rationalConstant_eq] using hqi U x i
    · intro U
      exact ⟨(overFunctor.{u + 1} _ U).mapIso (w ≪≫ b)⟩

/-- The lattice presentation of rational continuous coefficients with their prescribed norm.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-per-rational-stratum-finite-free-model). -/
def rationalLatticeRing (X : Scheme.{u}) : Rings X := by
  letI := coefficientExtensionNormedField l E
  exact latticeCoefficientSheaf X E

/-- Commute continuous functions with the universe lift, by the pointwise maps.
This transports to the coefficient presentation used by the recorded constructibility notion.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-per-rational-stratum-finite-free-model). -/
def rationalLatticeRingIso (X : Scheme.{u}) :
    rationalCoefficientSheaf l X E ≅ rationalLatticeRing l E X := by
  letI := coefficientExtensionNormedField l E
  exact
    { hom := ⟨{
        app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun f ↦ ULift.up
              ⟨fun x ↦ (f x).down, continuous_uliftDown.comp f.continuous⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun f ↦
              ⟨fun x ↦ ULift.up (f.down x), continuous_uliftUp.comp f.down.continuous⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by ext V f; rfl
      inv_hom_id := by ext V f; rfl }

/-- The recorded rational constructibility predicate after the explicit pointwise coefficient
isomorphism. This abbreviation makes no new constructibility notion.
Source: Bhatt--Scholze, Definitions 6.8.6 and 6.8.10
(blueprint: lem-per-rational-stratum-finite-free-model). -/
def rationalConstructible (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Modules (rationalCoefficientSheaf l X E)) : Prop := by
  letI := coefficientExtensionNormedField l E
  exact IsContinuousConstructible X E
    ((restrictScalars ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (rationalLatticeRingIso l E X).inv)).obj M)

private theorem presentation_eq (X : Scheme.{u}) :
    letI := coefficientExtensionNormedField l E
    coefficientPresentation X (RingEquiv.refl E) continuous_id continuous_id =
      (rationalLatticeRingIso l E X).symm := by
  let := coefficientExtensionNormedField l E
  apply Iso.ext
  ext U s
  rfl

set_option backward.isDefEq.respectTransparency false in
private def rationalRestrictionComparison (X : Scheme.{u}) [IsNoetherian X]
    {S : Scheme.{u}} (h : S ⟶ X) [IsImmersion h]
    (M : Modules (rationalCoefficientSheaf l X E)) :
    letI := coefficientExtensionNormedField l E
    continuousModulePullback h E
        ((proEtaleRingRestrictScalars (rationalLatticeRingIso l E X).inv).obj M) ≅
      (proEtaleRingRestrictScalars (rationalLatticeRingIso l E S).inv).obj
        (restrictRational l E h M) := by
  letI := coefficientExtensionNormedField l E
  have hi : IsIso (rationalPullback l E h) :=
    (continuousCoefficientPullback_isIso l E X h).2
  have hK : IsIso (continuousCoefficientPullback (ULift.{u + 1} E) h) := hi
  have := coefficientPresentation_isIso h (RingEquiv.refl E) continuous_id continuous_id
  let cR := asIso (continuousCoefficientInverseImageMap h E)
  let cS := asIso (rationalPullback l E h)
  have hs : cR.hom ≫ (rationalLatticeRingIso l E S).inv =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (rationalLatticeRingIso l E X).inv ≫ cS.hom := by
    have he := coefficientPresentation_pullback h (RingEquiv.refl E)
      continuous_id continuous_id
    rw [presentation_eq l E X, presentation_eq l E S] at he
    exact he.symm
  have := proEtaleRingRestrictionPullbackInv_isIso h
    (rationalLatticeRing l E X) (rationalCoefficientSheaf l X E)
    (rationalLatticeRing l E S) (rationalCoefficientSheaf l S E)
    (rationalLatticeRingIso l E X).inv (rationalLatticeRingIso l E S).inv cR cS hs
  exact asIso ((proEtaleRingRestrictionPullbackInv h
    (rationalLatticeRing l E X) (rationalCoefficientSheaf l X E)
    (rationalLatticeRing l E S) (rationalCoefficientSheaf l S E)
    (rationalLatticeRingIso l E X).inv (rationalLatticeRingIso l E S).inv cR cS hs).app M)

set_option backward.isDefEq.respectTransparency false in
private def constantComparison (S : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    (N : ModuleCat.{u + 1} R) :
    (adicLisseConstantModules S R).obj N ≅
      (constantModuleHomFunctor (ProEt.topology S) R).obj N := by
  let J := ProEt.topology S
  let η := toSheafify J ((Functor.const S.ProEtᵒᵖ).obj (RingCat.of R))
  let θ := adicLisseConstantUnit S R
  let c := (constantModuleHomRingIso J R).inv
  have hs : θ ≫ c.hom = η := by
    apply (cancel_mono (constantModuleHomRingIso J R).hom.hom).mp
    rw [Category.assoc]
    change θ ≫ ((constantModuleHomRingIso J R).inv ≫
      (constantModuleHomRingIso J R).hom).hom = _
    rw [Iso.inv_hom_id]
    change θ ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact (sheafComposeNatTrans_fac J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      (sheafificationAdjunction J CommRingCat.{u + 1})
      (sheafificationAdjunction J RingCat.{u + 1})
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of R))).symm
  let P := (siteConstantModulePresheafGeneral (C := S.ProEt) R).obj N
  let f := moduleSheafificationComparison J θ η c hs P
  have : IsIso f := moduleSheafificationComparison_isIso J θ η c hs P
  exact asIso f

private def scalarTransport (S : Scheme.{u}) {R T B : Rings S}
    (a : R ⟶ T) (b : R ⟶ B) (e : T ≅ B) (he : a ≫ e.hom = b)
    (M : Modules R) :
    changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} b M ≅
      (restrictScalars ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.inv)).obj
        (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M) := by
  let J := ProEt.topology S
  let F := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let t := coefficientTensorPresheafIso.{u} J b a (Iso.refl R) e he M
  exact (PresheafOfModules.sheafification.{u + 1} (R := F.obj B) (𝟙 _)).mapIso t ≪≫
    pushforwardSheafificationIso.{u} J J (𝟭 S.ProEt) (F.obj T) (F.obj B)
      (F.map e.inv) (changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} a M)

private theorem constantSquare (S : Scheme.{u}) :
    letI := coefficientExtensionNormedField l E
    rationalConstants l E S ≫ (rationalLatticeRingIso l E S).hom =
      continuousCoefficientConstantMap S E := by
  let := coefficientExtensionNormedField l E
  let J := ProEt.topology S
  let adj := sheafificationAdjunction J CommRingCat.{u + 1}
  apply (adj.homEquiv _ _).injective
  change toSheafify J ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E))) ≫
    ((rationalConstants l E S) ≫ (rationalLatticeRingIso l E S).hom).hom = _
  change (toSheafify J ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E))) ≫
    (rationalConstants l E S).hom) ≫ (rationalLatticeRingIso l E S).hom.hom = _
  change (toSheafify (ProEt.topology S)
    ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E))) ≫
      (continuousCoefficientConstantComparison S (K E)).hom) ≫ _ = _
  rw [continuousCoefficientConstantComparison_unit S (K E)]
  change _ = (adj.homEquiv
    ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E)))
    (latticeCoefficientSheaf S E))
    ((adj.homEquiv ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E)))
      (latticeCoefficientSheaf S E)).symm
        (AlgebraicGeometry.ProEtale.continuousCoefficientConstants S E))
  rw [Equiv.apply_symm_apply]
  rfl

private def rationalFreeTransport (S : Scheme.{u}) (r : ℕ) :
    letI := coefficientExtensionNormedField l E
    (restrictScalars ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (rationalLatticeRingIso l E S).inv)).obj (freeModel l E S r) ≅
      continuousCoefficientModule S E (ModuleCat.of (K E) (Fin r → K E)) := by
  letI := coefficientExtensionNormedField l E
  let P := ModuleCat.of (K E) (Fin r → K E)
  let F := Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} (rationalConstants l E S)
  let H := restrictScalars ((sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (rationalLatticeRingIso l E S).inv)
  let t := scalarTransport S (rationalConstants l E S)
    (continuousCoefficientConstantMap S E) (rationalLatticeRingIso l E S)
    (constantSquare l E S) ((adicLisseConstantModules S (K E)).obj P)
  let β := ConstantFiniteFreePresentationExtension.beta (ProEt.topology S) (K E)
    (rationalCoefficientSheaf l S E) (rationalConstants l E S)
  exact H.mapIso (β r).symm ≪≫
    (H.mapIso (F.mapIso (constantComparison S (K E) P))).symm ≪≫ t.symm

private theorem finiteFreeConstructible (X : Scheme.{u}) [IsNoetherian X]
    (M : Modules (rationalCoefficientSheaf l X E))
    (s : Scheme.FiniteLocallyClosedStratification X)
    (I : ∀ k : Fin s.n, Type (u + 1)) (U : ∀ k : Fin s.n, I k → (s.domain k).ProEt)
    (hcover : ∀ k : Fin s.n, (ProEt.topology (s.domain k)).CoversTop (U k))
    (hmodel : ∀ (k : Fin s.n) (i : I k), ∃ r : ℕ,
      Nonempty ((restrictRational l E (s.immersion k) M).over (U k i) ≅
        (freeModel l E (s.domain k) r).over (U k i))) :
    rationalConstructible l E X M := by
  let := coefficientExtensionNormedField l E
  let t : Scheme.Stratification X :=
    { n := s.n
      stratum := s.stratum
      isLocallyClosed_stratum := s.isLocallyClosed_stratum
      isConstructible_stratum := fun i ↦
        (s.isLocallyClosed_stratum i).isConstructible_of_noetherianSpace
      iUnion_stratum_eq_univ := s.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := s.pairwise_disjoint_stratum
      domain := s.domain
      immersion := s.immersion
      isImmersion := s.isImmersion
      range_immersion := s.range_immersion }
  refine ⟨t, fun k ↦ ⟨I k, U k, hcover k, fun i ↦ ?_⟩⟩
  obtain ⟨r, ⟨e⟩⟩ := hmodel k i
  let := s.isImmersion k
  refine ⟨ModuleCat.of (K E) (Fin r → K E), inferInstance, ⟨?_⟩⟩
  let S := s.domain k
  let V := U k i
  let a := ((sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (rationalLatticeRingIso l E S).inv)
  let aU := ((ProEt.topology S).overPullback RingCat.{u + 1} V).map a
  let H := restrictScalars aU
  exact (overFunctor.{u + 1} _ V).mapIso
      (rationalRestrictionComparison l E X (s.immersion k) M) ≪≫
    (show ((restrictScalars a).obj _).over V ≅
      H.obj ((restrictRational l E (s.immersion k) M).over V) from Iso.refl _) ≪≫
    H.mapIso e ≪≫
    (show H.obj ((freeModel l E S r).over V) ≅
      ((restrictScalars a).obj (freeModel l E S r)).over V from Iso.refl _) ≪≫
    (overFunctor.{u + 1} _ V).mapIso (rationalFreeTransport l E S r)

set_option backward.isDefEq.respectTransparency false in
/-- Every chosen local integral presentation rationalizes to a finite free model on that
very covering object. Source: Bhatt--Scholze, Definitions 6.8.6 and 6.8.10,
Proposition 6.8.14(2) (blueprint: lem-per-rational-stratum-finite-free-model).

Proof: Restrict the normalized immersion comparison to the specified U, and transport
scalar extension through the given local integral model. The ordinary rationalization
of the finitely presented module is finite dimensional over K. Its finite basis
identifies it with a finite power, and the normalized beta comparison realizes that
power as the free sheaf. Compose with scalarModelIso and scalar-tower reassociation.
All restrictions use the original covering object U. -/
theorem chosenLocalModel (X : Scheme.{u}) [IsNoetherian X]
    {S : Scheme.{u}} (h : S ⟶ X) [IsImmersion h]
    (M : Modules (integralCoefficientSheaf l X E)) (U : S.ProEt)
    (N : ModuleCat.{u + 1} (A l E)) [Module.FinitePresentation (A l E) N]
    (_model : (restrictIntegral l E h M).over U ≅ (integralModel l E S N).over U) :
    ∃ r : ℕ, Nonempty ((restrictRational l E h (rationalize l E X M)).over U ≅
      (freeModel l E S r).over U) := by
  classical
  let := (inclusion l E).toAlgebra
  have : Module.Finite (K E) (vectorSpace l E N) := by
    change Module.Finite (K E) (TensorProduct (A l E) (K E) N)
    infer_instance
  let r := Module.finrank (K E) (vectorSpace l E N)
  let b : ModuleCat.of (K E) (Fin r → K E) ≅ vectorSpace l E N :=
    (Module.finBasis (K E) (vectorSpace l E N)).equivFun.symm.toModuleIso
  let F := constantModuleHomFunctor.{u + 1, u} (ProEt.topology S) (K E) ⋙
    Scheme.PurScalar.tensorFunctor.{u + 1, u + 1, u} (rationalConstants l E S)
  let f := (ConstantFiniteFreePresentationExtension.beta (ProEt.topology S) (K E)
    (rationalCoefficientSheaf l S E) (rationalConstants l E S) r).symm ≪≫ F.mapIso b
  let φ := integralRationalCoefficientMap l E S
  let FU := scalarPerfectExtensionFunctor.{u + 1, u, u + 1} ((ProEt.topology S).over U)
    (((ProEt.topology S).overPullback CommRingCat.{u + 1} U).map φ)
  obtain ⟨e, _, _, _⟩ := immersionComparison l E X h
  obtain ⟨c, _, _, _, _⟩ := scalarModels l E S
  refine ⟨r, ⟨(overFunctor.{u + 1} _ U).mapIso (e M) ≪≫ ?_⟩⟩
  exact SheafOfModules.scalarOverIso.{u + 1, u, u + 1} φ (restrictIntegral l E h M) U ≪≫
    FU.mapIso _model ≪≫
    (SheafOfModules.scalarOverIso.{u + 1, u, u + 1} φ (integralModel l E S N) U).symm ≪≫
    (overFunctor.{u + 1} _ U).mapIso (reassociation l E S N ≪≫ c N inferInstance ≪≫ f.symm)


/-- Rationalization is locally finite free on the same given strata and the same given
covers, with a rank for each covering object, and is rationally constructible.
Source: Bhatt--Scholze, Lemma 6.8.2, Definitions 6.8.6 and 6.8.10,
Proposition 6.8.14(2) (blueprint: lem-per-rational-stratum-finite-free-model).

Proof: Apply chosenLocalModel to the given integral model on each specified covering
object of each stratum. The finite basis construction gives its rational finite-free
rank. Retain the given stratification and covers. Transport coefficient rings through
the explicit pointwise ULift isomorphism, commute this transport with immersion
restriction, and compare constant-module realizations. Each finite free ordinary
E-module is finitely presented. Locally closed strata of a noetherian scheme are
constructible, so these witnesses satisfy IsContinuousConstructible. -/
theorem rationalStratumFiniteFreeModel (X : Scheme.{u}) [IsNoetherian X]
    (M : Modules (integralCoefficientSheaf l X E))
    (s : Scheme.FiniteLocallyClosedStratification X)
    (I : ∀ k : Fin s.n, Type (u + 1)) (U : ∀ k : Fin s.n, I k → (s.domain k).ProEt)
    (_cover : ∀ k : Fin s.n, (ProEt.topology (s.domain k)).CoversTop (U k))
    (_models : ∀ (k : Fin s.n) (i : I k),
      ∃ N : ModuleCat.{u + 1} (A l E), Module.FinitePresentation (A l E) N ∧
        Nonempty ((restrictIntegral l E (s.immersion k) M).over (U k i) ≅
          (integralModel l E (s.domain k) N).over (U k i))) :
    (∀ (k : Fin s.n) (i : I k), ∃ r : ℕ,
      Nonempty ((restrictRational l E (s.immersion k) (rationalize l E X M)).over (U k i) ≅
        (freeModel l E (s.domain k) r).over (U k i))) ∧
      rationalConstructible l E X (rationalize l E X M) := by
  have hf : ∀ (k : Fin s.n) (i : I k), ∃ r : ℕ,
      Nonempty ((restrictRational l E (s.immersion k) (rationalize l E X M)).over (U k i) ≅
        (freeModel l E (s.domain k) r).over (U k i)) := by
    intro k i
    let := s.isImmersion k
    obtain ⟨N, hN, ⟨e⟩⟩ := _models k i
    exact chosenLocalModel l E X (s.immersion k) M (U k i) N e
  exact ⟨hf, finiteFreeConstructible l E X (rationalize l E X M) s I U _cover hf⟩


end Coefficients
end AlgebraicGeometry.ProEtale.RationalStratum
