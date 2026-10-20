/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PointDerivedHomEvaluation
public import Sheaf.Paper.PointFibreDerivedTensor
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.RingTheory.PrincipalIdealDomain
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Sheaf.Paper.PointSectionsReconstruction
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.ConnectedConstantH0

/-! # Perfect point evaluation and the specified strict-cone completion

Source: main-20261015 blueprint, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, second sentence, and
thm-pod-identification-of-the-comparison, third paragraph
(blueprint: lem-pod-point-completed-evaluation).

The extension objects are the existing sheafified constant modules followed by
change of rings. The tensor tower is identified with the quotient tower of the
ordinary tensor by its balancing formula. Completed evaluation is the completion
of ordinary evaluation through that identification and the specified coefficient
completion unit. The final equation uses the recorded canonical point tensorator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures.PointCompletedEvaluation

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing lifted valuation ring. Source: blueprint coefficient conventions
(blueprint: lem-pod-point-completed-evaluation). -/
abbrev R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The completed coefficient sheaf on the original small pro-etale site.
Source: blueprint point-dualizing proof (blueprint: lem-pod-point-completed-evaluation). -/
abbrev B := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))

/-- The recorded standard localization of completed-coefficient sheaf complexes.
Source: Stacks 05RU (blueprint: lem-pod-point-completed-evaluation). -/
abbrev sheafQ := @DerivedCategory.Q (integralTowerModules l E (Spec (.of D.k))) _ _
  (HasDerivedCategory.standard _)

/-- The same small-Hom localization of ordinary modules used by the point fibre.
Source: Stacks 05RU (blueprint: lem-pod-point-completed-evaluation). -/
abbrev moduleQ := @DerivedCategory.Q (ModuleCat.{u + 1} (R l E)) _ _
  (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- The existing constant-to-completed coefficient map.
Source: blueprint point-dualizing proof (blueprint: lem-pod-point-completed-evaluation). -/
abbrev alpha := PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true

/-- The ordinary coefficient complex R[0]. Source: Stacks 0A8H
(blueprint: lem-pod-point-completed-evaluation). -/
abbrev ringComplex := (CochainComplex.singleFunctor (ModuleCat.{u + 1} (R l E)) 0).obj
  (ModuleCat.of (R l E) (R l E))

/-- The completed coefficient complex B[0]. Source: blueprint point coefficients
(blueprint: lem-pod-point-completed-evaluation). -/
abbrev coefficient := (CochainComplex.singleFunctor
  (integralTowerModules l E (Spec (.of D.k))) 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))

/-- The functor is uniquely specified on objects and maps by the existing tensor construction.
Source: Stacks 03CY, 03EK; node proof step 1
(blueprint: lem-pod-point-completed-evaluation).
Proof: use the functoriality of constant-module sheafification and of change of rings.
Their identity, composition and additive laws hold on the sheafification generators,
by the corresponding laws for constant linear maps and tensoring with the identity.
The displayed object and morphism equations determine the functor uniquely. -/
theorem extension_existsUnique :
    ∃! L : ModuleCat.{u + 1} (R l E) ⥤ integralTowerModules l E (Spec (.of D.k)),
      (∀ M, L.obj M = PointDerivedHom.extensionObject.{u, u} D.k (B D l E)
        (alpha D l E) M) ∧
      L.Additive ∧
      (∀ (M N : ModuleCat.{u + 1} (R l E)) (f : M ⟶ N),
        HEq (L.map f) (PointDerivedHom.extensionMorphism.{u, u} D.k (B D l E)
          (alpha D l E) f)) := by
  sorry

/-- Actual constant-module extension, uniquely fixed by its existing object and map formulas.
Source: node proof step 1 (blueprint: lem-pod-point-completed-evaluation). -/
def extension := (extension_existsUnique D l E).exists.choose

/-- Additivity supplied by the canonical functor construction.
Source: Stacks 03EK (blueprint: lem-pod-point-completed-evaluation). -/
instance extension_additive : (extension D l E).Additive :=
  (extension_existsUnique D l E).exists.choose_spec.2.1

/-- Apply the canonical extension termwise.
Source: Stacks 0A8X (blueprint: lem-pod-point-completed-evaluation). -/
def extensionComplex := (extension D l E).mapHomologicalComplex (.up ℤ)

/-- The same tensor generator transported through the uniquely fixed object equality.
Source: Stacks 03EK (blueprint: lem-pod-point-completed-evaluation). -/
def generator (M : ModuleCat.{u + 1} (R l E))
    (U : (Spec (.of D.k)).ProEtᵒᵖ) (b : (B D l E).obj.obj U) (x : M) :
    ((extension D l E).obj M).val.obj U :=
  (eqToHom ((extension_existsUnique D l E).exists.choose_spec.1 M).symm).val.app U
    (PointDerivedHom.extensionElement.{u, u} D.k (B D l E) (alpha D l E) M U b x)

/-- The ordinary derived dual's bounded-projective chain model, with the recorded differential.
Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
abbrev dual (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  CochainComplex.moduleHomComplex P (ringComplex l E)

/-- The specified ordinary sheaf tensor model.
Source: Stacks 06YL (blueprint: lem-pod-point-completed-evaluation). -/
abbrev total (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  PointDerivedHom.total.{u, u} D.k (B D l E) C J

/-- The balancing identification of the two strict towers, uniquely on local generators.
Source: Bhatt--Scholze 3.4.10 and node proof step 6
(blueprint: lem-pod-point-completed-evaluation).
Proof: in every degree reassociate the balanced tensor products and total sums.
Send (x tensor a) tensor (y tensor b) to (x tensor y) tensor ab; the inverse sends
(x tensor y) tensor a to (x tensor 1) tensor (y tensor a). Balancing and the
signed differential give inverse chain maps. The quotient formulas commute with
all transitions. Sheafification and the total injections make the maps unique. -/
theorem towerBalancing_existsUnique
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ∃! rho : ((integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj (C, J)) ≅
        ((integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj
          (total D l E C J)),
      ∀ (n : ℕ) (p j : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
        (a b : (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n).obj.obj U)
        (x : (C.X p).val.obj U) (y : (J.X j).val.obj U),
        ((rho.hom.app (op n)).f (p + j)).val.app U
          (integralOperationsTotalTensorSection l E (Spec (.of D.k)) n C J p j U
            (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (C.X p) U a x)
            (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (J.X j) U b y)) =
          integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n
            ((total D l E C J).X (p + j)) U (a * b)
              (PointDerivedHom.totalElement.{u, u} D.k (B D l E) C J p j U x y) := by
  sorry

/-- Balancing of the specified strict towers, with no arbitrary cone filler.
Source: node proof step 6 (blueprint: lem-pod-point-completed-evaluation). -/
def towerBalancing (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  (towerBalancing_existsUnique D l E C J).exists.choose

/-- Its actual functorial shifted-cone map acts on both product coordinates.
Source: Stacks 08TC (blueprint: lem-pod-point-completed-evaluation). -/
def roosBalancing (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  integralOperationsRoosFunctor.mapIso (towerBalancing D l E C J)

/-- Completed evaluation is the strict-cone completion of ordinary evaluation, followed
by the inverse of the specified coefficient completion unit. Both cone coordinates
are therefore fixed before localization. Source: node proof steps 6--7
(blueprint: lem-pod-point-completed-evaluation). -/
def completedEvaluation
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (e : total D l E C.obj J.obj ⟶ coefficient D l E)
    (b : (sheafQ D l E).obj (coefficient D l E) ≅
      (sheafQ D l E).obj ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
        (Spec (.of D.k))).obj (coefficient D l E))) :
    (integralCompletedTensor l E (Spec (.of D.k))).obj
      ((sheafQ D l E).obj C.obj, (sheafQ D l E).obj J.obj) ⟶
        (sheafQ D l E).obj (coefficient D l E) :=
  (integralCompletedTensorComparison l E (Spec (.of D.k))).hom.app (C, J) ≫
    (sheafQ D l E).map (roosBalancing D l E C.obj J.obj).hom ≫
    (sheafQ D l E).map ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).map e) ≫ b.inv

/-- Reading the coefficient in a degree identified with zero uses the existing single-complex
isomorphism. Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
def moduleValue (n : ℤ) (h : n = 0) : (ringComplex l E).X n ⟶ ModuleCat.of (R l E) (R l E) :=
  (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (ModuleCat.of (R l E) (R l E)) n h).hom

/-- The same single-complex isomorphism for the coefficient sheaf.
Source: Stacks 0A8H (blueprint: lem-pod-point-completed-evaluation). -/
def sheafValue (n : ℤ) (h : n = 0) : (coefficient D l E).X n ⟶
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))) :=
  (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))
      n h).hom


/-- The actual model B tensor underline P, rather than an arbitrary equivalent complex.
Source: node statement (blueprint: lem-pod-point-completed-evaluation). -/
abbrev model (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  (extensionComplex D l E).obj P

/-- The tensor comparison after identifying sections of C with P by its canonical unit.
Source: node proof step 8 and lem-sf-point-fibre-derived-tensor
(blueprint: lem-pod-point-completed-evaluation). -/
@[no_expose] def tau (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (hC : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj C))
    (hJ : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((sheafQ D l E).obj J))
    (unit : P ≅ (pointIntegralComplexSections D l E).obj C) :
    (pointFibreIntegralAmbient D l E).obj
      ((integralCompletedTensor l E (Spec (.of D.k))).obj
        ((sheafQ D l E).obj C, (sheafQ D l E).obj J)) ⟶
      (moduleQ l E).obj P ⊗
        (pointFibreIntegralAmbient D l E).obj ((sheafQ D l E).obj J) :=
  (pointIntegralTensorComparison D l hl E S
    ⟨(sheafQ D l E).obj C, hC⟩ ⟨(sheafQ D l E).obj J, hJ⟩).hom ≫
    (MonoidalCategory.tensor _).map
      (Prod.mkHom ((pointIntegralDerivedFactors D l E).hom.app C ≫
        (moduleQ l E).map unit.inv) (𝟙 _))


/-- All assertions concern the fixed perfect models and normalized canonical maps.
Source: node statement and proof steps 3--8
(blueprint: lem-pod-point-completed-evaluation). -/
@[no_expose] def Result (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) : Prop :=
  ∃ (good_C : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E P)),
  ∃ (good_J : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E (dual l E P))),
  ∃ (_constructible_tensor : sfIntegralConstructible l E (Spec (.of D.k))
    ((sheafQ D l E).obj (total D l E (model D l E P) (model D l E (dual l E P))))),
  ∃ (ctf_C : finiteTorConstructibleIntegral l E (Spec (.of D.k))
    ((sheafQ D l E).obj (model D l E P))),
  ∃ (ctf_J : finiteTorConstructibleIntegral l E (Spec (.of D.k))
    ((sheafQ D l E).obj (model D l E (dual l E P)))),
  ∃ (homIso : model D l E (dual l E P) ≅
    PointDerivedHom.sheafHom.{u, u} D.k (B D l E) (model D l E P) (coefficient D l E)),
  ∃ (_hom_normalized : ∀ (p j : ℤ) (h : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b b' : (B D l E).obj.obj U) (f : (dual l E P).X j) (x : P.X p),
    (sheafValue D l E (p + j) h).val.app U
      (PointDerivedHom.homValue.{u, u} D.k (B D l E) (model D l E P) (coefficient D l E)
        j p U ((homIso.hom.f j).val.app U
          (generator D l E ((dual l E P).X j) U b f))
        (generator D l E (P.X p) U b' x)) =
      b * b' * PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U
        ((moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x))),
  ∃ (_derivedHom_isIso : IsIso ((sheafQ D l E).map homIso.hom ≫
    IntegralHom.homModelMap.{u, u} (Spec (.of D.k)) (B D l E)
      (model D l E P) (coefficient D l E))),
  ∃ (unit : P ≅ (pointIntegralComplexSections D l E).obj (model D l E P)),
  ∃ (_unit_normalized : ∀ (p : ℤ) (x : P.X p), (unit.hom.f p).hom x =
    generator D l E (P.X p) (op (PointDerivedHom.finalObject D.k)) 1 x),
  ∃ (coefficientUnit : ringComplex l E ≅
    (pointIntegralComplexSections D l E).obj (coefficient D l E)),
  ∃ (_coefficientUnit_normalized : ∀ x : (ringComplex l E).X 0,
    (sheafValue D l E 0 rfl).val.app (op (PointDerivedHom.finalObject D.k))
      ((coefficientUnit.hom.f 0).hom x) =
        pointIntegralSectionMap l E D.k ((moduleValue l E 0 rfl).hom x)),
  ∃ (q : (pointIntegralComplexSections D l E).obj (model D l E (dual l E P)) ≅ dual l E P),
  ∃ (_q_normalized : ∀ (p j : ℤ) (h : p + j = 0)
      (f : ((pointIntegralComplexSections D l E).obj
        (model D l E (dual l E P))).X j) (x : P.X p),
    pointIntegralSectionMap l E D.k
      ((moduleValue l E (p + j) h).hom ((((q.hom.f j).hom f).v p (p + j) rfl).hom x)) =
      (sheafValue D l E (p + j) h).val.app (op (PointDerivedHom.finalObject D.k))
        (PointDerivedHom.homValue.{u, u} D.k (B D l E) (model D l E P) (coefficient D l E)
          j p (op (PointDerivedHom.finalObject D.k))
          ((homIso.hom.f j).val.app (op (PointDerivedHom.finalObject D.k)) f)
          (generator D l E (P.X p) (op (PointDerivedHom.finalObject D.k)) 1 x))),
  ∃ (evaluation : total D l E (model D l E P) (model D l E (dual l E P)) ⟶ coefficient D l E),
  ∃ (_evaluation_normalized : ∀ (p j : ℤ) (h : p + j = 0) (U : (Spec (.of D.k)).ProEtᵒᵖ)
      (b b' : (B D l E).obj.obj U) (x : P.X p) (f : (dual l E P).X j),
    (sheafValue D l E (p + j) h).val.app U
      ((evaluation.f (p + j)).val.app U
        (PointDerivedHom.totalElement.{u, u} D.k (B D l E)
          (model D l E P) (model D l E (dual l E P)) p j U
          (generator D l E (P.X p) U b x)
          (generator D l E ((dual l E P).X j) U b' f))) =
      (p * j).negOnePow • (b * b' *
        PointDerivedHom.scalar.{u, u} D.k (B D l E) (alpha D l E) U
          ((moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x)))),
  ∃ (ringEvaluation : P ⊗ dual l E P ⟶ ringComplex l E),
  ∃ (_ringEvaluation_normalized : ∀ (p j : ℤ) (h : p + j = 0) (x : P.X p)
      (f : (dual l E P).X j),
    (moduleValue l E (p + j) h).hom ((ringEvaluation.f (p + j)).hom
      ((HomologicalComplex.ιTensorObj P (dual l E P) p j (p + j) rfl).hom
        (x ⊗ₜ[R l E] f))) =
        (p * j).negOnePow •
          (moduleValue l E (p + j) h).hom ((f.v p (p + j) rfl).hom x)),
  ∃ (coefficientCompletion : (sheafQ D l E).obj (coefficient D l E) ≅
    (sheafQ D l E).obj ((integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k))).obj (coefficient D l E))),
  ∃ (_coefficientCompletion_normalized : coefficientCompletion.hom =
    (sheafQ D l E).map ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
      (coefficient D l E))),
  ∃ (_tensorCompletion_isIso : IsIso ((sheafQ D l E).map
    ((completedScalarIdentityUnit l E (Spec (.of D.k))).app
      (total D l E (model D l E P) (model D l E (dual l E P)))))),
    (pointFibreIntegralAmbient D l E).map
      (completedEvaluation D l E ⟨model D l E P, good_C⟩
        ⟨model D l E (dual l E P), good_J⟩ evaluation coefficientCompletion) ≫
      (pointIntegralDerivedFactors D l E).hom.app (coefficient D l E) ≫
      (moduleQ l E).map coefficientUnit.inv =
    tau D l E hl S P (model D l E P) (model D l E (dual l E P)) ctf_C ctf_J unit ≫
      (MonoidalCategory.tensor _).map (Prod.mkHom (𝟙 ((moduleQ l E).obj P))
        ((pointIntegralDerivedFactors D l E).hom.app (model D l E (dual l E P)) ≫
          (moduleQ l E).map q.hom)) ≫
      Functor.LaxMonoidal.μ (moduleQ l E) P (dual l E P) ≫
      (moduleQ l E).map ringEvaluation


/-- Perfect-model evaluation respects the specified strict-cone derived completion.
Source: main-20261015 blueprint, point-dualizing proof second sentence, and comparison
identification third paragraph (blueprint: lem-pod-point-completed-evaluation).

Proof, following the node's eight steps:
1. The valuation-ring DVR/PID lemmas make R Noetherian. Constant sheafification is exact
and B is flat over the constant ring, so extension is exact. Point sections is exact.
The extension/sections adjunction sends h to x mapped to h(1 tensor x); its inverse
sends t to b tensor x mapped to b t(x) after restriction.
2. Connected constant H0 and sectionwise limits identify Gamma(B) with the quotient
limit of R, which is R by the integers-profinite-tower lemma. The actual unit is the
constant-value map, so the point reconstruction and ordinary evaluation hypotheses hold.
3. Duals and tensors of finite-projective summands remain finite projective. Boundedness
and Noetherianity give finite cohomology. Point reconstruction proves the three
constructible-complete assertions, including uniform reduction bounds. Bounded flat
complexes are K-flat, and their degree intervals give finite Tor amplitude.
4. The bounded-free RHom model identifies the ambient derived Hom with the ordinary
Hom complex. On finite free modules the displayed map b tensor f is the identity;
passing to summands proves homIso. Its formula commutes with the signed Hom differential.
5. The ordinary point-derived-Hom evaluation theorem gives q by evaluation at 1 tensor x.
On bidegree (p,j) both evaluation composites are (-1)^(pj)h(1 tensor x).
6. Balance the two finite reductions to the reduction of the ordinary tensor, compatibly
with every quotient transition. Apply the functorial shifted cone. The identity-extension
comparison supplies precisely the displayed completion units: quotient-product component
and zero shifted-product component.
7. The reductions of ordinary evaluation form a strict tower morphism. Its two product
maps commute with 1 minus shift. Hence its cone map composed with the tensor completion
unit equals the coefficient completion unit composed with evaluation. Invert the latter
unit to obtain exactly completedEvaluation, the canonical completed evaluation.
8. The canonical point tensorator has inverse the sections balancing map followed by this
same tensor completion unit, as specified by PointIntegralTensorCanonical. Apply sections
to step 7, substitute the evaluation square from step 5, and compose with that tensorator.
The displayed equality is therefore an equality in D(R), with the same Koszul sign and
both specified cone coordinates. Zero complexes, negative degrees and degree-zero models
are included throughout. -/
theorem point_completed_evaluation (hl : l ≠ D.p) :
    ∃ S : PointIntegralTensorData D l hl E,
      Nonempty (PointIntegralTensorCanonical D l hl E S) ∧
      ∀ (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) (a b : ℤ),
        P.IsStrictlyGE a → P.IsStrictlyLE b →
        (∀ i : ℤ, Module.Projective (R l E) (P.X i) ∧ Module.Finite (R l E) (P.X i)) →
        Result D l E hl S P := by
  sorry

attribute [instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules

end WeilConjectures.PointCompletedEvaluation
