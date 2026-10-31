/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystemComparison
public import WeilConjectures.AlgebraicGeometry.FieldProjectionSystemSquare
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma

/-! # Coefficient compatibility of the tower purity transpose

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md (2), tensor transpose
(blueprint: def-sp-field-purity-transpose-arrows).

All equalities are in the ordinary derived category of strict varying-coefficient
systems, in the published section coordinates. Index n means positive exponent n+1.
The maps below are actual adjunction transposes, rather than lifts of finite maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldPuritySystem

open FieldShriekSystem FieldExceptionalSystem
variable (P : PurityFiniteSetting.{u}) (D : Models P)

/-- The coefficient module already used by the tower orientation theorem.
Source: blueprint (2), J_A (blueprint: def-sp-field-purity-transpose-arrows). -/
abbrev coefficient (E : Index P) (T : Scheme.{u}) :=
  SpTowerClasses.coefficient T (SpTowerClasses.Arings P.coefficients.l E.val T)

/-- Its actual degree-zero complex, used to normalize the scalar unitor.
Source: blueprint (2), coefficient unit (blueprint: def-sp-field-purity-transpose-arrows). -/
abbrev coefficientComplex (E : Index P) (T : Scheme.{u}) :=
  (CochainComplex.singleFunctor (SpTowerShriek.S P.coefficients.l E.val T) 0).obj
    (coefficient P E T)

/-- The ordinary multiplication map is fixed by its composite with the scalar unit.
The derived map is its localization through the specified K-flat resolving counit.
Source: blueprint (2), canonical scalar unit identification
(blueprint: def-sp-field-purity-transpose-arrows). -/
structure ScalarUnit {E F : Index P} (h : E ≤ F) (T : Scheme.{u}) where
  ordinary : (D.scalars E F h T).model.E.obj (coefficient P E T) ≅ coefficient P F T
  sections : ∀ (U : (ℕ × T.ProEt)ᵒᵖ) (x : (coefficient P E T).val.obj U),
    ordinary.hom.val.app U
        (((D.scalars E F h T).ordinaryAdjunction.unit.app (coefficient P E T)).val.app U x) =
      (FieldShriekSystem.coefficientMap P (D.coefficients E F h) T).hom.app U x
  derived : (D.scalars E F h T).T.obj (SpTowerGamma.unit P.coefficients.l E.val T) ≅
    SpTowerGamma.unit P.coefficients.l F.val T
  model : derived.hom =
    (D.scalars E F h T).model.ε.app (coefficientComplex P E T) ≫
      DerivedCategory.Q.map
        (((D.scalars E F h T).model.E.mapCochainComplexSingleFunctor 0).hom.app
          (coefficient P E T) ≫ (CochainComplex.singleFunctor _ 0).map ordinary.hom)

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a)

/-- Canonically normalized tensor, pullback and coefficient-unit coordinates.
Membership fields merely put the existing objects in the recorded full subcategory.
This is data asserted to exist in the theorem, not an extra geometric hypothesis.
Source: blueprint (2), tensor and unit identifications
(blueprint: def-sp-field-purity-transpose-arrows). -/
structure Coordinates where
  tensors : ∀ (E : Index P) (T : Scheme.{u}), (T = X ∨ T = Y) →
    SpTowerP1.TensorData P.coefficients.l E.val (D.base E) T
  pullUnit : ∀ E : Index P, SpTowerClasses.CoefficientPullback P.coefficients.l E.val
    (D.base E) f ((D.operations E).geometry f)
  scalarUnit : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}), (T = X ∨ T = Y) →
    ScalarUnit P D h T
  unit_mem : ∀ E : Index P,
    normalized P D E Y (SpTowerGamma.unit P.coefficients.l E.val Y)
  tensor_mem : ∀ (E : Index P) (K : N P D E Y) (W : N P D E X),
    normalized P D E X ((SpTowerShriek.tensor P.coefficients.l E.val (D.base E) X).obj
      ((SpTowerShriek.pull P.coefficients.l E.val (D.base E)
        ((D.operations E).geometry f)).obj K.obj, W.obj))

variable (t : ProjectionTensorComparisons P D) (q : Coordinates P D (f := f))

/-- The actual coefficient unit as an object of the normalized full subcategory.
Source: blueprint (2), J_A (blueprint: def-sp-field-purity-transpose-arrows). -/
def unit (E : Index P) : N P D E Y :=
  ⟨SpTowerGamma.unit P.coefficients.l E.val Y, q.unit_mem E⟩

/-- The specified exceptional image of the coefficient unit.
Source: blueprint (2), omega_A (blueprint: def-sp-field-purity-transpose-arrows). -/
def omega (E : Index P) : N P D E X := (A.right E).obj (unit P D q E)

/-- Pullback of K tensor W, retained in the same full system category.
Source: blueprint (2), tensor source (blueprint: def-sp-field-purity-transpose-arrows). -/
def tensorSource (E : Index P) (K : N P D E Y) (W : N P D E X) : N P D E X :=
  ⟨_, q.tensor_mem E K W⟩

/-- The explicit inverse projection followed by identity tensor counit and right unit.
Source: blueprint (2), the displayed counit composite
(blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def projectionCounit (E : Index P) (K : N P D E Y)
    (hpf : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj)) :
    (support P D c a E).obj (tensorSource P D q E K (omega P D c b a A q E)) ⟶ K :=
  ObjectProperty.homMk
    (@inv _ _ _ _ (leftProjection P D t E c K.obj (omega P D c b a A q E).obj) hpf ≫
      (SpTowerShriek.tensor P.coefficients.l E.val (D.base E) Y).map
        (Prod.mkHom (𝟙 _) ((A.adj E).counit.app (unit P D q E)).hom) ≫
      ((q.tensors E Y (.inr rfl)).rightUnit P.coefficients.l E.val K.obj).hom)

/-- Tau is literally the tower adjunction transpose, including its counit normalization.
Source: blueprint (2), tau_A,K (blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def tau (E : Index P) (K : N P D E Y)
    (hpf : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj)) :
    tensorSource P D q E K (omega P D c b a A q E) ⟶ (A.right E).obj K :=
  (A.adj E).homEquiv _ _ (projectionCounit P D c b a A t q E K hpf)

/-- The exceptional unit component followed by G_B of the canonical scalar unitor.
Source: blueprint (2), c_JA under C_Y J_A = J_B
(blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def omegaComparison {E F : Index P} (h : E ≤ F) :
    (D.scalars E F h X).T.obj (omega P D c b a A q E).obj ⟶
      (omega P D c b a A q F).obj :=
  (component P D c b a A h (unit P D q E)).hom ≫
    ((A.right F).map (ObjectProperty.homMk (Y := unit P D q F)
      (q.scalarUnit E F h Y (.inr rfl)).derived.hom)).hom

/-- Exactly the two levelwise finite-Tor etale-origin witnesses in shriek-levels (2a).
No transition compatibility of the origins is imposed.
Source: blueprint (2), projection domain
(blueprint: def-sp-field-purity-transpose-arrows). -/
structure PairDomain (E : Index P) (K : N P D E Y) (W : N P D E X) where
  inputOrigin : ∀ n : ℕ, SpTowerShriek.Origin P.coefficients.l E.val (D.base E) Y n K.obj
  outputOrigin : ∀ n : ℕ, SpTowerShriek.Origin P.coefficients.l E.val (D.base E) X n W.obj
  inputTor : ∀ n : ℕ, SpTowerShriek.GoodLevel P.coefficients.l E.val (D.base E) Y n K.obj
  outputTor : ∀ n : ℕ, SpTowerShriek.GoodLevel P.coefficients.l E.val (D.base E) X n W.obj

/-- The first displayed whole-system equality, with its source comparison written out.
Source: blueprint (2), tensor-map transpose
(blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def TensorCompatibility {E F : Index P} (h : E ≤ F) (K : N P D E Y)
    (hA : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj))
    (hB : IsIso (leftProjection P D t F c ((scalar P D a h Y).obj K).obj
      (omega P D c b a A q F).obj)) : Prop :=
  (D.scalars E F h X).T.map (tau P D c b a A t q E K hA).hom ≫
      (component P D c b a A h K).hom =
    (projectionTarget P D t h f K.obj (omega P D c b a A q E).obj).hom ≫
      (SpTowerShriek.tensor P.coefficients.l F.val (D.base F) X).map
        (Prod.mkHom (𝟙 _) (omegaComparison P D c b a A q h)) ≫
      (tau P D c b a A t q F ((scalar P D a h Y).obj K) hB).hom

/-- Tensoring tau with the specified orientation, in its ordered twist presentation.
Source: blueprint (2), tau(1 tensor a) (blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def gamma (E : Index P) (w : SpChartAdmissibility.Twists P.coefficients.l E.val X)
    (d : ℕ) (orientation : SpTowerGamma.orderedLine P.coefficients.l E.val (D.base E) X w d ≅
      (omega P D c b a A q E).obj) (K : N P D E Y)
    (hpf : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj)) :=
  (SpTowerShriek.tensor P.coefficients.l E.val (D.base E) X).map
      (Prod.mkHom (𝟙 ((SpTowerShriek.pull P.coefficients.l E.val (D.base E)
        ((D.operations E).geometry f)).obj K.obj)) orientation.hom) ≫
    (tau P D c b a A t q E K hpf).hom

/-- The scalar source identification uses precisely the canonical tensorator and pullback
compositor, followed by the specified comparison of the shifted Tate lines.
Source: blueprint (2), canonical pullback/twist source comparison
(blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def puritySourceComparison {E F : Index P} (h : E ≤ F) (d : ℕ)
    (wE : SpChartAdmissibility.Twists P.coefficients.l E.val X)
    (wF : SpChartAdmissibility.Twists P.coefficients.l F.val X)
    (line : (D.scalars E F h X).T.obj
        (SpTowerGamma.orderedLine P.coefficients.l E.val (D.base E) X wE d) ≅
      SpTowerGamma.orderedLine P.coefficients.l F.val (D.base F) X wF d)
    (K : N P D E Y) :=
  projectionTarget P D t h f K.obj
      (SpTowerGamma.orderedLine P.coefficients.l E.val (D.base E) X wE d) ≪≫
    (SpTowerShriek.tensor P.coefficients.l F.val (D.base F) X).mapIso
      (Iso.prod (Iso.refl _) line)


/-- The coefficient-unit constraint on the tensor source, using the actual geometric
unit comparison and scalar multiplication, rather than an arbitrary endpoint iso.
Source: blueprint (2), tau at J (blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def unitConstraint (E : Index P) :
    (tensorSource P D q E (unit P D q E) (omega P D c b a A q E)).obj ≅
      (omega P D c b a A q E).obj :=
  (SpTowerShriek.tensor P.coefficients.l E.val (D.base E) X).mapIso
      (Iso.prod ((q.pullUnit E).derivedIso P.coefficients.l E.val)
        (Iso.refl (omega P D c b a A q E).obj)) ≪≫
    (q.tensors E X (.inl rfl)).leftUnit P.coefficients.l E.val
      (omega P D c b a A q E).obj

end AlgebraicGeometry.ProEtale.FieldPuritySystem
