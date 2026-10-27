/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedCoefficientPushforwardComparison
public import Sheaf.Paper.CompletedOperationTowerSubstitution
public import Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit
public import Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Normalized monoidal and adjunction transport for completed coefficients

Source: Stacks Project, algebraization.tex, Tags 099I and 099K; main-20261015,
lem-fix-operation-reduction.proof.md, final paragraph. The combined assertion and
its representative normalizations are taken from the dispatched transport item's proof
(blueprint: def-pur-completed-coefficient-tensor-transport-models).

The records below present canonical constructions, including their localization,
completion-unit and sectionwise normalizations. Their existence is a conclusion;
no tensor comparison, adjunction or preservation assertion is an extra hypothesis.
Sites have object universe t+1 and morphism universe t, independently of E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open WeilConjectures
namespace WeilConjectures.CompletedCoefficientTransport

/-- The monoidal structure induced by reflection, with its constraints fixed by the
actual reflection unit. The lax braided inclusion expresses precisely the associator,
both unitor and signed symmetry diagrams on ambient objects.
Source: node proof steps 4, 6--7
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
structure ReflectedTensor {D : Type a} [Category.{v} D]
    (T : MonoidalCategory D) (s : @SymmetricCategory D _ T)
    (C : D ⥤ D) (η : 𝟭 D ⟶ C) (P : ObjectProperty D) where
  monoidal : MonoidalCategory P.FullSubcategory
  symmetric : @SymmetricCategory _ _ monoidal
  tensor : @MonoidalCategory.tensor _ _ monoidal ⋙ P.ι ≅
    (P.ι.prod P.ι) ⋙ @MonoidalCategory.tensor D _ T ⋙ C
  unit : monoidal.tensorUnit.obj ≅ C.obj T.tensorUnit
  inclusion : letI := T; letI := s; letI := monoidal; letI := symmetric
    P.ι.LaxBraided
  tensor_unit : letI := T; letI := s; letI := monoidal; letI := symmetric
    letI := inclusion
    ∀ M N : P.FullSubcategory,
      Functor.LaxMonoidal.μ P.ι M N =
        η.app (T.tensorObj M.obj N.obj) ≫ tensor.inv.app (M, N)
  coefficient_unit : letI := T; letI := s; letI := monoidal; letI := symmetric
    letI := inclusion
    Functor.LaxMonoidal.ε P.ι = η.app T.tensorUnit ≫ unit.inv

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Constant integral coefficients on the original site.
Source: Stacks 099I
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
abbrev constant (W : Scheme.{t}) :=
  (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)))

/-- The completed integral coefficient ring, with commutativity retained.
Source: Stacks 099I
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
abbrev completed (W : Scheme.{t}) := completedIntegralCommRingSheafUnrestricted l E W

/-- The ordinary unbounded derived category of completed-coefficient modules.
Source: Stacks 099I
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
abbrev DR (W : Scheme.{t}) := IntegralOnSlice.D l E W none

/-- The ordinary unbounded derived category of constant-coefficient modules.
Source: Stacks 099I
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
abbrev DA (W : Scheme.{t}) :=
  DerivedCategory (CompletedCoefficientPushforward.Mod W
    (integralConstantRingOfUniverses l E W))

/-- The global constant uniformizer, before completion.
Source: node proof step 1 (Stacks 099I)
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
def constantUniformizer (W : Scheme.{t}) :
    (SheafOfModules.unit (integralConstantRingOfUniverses l E W)).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (toSheafify (Scheme.ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
          (ULift.up (Padic.coefficientExtensionUniformizer l E)))
    (by
      intro U V f
      exact (congrArg (fun h ↦ h
        (ULift.up (Padic.coefficientExtensionUniformizer l E)))
          ((toSheafify (Scheme.ProEt.topology W)
            ((Functor.const W.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{t + 1}
                (Padic.coefficientExtensionIntegers l E))))).naturality f)).symm)

/-- Completeness for the specified R-completion and its actual unit.
Source: Stacks 0A0E and 099I
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
def completeR (W : Scheme.{t}) : ObjectProperty (DR l E W) :=
  fun K ↦ IsIso ((IntegralOnSlice.completionUnit l E W none).app K)

/-- Canonical ambient coefficient data at one site. The constant-side completion is
its universal strict quotient Roos model; d is normalized on every ambient object.
The R-side functor and its unit are the already recorded quotient construction.
Source: node proof steps 1--4 and 6--7
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
structure Site (W : Scheme.{t}) where
  U : CompletedCoefficientPushforward.ExactImage
    (SheafOfModules.restrictScalars.{max u (t + 1)}
      (integralConstantToCompletionOfUniverses l E W))
  completion : PrincipalQuotientCompletion.Model.{t + 1, t, max u (t + 1),
      (max u (t + 1)) + 1} (J := Scheme.ProEt.topology W) (constant l E W)
    (constantUniformizer l E W)
  closed : RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
    (Scheme.ProEt.topology W) (constant l E W)
  d : IntegralOnSlice.completion l E W none ⋙ U.functor ≅ U.functor ⋙ completion.completion
  d_unit : ∀ K : DR l E W,
    U.functor.map ((IntegralOnSlice.completionUnit l E W none).app K) ≫ d.hom.app K =
      completion.unit.app (U.functor.obj K)
  r_complete : ∀ K : DR l E W, completeR l E W K ↔ IsDerivedCompleteUnrestricted l E W K
  r_output : ∀ K : DR l E W,
    completeR l E W ((IntegralOnSlice.completion l E W none).obj K)
  r_reflect : ∀ K N : DR l E W, completeR l E W N →
    Function.Bijective (fun h : (IntegralOnSlice.completion l E W none).obj K ⟶ N ↦
      (IntegralOnSlice.completionUnit l E W none).app K ≫ h)
  a_output : ∀ K : DA l E W, IsIso (completion.unit.app (completion.completion.obj K))
  a_reflect : ∀ K N : DA l E W, IsIso (completion.unit.app N) →
    Function.Bijective (fun h : completion.completion.obj K ⟶ N ↦ completion.unit.app K ≫ h)
  restrict_complete : ∀ K : DR l E W,
    completeR l E W K ↔ IsIso (completion.unit.app (U.functor.obj K))
  r_tensor : ReflectedTensor (IntegralOnSlice.duality l E W none).closed.monoidal
    (IntegralOnSlice.duality l E W none).symmetric
    (IntegralOnSlice.completion l E W none) (IntegralOnSlice.completionUnit l E W none)
    (completeR l E W)
  a_tensor : ReflectedTensor closed.closed.monoidal closed.symmetric completion.completion
    completion.unit (fun K ↦ IsIso (completion.unit.app K))

/-- The complete constant-coefficient subcategory, characterized by the actual unit.
Source: Stacks 099I
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
abbrev Site.completeA {W : Scheme.{t}} (S : Site l E W) : ObjectProperty (DA l E W) :=
  fun K ↦ IsIso (S.completion.unit.app K)

/-- Exact scalar restriction on the complete full subcategories.
Source: Stacks 099I
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
def Site.restriction {W : Scheme.{t}} (S : Site l E W) :
    (completeR l E W).FullSubcategory ⥤ (S.completeA l E).FullSubcategory :=
  (S.completeA l E).lift ((completeR l E W).ι ⋙ S.U.functor)
    (fun K ↦ (S.restrict_complete K.obj).mp K.property)

/-- The actual termwise scalar restriction, prior to localization.
Source: Stacks 099I
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
abbrev restrictionComplex (W : Scheme.{t}) :=
  (SheafOfModules.restrictScalars.{max u (t + 1)}
    (integralConstantToCompletionOfUniverses l E W)).mapHomologicalComplex (.up ℤ)

/-- The ordinary direct-sum total tensor before completion, on either coefficient ring.
Source: Stacks 07A4
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
abbrev total (W : Scheme.{t}) (B : Sheaf (Scheme.ProEt.topology W)
    CommRingCat.{max u (t + 1)}) :=
  coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W) B

/-- The finite comparison is a single map of strict systems. Its augmentation is the
balancing map, and every level is invertible. Consequently there are no independently
chosen levelwise arrows or omitted transition equations.
Source: node proof steps 3--4
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
def TowerBalancing (W : Scheme.{t})
    (P Q : CochainComplex (CompletedCoefficientPushforward.Mod W
      (completedIntegralCoefficientSheafUnrestricted l E W)) ℤ)
    (β : (total W (constant l E W)).obj
      ((restrictionComplex l E W).obj P, (restrictionComplex l E W).obj Q) ⟶
      (restrictionComplex l E W).obj ((total W (completed l E W)).obj (P, Q))) : Prop :=
  ∃ θ : ((PrincipalQuotientCompletion.quotientTower.{t + 1, t, max u (t + 1)}
      (J := Scheme.ProEt.topology W) (constant l E W)
      (constantUniformizer l E W)).obj ((total W (constant l E W)).obj
        ((restrictionComplex l E W).obj P, (restrictionComplex l E W).obj Q))).asFunctor ⟶
    ((PrincipalQuotientCompletion.quotientTower.{t + 1, t, max u (t + 1)}
      (J := Scheme.ProEt.topology W) (completed l E W)
      (PrincipalKoszulStrictReplacement.uniformizer l E W)).obj
        ((total W (completed l E W)).obj (P, Q))).asFunctor ⋙
          restrictionComplex l E W,
    (∀ n : ℕ, IsIso (θ.app (op n))) ∧
    ∀ n : ℕ,
      HEq (PrincipalQuotientCompletion.quotientMap.{t + 1, t, max u (t + 1)}
          (J := Scheme.ProEt.topology W) (constant l E W)
          (constantUniformizer l E W) _ n ≫ θ.app (op n))
        (β ≫ (restrictionComplex l E W).map
          (PrincipalQuotientCompletion.quotientMap.{t + 1, t, max u (t + 1)}
          (J := Scheme.ProEt.topology W) (completed l E W)
            (PrincipalKoszulStrictReplacement.uniformizer l E W) _ n))

/-- Monoidal scalar transport with the ordinary balancing map fixed on all local pure
homogeneous tensors, and its derived extension fixed on every K-flat representative.
The strict-system clause specifies the finite change-of-rings comparisons before limit.
Source: node proof steps 2--4 and 6--7
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
structure TensorTransport {W : Scheme.{t}} (S : Site l E W) where
  equivalence : (completeR l E W).FullSubcategory ≌ (S.completeA l E).FullSubcategory
  equivalence_functor : equivalence.functor = S.restriction l E
  monoidal : letI := S.r_tensor.monoidal; letI := S.a_tensor.monoidal
    (S.restriction l E).Monoidal
  braided : letI := S.r_tensor.monoidal; letI := S.a_tensor.monoidal
    letI := monoidal
    ∀ M N : (completeR l E W).FullSubcategory,
      Functor.LaxMonoidal.μ (S.restriction l E) M N ≫
          (S.restriction l E).map (S.r_tensor.symmetric.braiding M N).hom =
        (S.a_tensor.symmetric.braiding ((S.restriction l E).obj M)
          ((S.restriction l E).obj N)).hom ≫
            Functor.LaxMonoidal.μ (S.restriction l E) N M
  balancing : (S.U.functor.prod S.U.functor) ⋙ S.closed.closed.tensor ⟶
    (IntegralOnSlice.duality l E W none).closed.tensor ⋙ S.U.functor
  representatives : ∀ P Q : CochainComplex (CompletedCoefficientPushforward.Mod W
      (completedIntegralCoefficientSheafUnrestricted l E W)) ℤ,
    ∀ (hP : CochainComplex.IsKFlatIndependentCoefficients (R := completed l E W) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := completed l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (J := Scheme.ProEt.topology W) (R := completed l E W) (P.X i)) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (J := Scheme.ProEt.topology W) (R := completed l E W) (Q.X i)) →
    ∃ (hUP : CochainComplex.IsKFlatIndependentCoefficients (R := constant l E W)
        ((restrictionComplex l E W).obj P))
      (hUQ : CochainComplex.IsKFlatIndependentCoefficients (R := constant l E W)
        ((restrictionComplex l E W).obj Q))
      (β : (total W (constant l E W)).obj
        ((restrictionComplex l E W).obj P, (restrictionComplex l E W).obj Q) ⟶
        (restrictionComplex l E W).obj ((total W (completed l E W)).obj (P, Q))),
      (∀ (p q k : ℤ) (h : p + q = k) (V : W.ProEtᵒᵖ)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        HEq ((β.f k).val.app V
          (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
            (constant l E W) _ _ p q k h V x y))
          (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
            (completed l E W) P Q p q k h V x y)) ∧
      TowerBalancing l E W P Q β ∧
      balancing.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        S.closed.closed.tensor.map
            (Prod.mkHom (S.U.factors.hom.app P) (S.U.factors.hom.app Q)) ≫
          (S.closed.models.iso (Scheme.ProEt.topology W) (constant l E W) S.closed.closed
            ((restrictionComplex l E W).obj P)
            ((restrictionComplex l E W).obj Q) hUP hUQ).inv ≫ DerivedCategory.Q.map β ≫
          S.U.factors.inv.app _ ≫ S.U.functor.map
            ((IntegralOnSlice.duality l E W none).models.iso (Scheme.ProEt.topology W)
              (completed l E W) (IntegralOnSlice.duality l E W none).closed P Q hP hQ).hom

/-- The specified a comparison. Its tensorator orientation is the inverse of the
strong monoidal restriction tensorator; the two surrounding isomorphisms identify
the completed tensors with completion of the ordinary tensors.
Source: node proof step 4
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
def TensorTransport.a {W : Scheme.{t}} {S : Site l E W} (T : TensorTransport l E S)
    (M N : (completeR l E W).FullSubcategory) :
    S.U.functor.obj ((IntegralOnSlice.completedTensor l E W none).obj (M.obj, N.obj)) ≅
      S.completion.completion.obj (S.closed.closed.tensor.obj
        (S.U.functor.obj M.obj, S.U.functor.obj N.obj)) :=
  letI := S.r_tensor.monoidal
  letI := S.a_tensor.monoidal
  letI := T.monoidal
  S.U.functor.mapIso (S.r_tensor.tensor.app (M, N)).symm ≪≫
    (S.completeA l E).ι.mapIso (Functor.Monoidal.μIso (S.restriction l E) M N).symm ≪≫
      S.a_tensor.tensor.app ((S.restriction l E).obj M, (S.restriction l E).obj N)

/-- The actual completion-unit normalization of a. Together with the reflector
bijection and strict-system balancing, this identifies the inverse finite comparison
under total limit, rather than merely an isomorphic pair of objects.
Source: node proof step 4
(blueprint: def-pur-completed-coefficient-tensor-transport-models). -/
def TensorTransport.UnitNormalization {W : Scheme.{t}} {S : Site l E W}
    (T : TensorTransport l E S) : Prop :=
  ∀ M N : (completeR l E W).FullSubcategory,
    T.balancing.app (M.obj, N.obj) ≫
        S.U.functor.map ((IntegralOnSlice.completionUnit l E W none).app
          ((IntegralOnSlice.duality l E W none).closed.tensor.obj (M.obj, N.obj))) ≫
        (T.a l E M N).hom =
      S.completion.unit.app
        (S.closed.closed.tensor.obj (S.U.functor.obj M.obj, S.U.functor.obj N.obj))


end WeilConjectures.CompletedCoefficientTransport
