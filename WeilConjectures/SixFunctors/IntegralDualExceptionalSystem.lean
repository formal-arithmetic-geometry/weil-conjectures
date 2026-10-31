/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagramRealization
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.IntegralSystemDualityCompatibility
import WeilConjectures.SixFunctors.CompletedSystemPullbackPreservation
import WeilConjectures.AlgebraicGeometry.DirectImagesConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus

/-! # The integral dual-pullback-dual comparison as a system map

Source: Weil blueprint, prop-coef-integral-exceptional-adjoint, proof paragraph 1,
from the integral object H to compatibility with transitions
(blueprint: lem-coef-integral-dual-exceptional-system).

The comparisons below are composites in the ordinary derived strict-system category.
The only postponed assertion is their invertibility, preservation and compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralDualExceptionalSystem
open FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Integral duality into the specified total limit of the dualizing system.
Source: node paragraph 2 (blueprint: lem-coef-integral-dual-exceptional-system). -/
def integralDual (W : Scheme.{u}) (Ω : coefficientSequenceDerived l E W) :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ⥤
      DerivedCategory (scalarReductionSource l E W) :=
  (Functor.curry.obj (coefficientIntegralInternalHom l E W)).flip.obj
    ((coefficientSequenceLimit l E W).obj Ω)

/-- The evaluation-defined beta followed by internal Hom of the actual dualizing counit.
This definition is made before checking any finite evaluation.
Source: node displayed v (blueprint: lem-coef-integral-dual-exceptional-system). -/
def dualComparison (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E W)
    (Ω : coefficientSequenceDerived l E W)
    (P : DerivedCategory (scalarReductionSource l E W)) :
    S.reduction.obj ((integralDual l E W Ω).obj (op P)) ⟶
      (dual W Ω).obj (op (S.reduction.obj P)) :=
  coefficientBaseChangeHom S.integralClosed S.systemClosed S.reduction S.reductionTensor
      P ((coefficientSequenceLimit l E W).obj Ω) ≫
    (coefficientSequenceInternalHom l E W).map
      (Prod.mkHom (𝟙 _) (S.adjunction.counit.app Ω))

/-- The explicit finite duality comparison, including the actual dualizing coefficient map.
Source: node paragraph 3 (blueprint: lem-coef-integral-dual-exceptional-system). -/
def finiteDualComparison (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E W)
    (Ω : coefficientSequenceDerived l E W)
    (P : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).obj
        (S.reduction.obj ((integralDual l E W Ω).obj (op P))) ⟶
      (coefficientFiniteInternalHom l E W n).obj
        (op ((coefficientSequenceDerivedEvaluation l E W n).obj (S.reduction.obj P)),
          (coefficientSequenceDerivedEvaluation l E W n).obj Ω) :=
  (S.reductionEvaluation n).hom.app ((integralDual l E W Ω).obj (op P)) ≫
    coefficientBaseChangeHom S.integralClosed (S.finiteClosed n)
      (coefficientFiniteDerivedExtension l E W n) (S.finiteTensor n)
      P ((coefficientSequenceLimit l E W).obj Ω) ≫
    (coefficientFiniteInternalHom l E W n).map
      (Prod.mkHom (((S.reductionEvaluation n).hom.app P).op)
        ((S.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E W).obj Ω) ≫
          (coefficientSequenceDerivedEvaluation l E W n).map (S.adjunction.counit.app Ω)))

/-- Invertibility, naturality and finite evaluation for the specified dual comparison.
Source: node v and its evaluations
(blueprint: lem-coef-integral-dual-exceptional-system). -/
structure DualComparison (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E W)
    (Ω : (domain l E W).FullSubcategory) : Prop where
  dualizingCounit : IsIso (S.adjunction.counit.app Ω.obj)
  invertible : ∀ P : sfIntegralConstructibleCategory l E W,
    IsIso (dualComparison l E W S Ω.obj P.obj)
  naturality : ∀ (P Q : sfIntegralConstructibleCategory l E W) (a : P ⟶ Q),
    S.reduction.map ((integralDual l E W Ω.obj).map a.hom.op) ≫
        dualComparison l E W S Ω.obj P.obj =
      dualComparison l E W S Ω.obj Q.obj ≫
        (dual W Ω.obj).map (S.reduction.map a.hom).op
  evaluation : ∀ (P : sfIntegralConstructibleCategory l E W) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map
        (dualComparison l E W S Ω.obj P.obj) ≫
      (S.fiberHom (S.reduction.obj P.obj) Ω.obj
        (S.reduction_normalized P.obj) Ω.property.1 n).hom =
    finiteDualComparison l E W S Ω.obj P.obj n

private theorem finiteTor_of_iso (W : Scheme.{u}) (n : ℕ)
    {P Q : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1))}
    (e : P ≅ Q) (hP : FiniteExceptional.domain l E W n P) :
    FiniteExceptional.domain l E W n Q := by
  have : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W) :=
    (proEtale_bounded_constructible_isTriangulated W
      (Padic.coefficientExtensionRing l E (n + 1))).1
  refine ⟨ObjectProperty.prop_of_iso _ e hP.1, ?_⟩
  obtain ⟨a, b, hab, ht⟩ := hP.2
  refine ⟨a, b, hab, ?_⟩
  intro L T hL f hf hT M i hi
  exact ht L T (hL.map (fun eL ↦ eL ≪≫ e.symm)) f hf hT M i hi

private theorem reduction_mem (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    (S : CoefficientDerivedSystemCalculus l E W) (P : sfIntegralConstructibleCategory l E W) :
    domain l E W (S.reduction.obj P.obj) := by
  let (x : W) : Invertible (l : W.residueField x) :=
    (show IsUnit (l : W.residueField x) by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((W ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
  have hP : finiteTorConstructibleIntegral l E W P.obj :=
    (integral_residue_tor D l hl E W).2 ▸ P.property
  refine ⟨S.reduction_normalized P.obj, fun n ↦ ?_⟩
  obtain ⟨a, b, hab, ht⟩ := hP.2
  apply finiteTor_of_iso l E W n ((S.reductionEvaluation n).app P.obj).symm
  exact ⟨(P.property.2.choose_spec.choose_spec.2 n).1, a, b, ht n⟩

private theorem dualComparison_naturality (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E W) (Ω : coefficientSequenceDerived l E W)
    (P Q : DerivedCategory (scalarReductionSource l E W)) (a : P ⟶ Q) :
    S.reduction.map ((integralDual l E W Ω).map a.op) ≫
        dualComparison l E W S Ω P =
      dualComparison l E W S Ω Q ≫ (dual W Ω).map (S.reduction.map a).op := by
  dsimp only [integralDual, dual, Functor.flip_obj_obj, Functor.flip_obj_map,
    Functor.curry_obj_obj_obj, Functor.curry_obj_obj_map]
  let ω := (coefficientSequenceLimit l E W).obj Ω
  change S.reduction.map ((coefficientIntegralInternalHom l E W).map
      (Prod.mkHom a.op (𝟙 ω))) ≫ _ = _
  unfold dualComparison
  rw [← Category.assoc, S.reduction_compatible.naturality Q ω P ω a (𝟙 ω)]
  rw [S.reduction.map_id]
  simp only [Category.assoc]
  apply congrArg (fun z ↦
    coefficientBaseChangeHom S.integralClosed S.systemClosed S.reduction
      S.reductionTensor Q ω ≫ z)
  change (coefficientSequenceInternalHom l E W).map
      (Prod.mkHom (S.reduction.map a).op (𝟙 _)) ≫
      (coefficientSequenceInternalHom l E W).map
        (Prod.mkHom (𝟙 _) (S.adjunction.counit.app Ω)) =
    (coefficientSequenceInternalHom l E W).map
        (Prod.mkHom (𝟙 _) (S.adjunction.counit.app Ω)) ≫
      (coefficientSequenceInternalHom l E W).map
        (Prod.mkHom (S.reduction.map a).op (𝟙 _))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext <;> simp

private theorem dualComparison_evaluation (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E W)
    (Ω : (domain l E W).FullSubcategory)
    (P : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).map
        (dualComparison l E W S Ω.obj P) ≫
      (S.fiberHom (S.reduction.obj P) Ω.obj
        (S.reduction_normalized P) Ω.property.1 n).hom =
    finiteDualComparison l E W S Ω.obj P n := by
  dsimp only [dualComparison, finiteDualComparison, integralDual,
    Functor.flip_obj_obj, Functor.curry_obj_obj_obj]
  rw [Functor.map_comp, Category.assoc]
  have hn := S.fiber_naturality _ _ _ _ (S.reduction_normalized P) (S.reduction_normalized _)
      (S.reduction_normalized P) Ω.property.1 (𝟙 _) (S.adjunction.counit.app Ω.obj) n
  simp only [op_id] at hn
  rw [hn]
  rw [← Category.assoc, S.beta_evaluation, Category.assoc, Category.assoc]
  congr 2
  rw [← Functor.map_comp]
  congr 1
  ext <;> simp

private theorem inverse_square {C : Type*} [Category C]
    {A B T U : C} (e : A ≅ B) (d : T ≅ U)
    (h : A ⟶ T) (k : B ⟶ U) (hk : e.hom ≫ k = h ≫ d.hom) :
    e.inv ≫ h = k ≫ d.inv := by
  apply (cancel_epi e.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hk]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {l E}
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SY : CoefficientDerivedSystemCalculus l E Y)
  (ΩX : coefficientSequenceDerived l E X) (ΩY : coefficientSequenceDerived l E Y)

/-- The contravariant functor L ↦ F = L_X f* R_Y D_Y L.
Source: node definition of F (blueprint: lem-coef-integral-dual-exceptional-system). -/
def firstDualPullback : (DerivedCategory (scalarReductionSource l E Y))ᵒᵖ ⥤
    DerivedCategory (scalarReductionSource l E X) :=
  integralDual l E Y ΩY ⋙ SY.reduction ⋙ integralComparisonDerivedSequencePullback l E f ⋙
    coefficientSequenceLimit l E X

/-- The covariant integral functor L ↦ H = D_X F.
Source: node definition of H (blueprint: lem-coef-integral-dual-exceptional-system). -/
def doubleDualPullback : DerivedCategory (scalarReductionSource l E Y) ⥤
    DerivedCategory (scalarReductionSource l E X) :=
  (firstDualPullback f SY ΩY).rightOp ⋙ integralDual l E X ΩX

/-- Source of q, restricted only to the stated integral constructible inputs.
Source: node q (blueprint: lem-coef-integral-dual-exceptional-system). -/
def qSource : (sfIntegralConstructibleCategory l E Y)ᵒᵖ ⥤ coefficientSequenceDerived l E X :=
  (sfIntegralConstructible l E Y).ι.op ⋙ firstDualPullback f SY ΩY ⋙ SX.reduction

/-- Target of q, the finite pullback of the system dual of the reduction of L.
Source: node q (blueprint: lem-coef-integral-dual-exceptional-system). -/
def qTarget : (sfIntegralConstructibleCategory l E Y)ᵒᵖ ⥤ coefficientSequenceDerived l E X :=
  (sfIntegralConstructible l E Y).ι.op ⋙ SY.reduction.op ⋙ dual Y ΩY ⋙
    integralComparisonDerivedSequencePullback l E f

/-- q is the actual completed-pullback counit followed by f*(v_Y).
Source: node displayed q (blueprint: lem-coef-integral-dual-exceptional-system). -/
def qMap (L : sfIntegralConstructibleCategory l E Y) :
    (qSource f SX SY ΩY).obj (op L) ⟶ (qTarget f SY ΩY).obj (op L) :=
  SX.adjunction.counit.app
      ((integralComparisonDerivedSequencePullback l E f).obj
        (SY.reduction.obj ((integralDual l E Y ΩY).obj (op L.obj)))) ≫
    (integralComparisonDerivedSequencePullback l E f).map
      (dualComparison l E Y SY ΩY L.obj)

/-- Source of the desired covariant system comparison b.
Source: node b (blueprint: lem-coef-integral-dual-exceptional-system). -/
def bSource : sfIntegralConstructibleCategory l E Y ⥤ coefficientSequenceDerived l E X :=
  (sfIntegralConstructible l E Y).ι ⋙ doubleDualPullback f SY ΩX ΩY ⋙ SX.reduction

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  {SZ : CoefficientDerivedSystemCalculus l E c.Z}
  {SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k))}
  (r : Realization l E D hl f c SX SZ SY)
  (g : Geometry l E f SX SY)
  (aX : DualizingOperation (D := D) (hl := hl) X SX SS)
  (aY : DualizingOperation (D := D) (hl := hl) Y SY SS)
  (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
  (θ : Duality r aX aY βY g)

/-- The finite inverse q with both the finite dualizing and pullback identifications.
It is a specific composite, not an arbitrary lift of finite isomorphisms.
Source: node final system comparison
(blueprint: lem-coef-integral-dual-exceptional-system). -/
def finiteInverseQ
    (q : qSource f SX SY aY.omega.obj ≅ qTarget f SY aY.omega.obj)
    (L : sfIntegralConstructibleCategory l E Y) (n : ℕ) :
    (finiteDerivedPullback l E n f).obj
        ((coefficientFiniteInternalHom l E Y n).obj
          (op ((coefficientSequenceDerivedEvaluation l E Y n).obj (SY.reduction.obj L.obj)),
            integralDualizingFiniteTerm l E D Y n)) ⟶
      (coefficientSequenceDerivedEvaluation l E X n).obj
        (SX.reduction.obj ((firstDualPullback f SY aY.omega.obj).obj (op L.obj))) :=
  (finiteDerivedPullback l E n f).map
      ((coefficientFiniteInternalHom l E Y n).map
        (Prod.mkHom (𝟙 _) (aY.finiteOmega n).inv)) ≫
    (finiteDerivedPullback l E n f).map
      (SY.fiberHom (SY.reduction.obj L.obj) aY.omega.obj
        (SY.reduction_normalized L.obj) aY.omega.property.1 n).inv ≫
    (Geometry.pullEvaluation l E g n).inv.app
      ((dual Y aY.omega.obj).obj (op (SY.reduction.obj L.obj))) ≫
    (coefficientSequenceDerivedEvaluation l E X n).map (q.inv.app (op L))

/-- All clauses of the coherent dual-pullback-dual construction. The data q and b are
natural isomorphisms of actual system functors, pinned by their component equations.
Source: node paragraphs 2--4 (blueprint: lem-coef-integral-dual-exceptional-system). -/
structure Comparison where
  reductionX : ∀ P : sfIntegralConstructibleCategory l E X,
    domain l E X (SX.reduction.obj P.obj)
  reductionY : ∀ P : sfIntegralConstructibleCategory l E Y,
    domain l E Y (SY.reduction.obj P.obj)
  constructibleM : ∀ L : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l E Y ((integralDual l E Y aY.omega.obj).obj (op L.obj))
  constructibleF : ∀ L : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l E X ((firstDualPullback f SY aY.omega.obj).obj (op L.obj))
  constructibleH : ∀ L : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l E X ((doubleDualPullback f SY aX.omega.obj aY.omega.obj).obj L.obj)
  pullNormalized : ∀ L : sfIntegralConstructibleCategory l E Y,
    IsNormalizedCoefficientSequence l E X
      ((integralComparisonDerivedSequencePullback l E f).obj
        (SY.reduction.obj ((integralDual l E Y aY.omega.obj).obj (op L.obj))))
  dualX : DualComparison l E X SX aX.omega
  dualY : DualComparison l E Y SY aY.omega
  completedCounit : ∀ L : sfIntegralConstructibleCategory l E Y,
    IsIso (SX.adjunction.counit.app
      ((integralComparisonDerivedSequencePullback l E f).obj
        (SY.reduction.obj ((integralDual l E Y aY.omega.obj).obj (op L.obj)))))
  q : qSource f SX SY aY.omega.obj ≅ qTarget f SY aY.omega.obj
  q_component : ∀ L : sfIntegralConstructibleCategory l E Y,
    q.hom.app (op L) = qMap f SX SY aY.omega.obj L
  b : bSource f SX SY aX.omega.obj aY.omega.obj ≅
    reducedConstructible Y SY reductionY ⋙ r.G ⋙ (domain l E X).ι
  b_component : ∀ L : sfIntegralConstructibleCategory l E Y,
    b.hom.app L =
      dualComparison l E X SX aX.omega.obj
          ((firstDualPullback f SY aY.omega.obj).obj (op L.obj)) ≫
        (dual X aX.omega.obj).map (q.inv.app (op L)).op ≫
        θ.iso.inv.app ((reducedConstructible Y SY reductionY).obj L)
  finite_component : ∀ (L : sfIntegralConstructibleCategory l E Y) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E X n).map (b.hom.app L) ≫
      ((r.exceptionalEvaluation n).hom.app
        ((reducedConstructible Y SY reductionY).obj L)).hom =
    (coefficientSequenceDerivedEvaluation l E X n).map
        (dualComparison l E X SX aX.omega.obj
          ((firstDualPullback f SY aY.omega.obj).obj (op L.obj))) ≫
      (SX.fiberHom
        (SX.reduction.obj ((firstDualPullback f SY aY.omega.obj).obj (op L.obj))) aX.omega.obj
        (SX.reduction_normalized _) aX.omega.property.1 n).hom ≫
      (coefficientFiniteInternalHom l E X n).map
        (Prod.mkHom (finiteInverseQ f SX SY D hl g aY q L n).op
          (aX.finiteOmega n).hom) ≫
      (FiniteExceptional.dualFormulaIso l E D hl f c n).inv.app
        ((evaluation l E Y n).obj ((reducedConstructible Y SY reductionY).obj L))
  tor : ∀ (L : sfIntegralConstructibleCategory l E Y) (a b dX dY : ℤ),
    a ≤ b → 0 ≤ dX → 0 ≤ dY →
    topologicalKrullDim X ≤ (dX.toNat : WithBot ℕ∞) →
    topologicalKrullDim Y ≤ (dY.toNat : WithBot ℕ∞) →
    (∀ n : ℕ, HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E Y n).obj L.obj) a b) →
    ∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E X n).obj
        ((doubleDualPullback f SY aX.omega.obj aY.omega.obj).obj L.obj))
      (a - 2 * dX) (b + 2 * dY)

/-- The integral dual-pullback-dual object has the specified coherent finite exceptional
system, including its canonical maps, naturality and the two dimension contributions.
The previously fixed finite realization and its duality are the data used by the node;
none of the integral preservation or comparison conclusions is an assumption.

Source: prop-coef-integral-exceptional-adjoint, proof paragraph 1
(blueprint: lem-coef-integral-dual-exceptional-system).

Proof: (1) Apply lem-coef-integral-residue-tor to a common cohomological interval of
an integral constructible object. Its reduction system is normalized by the calculus,
and all its levels are finite-Tor constructible. Integral Verdier duality preserves M.
(2) Exact finite inverse image and quotient compatibility from
lem-pur-coefficient-system-derived-comparison preserve normalization and the finite
Tor interval. The coefficient ring is complete and its uniformizer a non-zero-divisor
by the complete-extension and DVR lemmas. (3) The total limit defining F is the completed
pullback of def-pur-integral-derived-operations, so
lem-pur-integral-operations-preserve-constructible makes F constructible. Integral
Verdier duality makes H constructible; the finite realization already preserves its
normalized domain. (4) lem-pur-normalized-actual-reconstruction-maps makes the actual
counit at the pulled-back system invertible. Its finite evaluations are the adjuncts
of the total-limit projections by SX.counit_projection. (5) The same theorem applies
to the normalized dualizing systems, whose limits and finite projections are those
of prop-coef-integral-dualizing. Compose beta with their actual counits. The evaluation
calculus identifies its fibers with the evaluation-defined integral Verdier comparisons;
these are invertible by thm-coef-integral-verdier. Joint conservativity proves v invertible.
(6) Form q from the counit followed by pullback of v. Apply the contravariant system
dual to q inverse, then theta inverse, after v at F. This gives exactly b_component.
(7) Naturality of beta, the counit and theta proves naturality of q and b. Evaluate
this composite using the calculus, the geometric pullback comparison and theta's
finiteFormula identity. This is finite_component, with both coefficient identifications;
transition compatibility holds already for these actual system maps.
(8) If L has Tor interval [a,b], integral Verdier on Y gives [-b-2dY,-a], pullback
preserves it, and integral Verdier on X gives [a-2dX,b+2dY]. The input interval for
the second application is ordered by a ≤ b and dY ≥ 0. Empty schemes permit bound
zero; zero complexes satisfy every interval. No integral exceptional adjunction is used. -/
theorem integralDualExceptionalSystem :
    Nonempty (Comparison f SX SY D hl c r g aX aY βY θ) := by
  classical
  have primeUnit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
      IsUnit (l : Γ(W, ⊤)) := by
    simpa using (finiteFieldDatumPrimeUnit D l hl).map
      ((W ↘ Spec (.of D.k)).appTop.hom.comp (Scheme.ΓSpecIso (.of D.k)).inv.hom)
  have redX := reduction_mem l E D hl X SX
  have redY := reduction_mem l E D hl Y SY
  obtain ⟨presX, isoX, torX⟩ :=
    integralSystemDualityCompatibility l E D hl X SX SS aX
  obtain ⟨presY, isoY, torY⟩ :=
    integralSystemDualityCompatibility l E D hl Y SY SS aY
  have hM (L : sfIntegralConstructibleCategory l E Y) := presY L
  have hPull (L : sfIntegralConstructibleCategory l E Y) :=
    completedSystemPullbackPreservation l E D f SY
      ⟨(integralDual l E Y aY.omega.obj).obj (op L.obj), hM L⟩
  have hF (L : sfIntegralConstructibleCategory l E Y) := (hPull L).1
  have hH (L : sfIntegralConstructibleCategory l E Y) :=
    presX ⟨(firstDualPullback f SY aY.omega.obj).obj (op L.obj), hF L⟩
  have hN (L : sfIntegralConstructibleCategory l E Y) :
      IsNormalizedCoefficientSequence l E X
        ((integralComparisonDerivedSequencePullback l E f).obj
          (SY.reduction.obj ((integralDual l E Y aY.omega.obj).obj (op L.obj)))) :=
    (hPull L).2.1
  have hc (L : sfIntegralConstructibleCategory l E Y) :=
    ((purNormalizedReconstruction l E X (primeUnit X) SX).1 _ (hN L)).2
  have dx : DualComparison l E X SX aX.omega :=
    ⟨((purNormalizedReconstruction l E X (primeUnit X) SX).1 _ aX.omega.property.1).2,
      isoX, fun P Q a ↦ dualComparison_naturality l E X SX _ P.obj Q.obj a.hom,
      fun P n ↦ dualComparison_evaluation l E X SX _ P.obj n⟩
  have dy : DualComparison l E Y SY aY.omega :=
    ⟨((purNormalizedReconstruction l E Y (primeUnit Y) SY).1 _ aY.omega.property.1).2,
      isoY, fun P Q a ↦ dualComparison_naturality l E Y SY _ P.obj Q.obj a.hom,
      fun P n ↦ dualComparison_evaluation l E Y SY _ P.obj n⟩
  have hq (L : sfIntegralConstructibleCategory l E Y) :
      IsIso (qMap f SX SY aY.omega.obj L) := by
    have := hc L
    have := dy.invertible L
    unfold qMap
    infer_instance
  let q : qSource f SX SY aY.omega.obj ≅ qTarget f SY aY.omega.obj :=
    NatIso.ofComponents (fun L ↦ asIso (qMap f SX SY aY.omega.obj L.unop)) (by
      intro L K a
      change SX.reduction.map ((coefficientSequenceLimit l E X).map
          ((integralComparisonDerivedSequencePullback l E f).map
            (SY.reduction.map ((integralDual l E Y aY.omega.obj).map a.unop.hom.op)))) ≫
          qMap f SX SY aY.omega.obj K.unop =
        qMap f SX SY aY.omega.obj L.unop ≫
          (integralComparisonDerivedSequencePullback l E f).map
            ((dual Y aY.omega.obj).map (SY.reduction.map a.unop.hom).op)
      unfold qMap
      have hv := congrArg (integralComparisonDerivedSequencePullback l E f).map
        (dualComparison_naturality l E Y SY aY.omega.obj _ _ a.unop.hom)
      simp only [Functor.map_comp] at hv
      erw [← Category.assoc, SX.adjunction.counit.naturality]
      simpa only [Functor.id_map, Category.assoc] using
        congrArg (fun z ↦ SX.adjunction.counit.app _ ≫ z) hv)
  let b : bSource f SX SY aX.omega.obj aY.omega.obj ≅
      reducedConstructible Y SY redY ⋙ r.G ⋙ (domain l E X).ι :=
    NatIso.ofComponents (fun L ↦
      @asIso _ _ _ _
          (dualComparison l E X SX aX.omega.obj
            ((firstDualPullback f SY aY.omega.obj).obj (op L.obj)))
          (dx.invertible ⟨_, hF L⟩) ≪≫
        (dual X aX.omega.obj).mapIso (q.app (op L)).symm.op ≪≫
        (θ.iso.app ((reducedConstructible Y SY redY).obj L)).symm) (by
      intro L K a
      dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.op_hom,
        asIso_hom, Iso.app_hom, Iso.app_inv]
      change SX.reduction.map ((integralDual l E X aX.omega.obj).map
          ((firstDualPullback f SY aY.omega.obj).map a.hom.op).op) ≫ _ = _
      erw [← Category.assoc, ← Category.assoc, dualComparison_naturality,
        Category.assoc, Category.assoc]
      have hn := q.inv.naturality a.op
      have hd := congrArg (fun z ↦ (dual X aX.omega.obj).map z.op) hn
      simp only [Functor.map_comp, op_comp] at hd
      have ht := θ.iso.inv.naturality ((reducedConstructible Y SY redY).map a)
      dsimp only [qSource, qTarget, firstDualPullback, Functor.comp_map,
        Functor.op_map, ObjectProperty.ι_map] at hd
      simp only [Category.assoc] at hd ⊢
      erw [← Category.assoc ((dual X aX.omega.obj).map _)
        ((dual X aX.omega.obj).map _) _, ← hd, Category.assoc]
      simpa only [dualComparison, dualFormula, reducedConstructible, Functor.comp_map,
        Functor.op_map, Functor.rightOp_map, ObjectProperty.lift_map,
        ObjectProperty.ι_map, ObjectProperty.homMk_hom, Quiver.Hom.unop_op,
        Quiver.Hom.op_unop, Iso.op_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
        using congrArg (fun z ↦
        dualComparison l E X SX aX.omega.obj
          ((firstDualPullback f SY aY.omega.obj).obj (op L.obj)) ≫
          (dual X aX.omega.obj).map (q.inv.app (op L)).op ≫ z) ht)
  refine ⟨{
    reductionX := redX
    reductionY := redY
    constructibleM := hM
    constructibleF := hF
    constructibleH := hH
    pullNormalized := hN
    dualX := dx
    dualY := dy
    completedCounit := hc
    q := q
    q_component := fun _ ↦ rfl
    b := b
    b_component := fun _ ↦ rfl
    finite_component := ?_
    tor := ?_ }⟩
  · intro L n
    let N := (reducedConstructible Y SY redY).obj L
    let ev := coefficientSequenceDerivedEvaluation l E X n
    let ψ := FiniteExceptional.dualFormulaIso l E D hl f c n
    have ht := θ.finiteFormula n N
    have hi : ev.map (θ.iso.inv.app N) ≫
        ((r.exceptionalEvaluation n).hom.app N).hom =
      (SX.fiberHom
        ((integralComparisonDerivedSequencePullback l E f).obj
          ((dual Y aY.omega.obj).obj (op N.obj))) aX.omega.obj
        (θ.pullDualNormalized N) aX.omega.property.1 n).hom ≫
      (coefficientFiniteInternalHom l E X n).map
        (Prod.mkHom
          (((finiteDerivedPullback l E n f).map
              ((coefficientFiniteInternalHom l E Y n).map
                (Prod.mkHom (𝟙 _) (aY.finiteOmega n).inv)) ≫
            (finiteDerivedPullback l E n f).map
              (SY.fiberHom N.obj aY.omega.obj N.property.1 aY.omega.property.1 n).inv ≫
            (Geometry.pullEvaluation l E g n).inv.app
              ((dual Y aY.omega.obj).obj (op N.obj))).op)
          (aX.finiteOmega n).hom) ≫
        ψ.inv.app ((evaluation l E Y n).obj N) := by
      simpa only [Functor.mapIso_inv, Iso.app_inv, Category.assoc] using
        inverse_square (ev.mapIso (θ.iso.app N))
          (ψ.app ((evaluation l E Y n).obj N)) _ _ ht
    have hn := SX.fiber_naturality _ _ _ _ (SX.reduction_normalized _)
      aX.omega.property.1 (θ.pullDualNormalized N) aX.omega.property.1
      (q.inv.app (op L)) (𝟙 _) n
    change ev.map
        (dualComparison l E X SX aX.omega.obj
          ((firstDualPullback f SY aY.omega.obj).obj (op L.obj)) ≫
        (dual X aX.omega.obj).map (q.inv.app (op L)).op ≫ θ.iso.inv.app N) ≫ _ = _
    simp only [Functor.map_comp, Category.assoc]
    erw [hi]
    dsimp only [dual, Functor.flip_obj_map, Functor.curry_obj_map_app]
    erw [← Category.assoc (ev.map ((coefficientSequenceInternalHom l E X).map _)) _ _, hn]
    simp only [Category.assoc]
    congr 2
    erw [← Category.assoc, ← Functor.map_comp]
    congr 1
    congr 1
    ext <;> simp [finiteInverseQ, op_comp, N, reducedConstructible, dual]
  · intro L a b dX dY hab hdX hdY hdimX hdimY ht
    have htM := torY L a b dY hab hdY hdimY ht
    have habM : -b - 2 * dY ≤ -a := by omega
    have htF := (hPull L).2.2 (-b - 2 * dY) (-a) habM htM
    have htH := torX ⟨_, hF L⟩ (-b - 2 * dY) (-a) dX habM hdX hdimX htF
    have hlo : -(-a) - 2 * dX = a - 2 * dX := by omega
    have hhi : -(-b - 2 * dY) = b + 2 * dY := by omega
    rw [hlo, hhi] at htH
    exact htH

end WeilConjectures.IntegralDualExceptionalSystem
