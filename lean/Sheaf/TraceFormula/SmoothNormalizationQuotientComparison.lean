module

public import Sheaf.TraceFormula.ConductorSmoothBaseChange
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Smooth comparison of normalization quotient sequences

Source: Stacks 07TD, 02KG, 02N4, 01I9, 00HD and 00DF; ILO Expose VIII,
2.2.1--2.2.4 and Lemma 2.2.9, unit-ideal specialization
(blueprint: lem-trf-smooth-normalization-quotient-comparison).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry
namespace SmoothNormalizationQuotient

/-- The actual normalization algebra as a module sheaf. Source: Stacks 035P
(blueprint: lem-trf-smooth-normalization-quotient-comparison). -/
noncomputable def algebra (X : Scheme.{u}) : X.Modules :=
  (Scheme.Modules.pushforward X.fromReducedNormalization).obj
    (SheafOfModules.unit X.reducedNormalization.ringCatSheaf)

/-- The actual normalization inclusion. Source: Stacks 035P
(blueprint: lem-trf-smooth-normalization-quotient-comparison). -/
noncomputable def inclusion (X : Scheme.{u}) :
    SheafOfModules.unit X.ringCatSheaf ⟶ algebra X :=
  SheafOfModules.unitToPushforwardObjUnit X.fromReducedNormalization.toRingCatSheafHom

/-- The actual cokernel projection defining the recorded conductor cokernel. Source: 07T8
(blueprint: lem-trf-smooth-normalization-quotient-comparison). -/
noncomputable def quotient (X : Scheme.{u}) : algebra X ⟶ conductorCokernel X :=
  cokernel.π (inclusion X)

/-- The normalization short complex, with its canonical maps. Source: Stacks 035P, 07T8
(blueprint: lem-trf-smooth-normalization-quotient-comparison). -/
noncomputable def sequence (X : Scheme.{u}) : ShortComplex X.Modules :=
  ShortComplex.mk (inclusion X) (quotient X) (cokernel.condition (inclusion X))

/-- Comparison data, with no arbitrary replacement for either canonical object.
Source: Stacks 07TD and 02KG
(blueprint: lem-trf-smooth-normalization-quotient-comparison). -/
structure Comparison {S T : Scheme.{u}} (h : T ⟶ S) where
  /-- The normalization isomorphism. -/
  theta : T.reducedNormalization ≅ pullback S.fromReducedNormalization h
  /-- It is an isomorphism over T. -/
  over : theta.hom ≫ pullback.snd S.fromReducedNormalization h = T.fromReducedNormalization
  /-- The algebra-sheaf comparison. -/
  alpha : (Scheme.Modules.tensorPullback h).obj (algebra S) ≅ algebra T
  /-- The quotient-sheaf comparison. -/
  beta : (Scheme.Modules.tensorPullback h).obj (conductorCokernel S) ≅ conductorCokernel T

/-- The induced normalization map. Source: Stacks 07TD
(blueprint: lem-trf-smooth-normalization-quotient-comparison). -/
noncomputable def Comparison.normalizationMap {S T : Scheme.{u}} {h : T ⟶ S}
    (d : Comparison h) : T.reducedNormalization ⟶ S.reducedNormalization :=
  d.theta.hom ≫ pullback.fst S.fromReducedNormalization h

/-- The chart pullback of a section, normalized by `1 tensor m`, restricted to V.
Source: Stacks 01I9, 0095
(blueprint: lem-trf-smooth-normalization-quotient-comparison). -/
noncomputable def chartSection {S T : Scheme.{u}} (h : T ⟶ S) (M : S.Modules)
    (U : S.affineOpens) (V : T.affineOpens) (hVU : V.1 ≤ h ⁻¹ᵁ U.1)
    (m : Γ(M, U.1)) : Γ((Scheme.Modules.tensorPullback h).obj M, V.1) :=
  ((Scheme.Modules.tensorPullback h).obj M).presheaf.map (homOfLE hVU).op
    (Scheme.Modules.tensorPullbackSection h M U.1 m)

/-- The affine tensor and quotient descriptions. Cokernels are expressed by exact,
surjective section maps; thus the quotient is precisely N/A and its scalar extension
is precisely (N tensor B)/B, including the embedded copy of B. Tensor factors are
written B tensor N, using Mathlib's scalar-extension convention.
Source: Stacks 02KG, 01I9, 00HD and 00DF
(blueprint: lem-trf-smooth-normalization-quotient-comparison). -/
def AffineFormula {S T : Scheme.{u}} {h : T ⟶ S} (d : Comparison h)
    (U : S.affineOpens) (V : T.affineOpens) (hVU : V.1 ≤ h ⁻¹ᵁ U.1) : Prop :=
  (h.appLE U.1 V.1 hVU).hom.Flat ∧
  Function.Injective ((inclusion S).val.app (op U.1)) ∧
  Function.Exact ((inclusion S).val.app (op U.1)) ((quotient S).val.app (op U.1)) ∧
  Function.Surjective ((quotient S).val.app (op U.1)) ∧
  Function.Injective ((inclusion T).val.app (op V.1)) ∧
  Function.Exact ((inclusion T).val.app (op V.1)) ((quotient T).val.app (op V.1)) ∧
  Function.Surjective ((quotient T).val.app (op V.1)) ∧
  Function.Injective ((ModuleCat.extendScalars (h.appLE U.1 V.1 hVU).hom).map
    ((inclusion S).val.app (op U.1))) ∧
  Function.Exact ((ModuleCat.extendScalars (h.appLE U.1 V.1 hVU).hom).map
    ((inclusion S).val.app (op U.1)))
    ((ModuleCat.extendScalars (h.appLE U.1 V.1 hVU).hom).map ((quotient S).val.app (op U.1))) ∧
  Function.Surjective ((ModuleCat.extendScalars (h.appLE U.1 V.1 hVU).hom).map
    ((quotient S).val.app (op U.1))) ∧
  ∃ (eN : (ModuleCat.extendScalars (h.appLE U.1 V.1 hVU).hom).obj
        ((algebra S).val.obj (op U.1)) ≅ (algebra T).val.obj (op V.1))
    (eQ : (ModuleCat.extendScalars (h.appLE U.1 V.1 hVU).hom).obj
        ((conductorCokernel S).val.obj (op U.1)) ≅
        (conductorCokernel T).val.obj (op V.1)),
    (∀ (b : Γ(T, V.1)) (n : Γ(algebra S, U.1)),
      eN.hom (b ⊗ₜ[Γ(S, U.1), (h.appLE U.1 V.1 hVU).hom] n) =
        d.alpha.hom.app V.1 (b • chartSection h (algebra S) U V hVU n)) ∧
    (∀ (b : Γ(T, V.1)) (c : Γ(conductorCokernel S, U.1)),
      eQ.hom (b ⊗ₜ[Γ(S, U.1), (h.appLE U.1 V.1 hVU).hom] c) =
        d.beta.hom.app V.1 (b • chartSection h (conductorCokernel S) U V hVU c)) ∧
    (∀ n m : Γ(S.reducedNormalization, S.fromReducedNormalization ⁻¹ᵁ U.1),
      eN.hom ((1 : Γ(T, V.1)) ⊗ₜ[Γ(S, U.1), (h.appLE U.1 V.1 hVU).hom] (n * m)) =
        (@Mul.mul Γ(T.reducedNormalization, T.fromReducedNormalization ⁻¹ᵁ V.1)
          inferInstance
          (eN.hom ((1 : Γ(T, V.1)) ⊗ₜ[Γ(S, U.1), (h.appLE U.1 V.1 hVU).hom] n))
          (eN.hom ((1 : Γ(T, V.1)) ⊗ₜ[Γ(S, U.1), (h.appLE U.1 V.1 hVU).hom] m)))) ∧
    eN.hom ((1 : Γ(T, V.1)) ⊗ₜ[Γ(S, U.1), (h.appLE U.1 V.1 hVU).hom]
      (1 : Γ(S.reducedNormalization, S.fromReducedNormalization ⁻¹ᵁ U.1))) =
        (1 : Γ(T.reducedNormalization, T.fromReducedNormalization ⁻¹ᵁ V.1)) ∧
    (ModuleCat.extendScalars (h.appLE U.1 V.1 hVU).hom).map ((quotient S).val.app (op U.1)) ≫
      eQ.hom = eN.hom ≫ (quotient T).val.app (op V.1)

/-- The comparisons are the canonical base-change map and its induced cokernel map.
The adjoint section equation pins alpha to theta; an arbitrary algebra automorphism
would not satisfy it. Source: Stacks 07TD, 02KG
(blueprint: lem-trf-smooth-normalization-quotient-comparison). -/
def Canonical {S T : Scheme.{u}} {h : T ⟶ S} (d : Comparison h) : Prop :=
  (∃ (w : d.normalizationMap ≫ S.fromReducedNormalization = T.fromReducedNormalization ≫ h),
    d.alpha.hom = Scheme.Modules.moduleBaseChangeMap S.fromReducedNormalization
      T.fromReducedNormalization h d.normalizationMap w
        (SheafOfModules.unit S.reducedNormalization.ringCatSheaf) ≫
      (Scheme.Modules.pushforward T.fromReducedNormalization).map
        (Scheme.Modules.tensorPullbackObjUnitToUnit d.normalizationMap)) ∧
  (Scheme.Modules.tensorPullback h).map (inclusion S) ≫ d.alpha.hom =
    Scheme.Modules.tensorPullbackObjUnitToUnit h ≫ inclusion T ∧
  (Scheme.Modules.tensorPullback h).map (quotient S) ≫ d.beta.hom =
    d.alpha.hom ≫ quotient T ∧
  (sequence S).ShortExact ∧ (sequence T).ShortExact ∧
  ∀ (U : S.affineOpens) (V : T.affineOpens) (hVU : V.1 ≤ h ⁻¹ᵁ U.1),
    AffineFormula d U V hVU

/-- Smooth pullback of the full finite normalization quotient sequence, with affine
formulas and coherence. Source: Stacks 07TD, 02KG, 02N4, 01I9, 00HD, 00DF;
ILO Expose VIII 2.2.1--2.2.4 and Lemma 2.2.9, unit ideal
(blueprint: lem-trf-smooth-normalization-quotient-comparison).

Proof: (1) Smoothness gives flatness and local finite presentation; quasi-compactness
gives finite type. Finite-type composition and Noetherian permanence give T finite
type and Noetherian, and smooth reduced ascent gives reduced T.
(2) Apply reduced algebraic normalization over Q to S and T for finiteness. The
finite-normalization quotient local criterion gives the two exact sequences and N/A.
(3) The coherent unit ideal has empty centre; normalizedBlowup_calculus identifies
its normalized blowup with normalization and gives theta and its cocycles.
(4) AffinePushforwardBaseChange applied to the structure sheaf defines alpha,
with its tensor formula, multiplication and unit; tensorPullbackObjUnitToUnit
identifies the inclusions. (5) FlatModulePullbackExact pulls back the exact sequence;
cokernel uniqueness defines beta. The affine flat criterion, affine pullback sections,
flat tensor exactness and tensor right exactness give its quotient formula.
(6) The sheaf basis equality test gives restriction compatibility. Smooth composition
and finite-type composition allow a second pullback; normalized-blowup and affine
base-change composition give theta and alpha cocycles. Cancel the epimorphic
pulled-back quotient for beta's cocycle. The identity formulas send n tensor a to an
and [n] tensor a to [an]. All comparisons are the canonical pullback compositors. -/
theorem smooth_normalization_quotient_comparison
    (S : Scheme.{u}) [IsReduced S]
    (q : S ⟶ Spec (.of (ULift.{u} ℚ))) [LocallyOfFiniteType q] [QuasiCompact q]
    (T : Scheme.{u}) (h : T ⟶ S) [Smooth h] [QuasiCompact h] :
    IsReduced T ∧ LocallyOfFiniteType (h ≫ q) ∧ QuasiCompact (h ≫ q) ∧
    IsFinite S.fromReducedNormalization ∧ IsFinite T.fromReducedNormalization ∧
    (∃! d : Comparison h, Canonical d) ∧
    (∀ d : Comparison (𝟙 S), Canonical d →
      d.normalizationMap = 𝟙 S.reducedNormalization ∧
      d.alpha.hom = (Scheme.Modules.tensorPullbackSectionId S).hom.app (algebra S) ∧
      d.beta.hom = (Scheme.Modules.tensorPullbackSectionId S).hom.app (conductorCokernel S)) ∧
    (∀ (U : Scheme.{u}) (g : U ⟶ T) [Smooth g] [QuasiCompact g]
        (dh : Comparison h) (dg : Comparison g) (dgh : Comparison (g ≫ h)),
      Canonical dh → Canonical dg → Canonical dgh →
      dgh.normalizationMap = dg.normalizationMap ≫ dh.normalizationMap ∧
      dgh.alpha.hom =
        (Scheme.Modules.tensorPullbackSectionComp g h).hom.app (algebra S) ≫
          (Scheme.Modules.tensorPullback g).map dh.alpha.hom ≫ dg.alpha.hom ∧
      dgh.beta.hom =
        (Scheme.Modules.tensorPullbackSectionComp g h).hom.app (conductorCokernel S) ≫
          (Scheme.Modules.tensorPullback g).map dh.beta.hom ≫ dg.beta.hom) := by
  sorry

end SmoothNormalizationQuotient
end AlgebraicGeometry
