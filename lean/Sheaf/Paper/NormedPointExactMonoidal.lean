module

public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

import Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.RingTheory.ProEtale.WContractible
import Sheaf.AlgebraicGeometry.ProEtale.Projective
import Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition
import Sheaf.Paper.CondensedPointBasisEvaluation
import Sheaf.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PartitionSectionTensorFlat
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence

/-! # Exact symmetric monoidal sections at a normed-coefficient geometric point

Source: Hemo--Richarz--Scholbach, Example 3.1, Section 3 and Lemma 4.1(1), pp.6--8
(blueprint: lem-sfb-normed-point-exact-monoidal).

The constant map, evaluation functor and inverse image are the specified constructions.
The monoidal structures in the statement are fixed by their unit and pure-tensor equations.
The harmless universe lift of F places the unit in the module universe; restriction along
ULift.ringEquiv identifies these modules with abstract F-modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u uA vA uB vB uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The internal coefficient module category, with the recorded relative tensor.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-exact-monoidal). -/
abbrev NormedPointModules (F : Type u) [NormedField F] (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (normContinuousRing F).X T)

/-- The ring of sections of the actual pulled-back coefficient at the final point object.
Source: HRS Example 3.1 (blueprint: lem-sfb-normed-point-exact-monoidal). -/
abbrev normedPointSectionRing (F : Type u) [NormedField F] (k : Type u) [Field k] :=
  (sectionRingSheaf (Scheme.ProEt.topology (Spec (.of k)))
    (condensedRingObj (normContinuousRing F).X (Spec (.of k)))).obj.obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))

/-- A constant section: evaluate the recorded constant scalar map on the integer unit.
Source: HRS Example 3.1 (blueprint: lem-sfb-normed-point-exact-monoidal). -/
def normedPointConstantValue (F : Type u) [NormedField F] (k : Type u) [Field k]
    (a : F) : normedPointSectionRing F k :=
  (normContinuousConstant (Spec (.of k)) a).hom.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
      (((Functor.LaxMonoidal.ε
        (sheafToPresheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})).app
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) (ULift.up (1 : ℤ)))

/-- Final-object evaluation with scalar action restricted along the constant-section map.
The internal/sectionwise equivalence keeps the section groups and maps unchanged.
Source: HRS Lemma 4.1(1) (blueprint: lem-sfb-normed-point-exact-monoidal). -/
def normedPointEvaluation (F : Type u) [NormedField F] (k : Type u) [Field k]
    (c : ULift.{u + 1} F →+* normedPointSectionRing F k) :
    NormedPointModules F (Spec (.of k)) ⥤ ModuleCat.{u + 1} (ULift.{u + 1} F) :=
  (sectionModuleEquivalence (Scheme.ProEt.topology (Spec (.of k)))
    (condensedRingObj (normContinuousRing F).X (Spec (.of k)))).functor ⋙
      SheafOfModules.evaluation _ (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) ⋙
        ModuleCat.restrictScalars c

/-- The specified geometric fibre: the recorded extension-of-scalars inverse image,
followed by point evaluation with the constant scalar action.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-exact-monoidal). -/
abbrev normedPointFibre (F : Type u) [NormedField F] {Z : Scheme.{u}}
    (k : Type u) [Field k] (x : Spec (.of k) ⟶ Z)
    (c : ULift.{u + 1} F →+* normedPointSectionRing F k) :
    NormedPointModules F Z ⥤ ModuleCat.{u + 1} (ULift.{u + 1} F) :=
  CondensedRing.upperStar (normContinuousRing F).X x ⋙ normedPointEvaluation F k c

/-- Insertion of one into the scalar extension defining the actual module inverse image.
This is a morphism of underlying abelian sheaves, not a new choice of pullback.
Source: HRS Section 3; Stacks 03EL (blueprint: lem-sfb-normed-point-exact-monoidal). -/
def normedPointPullbackInsertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStar Ab.{u + 1} f).obj M.X ⟶ ((CondensedRing.upperStar Λ f).obj M).X :=
  Mod.extendUnitHom (condensedPullbackHom Λ f)
    (((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj M)

/-- The two specified composite structure maps, expressed at the generic functor level
so checking their types does not unfold the internal/sectionwise equivalence.
Source: HRS Section 3 and Lemma 4.1(1), composition of the two tensor functors
(blueprint: lem-sfb-normed-point-exact-monoidal). -/
def normedPointCompositeMaps
    {A : Type uA} [Category.{vA} A] [MonoidalCategory A] [BraidedCategory A]
    {B : Type uB} [Category.{vB} B] [MonoidalCategory B] [BraidedCategory B]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [BraidedCategory D]
    (P : A ⥤ B) (E : B ⥤ D) (p : P.Braided) (e : E.Braided)
    (h : (P ⋙ E).Braided) : Prop :=
  (∀ M N : A, h.μ M N = e.μ (P.obj M) (P.obj N) ≫ E.map (p.μ M N)) ∧
    h.ε = e.ε ≫ E.map p.ε

/-- The constant-section map is a ring isomorphism; evaluation and the actual geometric
fibre are exact, additive and strong symmetric monoidal with the specified maps.
The equations for e fix b(n tensor n') = [n tensor n'] and its constant-section unit.
The equations for p fix q inverse on the inverse-image tensor generators and fix u inverse
through the coefficient isomorphism. The equations for h are exactly the displayed
composite tensorator and unit of the node. Braided includes the associativity, both unit
and symmetry equations and invertibility of every structural map.

Source: HRS Example 3.1, Section 3 and Lemma 4.1(1), pp.6--8
(blueprint: lem-sfb-normed-point-exact-monoidal).

Proof for stage 3:
1. Spec k is affine, strictly henselian and has one extremally disconnected component.
   By det-pe-wlocal-strict-contractible it is w-contractible. Apply det-pe-wcb-projective
   and det-pe-wcb-clopen-partition: terminal coverings refine the singleton partition.
2. By lem-weil-pbc-condensed-point-basis-evaluation the coefficient sections are C(*,F).
   Evaluation identifies this ring with F; its inverse is precisely the constant map c.
3. Transport through def-weil-pbc-internal-abelian-sheaf-module-equivalence and
   lem-pe-internal-section-tensor-comparison. By det-pe-sections-limits-colimits terminal
   evaluation preserves kernels and cokernels, hence is exact; it is sectionwise additive.
4. Apply lem-zl-partition-section-tensor-flat to the small pro-etale site and terminal
   object. Its balanced pairing is invertible and coherent. The internal tensor comparison
   fixes local pure tensors, so the resulting tensorator is exactly b and its unit is c.
5. The coefficient map alpha is invertible by sk-def-sfb-coefficient-morphisms.
   det-prop-sfb-module-pullback-exact-main gives exact additive module inverse image.
   Transport by lem-sfb-internal-module-operations-transport; apply the degree-zero case
   of lem-pur-cochain-pullback-tensor-coherence. The formulas multiply scalar factors and
   send a tensor r in the regular module to a alpha(r). Thus they give exactly q inverse
   and u, characterized by the two insertion equations below, with all coherences.
6. Compose these structures. Naturality moves the inner tensor comparisons through b;
   associativity, symmetry and both unit equations then follow from those for e and p.
   The composite formulas are h.mu = b followed by E(q inverse) and h.epsilon = c
   followed by E(u inverse). Exactness and additivity compose. No finiteness or
   completeness is used; zero modules and the identity point obey the same formulas. -/
theorem normed_point_exact_monoidal (F : Type u) [NormedField F]
    [TotallyDisconnectedSpace F] {Z : Scheme.{u}} (k : Type u) [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ Z) :
    ∃ c : ULift.{u + 1} F →+* normedPointSectionRing F k,
      (∀ a : F, c (ULift.up a) = normedPointConstantValue F k a) ∧
      Function.Bijective c ∧
      (normedPointEvaluation F k c).Additive ∧
      PreservesFiniteLimits (normedPointEvaluation F k c) ∧
      PreservesFiniteColimits (normedPointEvaluation F k c) ∧
      ∃ e : (normedPointEvaluation F k c).Braided,
        (∀ (N N' : NormedPointModules F (Spec (.of k)))
          (n : (normedPointEvaluation F k c).obj N)
          (n' : (normedPointEvaluation F k c).obj N'),
          (e.μ N N').hom (n ⊗ₜ[ULift.{u + 1} F] n') =
            ((Mod.tensorObjπ N N').hom.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
              (((Functor.LaxMonoidal.μ
                (sheafToPresheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
                N.X N'.X).app (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
                  (n ⊗ₜ[ℤ] n'))) ∧
        (∀ a : ULift.{u + 1} F, e.ε.hom a = c a) ∧
        ∃ p : (CondensedRing.upperStar (normContinuousRing F).X x).Braided,
          (∀ M N : NormedPointModules F Z,
            (normedPointPullbackInsertion (normContinuousRing F).X x M ⊗ₘ
                normedPointPullbackInsertion (normContinuousRing F).X x N) ≫
                Mod.tensorObjπ _ _ ≫ (p.μ M N).hom =
              Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} x) M.X N.X ≫
                (upperStar Ab.{u + 1} x).map (Mod.tensorObjπ M N) ≫
                  normedPointPullbackInsertion (normContinuousRing F).X x (M ⊗ N)) ∧
          (condensedPullbackHom (normContinuousRing F).X x ≫ p.ε.hom =
            normedPointPullbackInsertion (normContinuousRing F).X x
              (Mod.regular (condensedRingObj (normContinuousRing F).X Z))) ∧
          (normedPointFibre F k x c).Additive ∧
          PreservesFiniteLimits (normedPointFibre F k x c) ∧
          PreservesFiniteColimits (normedPointFibre F k x c) ∧
          ∃ h : (normedPointFibre F k x c).Braided,
            normedPointCompositeMaps (CondensedRing.upperStar (normContinuousRing F).X x)
              (normedPointEvaluation F k c) p e h := by
  sorry

end AlgebraicGeometry.ProEtale
