/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module
public import Sheaf.SixFunctors.PointEvaluationTensorCoherence
public import Sheaf.SixFunctors.PointEvaluationDerivedTensor
public import Sheaf.SixFunctors.PointEvaluationScalarCoherence
import Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.CategoryTheory.Localization.Predicate

/-! Source: Stacks 0991, 03EL, 07A4
(blueprint: lem-sf-point-ringed-evaluation-model). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.PointEvaluation
variable {k : Type u} [Field k]
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
/-- The lift in a pointed neighbourhood, as an arrow of the small site.
Full faithfulness changes only its category packaging.
Source: Stacks 0991 (blueprint: lem-sf-point-ringed-evaluation-model). -/
def pointedLift [IsAlgClosed k]
    (n : ProEtaleGeometricNeighbourhood (𝟙 (Spec (.of k)))) : finalObject k ⟶ n.right :=
  (Scheme.ProEt.forgetFullyFaithful (Spec (.of k))).preimage n.hom

/-- The actual ringed point, including the normalization of its ring and module inverse images.
The coefficient map is the identity because the point ring is the inverse-image ring itself.
Source: Stacks 0991, 03D2 (blueprint: lem-sf-point-ringed-evaluation-model). -/
def PointIdentification [IsAlgClosed k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) : Prop :=
  ∃ e : proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))) ≅
      (sheafSections (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))).obj
        (op (finalObject k)),
    (∀ (F : Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1)))
      (n : ProEtaleGeometricNeighbourhood (𝟙 (Spec (.of k)))) (x : F.obj.obj (op n.right)),
      e.hom.app F (colimit.ι (proEtaleGeometricStalkDiagram (𝟙 (Spec (.of k))) F) (op n) x) =
        F.obj.map (pointedLift n).op x) ∧
    ∃ p : GeometricMorphism (Type (u + 1))
        (Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))),
      p.inverse = proEtaleGeometricSetStalkFunctor (𝟙 (Spec (.of k))) ∧
      ∃ s : RingedSitePoint B p,
        s.ring = CommRingCat.of (sectionRing k B) ∧
        HEq s.ringUnderlying
          (e.app ((sheafCompose _ (CategoryTheory.forget CommRingCat.{u + 1})).obj B)) ∧
        HEq s.modules (pointModuleSections k B) ∧
        ∀ M : ModuleSheaves B,
          HEq (s.moduleUnderlying.hom.app M)
            (e.inv.app ((SheafOfModules.toSheaf _ ⋙
              sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M))

universe e

/-- The specified constant-section ring map, using only the unit of sheafification.
The ULift is the recorded coefficient-size transport and has inverse `down`.
Source: blueprint order 1455 (blueprint: lem-sf-point-ringed-evaluation-model). -/
def constantSection (k : Type u) [Field k] (A : Type e) [CommRing A] :
    A →+* (((constantSheaf (Scheme.ProEt.topology (Spec (.of k)))
      CommRingCat.{max e (u + 1)}).obj (CommRingCat.of (ULift.{u + 1} A))).obj.obj
        (op (finalObject k))) :=
  ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} A)))).app (op (finalObject k))).hom.comp
    (ULift.ringEquiv.symm.toRingHom)

/-- Integral constants followed by the actual map to the inverse-limit ring sheaf.
Source: blueprint order 1455 (blueprint: lem-sf-point-ringed-evaluation-model). -/
def integralSection (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : Type e) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Padic.coefficientExtensionIntegers l E →+*
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E (Spec (.of k))).obj.obj
        (op (finalObject k)) :=
  (((WeilConjectures.integralConstantToCompletionOfUniverses l E (Spec (.of k))).hom.app
    (op (finalObject k))).hom).comp (constantSection k (Padic.coefficientExtensionIntegers l E))

/-- Finite and completed section identifications are the specified constant and quotient maps.
The natural index n represents exponent n+1; no exponent zero is silently included.
Source: blueprint order 1455 and Bhatt--Scholze Lemma 4.2.12
(blueprint: lem-sf-point-ringed-evaluation-model). -/
def CoefficientsIdentified (k : Type u) [Field k] : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E : Type e) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E],
    (∀ n : ℕ, Function.Bijective (constantSection k (Padic.coefficientExtensionRing l E (n + 1)))) ∧
    Function.Bijective (integralSection k l E) ∧
    (∀ (n : ℕ) (a : Padic.coefficientExtensionIntegers l E),
      ((limit.π (WeilConjectures.integralCoefficientSheafSystem l E (Spec (.of k))) (op n)).hom.app
        (op (finalObject k))) (integralSection k l E a) =
      constantSection k (Padic.coefficientExtensionRing l E (n + 1))
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a)) ∧
    (∀ (n : ℕ) (a : Padic.coefficientExtensionRing l E (n + 2)),
      ((WeilConjectures.integralCoefficientSheafTransition l E (Spec (.of k)) n).hom.app
        (op (finalObject k))) (constantSection k (Padic.coefficientExtensionRing l E (n + 2)) a) =
      constantSection k (Padic.coefficientExtensionRing l E (n + 1))
        (Padic.coefficientExtensionTransition l E (n + 1) a))


/-- The unit comparison is exactly the degree-zero lift of the identity on B(s).
Source: Stacks 03EL, 07A4 (blueprint: lem-sf-point-ringed-evaluation-model). -/
def UnitNormalized (T : TensorModel B)
    [(pointModuleSections k B).PreservesZeroMorphisms] : Prop :=
  HEq T.unit
    ((HomologicalComplex.singleMapHomologicalComplex (W₁ := ModuleSheaves B)
      (W₂ := ModuleCat.{u + 1} (sectionRing k B)) (pointModuleSections k B) (.up ℤ) 0).app
      (SheafOfModules.unit.{u, u + 1, u + 1}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) ≪≫
      (HomologicalComplex.single (ModuleCat.{u + 1} (sectionRing k B)) (.up ℤ) 0).mapIso
        T.moduleUnit)

/-- Final-object evaluation realizes the actual ringed point and its signed derived tensor.
Source: Stacks 0991, 03EL, 03D2, 07A4; blueprint order 1455
(blueprint: lem-sf-point-ringed-evaluation-model).

Proof plan:
1. The pointed final neighbourhood is initial: its only arrow to (U,u) is u.
   Restriction along u computes the stalk colimit; use the geometric-stalk topos point.
2. Restriction preserves ring and module operations. Identity change of scalars therefore
   identifies the ringed module inverse image with final-object evaluation. Apply
   point_proEtale_sections_exact for exactness and the induced derived functor.
3. Specialize the canonical ringed tensor comparison. On each total summand its inverse
   is the section tensor; the cochain differential has the sign (-1)^i in its second term.
4. Pullback preserves flat terms and K-flatness. The representative square in 07A4
   identifies the localized comparison with the canonical derived comparison. Two-variable
   resolving localization gives uniqueness, naturality and independence of models.
5. On three pure generators reassociation preserves order; the unitors multiply scalars;
   exchanging degrees i,j contributes (-1)^(ij). Extend by the coproduct universal property.
6. For every coefficient morphism the tensor square is the balanced identity
   (a tensor x) tensor (b tensor y) maps to ab tensor (x tensor y). No flatness of the
   coefficient map is needed; this includes identity maps and composites.
7. Localize these equalities on flat-term K-flat representatives. The localization
   universal property gives the derived scalar square and all descended constraints.
8. Finite constant sections are constant functions on the singleton point. Evaluation
   identifies the specified constant-section and residue transition maps.
9. Sections commute with the residue-system limit. Completeness of the finite extension's
   integer ring identifies it with that limit, via its actual quotient maps. All tensors
   used above are the ordinary ambient tensor, before any completion. -/
theorem point_ringed_evaluation_model (k : Type u) [Field k] [IsAlgClosed k] :
    (∃ T : ∀ B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
        TensorModel B,
      (∀ B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
        PointIdentification B ∧ TensorCoherent B (T B) ∧
        (∀ [(pointModuleSections k B).PreservesZeroMorphisms], UnitNormalized B (T B)) ∧
        PreservesFiniteLimits (pointModuleSections k B) ∧
        PreservesFiniteColimits (pointModuleSections k B) ∧
        ∀ [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
          [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
          [(pointModuleSections k B).Additive]
          [PreservesFiniteLimits (pointModuleSections k B)]
          [PreservesFiniteColimits (pointModuleSections k B)],
          DerivedCompatible B (T B)) ∧
      (∀ (B B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
        (a : B ⟶ B'), ∃ S : ScalarModel a (T B) (T B'), ScalarCoherent a (T B) (T B') S ∧
          ∀ [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
            [HasDerivedCategory.{u + 2} (ModuleSheaves B')]
            [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
            [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B'))]
            [(pointModuleSections k B).Additive] [(pointModuleSections k B').Additive]
            [PreservesFiniteLimits (pointModuleSections k B)]
            [PreservesFiniteColimits (pointModuleSections k B)]
            [PreservesFiniteLimits (pointModuleSections k B')]
            [PreservesFiniteColimits (pointModuleSections k B')],
            ScalarDerivedCompatible B a (T B) (T B') S)) ∧
    CoefficientsIdentified.{u, e} k := by
  sorry

end AlgebraicGeometry.ProEtale.PointEvaluation
