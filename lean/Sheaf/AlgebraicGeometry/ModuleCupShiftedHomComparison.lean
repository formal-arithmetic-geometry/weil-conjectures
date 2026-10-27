module

public import Sheaf.AlgebraicGeometry.SingleTensorAugmentationCoherence
public import Sheaf.AlgebraicGeometry.LocalizationTensoratorSignedShifts
public import Sheaf.Paper.ModuleCohomologyCupProduct
public import Sheaf.Paper.ShiftedTensorMorphismCalculus
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import Sheaf.Paper.ModuleCupPairingExists
import Sheaf.Paper.ModuleCupResolutionExistence

/-! # Ordinary cup as tensor of normalized shifted derived morphisms

Source: Stacks Project, Cohomology, Tags 01DZ, 0FKU, 0FKV and 0FP2, including the
sign footnote to the proof of lemma-second-cup-equals-first.
(blueprint: lem-sfb-module-cup-shifted-hom-comparison)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- The complete normalized comparison assertion. The resolution equation uses
`InjectiveResolution.extMk`: its `extMk_hom` formula is evaluation on one followed by
localization of the cocycle map and the inverse localized augmentation. In particular
this fixes the equivalences, rather than merely requiring natural abstract isomorphisms.
The degree-zero and unit equations include the canonical zero-shift identification.
The cup equation uses exactly the augmentation of SingleTensorAugmentationCoherence
and the second-shift-first comparison of LocalizationTensoratorSignedShifts. Its first
three arrows are the inverse left unitor transported along localization's unit comparison.
Source: Stacks Project, Cohomology, Tags 01DZ, 0FKU, 0FKV and 0FP2
(blueprint: lem-sfb-module-cup-shifted-hom-comparison). -/
def SchemeModuleCupShiftedHomComparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] : Prop := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  letI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  letI : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  letI := schemeModule_hasFunctorialFlatResolution X
  letI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  letI := schemeDerivedTensorMonoidal X
  letI : EnoughInjectives A :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  letI : HasExt.{u} A := hasExt_of_enoughInjectives.{u, u, u + 1} A
  let Q := DerivedCategory.Q.{w} (C := A)
  letI := CategoryTheory.RingedDerivedNative.localization_isIso_ε (A := A)
  let s := DerivedCategory.singleFunctor A 0
  let t := CochainComplex.singleFunctor A 0
  let U := SheafOfModules.unit (moduleRings X.toRingedSpace)
  let H := RingedSpace.moduleCohomology X.toRingedSpace
  let ΓX := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let m := fun (F G : A) ↦ Functor.LaxMonoidal.μ Q (t.obj F) (t.obj G) ≫
    Q.map (DerivedCategory.moduleCup_singleTensorIso F G).hom
  exact ∃ e : ∀ (F : A) (n : ℕ),
      (H n).obj F ≃+ (s.obj U ⟶ (s.obj F)⟦(n : ℤ)⟧),
    (∀ (F : A) (I : InjectiveResolution F) (n : ℕ)
      (a : (RingedSpace.globalSectionsComplex I).cycles n)
      (φ : U ⟶ I.cocomplex.X n) (hφ : φ ≫ I.cocomplex.d n (n + 1) = 0),
      φ.val.app (op ⊤) (1 : Γ(X, ⊤)) =
        (RingedSpace.globalSectionsComplex I).iCycles n a →
      e F n ((I.isoRightDerivedObj ΓX n).inv
        ((RingedSpace.globalSectionsComplex I).homologyπ n a)) =
          (I.extMk φ (n + 1) rfl hφ).hom) ∧
    (∀ (F G : A) (φ : F ⟶ G) (n : ℕ) (a : (H n).obj F),
      e G n ((H n).map φ a) = e F n a ≫ (s.map φ)⟦(n : ℤ)⟧') ∧
    (∀ (F : A) (v : Γ(F, ⊤)) (φ : U ⟶ F),
      φ.val.app (op ⊤) (1 : Γ(X, ⊤)) = v →
      e F 0 ((ΓX.toRightDerivedZero.app F) v) =
        s.map φ ≫ (shiftFunctorZero (schemeDerivedCategory X) ℤ).inv.app (s.obj F)) ∧
    e U 0 ((ΓX.toRightDerivedZero.app U) (1 : Γ(X, ⊤))) =
      (shiftFunctorZero (schemeDerivedCategory X) ℤ).inv.app (s.obj U) ∧
    ∀ (F G : A) (p q : ℕ)
      (cup : (H p).obj F →ₗ[Γ(X, ⊤)] (H q).obj G →ₗ[Γ(X, ⊤)]
        (H (p + q)).obj (F ⊗ G)),
      Scheme.Modules.IsModuleCupProduct F G p q cup →
      ∀ (a : (H p).obj F) (b : (H q).obj G),
        e (F ⊗ G) (p + q) (cup a b) =
          inv (Functor.LaxMonoidal.ε Q) ≫ (λ_ (s.obj U)).inv ≫
            (Functor.LaxMonoidal.ε Q ⊗ₘ 𝟙 (s.obj U)) ≫
            (e F p a ⊗ₘ e G q b) ≫
            (schemeSignedDerivedTensorShift X (s.obj F) (s.obj G) p q).hom ≫
            eqToHom (congrArg (fun n : ℤ ↦ (s.obj F ⊗ s.obj G)⟦n⟧)
              (Nat.cast_add p q).symm) ≫
            (m F G)⟦((p + q : ℕ) : ℤ)⟧'

/-- Module cohomology is naturally shifted derived Hom from O_X, with the canonical
injective-resolution normalization, its degree-zero section and unit formulas, and the
ordinary unsigned cup formula for arbitrary module sheaves.
Source: Stacks Project, Cohomology, Tags 01DZ, 0FKU, 0FKV and 0FP2
(blueprint: lem-sfb-module-cup-shifted-hom-comparison).

Proof: (1) Resolve F by injectives. Evaluation on one identifies cocycles of global
sections with maps from O_X to the shifted resolution; boundaries are exactly homotopies.
Bounded-below injective complexes are K-injective, so localization gives an additive
bijection on these homotopy classes. Postcompose with the inverse localized augmentation.
(2) Comparing any two resolutions over F cancels their localized augmentations. Thus this
bijection has the displayed normalization for every I, exactly Mathlib's extMk_hom formula.
(3) A comparison extending a coefficient map induces its right-derived cohomology map
by lem-sp-derived-injective-resolution-naturality. Cancellation proves naturality.
In degree zero the augmentation cancels and leaves the actual module map sending one
to the section; the section one gives the identity with the zero-shift comparison.
(4) Choose computing resolution pairings by lem-sc-module-cup-pairing-exists, and realize
them on total tensor by lem-sc-module-cup-resolution-existence. The augmentation equation
lem-sc-module-cup-resolution-augmentation and lax tensorator naturality identify their
localized coefficient map with the fixed m of lem-sfb-single-tensor-augmentation-coherence.
(5) Represent the two classes by global cocycles. Their paired cocycle represents the
ordinary unsigned cup by def-sc-module-cohomology-cup-product. The corresponding shifted
chain maps have source in degree zero. Extracting the second shift first has sign
(-1)^(q*i), hence sign one on their images since i=0.
(6) Apply lem-sfb-localization-tensorator-signed-shifts to these arbitrary computing
complexes and use the unit equation of lem-sf-ringed-derived-native-tensor. This gives
the stated tensor of the two localized cocycle maps without requiring either computing
complex to be flat. Move the localized augmentations through the shift comparison by
lem-weil-pbc-derived-tensor-shift-descent and cancel them. Step (4) leaves precisely m.
This proves the formula for all nonnegative p,q and all F,G, with no geometric or
coefficient flatness assumptions. -/
theorem scheme_module_cup_shifted_hom_comparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    SchemeModuleCupShiftedHomComparison.{u, w} X := by
  sorry

end AlgebraicGeometry
