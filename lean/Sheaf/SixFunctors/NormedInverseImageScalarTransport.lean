module


public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula

/-!
# Normalized inverse-image and scalar transport for normed coefficients

Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport).

The statement records coefficient restriction, the normalized inverse-image comparison,
and its extension to point sections and unbounded derived categories.  The proof follows
naturality of the pulled-back coefficient maps, the internal/sectionwise module equivalence,
and exact localization of complexes.

## Main definitions and statement

* `normedContraction`: the scalar-isomorphism contraction of the specified inverse image.
* `normedScalarComparison`: the canonical inverse-image/restriction comparison.
* `IsNormedSectionScalarCompatible`: identity restriction and balanced-generator extension.
* `IsNormedPointScalarCompatible`: constant-field point sections and their unbounded localization.
* `normed_inverse_image_scalar_transport`: all the prescribed normalization properties.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open CategoryTheory.InternalAbelianSheafModule
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale

/-- The condensed coefficient ring attached to a normed field.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable abbrev normedCoefficient (F : Type u) [NormedField F] :
    Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1} :=
  Profinite.continuousMapRingObjOfUniverse.{u, u} F

/-- Canonical continuous-function ring object.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable instance normedCoefficientMonObj (F : Type u) [NormedField F] :
    MonObj (normedCoefficient F) :=
  Profinite.continuousMapRingObjOfUniverseMonObj F

/-- Commutativity of continuous-function coefficients.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable instance normedCoefficientComm (F : Type u) [NormedField F] :
    IsCommMonObj (normedCoefficient F) :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse F

/-- Postcomposition induces the pulled-back coefficient map.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable abbrev normedCoefficientMap {F F' : Type u} [NormedField F] [NormedField F']
    (a : F →+* F') (ha : Continuous a) (T : Scheme.{u}) :
    condensedRingObj (normedCoefficient F) T ⟶ condensedRingObj (normedCoefficient F') T :=
  (upperStarFromPoint T).map (Profinite.continuousMapRingObjMapOfUniverse.{u, u} a ha)

/-- Postcomposition is a morphism of coefficient ring objects.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable instance normedCoefficientMapMonHom {F F' : Type u}
    [NormedField F] [NormedField F'] (a : F →+* F') (ha : Continuous a) (T : Scheme.{u}) :
    IsMonHom (normedCoefficientMap a ha T) := by
  let := Profinite.isMonHom_continuousMapRingObjMapOfUniverse.{u, u} a ha
  exact inferInstanceAs
    (IsMonHom ((upperStarFromPoint T).map
      (Profinite.continuousMapRingObjMapOfUniverse.{u, u} a ha)))

/-- The internal category with the specified pulled-back continuous coefficients.
Source: Hemo--Richarz--Scholbach, Section 3
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable abbrev NormedModules (F : Type u) [NormedField F] (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
    (condensedRingObj (normedCoefficient F) T)

/-- Restriction along the actual pulled-back postcomposition morphism.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable abbrev normedRestriction {F F' : Type u} [NormedField F] [NormedField F']
    (a : F →+* F') (ha : Continuous a) (T : Scheme.{u}) :
    NormedModules F' T ⥤ NormedModules F T :=
  Mod.comap (normedCoefficientMap a ha T)

/-- Module inverse image, keeping the prescribed forward extension of scalars.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable abbrev normedPullback (F : Type u) [NormedField F]
    {X Y : Scheme.{u}} (f : Y ⟶ X) : NormedModules F X ⥤ NormedModules F Y :=
  CondensedRing.upperStar (normedCoefficient F) f

/-- The same inverse image with action restricted through the inverse coefficient isomorphism.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable abbrev normedTransportedPullback (F : Type u) [NormedField F]
    {X Y : Scheme.{u}} (f : Y ⟶ X) : NormedModules F X ⥤ NormedModules F Y :=
  (ProEtale.upperStar AddCommGrpCat.{u + 1} f).mapMod
      (condensedRingObj (normedCoefficient F) X) ⋙
    Mod.comap (asIso (condensedPullbackHom (normedCoefficient F) f)).inv

/-- The canonical scalar-isomorphism contraction, fixed by the extension adjunction.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable def normedContraction (F : Type u) [NormedField F]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    normedPullback F f ≅ normedTransportedPullback F f :=
  Functor.isoWhiskerLeft _
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom (normedCoefficient F) f))

/-- The canonical restriction/inverse-image comparison, oriented as in the node.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable def normedScalarComparison {F F' : Type u} [NormedField F] [NormedField F']
    (a : F →+* F') (ha : Continuous a) {X Y : Scheme.{u}} (f : Y ⟶ X) :
    normedRestriction a ha X ⋙ normedPullback F f ≅
      normedPullback F' f ⋙ normedRestriction a ha Y := by
  letI := Profinite.isMonHom_continuousMapRingObjMapOfUniverse.{u, u} a ha
  exact (CondensedRing.comapUpperStarIso
    (Profinite.continuousMapRingObjMapOfUniverse.{u, u} a ha) f).symm

/-- A scalar as a morphism from the condensed tensor unit, obtained from constant functions.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable def normedCondensedConstant (F : Type u) [NormedField F] (c : F) :
    𝟙_ (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) ⟶
      normedCoefficient F := by
  refine Functor.LaxMonoidal.ε
    (presheafToSheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) ≫
      ((sheafificationAdjunction (coherentTopology Profinite.{u})
        AddCommGrpCat.{u + 1}).homEquiv _ _).symm ?_
  refine
    { app := fun S ↦ ?_
      naturality := ?_ }
  · exact AddCommGrpCat.ofHom
      ((zmultiplesHom _ (ULift.up (ContinuousMap.const S.unop c))).comp
        AddEquiv.ulift.toAddMonoidHom)
  · intro S T f
    ext z
    rfl

/-- Constant scalar sections on the scheme, using monoidal inverse image from the point.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable def normedConstantSection (F : Type u) [NormedField F]
    (T : Scheme.{u}) (c : F) (U : T.ProEtᵒᵖ) :
    (condensedRingObj (normedCoefficient F) T).obj.obj U :=
  ((Functor.LaxMonoidal.ε
      (sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) ≫
    (sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).map
      (Functor.LaxMonoidal.ε (upperStarFromPoint T) ≫
        (upperStarFromPoint T).map (normedCondensedConstant F c))).app U) (ULift.up (1 : ℤ))

/-- The abstract field action on sections, by the specified constant scalar sections.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable def normedSectionAction (F : Type u) [NormedField F] (T : Scheme.{u})
    (M : NormedModules F T) (U : T.ProEtᵒᵖ) (c : F) (m : M.X.obj.obj U) :
    M.X.obj.obj U :=
  (((Functor.LaxMonoidal.μ
      (sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
      (condensedRingObj (normedCoefficient F) T) M.X).app U) ≫
    (Mod.act M.X).hom.app U) (normedConstantSection F T c U ⊗ₜ[ℤ] m)

/-- The action by constant sections satisfies the six module laws.
Source: Hemo--Richarz--Scholbach, Example 3.1 and Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport).
Proof: constant functions preserve one, sums and products. Monoidal inverse image and
section reconstruction preserve these ring identities. Apply the unit, associativity
and additivity axioms of the internal module action to these constant sections. -/
theorem normedSectionAction_laws (F : Type u) [NormedField F] (T : Scheme.{u})
    (M : NormedModules F T) (U : T.ProEtᵒᵖ) :
    (∀ m, normedSectionAction F T M U 1 m = m) ∧
    (∀ c d m, normedSectionAction F T M U (c * d) m =
      normedSectionAction F T M U c (normedSectionAction F T M U d m)) ∧
    (∀ c, normedSectionAction F T M U c 0 = 0) ∧
    (∀ c m n, normedSectionAction F T M U c (m + n) =
      normedSectionAction F T M U c m + normedSectionAction F T M U c n) ∧
    (∀ m, normedSectionAction F T M U 0 m = 0) ∧
    (∀ c d m, normedSectionAction F T M U (c + d) m =
      normedSectionAction F T M U c m + normedSectionAction F T M U d m) := by
  sorry

/-- The section module has precisely the action by the prescribed constant functions.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
@[instance_reducible]
noncomputable def normedSectionModule (F : Type u) [NormedField F] (T : Scheme.{u})
    (M : NormedModules F T) (U : T.ProEtᵒᵖ) : Module F (M.X.obj.obj U) where
  smul := normedSectionAction F T M U
  one_smul := (normedSectionAction_laws F T M U).1
  mul_smul := (normedSectionAction_laws F T M U).2.1
  smul_zero := (normedSectionAction_laws F T M U).2.2.1
  smul_add := (normedSectionAction_laws F T M U).2.2.2.1
  zero_smul := (normedSectionAction_laws F T M U).2.2.2.2.1
  add_smul := (normedSectionAction_laws F T M U).2.2.2.2.2

/-- Internal module morphisms are linear for the action by constant sections.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport).
Proof: evaluate the internal linearity equation on the tensor of the constant section c
with m. Naturality of the lax tensor comparison for sheaf-to-presheaf identifies its
two sides with the asserted formulas. -/
theorem normedSectionAction_map (F : Type u) [NormedField F] (T : Scheme.{u})
    {M N : NormedModules F T} (h : M ⟶ N) (U : T.ProEtᵒᵖ) (c : F) (m : M.X.obj.obj U) :
    h.hom.hom.app U (normedSectionAction F T M U c m) =
      normedSectionAction F T N U c (h.hom.hom.app U m) := by
  sorry

/-- Global sections as abstract F-modules, evaluated on the terminal pro-étale object.
Source: Hemo--Richarz--Scholbach, Lemma 4.1(1)
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable def normedSectionsModule (F : Type u) [NormedField F] (T : Scheme.{u}) :
    NormedModules F T ⥤ ModuleCat.{u + 1} F where
  obj M := by
    letI := normedSectionModule F T M (Opposite.op (Scheme.ProEt.mk (𝟙 T)))
    exact ModuleCat.of F (M.X.obj.obj (Opposite.op (Scheme.ProEt.mk (𝟙 T))))
  map {M N} h := by
    letI := normedSectionModule F T M (Opposite.op (Scheme.ProEt.mk (𝟙 T)))
    letI := normedSectionModule F T N (Opposite.op (Scheme.ProEt.mk (𝟙 T)))
    exact ModuleCat.ofHom
      { toFun := h.hom.hom.app (Opposite.op (Scheme.ProEt.mk (𝟙 T)))
        map_add' := map_add _
        map_smul' := normedSectionAction_map F T h _ }
  map_id M := by ext; rfl
  map_comp h g := by ext; rfl

/-- Addition of maps is evaluated sectionwise.
Source: Hemo--Richarz--Scholbach, Section 3 and Lemma 4.1(1)
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
instance normedSectionsModule_additive (F : Type u) [NormedField F] (T : Scheme.{u}) :
    (normedSectionsModule F T).Additive where
  map_add := by intros; ext m; rfl

/-- Standard ordinary unbounded localization for abstract coefficient modules.
Source: the compatible-size convention and Hemo--Richarz--Scholbach, Section 3
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable instance normedAbstractModulesDerived (F : Type u) [NormedField F] :
    HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} F) :=
  HasDerivedCategory.standard (ModuleCat.{u + 1} F)

/-- Point sections retain the specified scalar restriction, and their termwise comparison
has a localization to ordinary unbounded derived categories, normalized on every complex.
The comparison of additive maps is the evaluated internal comparison, so after the two
contractions it is identity. The factorization is required on all complexes.
Source: Hemo--Richarz--Scholbach, Section 3 and Lemma 4.1(1)
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
def IsNormedPointScalarCompatible {F F' : Type u} [NormedField F] [NormedField F']
    (a : F →+* F') (ha : Continuous a) {X : Scheme.{u}}
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X) : Prop :=
  ∃ pointComparison : normedRestriction a ha X ⋙ normedPullback F x ⋙
        normedSectionsModule F (Spec (.of k)) ≅
      normedPullback F' x ⋙ normedSectionsModule F' (Spec (.of k)) ⋙
        ModuleCat.restrictScalars a,
    (∀ (N : NormedModules F' X)
      (n : ((normedPullback F x).obj ((normedRestriction a ha X).obj N)).X.obj.obj
        (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))),
      (pointComparison.hom.app N) n =
        (((normedScalarComparison a ha x).hom.app N).hom.hom.app
          (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) n) ∧
    ∃ leftDerived rightDerived : DerivedCategory (NormedModules F' X) ⥤
        DerivedCategory (ModuleCat.{u + 1} F),
    ∃ leftFactors : DerivedCategory.Q ⋙ leftDerived ≅
        (normedRestriction a ha X ⋙ normedPullback F x ⋙
          normedSectionsModule F (Spec (.of k))).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
    ∃ rightFactors : DerivedCategory.Q ⋙ rightDerived ≅
        (normedPullback F' x ⋙ normedSectionsModule F' (Spec (.of k)) ⋙
          ModuleCat.restrictScalars a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
    ∃ derivedComparison : leftDerived ≅ rightDerived,
      ∀ K : CochainComplex (NormedModules F' X) ℤ,
        derivedComparison.hom.app (DerivedCategory.Q.obj K) ≫ rightFactors.hom.app K =
          leftFactors.hom.app K ≫ DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex pointComparison (.up ℤ)).hom.app K)

set_option maxHeartbeats 800000 in
-- Elaborating both reconstructed ring actions requires unfolding the section equivalence.
/-- The ordinary section comparison: restriction is identity and extension fixes balanced
local generators. Naturality is included; no assertion that all tensor sections are pure is made.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6; Stacks 03EK
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
def IsNormedSectionScalarCompatible (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] : Prop :=
  (∃ restriction : Mod.comap a ⋙
        (sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) R).functor ≅
      (sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) S).functor ⋙
        SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose (Scheme.ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) a)),
    ∀ (N : Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) S)
      (U : T.ProEtᵒᵖ) (n : N.X.obj.obj U), (restriction.hom.app N).val.app U n = n) ∧
  ∃ extension : ∀ M : Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) R,
      (sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) S).functor.obj
          ((Mod.extendScalars a).obj M) ≅
        SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) a)
          ((sectionModuleEquivalence
            (Scheme.ProEt.topology T) R).functor.obj M),
    (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) R) (h : M ⟶ N),
      (sectionModuleEquivalence
          (Scheme.ProEt.topology T) S).functor.map ((Mod.extendScalars a).map h) ≫
          (extension N).hom =
        (extension M).hom ≫ SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) a) _
          ((sectionModuleEquivalence
            (Scheme.ProEt.topology T) R).functor.map h)) ∧
    ∀ (M : Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) R)
      (U : T.ProEtᵒᵖ) (b : S.obj.obj U) (m : M.X.obj.obj U),
      SheafOfModules.scalarExtensionRingIsoTmul.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) a)
          ((sectionModuleEquivalence (Scheme.ProEt.topology T) R).functor.obj M) U
          (@id (((sectionModuleEquivalence (Scheme.ProEt.topology T) R).functor.obj M).val.obj U)
            m)
          (@id ((sectionRingSheaf (Scheme.ProEt.topology T) S).obj.obj U) b) =
        (extension M).hom.val.app U
          (internalScalarGenerator
            (Scheme.ProEt.topology T) a M U b m)

/-- Contraction is fixed on all generators and its inverse is the ordinary unit. Quantifying
all modules includes the regular module, so its ring-unit normalization is also specified.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
def IsNormedContractionNormalized (F : Type u) [NormedField F]
    {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∀ P : Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} f).obj
        (condensedRingObj (normedCoefficient F) X)),
    (Mod.extendπ (condensedPullbackHom (normedCoefficient F) f) P ≫
        ((Mod.extendScalarsIsoComapInv
          (condensedPullbackHom (normedCoefficient F) f)).hom.app P).hom =
      (asIso (condensedPullbackHom (normedCoefficient F) f)).inv ▷ P.X ≫ Mod.act P.X) ∧
    (((Mod.extendScalarsIsoComapInv
        (condensedPullbackHom (normedCoefficient F) f)).inv.app P).hom =
      Mod.extendUnitHom (condensedPullbackHom (normedCoefficient F) f) P)

/-- The derived comparison is localization of the termwise, normalized comparison.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6
(blueprint: lem-sfb-normed-inverse-image-scalar-transport). -/
noncomputable def normedDerivedScalarComparison {F F' : Type u}
    [NormedField F] [NormedField F'] (a : F →+* F') (ha : Continuous a)
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (normedRestriction a ha X ⋙ normedPullback F f).mapDerivedCategory ≅
      (normedPullback F' f ⋙ normedRestriction a ha Y).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (normedScalarComparison a ha f)

/-- Continuous normed coefficient restriction commutes with inverse image, with the
specified identity normalization, sectionwise balanced generators, point scalars and
ordinary unbounded localization.
Source: Hemo--Richarz--Scholbach, Section 3, printed p. 6, Example 3.1 and Lemma 4.1(1)
(blueprint: lem-sfb-normed-inverse-image-scalar-transport).

Proof:
1. Postcomposition with a gives the condensed ring map. Naturality of the coefficient
comparison (def-sfb-alpha) gives the square; composing with both inverses gives its
inverse form. This works for arbitrary commutative condensed rings.
2. Reconstruction leaves abelian sheaves fixed. Restriction therefore fixes sections.
The relative tensor comparison (lem-pe-internal-section-tensor-comparison) identifies
both extensions by sending each local balanced generator to itself; their S-actions agree.
3. For A = f⁻¹F_X, B = F_Y, the balanced map b tensor p to alpha⁻¹(b)p has inverse
p to 1 tensor p. Balancing proves both compositions are identities. The formulas are
linear, natural, and on the regular module give b tensor 1 to alpha⁻¹(b), preserving units.
4. Exact faithful forgetful functors detect exactness by
lem-weil-pbc-module-sheaves-colimits-forgetful and lem-weil-pbc-jointly-reflect-short-exact.
Restriction is identity on these functors and additive. Normalized inverse image has
underlying exact abelian inverse image (lem-sfb-finite-upper-star-exact), so is exact too.
5. The two normalized modules have underlying f⁻¹N and actions precomposed with the
two equal inverse-square maps. Their identity is linear and natural; conjugate it by
the contractions to obtain the comparison of the original extension functors.
6. At Spec of an algebraically closed field, take global sections. Constants restrict
by c to a(c), so the same identity is F-linear. This does not require an equivalence
of all point sheaves with vector spaces or exact sections on a general scheme.
7. Apply the comparisons termwise. Exact additive functors preserve quasi-isomorphisms by
lem-weil-pbc-exact-functor-derived-factorization. Localize both chain isomorphisms and their
inverses by def-weil-abstract-derived-category; the representative formulas are unchanged.
For point sections use exactness from lem-sfb-normed-point-exact-monoidal and apply the
same factorization. No boundedness, completeness, constructibility or flatness is used. -/
theorem normed_inverse_image_scalar_transport
    {F F' : Type u} [NormedField F] [NormedField F']
    [TotallyDisconnectedSpace F] [TotallyDisconnectedSpace F']
    (a : F →+* F') (ha : Continuous a) :
    (∀ T : Scheme.{u}, (normedRestriction a ha T).Additive ∧
      PreservesFiniteLimits (normedRestriction a ha T) ∧
      PreservesFiniteColimits (normedRestriction a ha T) ∧
      (normedRestriction a ha T ⋙ Mod.forget _) = Mod.forget _ ∧
      IsNormedSectionScalarCompatible T (normedCoefficientMap a ha T)) ∧
    ∀ (X Y : Scheme.{u}) (f : Y ⟶ X),
      IsIso (condensedPullbackHom (normedCoefficient F) f) ∧
      IsIso (condensedPullbackHom (normedCoefficient F') f) ∧
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} f).map (normedCoefficientMap a ha X) ≫
        condensedPullbackHom (normedCoefficient F') f =
          condensedPullbackHom (normedCoefficient F) f ≫ normedCoefficientMap a ha Y) ∧
      ((asIso (condensedPullbackHom (normedCoefficient F) f)).inv ≫
        (ProEtale.upperStar AddCommGrpCat.{u + 1} f).map (normedCoefficientMap a ha X) =
          normedCoefficientMap a ha Y ≫
            (asIso (condensedPullbackHom (normedCoefficient F') f)).inv) ∧
      IsNormedContractionNormalized F f ∧ IsNormedContractionNormalized F' f ∧
      IsNormedSectionScalarCompatible Y (condensedPullbackHom (normedCoefficient F) f) ∧
      IsNormedSectionScalarCompatible Y (condensedPullbackHom (normedCoefficient F') f) ∧
      (∀ N : NormedModules F' X,
        ((normedScalarComparison a ha f).hom.app N).hom ≫
            ((normedContraction F' f).hom.app N).hom =
          ((normedContraction F f).hom.app ((normedRestriction a ha X).obj N)).hom) ∧
      (∀ N : NormedModules F' X,
        Mod.act ((normedTransportedPullback F f).obj ((normedRestriction a ha X).obj N)).X =
          ((asIso (condensedPullbackHom (normedCoefficient F) f)).inv ≫
              (ProEtale.upperStar AddCommGrpCat.{u + 1} f).map
                (normedCoefficientMap a ha X)) ▷
            ((ProEtale.upperStar AddCommGrpCat.{u + 1} f).obj N.X) ≫
          Mod.act (((ProEtale.upperStar AddCommGrpCat.{u + 1} f).mapMod
            (condensedRingObj (normedCoefficient F') X)).obj N).X) ∧
      (∀ K : CochainComplex (NormedModules F' X) ℤ,
        (normedDerivedScalarComparison a ha f).hom.app (DerivedCategory.Q.obj K) ≫
          (normedPullback F' f ⋙ normedRestriction a ha Y).mapDerivedCategoryFactors.hom.app K =
        (normedRestriction a ha X ⋙ normedPullback F f).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (normedScalarComparison a ha f) (.up ℤ)).hom.app K)) ∧
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X),
        IsNormedPointScalarCompatible a ha k x := by
  sorry

end AlgebraicGeometry.ProEtale
