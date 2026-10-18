/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleModuleObjects
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.SheafTensorStructure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# Transport of internal module operations to sectionwise modules

Source: blueprint main-20261015, Nagata density normalization, sheaves proof, Steps 1--2;
Stacks Project, Modules on Sites, Tags 03D6 and 03D7; Categories, Tag 0B65.
(blueprint: lem-sfb-internal-module-operations-transport).

The sectionwise pushforward uses the actual section-ring homomorphism induced by eta_f.
Pullback is its canonical left adjoint, hence the sheafified tensor-formula pullback.
Open extension is the canonical left adjoint of restriction. Unique characterizations fix
all comparisons; in particular no arbitrary natural isomorphism is used for base change.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
namespace InternalModuleOperations

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The reconstructed section-ring sheaf B_T, using the recorded reconstruction.
Source: Stacks 00YV (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev ring (T : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T))

/-- The fixed internal/sectionwise equivalence E_T, not a new equivalence.
Source: Stacks 00YV (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev equivalence (T : Scheme.{u}) :=
  sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T)

/-- The base-change functor on the small pro-etale sites.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev siteMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

/-- Continuity of the existing base-change functor, exposed at this abbreviation.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
instance siteMap_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (siteMap f).IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overPullback f

/-- The adjunct of alpha_f induces the unique section-ring homomorphism with its given
underlying additive map.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport).
Proof: Step 2. Reconstruct multiplication and unit by evaluating the tensor action on pure
section tensors. Monoidality of eta_f gives preservation of multiplication and unit;
its naturality gives restriction compatibility. Faithfulness of the forgetful ring functor
makes this lift unique. The underlying pushforward is evaluation at V times_Y X. -/
theorem coefficientMap_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! φ : ring Λ Y ⟶ ((siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring Λ X),
      ∀ (V : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj V),
        (φ.hom.app V).hom r = ((condensedPushforwardHom Λ f).hom.app V).hom r := by
  sorry

/-- The canonical section-ring map B_Y -> f_* B_X, fixed by eta_f on every section.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def coefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ring Λ Y ⟶ ((siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring Λ X) :=
  (coefficientMap_existsUnique Λ f).exists.choose

/-- Ordinary direct image with scalar restriction along the adjunct of alpha_f.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.pushforward.{u + 1} (F := siteMap f) (coefficientMap Λ f)

/-- Presheaf pullback exists in the coefficient universe even though the small pro-etale
site has object universe u+1 and morphism universe u.
Source: the tensor-formula construction in Stacks 03D7
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: transport both sites and their presheaves to coefficient-sized small models.
On these models the presheaf pullback is the left Kan extension and sectionwise scalar
extension; its Hom bijection sends m to 1 tensor m. Transport that adjunction back.
No equality between the original site object and morphism universes is imposed. -/
@[instance]
theorem presheafLowerStar_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (PresheafOfModules.pushforward.{u + 1}
      (F := siteMap f) (coefficientMap Λ f).hom).IsRightAdjoint := by
  sorry

/-- The canonical sectionwise ringed-topos pullback, constructed by presheaf pullback
and sheafification: inverse image followed by B_X tensor_{f^{-1}B_Y} (-).
Source: Stacks 03D7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev upperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.forget (ring Λ Y) ⋙
    PresheafOfModules.pullback.{u + 1} (F := siteMap f) (coefficientMap Λ f).hom ⋙
      PresheafOfModules.sheafification (R₀ := (ring Λ X).obj) (𝟙 (ring Λ X).obj)

/-- The tensor-formula sectionwise adjunction, with its sheafification Hom bijection.
Source: Stacks 03D7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.PullbackConstruction.adjunction.{u + 1}
    (F := siteMap f) (coefficientMap Λ f)

/-- The canonical direct-image comparison is uniquely the identity on underlying sheaves.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport).
Proof: Steps 1--2. E preserves underlying sections and maps. The internal lax action is
eta_f(r) times n, precisely scalar restriction in the sectionwise direct image. Thus the
identity sheaf map and its inverse are linear and natural. Their underlying maps determine
them uniquely by faithfulness. -/
theorem lowerComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! r : CondensedRing.lowerStar Λ f ⋙ (equivalence Λ Y).functor ≅
        (equivalence Λ X).functor ⋙ lowerStar Λ f,
      ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
        (V : Y.ProEtᵒᵖ) (m : ((lowerStar Λ f).obj ((equivalence Λ X).functor.obj M)).val.obj V),
        ((r.hom.app M).val.app V).hom m = m := by
  sorry

/-- The identity-on-sections direct-image comparison.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def lowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.lowerStar Λ f ⋙ (equivalence Λ Y).functor ≅
      (equivalence Λ X).functor ⋙ lowerStar Λ f :=
  (lowerComparison_existsUnique Λ f).exists.choose

/-- The mate of the direct-image comparison is invertible and uniquely fixes pullback.
Source: Stacks 03D7, Categories 0B65
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Steps 3--4. Conjugate the specified internal adjunction by E. The two left
adjoints of the identified direct image are uniquely isomorphic by the unit equation
lem-weil-pbc-conjugate-iso-unit-equation. Undo the conjugation. The mate equation below
is exactly the Hom-transposition identity; evaluating it on identities gives both unit
and counit equations, by lem-weil-pbc-adjunction-of-natural-bijection. -/
theorem upperComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! c : CondensedRing.upperStar Λ f ⋙ (equivalence Λ X).functor ≅
        (equivalence Λ Y).functor ⋙ upperStar Λ f,
      (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
        (.mk _ _ _ _ c.inv)).natTrans =
        (lowerComparison Λ f).hom := by
  sorry

/-- The pullback comparison normalized by the actual specified adjunctions.
Source: Stacks 03D7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def upperComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStar Λ f ⋙ (equivalence Λ X).functor ≅
      (equivalence Λ Y).functor ⋙ upperStar Λ f :=
  (upperComparison_existsUnique Λ f).exists.choose

/-- For an open immersion, sectionwise restriction admits extension by zero.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Step 5. Conjugate the given internal open-extension adjunction by the fixed
E equivalences, and identify its right adjoint using upperComparison. This supplies
the sectionwise left adjoint, characterized uniquely by its extension-by-zero universal
property. The same underlying abelian extension by zero carries the transported action. -/
@[instance]
theorem upperStar_isRightAdjoint {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] : (upperStar Λ j).IsRightAdjoint := by
  sorry

/-- Sectionwise extension by zero, the canonical left adjoint of restriction.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev extension {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (upperStar Λ j).leftAdjoint

/-- The sectionwise open-extension adjunction to restriction.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev openAdjunction {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  Adjunction.ofIsRightAdjoint (upperStar Λ j)

/-- The canonical open-extension comparison, normalized by the specified adjunctions.
Source: blueprint module-lower-shriek, Extension by zero clause; Categories 0B65
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Step 5. Apply unit-normalized uniqueness of left adjoints again to the internal
open adjunction and the sectionwise one, with upperComparison identifying the right
adjoints. The mate equation identifies the Hom bijections, units and counits. -/
theorem openComparison_existsUnique {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    ∃! o : CondensedRing.openImmersionLowerShriek Λ j ⋙ (equivalence Λ T).functor ≅
        (equivalence Λ U).functor ⋙ extension Λ j,
      (mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
        (openAdjunction Λ j) (.mk _ _ _ _ o.inv)).natTrans = (upperComparison Λ j).hom := by
  sorry

/-- The uniquely adjunction-normalized comparison for extension by zero.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def openComparison {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek Λ j ⋙ (equivalence Λ T).functor ≅
      (equivalence Λ U).functor ⋙ extension Λ j :=
  (openComparison_existsUnique Λ j).exists.choose

/-- The sectionwise direct-image composition comparison is the ordinary sheaf comparison.
Source: blueprint module-upper-star-comp; Stacks 03D6
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Step 6. Evaluation rebrackets the iterated fibre product. The two scalar actions
agree by compatibility of eta_f with composition, so the underlying abelian comparison
is linear, natural and invertible. Faithfulness gives uniqueness. -/
theorem lowerComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! c : lowerStar Λ f ⋙ lowerStar Λ g ≅ lowerStar Λ (f ≫ g),
      ∀ (M : SheafOfModules.{u + 1} (ring Λ X)) (V : Z.ProEtᵒᵖ)
        (m : ((lowerStar Λ g).obj ((lowerStar Λ f).obj M)).val.obj V),
        ((c.hom.app M).val.app V).hom m =
          (((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
            ((SheafOfModules.toSheaf (ring Λ X)).obj M)).hom.app V).hom m := by
  sorry

/-- The canonical sectionwise direct-image composition comparison.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def lowerComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lowerStar Λ f ⋙ lowerStar Λ g ≅ lowerStar Λ (f ≫ g) :=
  (lowerComp_existsUnique Λ f g).exists.choose

/-- The sectionwise pullback-composition comparison, conjugate to direct-image composition.
Source: blueprint module-upper-star-comp
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def upperComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    upperStar Λ (f ≫ g) ≅ upperStar Λ g ⋙ upperStar Λ f :=
  (Adjunction.leftAdjointCompIso (adjunction Λ g) (adjunction Λ f)
    (adjunction Λ (f ≫ g)) (lowerComp Λ f g)).symm

/-- The actual internal pullback-composition comparison around a scheme square.
Source: blueprint module-upper-star-comp
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def internalSquare {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :
    CondensedRing.upperStar Λ j ⋙ CondensedRing.upperStar Λ g' ≅
      CondensedRing.upperStar Λ g ⋙ CondensedRing.upperStar Λ j' :=
  (CondensedRing.upperStarComp Λ g' j).symm ≪≫
    eqToIso (congrArg (CondensedRing.upperStar Λ) sq.w) ≪≫
      CondensedRing.upperStarComp Λ j' g

/-- The sectionwise pullback-composition comparison around the same square.
Source: blueprint module-upper-star-comp
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def sectionSquare {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :
    upperStar Λ j ⋙ upperStar Λ g' ≅ upperStar Λ g ⋙ upperStar Λ j' :=
  (upperComp Λ g' j).symm ≪≫ eqToIso (congrArg (upperStar Λ) sq.w) ≪≫ upperComp Λ j' g

/-- The internal open-extension base-change map, with the specified unit and counit.
Source: Stacks 07A7 and the node proof Step 7
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def internalBaseChange {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : ChosenCartesianSquare g' j' j g) :
    CondensedRing.upperStar Λ g' ⋙ CondensedRing.openImmersionLowerShriek Λ j' ⟶
      CondensedRing.openImmersionLowerShriek Λ j ⋙ CondensedRing.upperStar Λ g :=
  ((mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j')).symm
      (.mk _ _ _ _ (internalSquare Λ sq).hom)).natTrans

/-- The sectionwise map is the same adjunction mate of pullback composition.
Source: Stacks 07A7 and the node proof Step 7
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def sectionBaseChange {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : ChosenCartesianSquare g' j' j g) :
    upperStar Λ g' ⋙ extension Λ j' ⟶ extension Λ j ⋙ upperStar Λ g :=
  ((mateEquiv (openAdjunction Λ j) (openAdjunction Λ j')).symm
    (.mk _ _ _ _ (sectionSquare Λ sq).hom)).natTrans

/-- Comparison of the source of the open-extension base-change transformation.
Source: node proof Step 7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def baseChangeSourceComparison {U' U T' : Scheme.{u}}
    (g' : U' ⟶ U) (j' : U' ⟶ T') [IsOpenImmersion j'] :
    (CondensedRing.upperStar Λ g' ⋙ CondensedRing.openImmersionLowerShriek Λ j') ⋙
        (equivalence Λ T').functor ≅
      (equivalence Λ U).functor ⋙ (upperStar Λ g' ⋙ extension Λ j') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (openComparison Λ j') ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (upperComparison Λ g') _ ≪≫
      Functor.associator _ _ _

/-- Comparison of the target of the open-extension base-change transformation.
Source: node proof Step 7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def baseChangeTargetComparison {U T T' : Scheme.{u}}
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek Λ j ⋙ CondensedRing.upperStar Λ g) ⋙
        (equivalence Λ T').functor ≅
      (equivalence Λ U).functor ⋙ (extension Λ j ⋙ upperStar Λ g) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (upperComparison Λ g) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (openComparison Λ j) _ ≪≫
      Functor.associator _ _ _

/-- Internal module operations agree canonically with sectionwise operations, including
specified adjunctions, open-extension mates and exactness.
Source: blueprint main-20261015, Nagata density normalization sheaves proof, Steps 1--2;
Stacks 03D6, 03D7, 0B65 and 07A7
(blueprint: lem-sfb-internal-module-operations-transport).

Proof (the eight steps of the DAG node):
1. E_T preserves underlying section groups and maps. Its action formula is
   a(r tensor m), so it and its inverse preserve addition and zero of morphisms
   (def-weil-pbc-internal-abelian-sheaf-module-equivalence,
   det-def-sfb-sheaf-tensor-structure).
2. Both direct images evaluate N on V times_T T'. The lax tensor map sends pure
   tensors to the same tensors there. Their actions are eta_f(r) times n, where
   eta_f is f_* alpha_f after the abelian unit (def-sfb-finite-lower-star,
   def-sfb-finite-lower-star-lax-monoidal, def-sfb-module-lower-star,
   sk-def-sfb-coefficient-morphisms). Thus lowerComparison is the identity on sections.
3. Conjugate the specified internal adjunction by E, and use the unique unit-normalized
   left-adjoint comparison (lem-weil-pbc-conjugate-iso-unit-equation), with the sectionwise
   adjunction of lem-weil-pbc-ringed-topoi-module-adjunction.
4. Naturality of the Hom bijections gives the mate equation, hence the displayed unit
   and counit equations (lem-weil-pbc-adjunction-of-natural-bijection).
5. Repeat for the given internal open-extension adjunction
   (sk-def-sfb-module-lower-shriek) and the sectionwise extension-by-zero adjunction.
6. The direct-image comparisons commute with composition because their section maps
   are identities, and both compositions rebracket the same fibre product. Conjugation
   is injective, so the pullback comparisons commute with composition too
   (def-sfb-module-lower-star-comp, def-sfb-module-upper-star-comp,
   def-weil-pbc-adjunction-conjugate).
7. The open-extension map is the inverse mate of pullback composition: insert eta_j,
   apply the square comparison, then contract epsilon_j'. Steps 4--6 identify each
   factor, yielding the displayed transformation equation (def-weil-pbc-adjunction-mate).
8. The additive equivalences and their inverses preserve finite limits and colimits
   (lem-galois-equivalence-preserves-limits, def-weil-sheaf-of-modules-category).
   They therefore preserve and reflect exact sequences and exactness of operations.
   The transformation equation conjugates base change by isomorphisms; equivalences
   reflect isomorphisms, so sectionwise invertibility implies internal invertibility.
-/
theorem internal_module_operations_transport :
    (∀ (T : Scheme.{u}),
      (equivalence Λ T).functor.Additive ∧ (equivalence Λ T).inverse.Additive ∧
      PreservesFiniteLimits (equivalence Λ T).functor ∧
      PreservesFiniteColimits (equivalence Λ T).functor ∧
      PreservesFiniteLimits (equivalence Λ T).inverse ∧
      PreservesFiniteColimits (equivalence Λ T).inverse ∧
      (∀ (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj Λ T))),
        (S.map (equivalence Λ T).functor).Exact ↔ S.Exact) ∧
      (∀ (S : ShortComplex (SheafOfModules.{u + 1} (ring Λ T))),
        (S.map (equivalence Λ T).inverse).Exact ↔ S.Exact)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
          (.mk _ _ _ _ (upperComparison Λ f).inv)).natTrans = (lowerComparison Λ f).hom ∧
      (∀ M,
        (equivalence Λ Y).functor.map
            ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M) ≫
          (lowerComparison Λ f).hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          (lowerStar Λ f).map ((upperComparison Λ f).hom.app M) =
        (adjunction Λ f).unit.app ((equivalence Λ Y).functor.obj M)) ∧
      (∀ N,
        (upperStar Λ f).map ((lowerComparison Λ f).inv.app N) ≫
          (upperComparison Λ f).inv.app ((CondensedRing.lowerStar Λ f).obj N) ≫
          (equivalence Λ X).functor.map
            ((CondensedRing.upperStarLowerStarAdjunction Λ f).counit.app N) =
        (adjunction Λ f).counit.app ((equivalence Λ X).functor.obj N))) ∧
    (∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
      (mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
        (openAdjunction Λ j) (.mk _ _ _ _ (openComparison Λ j).inv)).natTrans =
        (upperComparison Λ j).hom ∧
      (∀ M,
        (equivalence Λ U).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M) ≫
          (upperComparison Λ j).hom.app ((CondensedRing.openImmersionLowerShriek Λ j).obj M) ≫
          (upperStar Λ j).map ((openComparison Λ j).hom.app M) =
        (openAdjunction Λ j).unit.app ((equivalence Λ U).functor.obj M)) ∧
      (∀ N,
        (extension Λ j).map ((upperComparison Λ j).inv.app N) ≫
          (openComparison Λ j).inv.app ((CondensedRing.upperStar Λ j).obj N) ≫
          (equivalence Λ T).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app N) =
        (openAdjunction Λ j).counit.app ((equivalence Λ T).functor.obj N))) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (PreservesFiniteLimits (CondensedRing.upperStar Λ f) ↔
        PreservesFiniteLimits (upperStar Λ f)) ∧
      (PreservesFiniteColimits (CondensedRing.upperStar Λ f) ↔
        PreservesFiniteColimits (upperStar Λ f)) ∧
      (PreservesFiniteLimits (CondensedRing.lowerStar Λ f) ↔
        PreservesFiniteLimits (lowerStar Λ f)) ∧
      (PreservesFiniteColimits (CondensedRing.lowerStar Λ f) ↔
        PreservesFiniteColimits (lowerStar Λ f))) ∧
    (∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
      (PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j) ↔
        PreservesFiniteLimits (extension Λ j)) ∧
      (PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ j) ↔
        PreservesFiniteColimits (extension Λ j))) ∧
    (∀ {U' U T' T : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ T'}
      {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
      (sq : ChosenCartesianSquare g' j' j g),
      Functor.whiskerRight (internalBaseChange Λ sq) (equivalence Λ T').functor ≫
          (baseChangeTargetComparison Λ j g).hom =
        (baseChangeSourceComparison Λ g' j').hom ≫
          Functor.whiskerLeft (equivalence Λ U).functor (sectionBaseChange Λ sq) ∧
      (IsIso (sectionBaseChange Λ sq) → IsIso (internalBaseChange Λ sq))) := by
  sorry

end InternalModuleOperations
end AlgebraicGeometry.ProEtale
