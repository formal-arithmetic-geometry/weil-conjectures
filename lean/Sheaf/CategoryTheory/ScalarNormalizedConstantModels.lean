/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.ConstantRingModuleSheaves
import Sheaf.CategoryTheory.FiniteTypeRestrictionExact
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Scalar-normalized constant module models

Source: Stacks Project, Tags 03CY and 03EI, and the finite-presentation argument in
`lem-sfb-scalar-normalized-constant-models`, steps 1--11
(blueprint: lem-sfb-scalar-normalized-constant-models).

The model functor uses the existing internal extension of scalars. Its generators
are the canonical maps `r ↦ r ⊗ p`. Localization uses the existing equivalence
with sectionwise module sheaves and the actual `overFunctor` and `overMap`.
For finitely presented coefficients, the restricted balancing coequalizer is the
local tensor model: restriction preserves its finite colimit and sheaf tensor.
No presentation, comparison isomorphism or ring action is chosen by an existence
axiom. The only postponed declarations are the six clauses of the node.
-/

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
@[expose] public section
namespace CategoryTheory.ScalarNormalizedConstantModels
variable {C : Type v} [Category.{w} C] [UnivLE.{max v w, u}]
  [UnivLE.{v, u}] [UnivLE.{w, u}] (B : Type u) [CommRing B]
/-- The constant module presheaf, with its given scalar action transported along
the identity map to the reconstructed section ring. Source: Stacks Project, Tags 03CY and 03EI;
node proof, step 1.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def constantPresheaf (P : ModuleCat.{u} B) :
    PresheafOfModules.{u} (InternalAbelianSheafModule.presheafRings
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B))) := by
  letI (Z : Cᵒᵖ) : Module
      ((InternalAbelianSheafModule.presheafRings
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B))).obj Z)
      (((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of P)).obj Z) := Module.compHom P
    ({ toFun := fun b ↦ b
       map_zero' := rfl
       map_one' := by change ((1 : ℤ) : B) = 1; exact Int.cast_one
       map_add' := fun _ _ ↦ rfl
       map_mul' := fun _ _ ↦ rfl } : (InternalAbelianSheafModule.presheafRings
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B))).obj Z →+* B)
  exact PresheafOfModules.ofPresheaf
    ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of P)) (fun _ _ _ _ _ ↦ rfl)
/-- The constant presheaf action regarded as an internal module, using the
recorded internal/sectionwise module interface. Source: Stacks Project, Tags 03CY and 03EI;
node proof, step 1.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def constantInternalPresheaf : ModuleCat.{u} B ⥤
    Mod (Cᵒᵖ ⥤ AddCommGrpCat.{u})
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B)) where
  obj P := InternalAbelianSheafModule.internalPresheafMod _ (constantPresheaf B P)
  map f := InternalAbelianSheafModule.internalPresheafMap _
    (PresheafOfModules.homMk ((Functor.const Cᵒᵖ).map
      (AddCommGrpCat.ofHom f.hom.toAddMonoidHom)) (fun _ r p ↦ f.hom.map_smul r p))
  map_id P := by apply Mod.hom_ext; rfl
  map_comp f g := by apply Mod.hom_ext; rfl


attribute [instance] Sheaf.monoidalCategory Sheaf.braidedCategory
variable (J : GrothendieckTopology C) [hSheafify : HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
/-- The pointwise constant functor respects braiding; its structure maps are
identities. Source: the pointwise tensor in node proof step 1.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
instance constantPresheafBraided : (Functor.const Cᵒᵖ (C := AddCommGrpCat.{u})).Braided where
  braided X Y := by
    apply NatTrans.ext
    funext Z
    change 𝟙 _ ≫ (β_ X Y).hom = (β_ X Y).hom ≫ 𝟙 _
    simp
/-- The commutative ring object obtained by monoidally sheafifying the
constant ring presheaf. Source: Stacks Project, Tags 03CY and 03EI; node proof, step 1.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def constantRing : CommMon (Sheaf J AddCommGrpCat.{u}) :=
  (presheafToSheaf J AddCommGrpCat.{u}).mapCommMon.obj
    ((Functor.const Cᵒᵖ).mapCommMon.obj (CommMon.mk (AddCommGrpCat.of B)))
/-- Left sheaf tensor preserves the coequalizers used for extension, by the
recorded closed tensor theorem. Source: blueprint sk-def-sfb-sheaf-tensor, clause 2.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable instance tensorLeftPreserves (X : Sheaf J AddCommGrpCat.{u}) :
    CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  ((sfbSheafTensor_properties.{v, w, u + 1, u, 0, 0} (A := AddCommGrpCat.{u}) J).2.2 X).1
/-- Right sheaf tensor preserves the coequalizers used for extension, by the
recorded closed tensor theorem. Source: blueprint sk-def-sfb-sheaf-tensor, clause 2.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable instance tensorRightPreserves (X : Sheaf J AddCommGrpCat.{u}) :
    CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
  ((sfbSheafTensor_properties.{v, w, u + 1, u, 0, 0} (A := AddCommGrpCat.{u}) J).2.2 X).2.1
/-- Monoidal sheafification of the constant internal module presheaf.
Its underlying abelian sheaf is the usual sheafified constant module.
Source: Stacks Project, Tags 03CY and 03EI; node proof, step 1.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def constantInternalModule : ModuleCat.{u} B ⥤
    Mod (Sheaf J AddCommGrpCat.{u})
      (constantRing B J).X :=
  constantInternalPresheaf (C := C) B ⋙ (presheafToSheaf J AddCommGrpCat.{u}).mapMod _
variable (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [hRcomm : IsCommMonObj R]
  (σ : (constantRing B J).X ⟶ R)
  [IsMonHom σ]
/-- The actual relative tensor model `R ⊗_{B̲} P̲`, functorial in every
ordinary linear map, using `Mod.extendScalars`.
Source: blueprint sk-def-sfb-change-of-scalars, clause 2; node proof step 2.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def model : ModuleCat.{u} B ⥤ Mod (Sheaf J AddCommGrpCat.{u}) R :=
  constantInternalModule B J ⋙ Mod.extendScalars σ
/-- The constant section indexed by `p`, expressed as a map from the
sheaf tensor unit using the unit of the monoidal constant functor.
Source: Stacks Project, Tags 03CY and 03EI; node proof, steps 1--2.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def constantElement (P : ModuleCat.{u} B) (p : P) :
    𝟙_ (Sheaf J AddCommGrpCat.{u}) ⟶
      (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of P) :=
  Functor.LaxMonoidal.ε (constantSheaf J AddCommGrpCat.{u}) ≫
    (constantSheaf J AddCommGrpCat.{u}).map
      (AddCommGrpCat.ofHom ((zmultiplesHom P p).comp
        (ULift.moduleEquiv (R := ℤ) (M := ℤ)).toLinearMap.toAddMonoidHom))
/-- The canonical regular-module map `r ↦ r ⊗ p`: apply the extension
unit to the constant element, then the regular-module universal property.
Source: blueprint sk-def-sfb-change-of-scalars, clause 2; node proof steps 2--3.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def modelGenerator (P : ModuleCat.{u} B) (p : P) :
    Mod.regular R ⟶ (model B J R σ).obj P :=
  Mod.regularLift _
    (constantElement B J P p ≫ Mod.extendUnitHom σ ((constantInternalModule B J).obj P))
/-- The endomorphism of the regular module multiplying by `σ(b)`.
Source: node statement, scalar normalization hypothesis; node proof step 3.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def scalarEndomorphism (b : B) : Mod.regular R ⟶ Mod.regular R :=
  Mod.regularLift _ (constantElement B J (ModuleCat.of B B) b ≫ σ)
variable (E : Mod (Sheaf J AddCommGrpCat.{u}) R ≌ Sheaf J (ModuleCat.{u} B))
  [hEadd : E.functor.Additive]
  (t : E.functor.obj (Mod.regular R) ≅
    (constantSheaf J (ModuleCat.{u} B)).obj (ModuleCat.of B B))
/-- The given regular-module identification intertwines each scalar
endomorphism with ordinary multiplication by the same element of `B`.
Source: node statement, hypothesis on `t`; node proof step 3.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
def scalarNormalized : Prop :=
  ∀ b : B, E.functor.map (scalarEndomorphism B J R σ b) ≫ t.hom =
    t.hom ≫ (constantSheaf J (ModuleCat.{u} B)).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton B B b))
/-- Naturality on all finitely presented modules and the normalization on
canonical generators. The latter is equivalently the prescribed finite-free
normalization: apply naturality to `B → P`, `b ↦ b • p`; on finite free modules
these maps are the standard summand injections.
Source: Stacks Project, Tags 03CY and 03EI; node proof, steps 3--7.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
def comparisonCondition
    (θ : ∀ (P : ModuleCat.{u} B) (_ : Module.FinitePresentation B P),
      E.functor.obj ((model B J R σ).obj P) ≅
        (constantSheaf J (ModuleCat.{u} B)).obj P) : Prop :=
  (∀ (P Q : ModuleCat.{u} B) (hP : Module.FinitePresentation B P)
    (hQ : Module.FinitePresentation B Q) (f : P ⟶ Q),
      E.functor.map ((model B J R σ).map f) ≫ (θ Q hQ).hom =
        (θ P hP).hom ≫ (constantSheaf J (ModuleCat.{u} B)).map f) ∧
  (∀ (P : ModuleCat.{u} B) (hP : Module.FinitePresentation B P) (p : P),
    E.functor.map (modelGenerator B J R σ P p) ≫ (θ P hP).hom =
      t.hom ≫ (constantSheaf J (ModuleCat.{u} B)).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton B P p)))
include hSheafify hRcomm hEadd in
/-- There is a unique natural comparison with the prescribed finite-free
normalization; hence it is independent of every presentation.
Source: Stacks Project, Tags 03CY and 03EI; node proof, steps 1--7.
(blueprint: lem-sfb-scalar-normalized-constant-models).

Proof: constant presheaves preserve finite sums and pointwise cokernels, and exact
abelian sheafification supplies the same cokernels in both module encodings
(step 1). Extension preserves finite colimits and identifies its regular module
with R by `r ⊗ b ↦ r σ(b)` and `r ↦ r ⊗ 1` (step 2). Additivity of E and
scalar normalization identify every finite scalar matrix, summand by summand,
including zero ranks (step 3). For a finite presentation, the cokernel universal
property produces the comparison and its inverse (step 4). A map P → Q lifts
from the finite free source of a presentation to the finite free target of a
presentation of Q by choosing preimages of its basis vectors (step 5).
Precompose the naturality equation with the epimorphic quotient projection;
the matrix equation proves it, independently of the lifts (step 6). Apply this
to the identity and two presentations to get presentation independence. Any
natural comparison normalized on free modules has the same composite with
every quotient projection and is therefore equal (step 7). -/
theorem exists_comparison (ht : scalarNormalized (C := C) B J R σ E t) :
    ∃! θ : ∀ (P : ModuleCat.{u} B) (_ : Module.FinitePresentation B P),
      E.functor.obj ((model B J R σ).obj P) ≅
        (constantSheaf J (ModuleCat.{u} B)).obj P,
      comparisonCondition B J R σ E t θ := by sorry

/-- The ring sheaf reconstructed by the recorded internal/sectionwise
equivalence, forgetting only commutativity. No ring data is redefined.
Source: Stacks 00YV; node proof step 8.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable abbrev sectionRing : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (InternalAbelianSheafModule.sectionRingSheaf J R)
/-- The actual restriction of an internal module in its sectionwise
coordinates. This is the recorded `sectionModuleFunctor` followed by Mathlib
`SheafOfModules.overFunctor`, with the original underlying sheaf and maps.
Source: Stacks 03DH, 04IX; node proof steps 8--9.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def restriction (U : C) :
    Mod (Sheaf J AddCommGrpCat.{u}) R ⥤
      SheafOfModules.{u} ((sectionRing J R).over U) :=
  InternalAbelianSheafModule.sectionModuleFunctor J R ⋙
    SheafOfModules.overFunctor (sectionRing J R) U
variable (θ : ∀ (P : ModuleCat.{u} B) (_ : Module.FinitePresentation B P),
  E.functor.obj ((model B J R σ).obj P) ≅
    (constantSheaf J (ModuleCat.{u} B)).obj P)
variable (U : C)
  (EU : SheafOfModules.{u} ((sectionRing J R).over U) ≌
    Sheaf (J.over U) (ModuleCat.{u} B))
  (eU : restriction J R U ⋙ EU.functor ≅
    E.functor ⋙ J.overPullback (ModuleCat.{u} B) U)
/-- The restriction of the global comparison, transported through the
supplied equivalence comparison and the canonical constant restriction iso.
The local model is the restriction of the balancing coequalizer defining `model`,
hence the canonical local extension model.
Source: Stacks 00XR, 03EH; node proof steps 8--10.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def localComparison (P : ModuleCat.{u} B)
    (hP : Module.FinitePresentation B P) :
    EU.functor.obj ((restriction J R U).obj ((model B J R σ).obj P)) ≅
      (constantSheaf (J.over U) (ModuleCat.{u} B)).obj P :=
  eU.app ((model B J R σ).obj P) ≪≫
    (J.overPullback (ModuleCat.{u} B) U).mapIso (θ P hP) ≪≫
      (J.overPullbackConstantSheafIso (ModuleCat.{u} B) U).app P

/-- The local comparison is natural in the same ordinary linear maps and
is normalized by `tU` on every canonical generator of the localized model.
Source: node statement, localization clause; node proof step 10.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
def localCondition
    (tU : EU.functor.obj ((restriction J R U).obj (Mod.regular R)) ≅
      (constantSheaf (J.over U) (ModuleCat.{u} B)).obj (ModuleCat.of B B))
    (η : ∀ (P : ModuleCat.{u} B) (_ : Module.FinitePresentation B P),
      EU.functor.obj ((restriction J R U).obj ((model B J R σ).obj P)) ≅
        (constantSheaf (J.over U) (ModuleCat.{u} B)).obj P) : Prop :=
  (∀ (P Q : ModuleCat.{u} B) (hP : Module.FinitePresentation B P)
    (hQ : Module.FinitePresentation B Q) (f : P ⟶ Q),
      EU.functor.map ((restriction J R U).map ((model B J R σ).map f)) ≫
        (η Q hQ).hom = (η P hP).hom ≫
          (constantSheaf (J.over U) (ModuleCat.{u} B)).map f) ∧
  (∀ (P : ModuleCat.{u} B) (hP : Module.FinitePresentation B P) (p : P),
    EU.functor.map ((restriction J R U).map (modelGenerator B J R σ P p)) ≫ (η P hP).hom =
      tU.hom ≫ (constantSheaf (J.over U) (ModuleCat.{u} B)).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton B P p)))
/-- The restricted comparison is exactly the unique locally normalized comparison.
Source: Stacks 03CY, 03EI, 00XR; node proof steps 8--10.
(blueprint: lem-sfb-scalar-normalized-constant-models).

Proof: restriction is exact and commutes with constant module sheafification
(step 8). Restrict a finite scalar presentation. The resulting quotient,
with generators `r ⊗ e_j`, is precisely the localized balanced tensor model;
its uniqueness also makes the identification independent of presentation
(step 9). Naturality of the supplied equivalence comparison and its equality
with tU on the regular module identify the generator normalization on both
sides. Test any two locally normalized comparisons after the epimorphic
quotient projection of a finite presentation. Both composites are the same
finite sum of the tU-normalized generators, so the comparisons agree (step 10). -/
theorem localComparison_properties
    (hθ : comparisonCondition (C := C) B J R σ E t θ)
    (tU : EU.functor.obj ((restriction J R U).obj (Mod.regular R)) ≅
      (constantSheaf (J.over U) (ModuleCat.{u} B)).obj (ModuleCat.of B B))
    (htU : (eU.app (Mod.regular R)).hom ≫
      (J.overPullback (ModuleCat.{u} B) U).map t.hom ≫
        ((J.overPullbackConstantSheafIso (ModuleCat.{u} B) U).app
          (ModuleCat.of B B)).hom = tU.hom) :
    localCondition (C := C) B J R σ U EU tU
      (localComparison (C := C) B J R σ E θ U EU eU) ∧
    ∀ η, localCondition (C := C) B J R σ U EU tU η →
      η = localComparison (C := C) B J R σ E θ U EU eU := by sorry


/-- Every finite scalar presentation gives the two specified cokernel
projections, and the comparison identifies them using t on free summands.
Source: Stacks Project, Tags 03CY and 03EI; node proof, steps 1--4 and 7.
(blueprint: lem-sfb-scalar-normalized-constant-models).

Proof: exactness and surjectivity make π a module cokernel of q. Constant
sheafification and internal extension preserve this cokernel (steps 1--2),
as does E. The scalar matrix equality on each summand is the normalization
hypothesis and additivity (step 3). The comparison is the unique induced
cokernel isomorphism (step 4); naturality for π is its displayed equation.
Applying the identity to two presentations gives the same map (step 7). -/
theorem presentationComparison
    (hθ : comparisonCondition (C := C) B J R σ E t θ)
    (P : ModuleCat.{u} B) (hP : Module.FinitePresentation B P) (m n : ℕ)
    (q : ModuleCat.of B (Fin m → B) ⟶ ModuleCat.of B (Fin n → B))
    (π : ModuleCat.of B (Fin n → B) ⟶ P)
    (hex : Function.Exact q.hom π.hom) (hsurj : Function.Surjective π.hom) :
    (∃ hrel : E.functor.map ((model B J R σ).map q) ≫
        E.functor.map ((model B J R σ).map π) = 0,
      Nonempty (Limits.IsColimit (Limits.CokernelCofork.ofπ
        (E.functor.map ((model B J R σ).map π)) hrel))) ∧
    (∃ hrel : (constantSheaf J (ModuleCat.{u} B)).map q ≫
        (constantSheaf J (ModuleCat.{u} B)).map π = 0,
      Nonempty (Limits.IsColimit (Limits.CokernelCofork.ofπ
        ((constantSheaf J (ModuleCat.{u} B)).map π) hrel))) ∧
    E.functor.map ((model B J R σ).map π) ≫ (θ P hP).hom =
      (θ (ModuleCat.of B (Fin n → B)) inferInstance).hom ≫
        (constantSheaf J (ModuleCat.{u} B)).map π := by sorry

/-- On the localized site the actual restricted model has the same finite
scalar cokernel presentation, and the local comparison identifies its quotient
projection with the constant quotient projection.
Source: Stacks 03CY, 03EI, 03DH and 00XR; node proof steps 8--10
(blueprint: lem-sfb-scalar-normalized-constant-models).

Proof: the global finite scalar presentation presents the balanced-tensor
object `model P`. Restriction of sectionwise modules is exact and
preserves its cokernel, and monoidal restriction identifies its scalar matrix
with the restricted scalar matrix on the local regular module. Thus this is
the finite presentation of the canonical local relative tensor model.
EU preserves its cokernel. Constant restriction carries the constant quotient
to its slice version, including the sheafification units. The formula defining
`localComparison` and naturality of eU give the displayed quotient equation.
When the supplied local regular identification is used, the generator
normalization is exactly `localComparison_properties`. -/
theorem localPresentationComparison
    (hθ : comparisonCondition (C := C) B J R σ E t θ)
    (P : ModuleCat.{u} B) (hP : Module.FinitePresentation B P) (m n : ℕ)
    (q : ModuleCat.of B (Fin m → B) ⟶ ModuleCat.of B (Fin n → B))
    (π : ModuleCat.of B (Fin n → B) ⟶ P)
    (hex : Function.Exact q.hom π.hom) (hsurj : Function.Surjective π.hom) :
    (∃ hrel : EU.functor.map ((restriction J R U).map ((model B J R σ).map q)) ≫
        EU.functor.map ((restriction J R U).map ((model B J R σ).map π)) = 0,
      Nonempty (Limits.IsColimit (Limits.CokernelCofork.ofπ
        (EU.functor.map ((restriction J R U).map ((model B J R σ).map π))) hrel))) ∧
    (∃ hrel : (constantSheaf (J.over U) (ModuleCat.{u} B)).map q ≫
        (constantSheaf (J.over U) (ModuleCat.{u} B)).map π = 0,
      Nonempty (Limits.IsColimit (Limits.CokernelCofork.ofπ
        ((constantSheaf (J.over U) (ModuleCat.{u} B)).map π) hrel))) ∧
    EU.functor.map ((restriction J R U).map ((model B J R σ).map π)) ≫
        (localComparison (C := C) B J R σ E θ U EU eU P hP).hom =
      (localComparison (C := C) B J R σ E θ U EU eU
        (ModuleCat.of B (Fin n → B)) inferInstance).hom ≫
        (constantSheaf (J.over U) (ModuleCat.{u} B)).map π := by sorry

/-- The canonical comparison between constants on successive slices.
It is built from the actual constant restriction and relocalization isos.
Source: Stacks 00XR, 03EH; node proof steps 8--10.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def constantRelocalization {V W : C} (f : V ⟶ W)
    (P : ModuleCat.{u} B) :
    (J.overMapPullback (ModuleCat.{u} B) f).obj
        ((constantSheaf (J.over W) (ModuleCat.{u} B)).obj P) ≅
      (constantSheaf (J.over V) (ModuleCat.{u} B)).obj P :=
  ((J.overMapPullback (ModuleCat.{u} B) f).mapIso
    ((J.overPullbackConstantSheafIso (ModuleCat.{u} B) W).app P)).symm ≪≫
      ((constantSheaf J (ModuleCat.{u} B)).obj P).pushforwardOverMapIso f ≪≫
        (J.overPullbackConstantSheafIso (ModuleCat.{u} B) V).app P

/-- The actual sectionwise relocalization isomorphism, not a selected
isomorphism of abstract models. Source: Stacks 03EH; node proof steps 8--9.
(blueprint: lem-sfb-scalar-normalized-constant-models). -/
noncomputable def moduleRelocalization {V W : C} (f : V ⟶ W)
    (M : Mod (Sheaf J AddCommGrpCat.{u}) R) :
    (SheafOfModules.overMap (sectionRing J R) f).obj ((restriction J R W).obj M) ≅
      (restriction J R V).obj M :=
  (SheafOfModules.overFunctorMap (sectionRing J R) f).app
    ((InternalAbelianSheafModule.sectionModuleFunctor J R).obj M)

/-- The comparisons commute with every further localization whenever
the supplied equivalence comparisons are coherent.
Source: Stacks 03EH; node proof steps 9--10.
(blueprint: lem-sfb-scalar-normalized-constant-models).

Proof: expand the three defining isomorphisms of `localComparison`. The
hypothesis hcoh identifies the two equivalence-comparison composites on
`model P`. Naturality of δ moves the restricted global θ past that
comparison. The definition of `constantRelocalization` identifies the
remaining constant restriction composites. Equivalently, both maps preserve
the same normalized quotient projection of every finite presentation;
epimorphic cancellation proves equality. This applies to every arrow
V → U and is the sectionwise identification of iterated slices in step 10. -/
theorem localComparison_coherent (V : C) (f : V ⟶ U)
    (EV : SheafOfModules.{u} ((sectionRing J R).over V) ≌
      Sheaf (J.over V) (ModuleCat.{u} B))
    (eV : restriction J R V ⋙ EV.functor ≅
      E.functor ⋙ J.overPullback (ModuleCat.{u} B) V)
    (δ : SheafOfModules.overMap (sectionRing J R) f ⋙ EV.functor ≅
      EU.functor ⋙ J.overMapPullback (ModuleCat.{u} B) f)
    (hcoh : ∀ M : Mod (Sheaf J AddCommGrpCat.{u}) R,
      EV.functor.map (moduleRelocalization J R f M).hom ≫ (eV.app M).hom =
        (δ.app ((restriction J R U).obj M)).hom ≫
          (J.overMapPullback (ModuleCat.{u} B) f).map (eU.app M).hom ≫
            ((E.functor.obj M).pushforwardOverMapIso f).hom)
    (P : ModuleCat.{u} B) (hP : Module.FinitePresentation B P) :
    EV.functor.map (moduleRelocalization J R f ((model B J R σ).obj P)).hom ≫
        (localComparison (C := C) B J R σ E θ V EV eV P hP).hom =
      (δ.app ((restriction J R U).obj ((model B J R σ).obj P))).hom ≫
        (J.overMapPullback (ModuleCat.{u} B) f).map
          (localComparison (C := C) B J R σ E θ U EU eU P hP).hom ≫
            (constantRelocalization B J f P).hom := by sorry

universe z

/-- On the specified covering family, the same finitely presented
coefficients give local internal models exactly when they give constant
local models after applying E. Source: node proof step 11.
(blueprint: lem-sfb-scalar-normalized-constant-models).

Proof: at each covering member, apply EW to a local model isomorphism,
then compose with the localized comparison and the inverse equivalence
comparison eW. Conversely, compose a constant local model isomorphism
with the inverse localized comparison and eW, and lift it through the
fully faithful EW. Full faithfulness reflects inverses. The index set,
covering arrows and the individual modules P i are unchanged. Empty
covers give two vacuous universal propositions. No finiteness or
Noetherian assumption on B, and no points of the site, are used. -/
theorem coverModels_iff
    (hθ : comparisonCondition (C := C) B J R σ E t θ)
    (X : C) (I : Type z) (W : I → C) (f : ∀ i, W i ⟶ X)
    (hcover : Sieve.ofArrows W f ∈ J X) (M : Mod (Sheaf J AddCommGrpCat.{u}) R)
    (P : I → ModuleCat.{u} B) (hP : ∀ i, Module.FinitePresentation B (P i))
    (EW : ∀ i, SheafOfModules.{u} ((sectionRing J R).over (W i)) ≌
      Sheaf (J.over (W i)) (ModuleCat.{u} B))
    (eW : ∀ i, restriction J R (W i) ⋙ (EW i).functor ≅
      E.functor ⋙ J.overPullback (ModuleCat.{u} B) (W i)) :
    (∀ i, Nonempty ((restriction J R (W i)).obj M ≅
      (restriction J R (W i)).obj ((model B J R σ).obj (P i)))) ↔
    (∀ i, Nonempty ((E.functor.obj M).over (W i) ≅
      (constantSheaf (J.over (W i)) (ModuleCat.{u} B)).obj (P i))) := by sorry

end CategoryTheory.ScalarNormalizedConstantModels
