module

public import Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.Paper.AdicConstructibilityPredicateComparison
import Sheaf.Paper.CoefficientHeartStratificationDefs
import Sheaf.Paper.QlbarDirectImageComparison
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.SixFunctors.IntegralModelsGenerators
import Sheaf.Paper.RingedProjectionFirstShift
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Paper.RingedCoefficientProjectionCocycle

/-! # Finite geometric cohomology and normalized scalar projection

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
geometric finite-coefficient cohomology and coefficient projection before descent.

The arbitrary-Omega coefficient construction belongs to this item. The shared
PadicAlgCl coefficient dependency and its recorded declarations are unchanged.
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeometricFiniteScalar.FiniteSubextension

variable (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω]

/-- Finite intermediate fields are directed by inclusion, using their finite compositum.
Source: blueprint condensed algebraic-closure coefficients, directed-poset clause
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model).
Proof: for finite E and F choose their compositum E sup F. Finite bases generate this
compositum as an algebra; products of the two finite bases span it over Q_ell. The two
inclusions are the lattice inequalities le_sup_left and le_sup_right.
-/
theorem finiteIntermediateFields_directed
    (E F : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] F] :
    ∃ H : IntermediateField ℚ_[ℓ] Ω, FiniteDimensional ℚ_[ℓ] H ∧ E ≤ H ∧ F ≤ H := by
  sorry

/-- A continuous function has image in one finite intermediate field.
Source: blueprint condensed algebraic-closure coefficients, displayed section formula
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def IsFiniteValued (P : Profinite.{u}) (f : C(P, Ω)) : Prop :=
  ∃ E : IntermediateField ℚ_[ℓ] Ω, FiniteDimensional ℚ_[ℓ] E ∧ ∀ t : P, f t ∈ E

/-- Finite-valued functions form a subring.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model).
Proof: constants zero and one lie in the ground field. Negatives stay in the same
intermediate field. Sums and products of functions valued in E and F lie in E sup F;
the compositum of two finite subextensions is finite. This includes the empty parameter.
-/
theorem finiteValued_closed (P : Profinite.{u}) :
    IsFiniteValued ℓ Ω P 0 ∧ IsFiniteValued ℓ Ω P 1 ∧
    (∀ f g : C(P, Ω), IsFiniteValued ℓ Ω P f → IsFiniteValued ℓ Ω P g →
      IsFiniteValued ℓ Ω P (f + g)) ∧
    (∀ f g : C(P, Ω), IsFiniteValued ℓ Ω P f → IsFiniteValued ℓ Ω P g →
      IsFiniteValued ℓ Ω P (f * g)) ∧
    (∀ f : C(P, Ω), IsFiniteValued ℓ Ω P f → IsFiniteValued ℓ Ω P (-f)) := by
  sorry

/-- The actual subring of finite-subextension-valued functions.
Source: blueprint condensed algebraic-closure coefficients, displayed section formula
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def sectionSubring (P : Profinite.{u}) : Subring C(P, Ω) where
  carrier := {f | IsFiniteValued ℓ Ω P f}
  zero_mem' := (finiteValued_closed ℓ Ω P).1
  one_mem' := (finiteValued_closed ℓ Ω P).2.1
  add_mem' := (finiteValued_closed ℓ Ω P).2.2.1 _ _
  mul_mem' := (finiteValued_closed ℓ Ω P).2.2.2.1 _ _
  neg_mem' := (finiteValued_closed ℓ Ω P).2.2.2.2 _

/-- Precomposition does not enlarge the finite intermediate field containing the image.
Source: blueprint condensed algebraic-closure coefficients, restriction formula
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model).
Proof: if f takes values in E, f composed with q takes values in that same E.
-/
theorem finiteValued_comp {P Q : Profinite.{u}} (q : Q ⟶ P) (f : sectionSubring ℓ Ω P) :
    IsFiniteValued ℓ Ω Q (f.val.comp q.hom.hom) := by
  sorry

/-- Restriction is the lifted pointwise precomposition ring map.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def ringPresheaf : Profinite.{u}ᵒᵖ ⥤ RingCat.{u + 1} where
  obj P := RingCat.of (ULift.{u + 1} (sectionSubring ℓ Ω P.unop))
  map q := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (((((ContinuousMap.compRightAlgHom ℤ Ω q.unop.hom.hom).toRingHom).comp
      (sectionSubring ℓ Ω _).subtype).codRestrict (sectionSubring ℓ Ω _)
        (fun f ↦ finiteValued_comp ℓ Ω q.unop f)).comp ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The finite-valued presheaf is already a sheaf, without sheafification.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model).
Proof: refine a coherent cover by a finite jointly surjective family. Continuous
functions descend along the resulting compact Hausdorff quotient. Each covering
function takes values in a finite intermediate field. Their finite compositum contains
the descended function's image. Uniqueness is pointwise uniqueness of functions;
the empty parameter has its unique function. Forgetting ring structure reflects sheafness.
-/
theorem isSheaf_ringPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) (ringPresheaf ℓ Ω) := by
  sorry

/-- The specified finite-subextension-valued condensed ring C.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def ringSheaf : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  ⟨ringPresheaf ℓ Ω, isSheaf_ringPresheaf ℓ Ω⟩

/-- The abelian sheaf underlying C, with the existing ring-sheaf monoid construction.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
abbrev ringObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (ringSheaf ℓ Ω)

/-- Pointwise multiplication is commutative.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
instance ringObj_comm : IsCommMonObj (ringObj ℓ Ω) :=
  Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u}) (ringSheaf ℓ Ω)
    fun P (f g : ULift.{u + 1} (sectionSubring ℓ Ω P.unop)) ↦ mul_comm f g

/-- The sectionwise inclusion C to B as an actual ring-sheaf morphism.
Source: blueprint condensed algebraic-closure coefficients, inclusion into C(-,Omega)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def inclusionRing : ringSheaf ℓ Ω ⟶ Profinite.continuousCoefficientRingSheaf Ω :=
  ⟨{ app := fun P ↦ RingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        ((sectionSubring ℓ Ω P.unop).subtype.comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The actual inclusion as a morphism of internal ring objects.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def inclusion : ringObj ℓ Ω ⟶ Profinite.continuousCoefficientRingObj Ω :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (inclusionRing ℓ Ω)

/-- The inclusion preserves units and multiplication because every section map is a ring map.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
instance inclusion_isMonHom : IsMonHom (inclusion ℓ Ω) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (inclusionRing ℓ Ω)))

variable (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]

/-- The inclusion E underline to C on sections, using the specified embedded E.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def finiteRingMap : Profinite.continuousCoefficientRingSheaf E ⟶ ringSheaf ℓ Ω :=
  ⟨{ app := fun P ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((((algebraMap E Ω).compLeftContinuous P.unop continuous_subtype_val).codRestrict
        (sectionSubring ℓ Ω P.unop) (fun f ↦ by
          change IsFiniteValued ℓ Ω P.unop _
          exact ⟨E, inferInstance, fun t ↦ (f t).2⟩)).comp
          ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The same finite-field inclusion between internal ring objects.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def finiteMap : Profinite.continuousCoefficientRingObj E ⟶ ringObj ℓ Ω :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (finiteRingMap ℓ Ω E)

/-- The finite-field inclusion preserves the pointwise ring operations.
Source: blueprint condensed algebraic-closure coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
instance finiteMap_isMonHom : IsMonHom (finiteMap ℓ Ω E) :=
  inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (finiteRingMap ℓ Ω E)))

end AlgebraicGeometry.ProEtale.GeometricFiniteScalar.FiniteSubextension

namespace AlgebraicGeometry.ProEtale.GeometricFiniteScalar
open CondensedGalois
open CategoryTheory.CondensedBar

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]
  (X : Scheme.{u}) (a : X ⟶ Spec (.of k))

/-- The existing internal equivariant category, with the Krull-topological Galois group.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
abbrev Actions (R : Coefficients.{u}) := Equivariant R (ks ≃ₐ[k] ks)

/-- Bundle the recorded continuous finite coefficient field with its induced norm topology.
Source: blueprint paragraph (3), A = E underline
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
abbrev finiteRing (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) : Coefficients.{u} :=
  CommMon.mk (Profinite.continuousCoefficientRingObj E)

/-- Bundle this item's finite-subextension-valued coefficient ring C over the given Omega.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
abbrev closureRing (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω] :
    Coefficients.{u} := CommMon.mk (FiniteSubextension.ringObj ℓ Ω)

/-- Bundle the recorded all-continuous norm-topological coefficient ring B.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
abbrev normRing (Ω : Type u) [NormedField Ω] : Coefficients.{u} :=
  CommMon.mk (Profinite.continuousCoefficientRingObj Ω)

/-- The actual sectionwise coefficient inclusion, bundled as a ring-object map.
Source: blueprint paragraph (3), c:C to B
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def inclusion (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω] :
    closureRing ℓ Ω ⟶ normRing Ω :=
  CommMon.homMk ⟨FiniteSubextension.inclusion ℓ Ω⟩

/-- The sectionwise inclusion of the specified finite coefficient subfield into C.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def finiteInclusion (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E] :
    finiteRing ℓ Ω E ⟶ closureRing ℓ Ω :=
  CommMon.homMk ⟨FiniteSubextension.finiteMap ℓ Ω E⟩

/-- Commutativity transported by the existing strong monoidal point pullback.
Source: blueprint paragraph (3), pulled-back commutative coefficients
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
instance schemeComm (R : Coefficients.{u}) (Y : Scheme.{u}) :
    IsCommMonObj (coefficientRing Y R.toMon).X :=
  Functor.isCommMonObj_obj (F := upperStarFromPoint Y)

section Systems
variable [∀ R : Coefficients.{u}, ActionAbelian R (ks ≃ₐ[k] ks)]
  [∀ R : Coefficients.{u}, IsGrothendieckAbelian.{u + 1} (Actions k ks R)]
  [∀ R : Coefficients.{u}, PreservesFiniteLimits (forgetAction (A := R) (G := ks ≃ₐ[k] ks))]
  [∀ R : Coefficients.{u}, PreservesFiniteColimits
    (forgetAction (A := R) (G := ks ≃ₐ[k] ks))]

/-- Forget the action exactly on ordinary derived categories.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
abbrev forgetDerived (R : Coefficients.{u}) :=
  (forgetAction (A := R) (G := ks ≃ₐ[k] ks)).mapDerivedCategory

variable {R S : Coefficients.{u}} (φ : R ⟶ S)
  (r : ScalarAction φ (ks ≃ₐ[k] ks))
  [PreservesFiniteLimits r.functor] [PreservesFiniteColimits r.functor]

/-- The canonical forget/restriction comparison is termwise the supplied scalar comparison.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def restrictionForget :
    r.functor.mapDerivedCategory ⋙ forgetDerived k ks R ≅
      forgetDerived k ks S ⋙ (Mod.comap φ.hom.hom).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso r.underlying ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The ordinary scalar adjunction in the localization universe used by descent.
It derives the existing ordinary extension/restriction adjunction, with exact restriction.
Source: blueprint paragraph (3), internal ordinary relative tensor
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def internalAdjunction :
    ((Mod.extendScalars φ.hom.hom).leftDerivedFunctor.{
      u + 2, u + 2, u + 1, u + 1, u + 2, u + 2} :
      DerivedCategory (CategoryTheory.CondensedBar.Modules R) ⥤
        DerivedCategory (CategoryTheory.CondensedBar.Modules S)) ⊣
      (Mod.comap φ.hom.hom).mapDerivedCategory :=
  (Mod.extendRestrictAdjunction φ.hom.hom).derivedAdjunction.{
      u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}.ofNatIsoRight
    (Mod.comap φ.hom.hom).rightDerivedFunctorIsoMapDerivedCategory

/-- Derived scalar extension in the equivariant category. Its underlying functor is
ordinary internal K-flat scalar extension. The unit equation fixes its adjunction,
so a separately chosen isomorphism cannot replace the actual coefficient projection.
Source: blueprint paragraph (3), beta_R and the unit v maps to 1 tensor v
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
structure Extension where
  /-- Equivariant derived scalar extension. -/
  functor : DerivedCategory (Actions k ks R) ⥤ DerivedCategory (Actions k ks S)
  /-- The adjunction with actual exact scalar restriction. -/
  adjunction : functor ⊣ r.functor.mapDerivedCategory
  /-- Normalization by the existing internal ordinary derived relative tensor. -/
  underlying : functor ⋙ forgetDerived k ks S ≅
    forgetDerived k ks R ⋙ (Mod.extendScalars φ.hom.hom).leftDerivedFunctor.{
      u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
  /-- The equivariant unit forgets to the standard K-flat scalar unit. -/
  unit : ∀ M : DerivedCategory (Actions k ks R),
    (forgetDerived k ks R).map (adjunction.unit.app M) ≫
        (restrictionForget k ks φ r).hom.app (functor.obj M) ≫
        (Mod.comap φ.hom.hom).mapDerivedCategory.map (underlying.hom.app M) =
      (internalAdjunction φ).unit.app
        ((forgetDerived k ks R).obj M)

/-- The shift structure uniquely induced by the adjunction and exact restriction.
Source: blueprint paragraph (3), canonical shifts
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
instance Extension.shift (e : Extension k ks φ r) : e.functor.CommShift ℤ :=
  e.adjunction.leftAdjointCommShift ℤ

variable (d : ∀ T : Coefficients.{u}, OrdinaryData k ks X a T)

/-- A scalar system uses the normalized scalar comparison of the recorded descent node.
Every field is conclusion data of the final theorem, never an added assumption on V.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
structure ScalarSystem where
  /-- Actual restriction of the internal action. -/
  restriction : ScalarAction φ (ks ≃ₐ[k] ks)
  /-- Restriction is left exact. -/
  [limits : PreservesFiniteLimits restriction.functor]
  /-- Restriction is right exact. -/
  [colimits : PreservesFiniteColimits restriction.functor]
  /-- The geometric comparison includes the section and total-derived-unit normalizations. -/
  comparison : ScalarData k ks X a φ (d R) (d S) restriction
  /-- Extension is normalized by ordinary relative tensor and its unit. -/
  extension : Extension k ks φ restriction

attribute [instance] ScalarSystem.limits ScalarSystem.colimits

/-- Ordinary derived coefficient extension on the scheme, using the pulled-back ring map.
Source: blueprint paragraph (3), R_X tensor over A_X
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
abbrev extendOnScheme :
    DerivedCategory (CondensedGalois.Modules R.toMon X) ⥤
      DerivedCategory (CondensedGalois.Modules S.toMon X) :=
  (Mod.extendScalars (R := (coefficientRing X R.toMon).X)
    (S := (coefficientRing X S.toMon).X)
    ((upperStarFromPoint X).map φ.hom.hom)).leftDerivedFunctor.{
      u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}

/-- The standard derived scalar adjunction on the scheme, in the descent universe.
Source: blueprint paragraph (3), eta_V
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def schemeAdjunction : extendOnScheme X φ ⊣ (restrictX φ X).mapDerivedCategory :=
  ((Mod.extendRestrictAdjunction (R := (coefficientRing X R.toMon).X)
    (S := (coefficientRing X S.toMon).X)
    ((upperStarFromPoint X).map φ.hom.hom)).derivedAdjunction.{
      u + 2, u + 2, u + 1, u + 1, u + 2, u + 2} :
    extendOnScheme X φ ⊣ (restrictX φ X).rightDerivedFunctor)
    |>.ofNatIsoRight (restrictX φ X).rightDerivedFunctorIsoMapDerivedCategory

/-- The canonical scalar-extension shifts are induced from exact restriction.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
instance schemeShift : (extendOnScheme X φ).CommShift ℤ :=
  (schemeAdjunction X φ).leftAdjointCommShift ℤ

/-- The specified projection is the transpose of the geometric image of the unit,
followed by the canonical scalar-restriction comparison.
Source: blueprint paragraph (3), displayed beta_R
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def projectionComponent (s : ScalarSystem k ks X a φ d)
    (V : DerivedCategory (CondensedGalois.Modules R.toMon X)) :=
  (s.extension.adjunction.homEquiv _ _).symm
    ((d R).geometric.functor.rightDerivedFunctor.map
        ((schemeAdjunction X φ).unit.app V) ≫
      s.comparison.geometric.derived.hom.app ((extendOnScheme X φ).obj V))

/-- A natural projection with exactly the specified components and canonical shifts.
Source: blueprint paragraph (3), beta_R, naturality and shifts
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
structure Projection (s : ScalarSystem k ks X a φ d) where
  /-- The natural transformation on all derived inputs. -/
  transformation : (d R).geometric.functor.rightDerivedFunctor ⋙ s.extension.functor ⟶
    extendOnScheme X φ ⋙ (d S).geometric.functor.rightDerivedFunctor
  /-- Every component is the actual adjunction transpose, including the zero input. -/
  normalization : ∀ V, transformation.app V = projectionComponent k ks X a φ d s V
  /-- Compatibility with the canonical shifts. -/
  shift : NatTrans.CommShift transformation ℤ

/-- Finite-dimensional continuous E-representations realizing an equivariant module.
The additive identifications commute with restriction, the actual internal scalar action,
and every generalized Galois element. The norm topology is part of the displayed data.
Source: blueprint paragraph (3), W_q and its equivariant condensation
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
structure CohomologyModel (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    (H : Actions k ks (finiteRing ℓ Ω E)) where
  /-- A carrier in the section universe; finite dimension imposes no restriction on rank. -/
  W : Type (u + 1)
  /-- The vector space has its norm topology. -/
  [normedGroup : NormedAddCommGroup W]
  /-- The norm extends the fixed topology on E. -/
  [normedSpace : NormedSpace E W]
  /-- Finite dimension over the same E as the input complex. -/
  finite : FiniteDimensional E W
  /-- An E-linear Galois action; inverses in G make each endomorphism invertible. -/
  representation : (ks ≃ₐ[k] ks) →* Module.End E W
  /-- Joint continuity for the Krull and norm topologies. -/
  continuous : Continuous (fun z : (ks ≃ₐ[k] ks) × W ↦ representation z.1 z.2)
  /-- Condensation on every profinite set, including the empty set. -/
  sections : ∀ P : Profinite.{u}, H.module.X.obj.obj (op P) ≃+ C(P, W)
  /-- Restriction is precomposition. -/
  restriction : ∀ (P Q : Profinite.{u}) (f : Q ⟶ P) (m : H.module.X.obj.obj (op P)),
    sections Q (H.module.X.obj.map f.op m) = (sections P m).comp f.hom.hom
  /-- The internal E-action is pointwise multiplication, via the canonical tensor map. -/
  scalar : ∀ (P : Profinite.{u}) (b : C(P, E)) (m : H.module.X.obj.obj (op P)) (t : P),
    sections P ((ModObj.smul (M := (finiteRing ℓ Ω E).X) (X := H.module.X)).hom.app (op P)
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (finiteRing ℓ Ω E).X H.module.X).app (op P) (TensorProduct.tmul ℤ (ULift.up b) m))) t =
      b t • sections P m t
  /-- Equivariance for all continuous generalized Galois elements. -/
  action : ∀ (P : Profinite.{u}) (g : C(P, ks ≃ₐ[k] ks))
    (m : Profinite.CondensedAction.sectionModule (finiteRing ℓ Ω E).toMon H.module P) (t : P),
    sections P (H.act P g m) t = representation (g t) (sections P m t)

/-- Canonical transitivity of restriction on the scheme. Its underlying sheaf map is
literally the identity, fixing all coherence maps rather than choosing derived arrows.
Source: blueprint paragraph (3), coefficient square
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
structure SchemeComposition {T : Coefficients.{u}} (ψ : S ⟶ T) where
  /-- Restriction along a composite is successive restriction. -/
  ordinary : restrictX (φ ≫ ψ) X ≅ restrictX ψ X ⋙ restrictX φ X
  /-- The same section is viewed with the same restricted scalar action. -/
  normalization : ∀ N, (ordinary.hom.app N).hom = 𝟙 N.X

/-- Derive the canonical restriction-transitivity map term by term.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def SchemeComposition.derived {T : Coefficients.{u}} {ψ : S ⟶ T}
    (t : SchemeComposition X φ ψ) :
    (restrictX (φ ≫ ψ) X).mapDerivedCategory ≅
      (restrictX ψ X).mapDerivedCategory ⋙ (restrictX φ X).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso t.ordinary ≪≫ Functor.mapDerivedCategoryCompIso _ _

/-- Transitivity of equivariant scalar restriction, normalized after forgetting action.
Source: blueprint paragraph (3), coefficient square
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
structure ActionComposition {T : Coefficients.{u}} (ψ : S ⟶ T)
    (sφ : ScalarSystem k ks X a φ d) (sψ : ScalarSystem k ks X a ψ d)
    (sφψ : ScalarSystem k ks X a (φ ≫ ψ) d) where
  /-- The canonical comparison between the two restrictions. -/
  ordinary : sφψ.restriction.functor ≅ sψ.restriction.functor ⋙ sφ.restriction.functor
  /-- Underlying maps agree with the existing internal-module restriction coherence. -/
  normalization : ∀ N : Actions k ks T,
    (ordinary.hom.app N).val ≫
        sφ.restriction.underlying.hom.app (sψ.restriction.functor.obj N) ≫
        (Mod.comap φ.hom.hom).map (sψ.restriction.underlying.hom.app N) =
      sφψ.restriction.underlying.hom.app N ≫
        (Mod.comapComp φ.hom.hom ψ.hom.hom).hom.app N.module

/-- The derived action-restriction coherence is the exact termwise ordinary coherence.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def ActionComposition.derived {T : Coefficients.{u}} {ψ : S ⟶ T}
    {sφ : ScalarSystem k ks X a φ d} {sψ : ScalarSystem k ks X a ψ d}
    {sφψ : ScalarSystem k ks X a (φ ≫ ψ) d}
    (t : ActionComposition k ks X a φ d ψ sφ sψ sφψ) :
    sφψ.restriction.functor.mapDerivedCategory ≅
      sψ.restriction.functor.mapDerivedCategory ⋙ sφ.restriction.functor.mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso t.ordinary ≪≫ Functor.mapDerivedCategoryCompIso _ _

/-- The scheme coefficient change is the transpose of the composite coefficient unit.
On a K-flat model it sends z tensor v to c_X(z) tensor v.
Source: blueprint paragraph (3), the map entering kappa
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def schemeChange {T : Coefficients.{u}} (ψ : S ⟶ T)
    (t : SchemeComposition X φ ψ)
    (V : DerivedCategory (CondensedGalois.Modules R.toMon X)) :=
  ((schemeAdjunction X φ).homEquiv _ _).symm
    ((schemeAdjunction X (φ ≫ ψ)).unit.app V ≫
      t.derived.hom.app ((extendOnScheme X (φ ≫ ψ)).obj V))

/-- The complete coefficient square, with specified natural transformations and shifts.
Source: blueprint paragraph (3), Res_c(beta_B) gamma = kappa beta_C
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
structure Square {T : Coefficients.{u}} (ψ : S ⟶ T)
    (sφ : ScalarSystem k ks X a φ d) (sψ : ScalarSystem k ks X a ψ d)
    (sφψ : ScalarSystem k ks X a (φ ≫ ψ) d)
    (bφ : Projection k ks X a φ d sφ) (bφψ : Projection k ks X a (φ ≫ ψ) d sφψ) where
  /-- Coherent exact restriction on equivariant modules. -/
  actionComposition : ActionComposition k ks X a φ d ψ sφ sψ sφψ
  /-- Coherent exact restriction on module sheaves. -/
  schemeComposition : SchemeComposition X φ ψ
  /-- The coefficient inclusion on geometric complexes. -/
  gamma : sφ.extension.functor ⟶
    sφψ.extension.functor ⋙ sψ.restriction.functor.mapDerivedCategory
  /-- The coefficient inclusion is fixed by its adjoint unit, for every complex. -/
  gamma_normalization : ∀ M,
    gamma.app M = (sφ.extension.adjunction.homEquiv _ _).symm
      (sφψ.extension.adjunction.unit.app M ≫
        actionComposition.derived.hom.app (sφψ.extension.functor.obj M))
  /-- Kappa is a natural map on the original V. -/
  kappa : extendOnScheme X φ ⋙ (d S).geometric.functor.rightDerivedFunctor ⟶
    extendOnScheme X (φ ≫ ψ) ⋙ (d T).geometric.functor.rightDerivedFunctor ⋙
      sψ.restriction.functor.mapDerivedCategory
  /-- Its components are geometric sections of the actual scheme coefficient inclusion. -/
  kappa_normalization : ∀ V,
    kappa.app V = (d S).geometric.functor.rightDerivedFunctor.map
        (schemeChange X φ ψ schemeComposition V) ≫
      sψ.comparison.geometric.derived.hom.app ((extendOnScheme X (φ ≫ ψ)).obj V)
  /-- Both comparison arrows preserve the canonical shifts. -/
  gamma_shift : NatTrans.CommShift gamma ℤ
  /-- Both comparison arrows preserve the canonical shifts. -/
  kappa_shift : NatTrans.CommShift kappa ℤ
  /-- The square already commutes in D(A_G(S)); further restriction preserves it. -/
  commutes : ∀ V, constantModelBoundedConstructible R.X X V →
    gamma.app ((d R).geometric.functor.rightDerivedFunctor.obj V) ≫
        sψ.restriction.functor.mapDerivedCategory.map (bφψ.transformation.app V) =
      bφ.transformation.app V ≫ kappa.app V

/-- The finite geometric assertion for the two actual coefficient projections.
Source: blueprint paragraph (3), boundedness, finite-dimensional cohomology and projections
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def FiniteAssertion (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    (c : closureRing ℓ Ω ⟶ normRing Ω)
    (sC : ScalarSystem k ks X a (finiteInclusion ℓ Ω E) d)
    (sB : ScalarSystem k ks X a (finiteInclusion ℓ Ω E ≫ c) d)
    (sc : ScalarSystem k ks X a c d) : Prop :=
  ∃ (bC : Projection k ks X a (finiteInclusion ℓ Ω E) d sC)
    (bB : Projection k ks X a (finiteInclusion ℓ Ω E ≫ c) d sB),
    Nonempty (Square k ks X a (finiteInclusion ℓ Ω E) d c sC sc sB bC bB) ∧
    ∀ (V : DerivedCategory (CondensedGalois.Modules (finiteRing ℓ Ω E).toMon X)),
      constantModelBoundedConstructible (finiteRing ℓ Ω E).X X V →
      DerivedCategory.TStructure.t.bounded
        ((d (finiteRing ℓ Ω E)).geometric.functor.rightDerivedFunctor.obj V) ∧
      (∃ (lo hi : ℤ)
        (m : ∀ q : ℤ, CohomologyModel k ks ℓ Ω E
          ((DerivedCategory.homologyFunctor _ q).obj
            ((d (finiteRing ℓ Ω E)).geometric.functor.rightDerivedFunctor.obj V))),
        ∀ q : ℤ, q < lo ∨ hi < q → Subsingleton (m q).W) ∧
      IsIso (bC.transformation.app V) ∧ IsIso (bB.transformation.app V)

end Systems

/-- All categorical structures are supplied in the conclusion. The geometric functors and
scalar comparisons retain the section and derived-unit normalization of the descent node.
Source: blueprint paragraph (3)
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model). -/
def Assertion (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E]
    (c : closureRing ℓ Ω ⟶ normRing Ω) : Prop := by
  refine ∃ h : ∀ R : Coefficients.{u}, ActionAbelian R (ks ≃ₐ[k] ks), ?_
  letI (R : Coefficients.{u}) : ActionAbelian R (ks ≃ₐ[k] ks) := h R
  refine ∃ g : ∀ R : Coefficients.{u},
    IsGrothendieckAbelian.{u + 1} (Actions k ks R), ?_
  letI (R : Coefficients.{u}) : IsGrothendieckAbelian.{u + 1} (Actions k ks R) := g R
  refine ∃ fl : ∀ R : Coefficients.{u},
    PreservesFiniteLimits (forgetAction (A := R) (G := ks ≃ₐ[k] ks)), ?_
  letI (R : Coefficients.{u}) :
    PreservesFiniteLimits (forgetAction (A := R) (G := ks ≃ₐ[k] ks)) := fl R
  refine ∃ fc : ∀ R : Coefficients.{u},
    PreservesFiniteColimits (forgetAction (A := R) (G := ks ≃ₐ[k] ks)), ?_
  letI (R : Coefficients.{u}) :
    PreservesFiniteColimits (forgetAction (A := R) (G := ks ≃ₐ[k] ks)) := fc R
  exact ∃ (d : ∀ R : Coefficients.{u}, OrdinaryData k ks X a R)
    (sC : ScalarSystem k ks X a (finiteInclusion ℓ Ω E) d)
    (sB : ScalarSystem k ks X a (finiteInclusion ℓ Ω E ≫ c) d)
    (sc : ScalarSystem k ks X a c d), FiniteAssertion k ks X a d ℓ Ω E c sC sB sc

/-- Geometric cohomology is bounded with finite-dimensional continuous E-representation
cohomology. Both specified scalar projections are invertible, and their normalized
C-linear square is natural and compatible with shifts.

The algebraic closure Omega is arbitrary, its norm extends the norm on Q_ell, and E
is the specified embedded finite intermediate field. All inclusion maps are sectionwise.
Source: main-20261015 blueprint, direct-images proof paragraph (3), structural input;
exact literature proof WANTED
(blueprint: lem-sfb-geometric-condensed-finite-scalar-model).

Proof plan:
1. Put $s=\operatorname{Spec}k$ and write $a:X\to s$ for the structure map. By
[lem-sfb-field-action-derived-section-transport] use the exact normalized equivalences $E_R$ from
field module sheaves to condensed $G$-modules. They identify $\mathcal K_R$ with $D(E_R)Ra_{*,R}$,
preserve scalar adjunction units and counits, and identify the specified $\beta_R$ with the
canonical coefficient projection for $a$. Thus this is a comparison of the actual maps of the
statement. The same input identifies forgetting $G$ with geometric derived sections over $X^s$ and
makes it an exact conservative functor; below this permits detecting an isomorphism after
forgetting the action. Uses: lem-sfb-field-action-derived-section-transport.

2. Apply [lem-sfb-dc-lower-star-preserves] with coefficient $\underline E$ to $a:X\to s$. Its
hypotheses are met: $\underline E$ for the finite normed $E$ is one of its coefficient rings, and
$X$, $s$ and $a$ lie in the setting of the item ($k$ of characteristic $p\ne\ell$, separated
finite-type $k$-schemes). Its input is bounded constructible in the stratified
local-finite-presentation sense, whereas $V$ is given in the finite constant local model sense; a
finite constant local model is locally finitely presented by
[det-def-sfb-constructible-local-model], on the same constructible strata, so $V$ qualifies. Hence
every $H^q(Ra_{*,A}V)$ is constructible in the local-finite-presentation sense, and only finitely
many are nonzero. Since $s=\operatorname{Spec}k$ is Noetherian and $\underline E$ carries
certificate (i), [lem-sfb-adic-constructibility-predicate-comparison] converts this into the
finite constant local model sense of [sk-def-sfb-constructible]. On the one-point scheme $s$ the
only nonempty stratum is $s$ itself, and a finitely presented $E$-module is a finite-dimensional
vector space, hence free of finite rank. So on a pro-étale cover each $H^q(Ra_{*,A}V)$ is
$A_{U_i}^{n_i}$, that is, lisse [def-sfb-lisse-coefficient-module]. The last clause of
[lem-sfb-field-action-derived-section-transport] gives a finite-dimensional norm-topological
$E$-representation $W_q$ of $G$ realizing it. T-exactness of $D(E_A)$ identifies this realization
with $H^q(K_A)$. Since there are only finitely many nonzero cohomology sheaves, choose $W_q=0$
outside the same finite interval. This proves boundedness in the equivariant category, without
taking arithmetic invariants. Uses: lem-sfb-dc-lower-star-preserves,
det-def-sfb-constructible-local-model, lem-sfb-adic-constructibility-predicate-comparison,
sk-def-sfb-constructible, def-sfb-lisse-coefficient-module,
lem-sfb-field-action-derived-section-transport.

3. For $R=C$, apply [lem-sfb-qlbar-direct-image-comparison] to $a$ and the bounded (hence
bounded-below) complex $V$. The morphism is qcqs because it is separated of finite type; in
particular the source is qcqs by [lem-weil-pbc-qcqs-over-affine]. This theorem uses exactly the
finite-subextension-valued ring $C$, not $B$. It says the counit-adjoint projection is an
isomorphism in the target module derived category. Applying $D(E_C)$ and the unit/counit
normalization in [lem-sfb-field-action-derived-section-transport] proves that the actual $\beta_C$
is an isomorphism. Uses: lem-sfb-qlbar-direct-image-comparison, lem-weil-pbc-qcqs-over-affine,
lem-sfb-field-action-derived-section-transport.

4. For $R=B$, forget $G$ using [lem-sfb-field-action-derived-section-transport]. The resulting map
is the coefficient projection $B\otimes_A^L Rp_{X^s*}V^s\to
Rp_{X^s*}(B_{X^s}\otimes^L_{A_{X^s}}V^s)$, where $V^s=u^*V$. Pullback is exact by
[det-prop-sfb-module-pullback-exact-main], so $H^q(V^s)=u^*H^q(V)$ and $V^s$ is bounded. By
[det-def-sfb-constructible-local-model] each $H^q(V)$ is constructible in the
local-finite-presentation sense, and [lem-weil-pbc-module-constructible-pullback] shows that
$u^*H^q(V)$ is again constructible in that sense. The scheme $X^s$ is separated of finite type
over the separably closed positive-characteristic field $k^s$, hence Noetherian, so
[lem-sfb-adic-constructibility-predicate-comparison] (certificate (i) for $\underline E$) puts
$V^s$ in $\Dbc(X^s,E)$ of [sk-def-sfb-constructible], the finite constant local model convention
used by the generator lemma. By [det-lem-integral-models-generators](1), $V^s$ is obtained by
finitely many cones and shifts from objects $Q=(a_!L_0)[1/\ell]$, with $a:S\hookrightarrow X^s$
locally closed and $L_0$ lisse finite free over $\mathcal O_{E,S}$. The coefficient field remains
this same $E$; no field descent of the whole complex is being asserted. Uses:
lem-sfb-field-action-derived-section-transport, det-prop-sfb-module-pullback-exact-main,
det-def-sfb-constructible-local-model, lem-weil-pbc-module-constructible-pullback,
lem-sfb-adic-constructibility-predicate-comparison, sk-def-sfb-constructible,
det-lem-integral-models-generators.

5. For each generator $Q$ just obtained, [lem-sfb-supported-lattice-norm-projection], applied with
$K=k^s$ and $T=X^s$, proves invertibility of exactly this projection map. To pass through the
finite construction, fix the coefficient object $B$ and use
[lem-sfb-ringed-projection-first-shift]: projection is a natural transformation of exact functors
in the geometric input, compatible with its shifts and the third arrows of triangles. Thus the
isomorphism locus contains every shift of a generator and is closed under cones by
[lem-sf-triangle-two-out-of-three]. Induction on the finite number of shifts and cones in step 4
proves invertibility for $V^s$. Exact conservativity of forgetting $G$ from step 1 now proves
invertibility of $\beta_B$ in $D(\mathcal A_G(B))$. This uses no commutation of tensor with an
infinite totalization. Uses: lem-sfb-supported-lattice-norm-projection,
lem-sfb-ringed-projection-first-shift, lem-sf-triangle-two-out-of-three,
lem-sfb-field-action-derived-section-transport.

6. It remains to check the prescribed square rather than choose unrelated isomorphisms. Work first
on $s_{\mathrm{proet}}$ and use the canonical coefficient maps $A_s\to C_s\xrightarrow{c_s}B_s$.
The normalized projections are the $\chi$ of [lem-pur-ringed-coefficient-projection-cocycle]. Its
cocycle identity identifies the projection for the composite $A_s\to B_s$ with the successive
projections for $A_s\to C_s$ and $C_s\to B_s$, under balanced tensor associativity. Precompose the
latter identity with the scalar unit
$C_s\otimes^L_{A_s}Ra_*V\to\operatorname{Res}_{c_s}(B_s\otimes^L_{A_s}Ra_*V)$. The scalar
adjunction triangle identity then gives
$$\operatorname{Res}_{c_s}(\chi_{A,B})\circ\gamma_s=\kappa_s\circ\chi_{A,C}.$$ More explicitly,
the transpose of either side is $Ra_*V\to\operatorname{Res}_{A,B}Ra_{*,B}(B_X\otimes^L_{A_X}V)$
induced by the same unit $v\mapsto1\otimes v$; the route through $C$ sends it to $1\otimes
v\mapsto c(1)\otimes v=1\otimes v$. Uniqueness of adjoints proves equality of these derived
arrows. Transport by the coefficient-compatible equivalences of
[lem-sfb-field-action-derived-section-transport] gives exactly
$\operatorname{Res}_c(\beta_B)\circ\gamma=\kappa\circ\beta_C$. This is an equality in the
$C$-equivariant derived category and therefore remains one after restriction to $A$. Uses:
lem-pur-ringed-coefficient-projection-cocycle, lem-sfb-field-action-derived-section-transport.

7. All projections in the preceding steps are the counit-adjoint maps. Naturality in $V$ follows
from naturality of the derived scalar unit and the comparison with restriction, preserved by the
normalized transport. Compatibility with the canonical shifts follows from
[lem-sfb-ringed-projection-first-shift] and the shift compatibility in
[lem-pur-ringed-coefficient-projection-cocycle] and
[lem-sfb-field-action-derived-section-transport]. These give the claimed naturality and shift
assertion for both isomorphisms and their square. If $V=0$ or $X=\varnothing$, every geometric
object and map here is zero; if $G=1$, transport forgets no action and the same proof applies.
Uses: lem-sfb-ringed-projection-first-shift, lem-pur-ringed-coefficient-projection-cocycle,
lem-sfb-field-action-derived-section-transport.
-/
theorem geometric_condensed_finite_scalar_model
    (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (E : IntermediateField ℚ_[ℓ] Ω) [FiniteDimensional ℚ_[ℓ] E] :
    Assertion k ks X a ℓ Ω E (inclusion ℓ Ω) := by
  sorry

end AlgebraicGeometry.ProEtale.GeometricFiniteScalar
