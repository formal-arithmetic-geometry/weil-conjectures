/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.CategoryTheory.InternalActionSitePresentation
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Geometric restriction for sheaves with an internal group action

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images, paragraph (3),
agent-formulated internal-group infrastructure; Stacks 04TQ for morphism gluing.
(blueprint: lem-sfb-action-topos-geometric-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]

/-- The underlying set sheaf of a group sheaf, retaining the given section groups.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
def groupSheaf (J : Precoverage C) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    Sheaf J.toGrothendieck (Type u) := ⟨K ⋙ forget GrpCat.{u}, hK⟩

/-- Unit and multiplication are natural sectionwise maps.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction).
Proof: every group restriction preserves 1 and multiplication, respectively. -/
theorem groupOperations_naturality (J : Precoverage C) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    (∀ (X Y : Cᵒᵖ) (f : X ⟶ Y),
      (𝟙_ (Sheaf J.toGrothendieck (Type u))).obj.map f ≫
          (↾fun _ ↦ (1 : K.obj Y)) =
        (↾fun _ ↦ (1 : K.obj X)) ≫ (groupSheaf J K hK).obj.map f) ∧
    (∀ (X Y : Cᵒᵖ) (f : X ⟶ Y),
      ((groupSheaf J K hK) ⊗ (groupSheaf J K hK)).obj.map f ≫
          (↾fun p : K.obj Y × K.obj Y ↦ p.1 * p.2) =
        (↾fun p : K.obj X × K.obj X ↦ p.1 * p.2) ≫
          (groupSheaf J K hK).obj.map f) := by
  sorry

/-- The unit of the underlying internal monoid is the actual group unit.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
def groupOne (J : Precoverage C) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    𝟙_ (Sheaf J.toGrothendieck (Type u)) ⟶ groupSheaf J K hK where
  hom := { app := fun X ↦ ↾fun _ ↦ (1 : K.obj X)
           naturality := fun _ _ f ↦ (groupOperations_naturality J K hK).1 _ _ f }

/-- Multiplication of the underlying internal monoid is actual group multiplication.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
def groupMul (J : Precoverage C) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    groupSheaf J K hK ⊗ groupSheaf J K hK ⟶ groupSheaf J K hK where
  hom := { app := fun X ↦ ↾fun p : K.obj X × K.obj X ↦ p.1 * p.2
           naturality := fun _ _ f ↦ (groupOperations_naturality J K hK).2 _ _ f }

/-- The internal monoid laws are precisely the sectionwise group laws.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction).
Proof: evaluate each diagram on sections. The unit diagrams are 1a=a and a1=a;
the associativity diagram is (ab)c=a(bc). Equality of sheaf maps is sectionwise. -/
theorem groupMonoid_laws (J : Precoverage C) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    (groupOne J K hK ▷ groupSheaf J K hK ≫ groupMul J K hK =
      (λ_ (groupSheaf J K hK)).hom) ∧
    (groupSheaf J K hK ◁ groupOne J K hK ≫ groupMul J K hK =
      (ρ_ (groupSheaf J K hK)).hom) ∧
    (groupMul J K hK ▷ groupSheaf J K hK ≫ groupMul J K hK =
      (α_ _ _ _).hom ≫ groupSheaf J K hK ◁ groupMul J K hK ≫ groupMul J K hK) := by
  sorry

/-- The canonical internal monoid on a group sheaf, with real operation maps.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
instance groupMonoid (J : Precoverage C) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    MonObj (groupSheaf J K hK) where
  one := groupOne J K hK
  mul := groupMul J K hK
  one_mul := (groupMonoid_laws J K hK).1
  mul_one := (groupMonoid_laws J K hK).2.1
  mul_assoc := (groupMonoid_laws J K hK).2.2

/-- Internal group actions use Mathlib's category of internal monoid modules.
Its objects have an action sheaf morphism and its morphisms are equivariant sheaf maps.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
abbrev SetActions (J : Precoverage C) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :=
  Mod (Sheaf J.toGrothendieck (Type u)) (groupSheaf J K hK)

/-- The section action evaluates the actual internal action morphism.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
def setAction (J : Precoverage C) (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (M : SetActions J K hK) (X : Cᵒᵖ) (a : K.obj X) (x : M.X.obj.obj X) :
    M.X.obj.obj X := (ModObj.smul (M := groupSheaf J K hK) (X := M.X)).hom.app X (a, x)

/-- Restriction changes an arrow label by the given morphism of group presheaves.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction).
Proof: identity labels map to 1. For composition commute theta with restriction
by naturality, and use its multiplicativity on b g*a. -/
theorem restrictionSite_laws {K L : Cᵒᵖ ⥤ GrpCat.{u}} (θ : L ⟶ K) :
    (∀ X : C, θ.app (op X) 1 = 1) ∧
    (∀ (X Y : C) (f : X ⟶ Y) (a : L.obj (op X)) (b : L.obj (op Y)),
      θ.app (op X) (a * L.map f.op b) =
        θ.app (op X) a * K.map f.op (θ.app (op Y) b)) := by
  sorry

/-- The actual label-changing functor on the already defined twisted sites.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
def restrictionSite {K L : Cᵒᵖ ⥤ GrpCat.{u}} (θ : L ⟶ K) : Object L ⥤ Object K where
  obj X := ⟨X.base⟩
  map f := ⟨f.base, θ.app _ f.label⟩
  map_id X := congrArg
    (fun a : K.obj (op X.base) ↦
      (Arrow.mk (K := K) (𝟙 X.base) a :
        Object.mk (K := K) X.base ⟶ Object.mk (K := K) X.base))
    ((restrictionSite_laws θ).1 X.base)
  map_comp {X _Y Z} f g := congrArg
    (fun a : K.obj (op X.base) ↦
      (Arrow.mk (K := K) (f.base ≫ g.base) a :
        Object.mk (K := K) X.base ⟶ Object.mk (K := K) Z.base))
    ((restrictionSite_laws θ).2 _ _ f.base f.label g.label)

/-- Precomposition along label change and projection preserves sheaves.
Source: internal-group infrastructure, paragraph (3), proof steps 1--2 and 7
(blueprint: lem-sfb-action-topos-geometric-restriction).
Proof: normalize covering arrows by their invertible labels. A matching family for
either precomposition is then exactly a base matching family; uniqueness and gluing
follow from the source sheaf. Use the label-1 characterization of the generated topology. -/
theorem actionPrecomposition_isSheaf [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings) {K L : Cᵒᵖ ⥤ GrpCat.{u}} (θ : L ⟶ K)
    (A : Type (u + 1)) [Category.{u} A] :
    (∀ M : Sheaf (topology K J) A,
      Presheaf.IsSheaf (topology L J) ((restrictionSite θ).op ⋙ M.obj)) ∧
    (∀ M : Sheaf J.toGrothendieck A,
      Presheaf.IsSheaf (topology K J) ((projection K).op ⋙ M.obj)) := by
  sorry

/-- Precomposition lifted to the existing full category of sheaves.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
def precomposition {D : Type u} [SmallCategory D]
    (J : GrothendieckTopology C) (T : GrothendieckTopology D) (F : D ⥤ C)
    (A : Type (u + 1)) [Category.{u} A]
    (hF : ∀ M : Sheaf J A, Presheaf.IsSheaf T (F.op ⋙ M.obj)) :
    Sheaf J A ⥤ Sheaf T A :=
  ObjectProperty.lift _
    (sheafToPresheaf J A ⋙ (Functor.whiskeringLeft _ _ A).obj F.op) hF

/-- Restriction of actions on their action-site presentation, by actual precomposition.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
def restriction [HasFiniteLimits C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    {K L : Cᵒᵖ ⥤ GrpCat.{u}} (θ : L ⟶ K) (A : Type (u + 1)) [Category.{u} A] :
    Sheaf (topology K J) A ⥤ Sheaf (topology L J) A :=
  precomposition _ _ (restrictionSite θ) A ((actionPrecomposition_isSheaf J hJ θ A).1)

/-- Inflation by the trivial action on the action-site presentation.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
def inflation [HasFiniteLimits C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (K : Cᵒᵖ ⥤ GrpCat.{u}) (A : Type (u + 1)) [Category.{u} A] :
    Sheaf J.toGrothendieck A ⥤ Sheaf (topology K J) A :=
  precomposition _ _ (projection K) A ((actionPrecomposition_isSheaf J hJ (𝟙 K) A).2)

/-- Underlying set sheaves of modules, using the recorded module category.
Source: Modules on Sites, 03D1--03D3
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
noncomputable abbrev moduleSets (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) :=
  SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat.{u})

/-- A normalized module pullback for the recorded ringed geometric morphism.
The Hom identification is the given set-sheaf adjunction, so this is its induced
module pullback and not an unspecified left adjoint with an unspecified comparison.
Source: Modules on Sites, 03D1--03D3
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
structure ModulePullback {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} {T : GrothendieckTopology D}
    {A : Sheaf T RingCat.{u}} {B : Sheaf J RingCat.{u}}
    (f : RingedToposMorphism A B) where
  /-- The actual module inverse image. -/
  functor : ringedSiteModules.{u} B ⥤ ringedSiteModules.{u} A
  /-- The module adjunction. -/
  adjunction : functor ⊣ f.modules
  /-- Its inverse image on underlying sheaves. -/
  underlying : functor ⋙ moduleSets T A ≅ moduleSets J B ⋙ f.inverse
  /-- The adjunction is induced by the set-sheaf adjunction. -/
  normalization (M : ringedSiteModules.{u} B) (N : ringedSiteModules.{u} A)
      (g : functor.obj M ⟶ N) :
    (moduleSets J B).map (adjunction.homEquiv M N g) ≫ f.underlying.hom.app N =
      f.adj.homEquiv _ _ (underlying.inv.app M ≫ (moduleSets T A).map g)

/-- The pulled coefficient has its actual presheaf, with no choice of ring structure.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
def pulledCoefficient {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} (T : GrothendieckTopology D) (F : D ⥤ C)
    (R : Sheaf J CommRingCat.{u}) (hR : Presheaf.IsSheaf T (F.op ⋙ R.obj)) :
    Sheaf T CommRingCat.{u} := ⟨F.op ⋙ R.obj, hR⟩

/-- Ringed realization and exact module pullback for a specified precomposition.
Every comparison is normalized on sections, including the tensor and regular unit.
Source: internal-group infrastructure, paragraph (3), steps 8--11
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
structure PrecompositionPullback {D : Type u} [SmallCategory D]
    (J : GrothendieckTopology C) (T : GrothendieckTopology D) (F : D ⥤ C)
    (hF : ∀ M : Sheaf J (Type u), Presheaf.IsSheaf T (F.op ⋙ M.obj))
    (R : Sheaf J CommRingCat.{u}) (hR : Presheaf.IsSheaf T (F.op ⋙ R.obj)) where
  /-- A ringed geometric morphism with the prescribed inverse image. -/
  ringed : RingedToposMorphism (baseRing T (pulledCoefficient T F R hR)) (baseRing J R)
  /-- The inverse image is the literal precomposition, on both objects and maps. -/
  inverse_eq : ringed.inverse = precomposition J T F (Type u) hF
  /-- The structural ring map is the identity, under this literal identification. -/
  structural :
    (eqToIso inverse_eq).inv.app ((sheafCompose J (forget RingCat)).obj (baseRing J R)) ≫
      ringed.ringMap = 𝟙 _
  /-- The induced module pullback with its normalized adjunction. -/
  pullback : ModulePullback ringed
  /-- Additivity of the module pullback. -/
  additive : pullback.functor.Additive
  /-- Exactness: kernels are preserved. -/
  limits : PreservesFiniteLimits pullback.functor
  /-- Exactness: cokernels are preserved. -/
  colimits : PreservesFiniteColimits pullback.functor
  /-- The section modules are unchanged by precomposition. -/
  sections (M : ringedSiteModules.{u} (baseRing J R)) (U : Dᵒᵖ) :
    (pullback.functor.obj M).val.obj U ≃ₗ[R.obj.obj (F.op.obj U)] M.val.obj (F.op.obj U)
  /-- Every restriction is exactly the original restriction along F. -/
  restrictions (M : ringedSiteModules.{u} (baseRing J R)) {U V : Dᵒᵖ} (a : U ⟶ V)
      (x : (pullback.functor.obj M).val.obj U) :
    sections M V ((pullback.functor.obj M).val.map a x) =
      M.val.map (F.op.map a) (sections M U x)
  /-- The section identification is the underlying-set identification of the module
  pullback with the literal inverse image, so it is the one normalized by the adjunction. -/
  sections_underlying (M : ringedSiteModules.{u} (baseRing J R)) (U : Dᵒᵖ)
      (x : (pullback.functor.obj M).val.obj U) :
    (pullback.underlying.hom.app M ≫ eqToHom (congrArg
        (fun G : Sheaf J (Type u) ⥤ Sheaf T (Type u) ↦
          G.obj ((moduleSets J (baseRing J R)).obj M)) inverse_eq)).hom.app U x =
      sections M U x
  /-- Every module morphism has its original components. -/
  morphisms {M N : ringedSiteModules.{u} (baseRing J R)} (g : M ⟶ N) (U : Dᵒᵖ)
      (x : (pullback.functor.obj M).val.obj U) :
    sections N U ((pullback.functor.map g).val.app U x) =
      g.val.app (F.op.obj U) (sections M U x)
  /-- The tensor comparison for the recorded sheafified presheaf tensor. -/
  tensor (M N : ringedSiteModules.{u} (baseRing J R)) :
    pullback.functor.obj ((SheafOfModules.siteSheafTensorRight N).obj M) ≅
      (SheafOfModules.siteSheafTensorRight (pullback.functor.obj N)).obj
        (pullback.functor.obj M)
  /-- On local pure tensors this comparison is x tensor y mapped to x tensor y. -/
  tensor_pure (M N : ringedSiteModules.{u} (baseRing J R)) (U : Dᵒᵖ)
      (x : M.val.obj (F.op.obj U)) (y : N.val.obj (F.op.obj U)) :
    (tensor M N).hom.val.app U
        ((sections ((SheafOfModules.siteSheafTensorRight N).obj M) U).symm
          (SheafOfModules.siteSheafTensorTmul M N (F.op.obj U) x y)) =
      SheafOfModules.siteSheafTensorTmul (pullback.functor.obj M) (pullback.functor.obj N)
        U ((sections M U).symm x) ((sections N U).symm y)
  /-- The regular coefficient module is the unit. -/
  unitComparison : pullback.functor.obj (SheafOfModules.unit (baseRing J R)) ≅
    SheafOfModules.unit (baseRing T (pulledCoefficient T F R hR))
  /-- The comparison is the identity on the underlying regular ring sections. -/
  unit_sections (U : Dᵒᵖ)
      (x : (pullback.functor.obj (SheafOfModules.unit (baseRing J R))).val.obj U) :
    unitComparison.hom.val.app U x = sections (SheafOfModules.unit (baseRing J R)) U x

/-- The identity geometric morphism equipped with the specified coefficient map.
Source: internal-group infrastructure, paragraph (3), step 11
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
structure CoefficientChange (J : GrothendieckTopology C)
    {R R' : Sheaf J CommRingCat.{u}} (φ : R ⟶ R') where
  /-- The vertical ringed morphism has the contravariant direction of ring maps. -/
  ringed : RingedToposMorphism (baseRing J R') (baseRing J R)
  /-- Its underlying geometric inverse image is the identity functor. -/
  inverse_eq : ringed.inverse = 𝟭 _
  /-- Its structural ring map is precisely phi. -/
  structural :
    (eqToIso inverse_eq).inv.app ((sheafCompose J (forget RingCat)).obj (baseRing J R)) ≫
        ringed.ringMap =
      (sheafCompose J (forget RingCat)).map
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

/-- All geometric restriction assertions, including their canonical section normalizations.
The action category is Mathlib Mod in the cartesian category of sheaves; the site,
module category and tensor are exactly the recorded dependency constructions.
Source: internal-group infrastructure, paragraph (3)
(blueprint: lem-sfb-action-topos-geometric-restriction). -/
structure GeometricRestriction [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings) where
  /-- The set-valued action-site equivalence. -/
  equivalence (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    SetActions J K hK ≌ Sheaf (topology K J) (Type u)
  /-- The equivalence has the same section sets. -/
  sections (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (M : SetActions J K hK) (X : C) :
    ((equivalence K hK).functor.obj M).obj.obj (op (Object.mk (K := K) X)) ≃
      M.X.obj.obj (op X)
  /-- The forward equivalence has restriction x mapped to a acting on f-star x. -/
  action_restriction (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (M : SetActions J K hK) {X Y : C} (f : X ⟶ Y) (a : K.obj (op X))
    (x : ((equivalence K hK).functor.obj M).obj.obj (op (Object.mk (K := K) Y))) :
    sections K hK M X (((equivalence K hK).functor.obj M).obj.map (opArrow K f a) x) =
      setAction J K hK M (op X) a (M.X.obj.map f.op (sections K hK M Y x))
  /-- The equivalence has the same underlying sheaf maps, not merely section bijections. -/
  morphisms (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    {M N : SetActions J K hK} (g : M ⟶ N) (X : C)
    (x : ((equivalence K hK).functor.obj M).obj.obj (op (Object.mk (K := K) X))) :
    sections K hK N X (((equivalence K hK).functor.map g).hom.app _ x) =
      g.hom.hom.app (op X) (sections K hK M X x)
  /-- The presenting site is small in the stated universe. -/
  topos (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    IsGrothendieckTopos.{u} (SetActions J K hK)
  /-- Restriction is the inverse image of a geometric morphism. -/
  restriction_adj (K L : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (hL : Presheaf.IsSheaf J.toGrothendieck (L ⋙ forget GrpCat.{u})) (θ : L ⟶ K) :
    (restriction J hJ θ (Type u)).IsLeftAdjoint
  /-- Restriction preserves finite limits. -/
  restriction_limits (K L : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (hL : Presheaf.IsSheaf J.toGrothendieck (L ⋙ forget GrpCat.{u})) (θ : L ⟶ K) :
    PreservesFiniteLimits (restriction J hJ θ (Type u))
  /-- Trivial inflation is the inverse image of p_K. -/
  inflation_adj (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    (inflation J hJ K (Type u)).IsLeftAdjoint
  /-- Trivial inflation preserves finite limits. -/
  inflation_limits (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})) :
    PreservesFiniteLimits (inflation J hJ K (Type u))
  /-- The inverse equivalence recovers the trivial action on an inflated sheaf. -/
  inflation_trivial (K : Cᵒᵖ ⥤ GrpCat.{u})
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (M : Sheaf J.toGrothendieck (Type u)) (X : Cᵒᵖ) (a : K.obj X)
    (x : ((equivalence K hK).inverse.obj ((inflation J hJ K (Type u)).obj M)).X.obj.obj X) :
    setAction J K hK ((equivalence K hK).inverse.obj
      ((inflation J hJ K (Type u)).obj M)) X a x = x
  /-- The identity on inverse images specifies p_K q_theta isomorphic to p_L. -/
  over_base (K L : Cᵒᵖ ⥤ GrpCat.{u}) (θ : L ⟶ K) :
    inflation J hJ K (Type u) ⋙ restriction J hJ θ (Type u) =
      inflation J hJ L (Type u)
  /-- The same literal identity on ring sheaves is the ringed-square comparison. -/
  over_base_rings (K L : Cᵒᵖ ⥤ GrpCat.{u}) (θ : L ⟶ K) :
    inflation J hJ K CommRingCat.{u} ⋙ restriction J hJ θ CommRingCat.{u} =
      inflation J hJ L CommRingCat.{u}
  /-- Identity restriction has its literal identity identification. -/
  identity_restriction (K : Cᵒᵖ ⥤ GrpCat.{u}) :
    restriction J hJ (𝟙 K) (Type u) = 𝟭 _
  /-- Successive restriction has its literal composition identification. -/
  composition_restriction (K L H : Cᵒᵖ ⥤ GrpCat.{u}) (θ : L ⟶ K) (ψ : H ⟶ L) :
    restriction J hJ θ (Type u) ⋙ restriction J hJ ψ (Type u) =
      restriction J hJ (ψ ≫ θ) (Type u)
  /-- Exact trivial inflation of modules, with tensor and unit normalization. -/
  inflation_modules (K : Cᵒᵖ ⥤ GrpCat.{u})
      (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
      (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    PrecompositionPullback J.toGrothendieck (topology K J) (projection K)
      ((actionPrecomposition_isSheaf J hJ (𝟙 K) (Type u)).2) R
      ((actionPrecomposition_isSheaf J hJ (𝟙 K) CommRingCat.{u}).2 R)
  /-- Exact restriction of module actions, with tensor and unit normalization. -/
  restriction_modules (K L : Cᵒᵖ ⥤ GrpCat.{u})
      (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
      (hL : Presheaf.IsSheaf J.toGrothendieck (L ⋙ forget GrpCat.{u})) (θ : L ⟶ K)
      (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    PrecompositionPullback (topology K J) (topology L J) (restrictionSite θ)
      ((actionPrecomposition_isSheaf J hJ θ (Type u)).1) (coefficientSheaf K J hJ R)
      ((actionPrecomposition_isSheaf J hJ θ CommRingCat.{u}).1 (coefficientSheaf K J hJ R))
  /-- A coefficient map gives its identity geometric morphism on the base. -/
  coefficient_base {R R' : Sheaf J.toGrothendieck CommRingCat.{u}} (φ : R ⟶ R') :
    CoefficientChange J.toGrothendieck φ
  /-- The same componentwise coefficient map on the action site gives its ringed morphism. -/
  coefficient_action (K : Cᵒᵖ ⥤ GrpCat.{u})
      {R R' : Sheaf J.toGrothendieck CommRingCat.{u}} (φ : R ⟶ R') :
    CoefficientChange (topology K J) ((inflation J hJ K CommRingCat.{u}).map φ)
  /-- The structural coefficient square commutes, with identity underlying comparison. -/
  coefficient_square (K L : Cᵒᵖ ⥤ GrpCat.{u}) (θ : L ⟶ K)
      {R R' : Sheaf J.toGrothendieck CommRingCat.{u}} (φ : R ⟶ R') :
    (restriction J hJ θ CommRingCat.{u}).map
        ((inflation J hJ K CommRingCat.{u}).map φ) ≫
          (eqToIso (over_base_rings K L θ)).hom.app R' =
      (eqToIso (over_base_rings K L θ)).hom.app R ≫
        (inflation J hJ L CommRingCat.{u}).map φ

/-- Topoi of internal group actions, restriction geometric morphisms, and their exact
ringed module inverse images with canonical tensor, unit, and coefficient comparisons.
Source: main-20261015, sk-thm-sf-ctf-stability-direct-images, paragraph (3),
agent-formulated categorical infrastructure; Stacks 04TQ for morphism gluing.
(blueprint: lem-sfb-action-topos-geometric-restriction).

Proof: Steps 1--2 use the twisted category and label-1 topology characterization from
lem-sfb-internal-action-site-presentation. Send an internal action to the same sections
with restriction a f*x; recover ordinary restrictions from (f,1) and actions from (1,a).
Their composition laws give inverse functors, and equivariant maps are exactly natural
maps on the action site. Normalize covering sieves to label-1 arrows: the matching
families are the original base matching families, proving the equivalence on sheaves.
Finite limits are created in underlying sheaves (step 3). Products act coordinatewise
and equalizers have the restricted action; restriction changes neither construction.
For steps 4--6 construct the right adjoint as equivariant maps K|_U to Y|_U on every
slice test object, satisfying F(theta(l)k)=l F(k). Lem-pe-set-sheaf-cover-descent glues
maps on covers; separatedness makes the glued map equivariant. Right translation
(a F)(k)=F(ka) gives its K-action. The natural Hom bijection sends u to the map
x mapped to (k mapped to u(kx)), and its inverse evaluates at 1. Checking the two
composites sectionwise gives the adjunction. Smallness bounds its function sets.
For p_K apply the same construction to K mapping to the terminal group (step 7).
Restriction and trivial action have literal identity and composition identifications;
the identity over the base specifies the geometric comparison by uniqueness of mates.
For step 8 use lem-weil-pbc-ringed-topoi-module-adjunction with the identity structural
ring map: R tensor_R M identifies canonically with M by r tensor m mapped to rm,
inverse m mapped to 1 tensor m. Normalize its module adjunction by the set adjunction.
Step 9 uses the action-site presentation's creation of sectionwise kernels and
sheafified cokernels, so both module pullbacks are additive and exact. Step 10 uses
def-pur-sheaf-tensor-product: the identity on presheaf pure tensors descends through
sheafification, giving the diagonal action and the displayed tensor comparison.
The regular coefficient module is unchanged, giving the identity unit comparison.
Finally a coefficient map has the same components after inflation and restriction;
the inverse-image and structural maps in both ringed squares agree sectionwise,
which proves step 11 and all identity comparisons. -/
theorem geometricRestriction [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings) : Nonempty (GeometricRestriction J hJ) := by
  sorry

end CategoryTheory.InternalActionSite
