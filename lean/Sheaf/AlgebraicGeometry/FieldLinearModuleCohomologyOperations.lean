/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Functors

/-! # Field-linear cohomology, pullback and cup product of scheme modules

Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED,
the maps preceding equation `equation-kunneth-on-cech`
(blueprint: def-sc-field-linear-module-cohomology-operations).

Cohomology is the recorded right derived functor on O-modules, with scalars restricted
along the structure map. Its canonical comparison with Ext transports exact inverse-image
and tensor operations on sheaves of k-vector spaces back to these cohomology modules.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k))
/-- scalar Map.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarMap (U : X.Opens) : k →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top (a := U))).op).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom
/-- KSheaf.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
abbrev KSheaf (X : Scheme.{u}) (k : Type u) [Field k] :=
  Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)
/-- scalar Obj.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarObj (F : (SheafOfModules.{u} X.ringCatSheaf)) (U : (Opens X)ᵒᵖ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (scalarMap f U.unop)).obj (F.val.obj U)
/-- scalar Restriction linear.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarRestriction_linear (F : SheafOfModules.{u} X.ringCatSheaf)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ∀ (r : k) (x : scalarObj f F U),
      ((F.val.map i).hom.toAddMonoidHom
        (@SMul.smul k (F.val.obj U)
          (Module.compHom _ (scalarMap f U.unop)).toSMul r x) : scalarObj f F V) =
        @SMul.smul k (F.val.obj V) (Module.compHom _ (scalarMap f V.unop)).toSMul r
        ((F.val.map i).hom.toAddMonoidHom x) := by
  sorry
/-- scalar Restriction.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarRestriction (F : (SheafOfModules.{u} X.ringCatSheaf)) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    scalarObj f F U ⟶ scalarObj f F V :=
  letI : Module k (F.val.obj U) := Module.compHom _ (scalarMap f U.unop)
  letI : Module k (F.val.obj V) := Module.compHom _ (scalarMap f V.unop)
  ModuleCat.ofHom
    { toFun := fun x : scalarObj f F U ↦ ((F.val.map i).hom.toAddMonoidHom x : scalarObj f F V)
      map_add' := fun a b ↦ (F.val.map i).hom.map_add a b
      map_smul' := scalarRestriction_linear f F i }
/-- scalar Restriction id.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarRestriction_id (F : (SheafOfModules.{u} X.ringCatSheaf)) (U : (Opens X)ᵒᵖ) :
    scalarRestriction f F (𝟙 U) = 𝟙 (scalarObj f F U) := by
  sorry
/-- scalar Restriction comp.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarRestriction_comp (F : (SheafOfModules.{u} X.ringCatSheaf)) {U V W : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    scalarRestriction f F (i ≫ j) = scalarRestriction f F i ≫ scalarRestriction f F j := by
  sorry
/-- scalar Presheaf.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarPresheaf (F : (SheafOfModules.{u} X.ringCatSheaf)) : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj := scalarObj f F
  map := scalarRestriction f F
  map_id := scalarRestriction_id f F
  map_comp := scalarRestriction_comp f F
/-- scalar Presheaf is Sheaf.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Restriction of scalars leaves the underlying sections and restriction maps unchanged.
The gluing and uniqueness axioms for F therefore give the sheaf axiom for this presheaf. -/
theorem scalarPresheaf_isSheaf (F : (SheafOfModules.{u} X.ringCatSheaf)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (scalarPresheaf f F) := by
  sorry
/-- scalar Sheaf.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarSheaf (F : (SheafOfModules.{u} X.ringCatSheaf)) : KSheaf X k :=
  ⟨scalarPresheaf f F, scalarPresheaf_isSheaf f F⟩
/-- scalar Hom linear.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarHom_linear {F G : SheafOfModules.{u} X.ringCatSheaf}
    (a : F ⟶ G) (U : (Opens X)ᵒᵖ) :
    ∀ (r : k) (x : scalarObj f F U),
      ((a.val.app U).hom.toAddMonoidHom
        (@SMul.smul k (F.val.obj U)
          (Module.compHom _ (scalarMap f U.unop)).toSMul r x) : scalarObj f G U) =
        @SMul.smul k (G.val.obj U) (Module.compHom _ (scalarMap f U.unop)).toSMul r
        ((a.val.app U).hom.toAddMonoidHom x) := by
  sorry
/-- scalar Hom App.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarHomApp {F G : (SheafOfModules.{u} X.ringCatSheaf)} (a : F ⟶ G) (U : (Opens X)ᵒᵖ) :
    scalarObj f F U ⟶ scalarObj f G U :=
  letI : Module k (F.val.obj U) := Module.compHom _ (scalarMap f U.unop)
  letI : Module k (G.val.obj U) := Module.compHom _ (scalarMap f U.unop)
  ModuleCat.ofHom
    { toFun := fun x : scalarObj f F U ↦ ((a.val.app U).hom.toAddMonoidHom x : scalarObj f G U)
      map_add' := fun x y ↦ (a.val.app U).hom.map_add x y
      map_smul' := scalarHom_linear f a U }
/-- scalar Hom naturality.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarHom_naturality {F G : (SheafOfModules.{u} X.ringCatSheaf)} (a : F ⟶ G)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    scalarRestriction f F i ≫ scalarHomApp f a V =
      scalarHomApp f a U ≫ scalarRestriction f G i := by
  sorry
/-- scalar Hom.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarHom {F G : SheafOfModules.{u} X.ringCatSheaf} (a : F ⟶ G) :
    scalarSheaf f F ⟶ scalarSheaf f G :=
  ⟨{ app := scalarHomApp f a, naturality := fun _ _ i ↦ scalarHom_naturality f a i }⟩
/-- scalar Hom id.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarHom_id (F : SheafOfModules.{u} X.ringCatSheaf) :
    scalarHom f (𝟙 F) = 𝟙 (scalarSheaf f F) := by
  sorry
/-- scalar Hom comp.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
theorem scalarHom_comp {F G H : (SheafOfModules.{u} X.ringCatSheaf)} (a : F ⟶ G) (b : G ⟶ H) :
    scalarHom f (a ≫ b) = scalarHom f a ≫ scalarHom f b := by
  sorry
/-- scalar Functor.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarFunctor : (SheafOfModules.{u} X.ringCatSheaf) ⥤ KSheaf X k where
  obj := scalarSheaf f
  map := scalarHom f
  map_id := scalarHom_id f
  map_comp := scalarHom_comp f
/-- scalar Functor additive.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the corresponding sectionwise module-map law and naturality of the structure
ring map. Restriction of scalars changes neither the functions nor their compositions;
the same equalities give this compatibility. -/
@[instance] theorem scalarFunctor_additive : (scalarFunctor f).Additive := by
  sorry
/-- scalar Functor preserves Finite Limits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Finite limits of module sheaves and of k-vector-space sheaves are computed
sectionwise. Restriction of scalars preserves module limits and retains every underlying
section and restriction map. Hence the canonical comparison with each finite limit is
a sectionwise isomorphism and therefore a sheaf isomorphism. -/
@[instance] theorem scalarFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (scalarFunctor f) := by
  sorry
/-- scalar Functor preserves Finite Colimits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Check the comparison morphism on stalks. Stalks preserve finite colimits of
module sheaves, and stalks of scalarSheaf f F are the underlying k-modules of the
O_X-stalks. Restriction of scalars preserves cokernels and finite direct sums of modules.
Thus the comparison is an isomorphism on every stalk, hence an isomorphism of sheaves. -/
@[instance] theorem scalarFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (scalarFunctor f) := by
  sorry
local instance : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
local instance : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
  hasExt_of_enoughInjectives.{u, u, u + 1} (SheafOfModules.{u} X.ringCatSheaf)
local instance : HasExt.{u + 1} (KSheaf X k) := HasExt.standard (KSheaf X k)
local instance : MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _

/-- The carrier of the recorded O-module cohomology before restricting scalars.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
abbrev scalarCohomologyCarrier (_f : X ⟶ Spec (CommRingCat.of k))
    (F : (SheafOfModules.{u} X.ringCatSheaf)) (n : ℕ) :=
  (RingedSpace.moduleCohomology X.toRingedSpace n).obj F

/-- Restrict the cohomology module action along the structure map k → Γ(X, O_X).
Source: Stacks Project, Cohomology, Tag 01DZ; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
instance scalarCohomologyModule (f : X ⟶ Spec (CommRingCat.of k))
    (F : (SheafOfModules.{u} X.ringCatSheaf)) (n : ℕ) :
    Module k (scalarCohomologyCarrier f F n) :=
  Module.compHom _ (scalarMap f ⊤)

/-- The recorded O-module cohomology with its restricted k-vector-space structure.
Source: Stacks Project, Cohomology, Tag 01DZ; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomology (F : (SheafOfModules.{u} X.ringCatSheaf)) (n : ℕ) : ModuleCat.{u} k :=
  ModuleCat.of k (scalarCohomologyCarrier f F n)

/-- exists module Ext Equiv.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Evaluate module morphisms from the structure sheaf at 1. This identifies the Hom complex
with the global-sections complex. Compare degree-n homology via the injective-resolution
comparison isomorphism, giving precisely the displayed cocycle formula. -/
theorem exists_moduleExtEquiv (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    ∃ e : ((RingedSpace.moduleCohomology X.toRingedSpace n).obj F) ≃+
        Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F n,
      ∀ (I : InjectiveResolution F)
        (a : (RingedSpace.globalSectionsComplex I).cycles n)
        (φ : SheafOfModules.unit X.ringCatSheaf ⟶ I.cocomplex.X n)
        (hφ : φ ≫ I.cocomplex.d n (n+1) = 0),
        φ.val.app (op ⊤) (1 : Γ(X, ⊤)) =
          (RingedSpace.globalSectionsComplex I).iCycles n a →
        e ((I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv
          ((RingedSpace.globalSectionsComplex I).homologyπ n a)) =
            InjectiveResolution.extMk.{u, u, u + 1} I φ (n+1) rfl hφ := by
  sorry

/-- module Ext Equiv.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def moduleExtEquiv (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    ((RingedSpace.moduleCohomology X.toRingedSpace n).obj F) ≃+
      Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F n :=
  Classical.choose (exists_moduleExtEquiv F n)

/-- constant Scalar Unit.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def constantScalarUnit : KSheaf X k :=
  (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)).obj (ModuleCat.of k k)

/-- constant Scalar Unit Iso.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def constantScalarUnitIso : constantScalarUnit (X := X) (k := k) ≅ 𝟙_ (KSheaf X k) :=
  (Functor.Monoidal.εIso
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k))).symm

/-- exists scalar Unit Linear.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: The scalar ring map is additive and k-linear for the restricted action.
Bundle it as a module morphism; its value at r is the displayed scalar section. -/
theorem exists_scalarUnitLinear :
    ∃ η : ModuleCat.of k k ⟶
        (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op ⊤),
      ∀ r : k, η r = scalarMap f ⊤ r := by
  sorry

/-- scalar Unit Linear.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarUnitLinear : ModuleCat.of k k ⟶
    (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op ⊤) :=
  Classical.choose (exists_scalarUnitLinear f)

/-- scalar Unit Morphism.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarUnitMorphism : 𝟙_ (KSheaf X k) ⟶
    scalarSheaf f (SheafOfModules.unit X.ringCatSheaf) :=
  constantScalarUnitIso.inv ≫
    ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} k)
      isTerminalTop).homEquiv _ _).symm (scalarUnitLinear f)

/-- scalar Ext Map.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarExtMap (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ)
    (a : Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F n) :
    Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (scalarSheaf f F) n :=
  (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
    (a.mapExactFunctor (scalarFunctor f)) (zero_add n)

/-- scalar Cohomology Ext Map.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomologyExtMap (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ)
    (a : scalarCohomology f F n) :
    Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (scalarSheaf f F) n :=
  scalarExtMap f F n (moduleExtEquiv F n a)

/-- scalar Cohomology Ext Map add.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: The injective-resolution comparison is additive and k-linear, as are exact-functor
transport on Ext and precomposition by the scalar-unit morphism. Compose these maps. -/
theorem scalarCohomologyExtMap_add (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ)
    (a b : scalarCohomology f F n) :
    scalarCohomologyExtMap f F n (a+b) =
      scalarCohomologyExtMap f F n a + scalarCohomologyExtMap f F n b := by
  sorry

/-- scalar Cohomology Ext Map smul.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: The injective-resolution comparison is additive and k-linear, as are exact-functor
transport on Ext and precomposition by the scalar-unit morphism. Compose these maps. -/
theorem scalarCohomologyExtMap_smul (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ)
    (r : k) (a : scalarCohomology f F n) :
    scalarCohomologyExtMap f F n (r • a) = r • scalarCohomologyExtMap f F n a := by
  sorry

/-- scalar Cohomology Ext Map bijective.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Restriction of scalars preserves injective acyclicity for global sections: its left
adjoint tensors with the structure sheaf, which is exact over the field k. Compare the
two derived global-sections functors using evaluation at 1 and the constant-sheaf adjunction. -/
theorem scalarCohomologyExtMap_bijective (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    Function.Bijective (scalarCohomologyExtMap f F n) := by
  sorry

/-- scalar Cohomology Ext Equiv: the comparison `scalarCohomologyExtMap` as an additive
equivalence; it is k-linear by `scalarCohomologyExtMap_smul`.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomologyExtEquiv (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    scalarCohomology f F n ≃+
      Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (scalarSheaf f F) n :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (scalarCohomologyExtMap f F n) (scalarCohomologyExtMap_add f F n))
    (scalarCohomologyExtMap_bijective f F n)

attribute [irreducible] scalarCohomologyExtEquiv
  scalarCohomologyExtMap scalarExtMap moduleExtEquiv

variable {Y : Scheme.{u}}

/-- scalar Inverse Image.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarInverseImage (a : Y ⟶ X) : KSheaf X k ⥤ KSheaf Y k :=
  (Opens.map a.base).sheafPullback (ModuleCat.{u} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)

/-- scalar Inverse Image additive.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Inverse image on sheaves is exact and additive. This follows from the stalk
formula and filtered-colimit exactness for vector spaces, and from its left adjunction. -/
@[instance] theorem scalarInverseImage_additive (a : Y ⟶ X) :
    (scalarInverseImage (k := k) a).Additive := by
  sorry
/-- scalar Inverse Image preserves Finite Limits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Inverse image on sheaves is exact and additive. This follows from the stalk
formula and filtered-colimit exactness for vector spaces, and from its left adjunction. -/
@[instance] theorem scalarInverseImage_preservesFiniteLimits (a : Y ⟶ X) :
    PreservesFiniteLimits (scalarInverseImage (k := k) a) := by
  sorry
/-- scalar Inverse Image preserves Finite Colimits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Inverse image on sheaves is exact and additive. This follows from the stalk
formula and filtered-colimit exactness for vector spaces, and from its left adjunction. -/
@[instance] theorem scalarInverseImage_preservesFiniteColimits (a : Y ⟶ X) :
    PreservesFiniteColimits (scalarInverseImage (k := k) a) := by
  sorry

local instance : MonoidalCategory (KSheaf Y k) := Sheaf.monoidalCategory _ _
local instance : HasExt.{u + 1} (KSheaf Y k) := HasExt.standard (KSheaf Y k)

/-- scalar Inverse Unit Iso.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarInverseUnitIso (a : Y ⟶ X) :
    (scalarInverseImage (k := k) a).obj (𝟙_ (KSheaf X k)) ≅ 𝟙_ (KSheaf Y k) :=
  (scalarInverseImage a).mapIso constantScalarUnitIso.symm ≪≫
    ((Opens.map a.base).constantSheafsheafPullbackIso (ModuleCat.{u} k) _ _
      isTerminalTop isTerminalTop).app (ModuleCat.of k k) ≪≫ constantScalarUnitIso

/-- exists scalar Pullback Coefficient.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Use the inverse-image/direct-image adjunction on sheaves of k-vector spaces.
The canonical unit of tensor pullback is k-linear because a is over Spec k. Its adjoint
is the coefficient map, and the adjunction formula is exactly the displayed equality. -/
theorem exists_scalarPullbackCoefficient (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : SheafOfModules.{u} X.ringCatSheaf) :
    ∃ j : (scalarInverseImage a).obj (scalarSheaf f F) ⟶
        scalarSheaf g ((tensorPullback a).obj F),
      ∀ (U : X.Opens) (s : F.val.obj (op U)),
        ((((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k) _ _).homEquiv
          _ _) j).hom.app (op U) s =
            ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app F).val.app
              (op U) s := by
  sorry

/-- scalar Pullback Coefficient.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarPullbackCoefficient (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : SheafOfModules.{u} X.ringCatSheaf) :
    (scalarInverseImage a).obj (scalarSheaf f F) ⟶
      scalarSheaf g ((tensorPullback a).obj F) :=
  Classical.choose (exists_scalarPullbackCoefficient f g a h F)

/-- scalar Cohomology Pullback.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomologyPullback (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : SheafOfModules.{u} X.ringCatSheaf)
    (n : ℕ) (x : scalarCohomology f F n) :
    scalarCohomology g ((tensorPullback a).obj F) n :=
  (scalarCohomologyExtEquiv g _ n).symm
    (((Abelian.Ext.mk₀ (scalarInverseUnitIso a).inv).comp
      ((scalarCohomologyExtEquiv f F n x).mapExactFunctor (scalarInverseImage a))
      (zero_add n)).comp (Abelian.Ext.mk₀ (scalarPullbackCoefficient f g a h F)) (add_zero n))

attribute [irreducible] scalarCohomologyPullback scalarPullbackCoefficient
  scalarInverseUnitIso scalarUnitMorphism

local instance : MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  SheafOfModules.monoidalCategory X.sheaf
local instance : SymmetricCategory (KSheaf X k) := Sheaf.symmetricCategory _ _
local instance : MonoidalPreadditive (KSheaf X k) := Sheaf.monoidalPreadditive

/-- scalar Tensor Left Limits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Tensoring sheaves of k-vector spaces is exact: check stalks, where tensoring
over the field k is exact. Exactness gives preservation of finite limits and colimits. -/
@[instance] theorem scalarTensorLeftLimits (M : KSheaf X k) :
    PreservesFiniteLimits (tensorLeft M) := by
  sorry
/-- scalar Tensor Left Colimits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Tensoring sheaves of k-vector spaces is exact: check stalks, where tensoring
over the field k is exact. Exactness gives preservation of finite limits and colimits. -/
@[instance] theorem scalarTensorLeftColimits (M : KSheaf X k) :
    PreservesFiniteColimits (tensorLeft M) := by
  sorry
/-- scalar Tensor Right Limits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Tensoring sheaves of k-vector spaces is exact: check stalks, where tensoring
over the field k is exact. Exactness gives preservation of finite limits and colimits. -/
@[instance] theorem scalarTensorRightLimits (M : KSheaf X k) :
    PreservesFiniteLimits (tensorRight M) := by
  sorry
/-- scalar Tensor Right Colimits.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: Tensoring sheaves of k-vector spaces is exact: check stalks, where tensoring
over the field k is exact. Exactness gives preservation of finite limits and colimits. -/
@[instance] theorem scalarTensorRightColimits (M : KSheaf X k) :
    PreservesFiniteColimits (tensorRight M) := by
  sorry

/-- scalar Ext Cup.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarExtCup {A B : KSheaf X k} {p q : ℕ}
    (a : Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) A p)
    (b : Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) B q) :
    Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) (A ⊗ B) (p+q) :=
  ((Abelian.Ext.mk₀ (λ_ (𝟙_ (KSheaf X k))).inv).comp
    (a.mapExactFunctor (tensorRight (𝟙_ (KSheaf X k)))) (zero_add p)).comp
      (b.mapExactFunctor (tensorLeft A)) rfl

/-- exists scalar Tensor Coefficient.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations).
Proof: On each open send s tensor t to the sheaf tensor section tmulSection s t.
This map is k-bilinear and commutes with restriction. The universal properties of the
section tensor product and sheafification give the asserted sheaf morphism. -/
theorem exists_scalarTensorCoefficient (F G : SheafOfModules.{u} X.ringCatSheaf) :
    ∃ τ : scalarSheaf f F ⊗ scalarSheaf f G ⟶ scalarSheaf f (F ⊗ G),
      ∀ (U : X.Opens) (s : scalarObj f F (op U)) (t : scalarObj f G (op U)),
        τ.hom.app (op U)
          (((Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology X)
            (ModuleCat.{u} k)) (scalarSheaf f F) (scalarSheaf f G)).app (op U))
              (s ⊗ₜ[k] t)) = tmulSection s t := by
  sorry

/-- scalar Tensor Coefficient.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarTensorCoefficient (F G : SheafOfModules.{u} X.ringCatSheaf) :
    scalarSheaf f F ⊗ scalarSheaf f G ⟶ scalarSheaf f (F ⊗ G) :=
  Classical.choose (exists_scalarTensorCoefficient f F G)

/-- scalar Cohomology Cup.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomologyCup (F G : SheafOfModules.{u} X.ringCatSheaf) (p q : ℕ)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomology f (F ⊗ G) (p+q) :=
  (scalarCohomologyExtEquiv f _ (p+q)).symm
    ((scalarExtCup (scalarCohomologyExtEquiv f F p a)
      (scalarCohomologyExtEquiv f G q b)).comp
        (Abelian.Ext.mk₀ (scalarTensorCoefficient f F G)) (add_zero _))

/-- The normalized tensor-pullback adjunction, with its sectionwise unit.
Source: Stacks Project, Tag 0096
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarPullbackAdjunction {A B : Scheme.{u}} (a : A ⟶ B) :
    tensorPullback a ⊣ pushforward a :=
  Classical.choose (exists_tensorPullbackAdjunction a)

attribute [irreducible] scalarPullbackAdjunction scalarCohomologyCup

/-- The canonical composition comparison for tensor pullback, using its normalized adjunction.
Source: Stacks Project, Tag 0097; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarPullbackCompIso {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    tensorPullback (a ≫ b) ≅ tensorPullback b ⋙ tensorPullback a :=
  (scalarPullbackAdjunction (a ≫ b)).leftAdjointUniq
    (((scalarPullbackAdjunction b).comp
      (scalarPullbackAdjunction a)).ofNatIsoRight
        (pushforwardComp a b))

attribute [irreducible] scalarPullbackCompIso

/-- The canonical comparison associated to a commutative square of scheme morphisms.
Source: Stacks Project, Tag 0097; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarPullbackSquareIso {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) (M : D.Modules) :
    (tensorPullback a).obj ((tensorPullback b).obj M) ≅
      (tensorPullback c).obj ((tensorPullback d).obj M) :=
  ((scalarPullbackCompIso a b).app M).symm ≪≫
    eqToIso (congrArg (fun t ↦ (tensorPullback t).obj M) h) ≪≫
      (scalarPullbackCompIso c d).app M

/-- Coefficient functoriality on the recorded derived-functor cohomology.
Source: Stacks Project, Tag 01DZ
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def scalarCohomologyMap {M N : SheafOfModules.{u} X.ringCatSheaf}
    (a : M ⟶ N) (n : ℕ) (x : scalarCohomology f M n) : scalarCohomology f N n :=
  ((ModuleCat.restrictScalars (scalarMap f ⊤)).map
    ((RingedSpace.moduleCohomology X.toRingedSpace n).map a)).hom x

/-- Coefficients of the external cup product on a fibre product.
Source: Stacks Project, Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
abbrev externalCupCoefficients {A B : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))
    (b : B ⟶ Spec (CommRingCat.of k)) (M : A.Modules) (N : B.Modules) :
    (Limits.pullback a b).Modules :=
  (tensorPullback (Limits.pullback.fst a b)).obj M ⊗
    (tensorPullback (Limits.pullback.snd a b)).obj N

/-- Pull back both classes and take their cup product.
Source: Stacks Project, Varieties, Tag 0BED, maps preceding equation-kunneth-on-cech
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def externalCup {A B : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))
    (b : B ⟶ Spec (CommRingCat.of k)) (M : A.Modules) (N : B.Modules) (p q : ℕ)
    (x : scalarCohomology a M p) (y : scalarCohomology b N q) :
    scalarCohomology (Limits.pullback.fst a b ≫ a) (externalCupCoefficients a b M N) (p + q) :=
  scalarCohomologyCup (Limits.pullback.fst a b ≫ a) _ _ p q
    (scalarCohomologyPullback a (Limits.pullback.fst a b ≫ a) (Limits.pullback.fst a b) rfl M p x)
    (scalarCohomologyPullback b (Limits.pullback.fst a b ≫ a) (Limits.pullback.snd a b)
      (Limits.pullback.condition.symm) N q y)

/-- The canonical coefficient comparison for pullback of the external tensor product.
Source: Stacks Project, Tags 0097 and 01CD; Varieties, Tag 0BED
(blueprint: def-sc-field-linear-module-cohomology-operations). -/
def externalCupPullbackIso {A B A' B' : Scheme.{u}}
    (a : A ⟶ Spec (CommRingCat.of k)) (b : B ⟶ Spec (CommRingCat.of k))
    (a' : A' ⟶ Spec (CommRingCat.of k)) (b' : B' ⟶ Spec (CommRingCat.of k))
    (u : A' ⟶ A) (v : B' ⟶ B) (w : Limits.pullback a' b' ⟶ Limits.pullback a b)
    (h₁ : w ≫ Limits.pullback.fst a b = Limits.pullback.fst a' b' ≫ u)
    (h₂ : w ≫ Limits.pullback.snd a b = Limits.pullback.snd a' b' ≫ v)
    (M : A.Modules) (N : B.Modules) :
    (tensorPullback w).obj (externalCupCoefficients a b M N) ≅
      externalCupCoefficients a' b' ((tensorPullback u).obj M)
        ((tensorPullback v).obj N) :=
  (Classical.choose (module_pullback_tensor w)) _ _ ≪≫
    tensorIso
      (scalarPullbackSquareIso w (Limits.pullback.fst a b) (Limits.pullback.fst a' b') u h₁ M)
      (scalarPullbackSquareIso w (Limits.pullback.snd a b) (Limits.pullback.snd a' b') v h₂ N)
end
end AlgebraicGeometry.Scheme.Modules
