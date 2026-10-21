/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # The constant/limit ringed sequence projection

Source: Stacks, sites-cohomology.tex, Tags 0940 and 06YY; Zheng, Construction 4.1,
printed p. 21 (blueprint: lem-pur-sequence-site-completion-projection).

The index `n : ℕ` denotes the positive level `n+1`. All systems retain their actual
horizontal section maps. The record below specifies the geometric morphism, its
ordinary module adjunction, and its simultaneous K-flat derived comparison.

## Main definitions

- `CategoryTheory.RingedToposMorphismOfUniverses`: the same ringed-topos fields
  as the recorded interface, with independent site universes.
- `completionSystemEquivalence`: the equivalence in the recorded systems realization.
- `SequenceSetProjection`: the constant/limit geometric morphism and ring map.
- `SequenceModuleRestriction`: exact scalar restriction with the actual transitions.
- `SequenceOrdinaryPullback`: the normalized simultaneous ordinary tensor model.
- `SequenceDerivedPullback`: the unbounded derived functor and representative comparison.
- `SequenceCompletionProjection`: the preceding compatible canonical data.

## Main statements

- `sequenceSiteCompletionProjection`: exactness of the canonical equivalence and
  existence of the compatible constant/limit projection data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe c d v w r
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Forgetting ring structure preserves sheaves in the selected coefficient universe.
Source: Stacks 03CZ (blueprint: lem-pur-sequence-site-completion-projection). -/
instance (priority := 1100) ringedToposRingForgetCompose
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) : J.HasSheafCompose (forget RingCat.{r}) :=
  (equivSmallModel.{r} C).hasSheafCompose J
    ((equivSmallModel.{r} C).inverse.inducedTopology J) (forget RingCat.{r})

attribute [-instance] ringedToposRingForgetCompose
scoped[CategoryTheory] attribute [instance 1100] ringedToposRingForgetCompose

/-- Forgetting abelian-group structure preserves sheaves in the coefficient universe.
Source: Stacks 03CZ (blueprint: lem-pur-sequence-site-completion-projection). -/
instance (priority := 1100) ringedToposAbelianForgetCompose
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) : J.HasSheafCompose (forget AddCommGrpCat.{r}) :=
  (equivSmallModel.{r} C).hasSheafCompose J
    ((equivSmallModel.{r} C).inverse.inducedTopology J) (forget AddCommGrpCat.{r})

attribute [-instance] ringedToposAbelianForgetCompose
scoped[CategoryTheory] attribute [instance 1100] ringedToposAbelianForgetCompose

/-- Forgetting commutativity preserves sheaves in the selected coefficient universe.
Source: Stacks 03CZ (blueprint: lem-pur-sequence-site-completion-projection). -/
instance (priority := 1100) ringedToposCommRingForgetCompose
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) :=
  (equivSmallModel.{r} C).hasSheafCompose J
    ((equivSmallModel.{r} C).inverse.inducedTopology J) (forget₂ CommRingCat.{r} RingCat.{r})

attribute [-instance] ringedToposCommRingForgetCompose
scoped[CategoryTheory] attribute [instance 1100] ringedToposCommRingForgetCompose

/-- A geometric morphism with a structural ring map and the induced direct image on modules.

Source: Stacks Project, Sites, Definition 00XA, and Modules on Sites, pushforward of modules
(blueprint: lem-pur-sequence-site-completion-projection).

The ring identities test every generalized element of the target topos. Left exactness
identifies the inverse image of products and the terminal object, so these are precisely
the identities for a morphism of ring objects. The last identity specifies addition and
scalar multiplication on the module direct image under the sheaf adjunction. It includes
zero by taking all three module elements zero. Thus the supplied module direct image is
the usual induced one, up to its displayed natural identification, not an arbitrary lift.
No exactness of the tensor module pullback or preservation of K-injectives is assumed. -/
structure RingedToposMorphismOfUniverses
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{w} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{r}) (B : Sheaf K RingCat.{r}) where
  /-- Inverse image of sheaves of sets. -/
  inverse : Sheaf K (Type r) ⥤ Sheaf J (Type r)
  /-- Direct image of sheaves of sets. -/
  direct : Sheaf J (Type r) ⥤ Sheaf K (Type r)
  /-- The geometric adjunction. -/
  adj : inverse ⊣ direct
  /-- Left exactness is required only for the underlying inverse image. -/
  leftExact : PreservesFiniteLimits inverse
  /-- The structural map, with ring structure specified by generalized elements below. -/
  ringMap : inverse.obj ((sheafCompose K (forget RingCat.{r})).obj B) ⟶
    (sheafCompose J (forget RingCat.{r})).obj A
  /-- Preservation of zero. -/
  ring_zero : ∀ (T : Sheaf K (Type r))
    (z : T ⟶ (sheafCompose K (forget RingCat.{r})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Zero.zero (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @Zero.zero (A.obj.obj U) inferInstance
  /-- Preservation of one. -/
  ring_one : ∀ (T : Sheaf K (Type r))
    (z : T ⟶ (sheafCompose K (forget RingCat.{r})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @One.one (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @One.one (A.obj.obj U) inferInstance
  /-- Preservation of add. -/
  ring_add : ∀ (T : Sheaf K (Type r))
    (x y z : T ⟶ (sheafCompose K (forget RingCat.{r})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Add.add (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)
  /-- Preservation of mul. -/
  ring_mul : ∀ (T : Sheaf K (Type r))
    (x y z : T ⟶ (sheafCompose K (forget RingCat.{r})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Mul.mul (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Mul.mul (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)
  /-- The induced direct image on module sheaves. -/
  modules : ringedSiteModules.{r} A ⥤ ringedSiteModules.{r} B
  /-- Additivity of the induced direct image. -/
  additive : modules.Additive
  /-- The underlying direct image of sheaves of sets, naturally in the module. -/
  underlying :
    modules ⋙ SheafOfModules.toSheaf B ⋙ sheafCompose K (forget AddCommGrpCat.{r}) ≅
      (SheafOfModules.toSheaf A ⋙ sheafCompose J (forget AddCommGrpCat.{r})) ⋙ direct
  /-- Addition and the structural-map-induced scalar action, under adjunction. -/
  module_linear : ∀ (M : ringedSiteModules.{r} A) (T : Sheaf K (Type r))
    (a : T ⟶ (sheafCompose K (forget RingCat.{r})).obj B)
    (x y z : T ⟶ (sheafCompose K (forget AddCommGrpCat.{r})).obj
      ((SheafOfModules.toSheaf B).obj (modules.obj M))),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add ((modules.obj M).val.obj U) inferInstance
        (@SMul.smul (B.obj.obj U) ((modules.obj M).val.obj U) inferInstance
          (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((adj.homEquiv T _).symm (z ≫ underlying.hom.app M)).hom.app U t =
        @Add.add (M.val.obj U) inferInstance
          (@SMul.smul (A.obj.obj U) (M.val.obj U) inferInstance
            (((inverse.map a) ≫ ringMap).hom.app U t)
            (((adj.homEquiv T _).symm (x ≫ underlying.hom.app M)).hom.app U t))
          (((adj.homEquiv T _).symm (y ≫ underlying.hom.app M)).hom.app U t)

attribute [instance] RingedToposMorphismOfUniverses.additive

end CategoryTheory

open scoped CategoryTheory

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  (B : ℕ → Sheaf J CommRingCat.{r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The sequence-site realization of strict systems used by the recorded model.
Source: Zheng, Construction 4.1, p. 21; Stacks 0940
(blueprint: lem-pur-sequence-site-completion-projection).

`def-coef-semilinear-system-models` defines `Systems` as these very module sheaves.
Thus the canonical equivalence in this realization is the identity on the actual
objects, horizontal restrictions, scalar actions and morphisms. -/
def completionSystemEquivalence :
    Mod.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J B τ) ≌
      Systems.{c, v, r} J B τ :=
  CategoryTheory.Equivalence.refl

/-- The underlying sheaf of sets of the existing module category.
Source: Stacks 03D1 and 03D6
(blueprint: lem-pur-sequence-site-completion-projection). -/
abbrev completionUnderlying (R : Sheaf J CommRingCat.{r}) :
    Mod.{c, v, r} J R ⥤ Sheaf J (Type r) :=
  SheafOfModules.toSheaf (ring.{c, v, r} J R) ⋙
    sheafCompose J (forget AddCommGrpCat.{r})

/-- The existing ordinary localization, with the recorded size instance explicit.
Source: Stacks 05RU and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
abbrev completionLocalization (R : Sheaf J CommRingCat.{r}) :
    CochainComplex (Mod.{c, v, r} J R) ℤ ⥤ D.{c, v, r} J R :=
  @DerivedCategory.Q (Mod.{c, v, r} J R) _ _ (hasDerived.{c, v, r} J R)

/-- A sheafified pure scalar-extension tensor, in the dependency's actual ordinary model.
Source: Stacks 03CZ and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
def completionScalarSection {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    (A : ScalarData.{c, v, r} φ) (M : Mod.{c, v, r} J R) (U : Cᵒᵖ)
    (a : S.obj.obj U) (x : M.val.obj U) : (A.model.E.obj M).val.obj U :=
  @SMul.smul ((ring.{c, v, r} J S).obj.obj U) ((A.model.E.obj M).val.obj U)
    ((A.model.E.obj M).val.obj U).isModule.toSMul a
      ((eqToHom (A.model.obj_eq M).symm).val.app U (extensionUnit.{c, v, r} φ M U x))

/-- The constant/limit geometric morphism with its canonical structural ring map.
The section equations fix the coordinate-wise adjunction and ring projection.
No condition on coefficient flatness or transition surjectivity is imposed.
Source: Stacks 0940, 03D6, 03D7 and 06YY; Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-sequence-site-completion-projection). -/
structure SequenceSetProjection (b : Cone (rings.{c, v, r} J B τ)) where
  /-- The ringed geometric morphism, with the induced action on module direct image. -/
  π : RingedToposMorphismOfUniverses
    (ring.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, r} J B τ))
    (ring.{c, v, r} J b.pt)
  /-- Inverse image is the actual constant sequence, on presheaves and their maps. -/
  inverseUnderlying : π.inverse ⋙ sheafToPresheaf (coefficientSequenceTopology J) (Type r) ≅
    sheafToPresheaf J (Type r) ⋙
      (Functor.whiskeringLeft (ℕ × C)ᵒᵖ Cᵒᵖ (Type r)).obj (CategoryTheory.Prod.snd ℕ C).op
  /-- The structural map has exactly the prescribed inverse-limit projections. -/
  ring_section : ∀ (n : ℕ) (U : Cᵒᵖ) (a : b.pt.obj.obj U),
    π.ringMap.hom.app (op (n, U.unop))
      (((inverseUnderlying.inv.app
        ((sheafCompose J (forget RingCat.{r})).obj (ring.{c, v, r} J b.pt))).app
          (op (n, U.unop))) a) = (b.π.app (op n)).hom.app U a
  /-- The actual set-sheaf tower obtained by restriction to vertical slices. -/
  setsTower : Sheaf (coefficientSequenceTopology J) (Type r) ⥤
    (ℕᵒᵖ ⥤ Sheaf J (Type r))
  /-- The vertical component is restriction, with the identity section identification. -/
  setsTower_obj : ∀ (F : Sheaf (coefficientSequenceTopology J) (Type r)) (n : ℕ),
    (setsTower.obj F).obj (op n) =
      ((Prod.sectR n C).sheafPushforwardContinuous (Type r)
        J (coefficientSequenceTopology J)).obj F
  /-- Horizontal maps remain the actual presheaf restrictions. -/
  setsTower_transition : ∀ (F : Sheaf (coefficientSequenceTopology J) (Type r))
    (m n : ℕ) (h : n ≤ m) (U : Cᵒᵖ),
    HEq (fun x ↦ (((setsTower.obj F).map (homOfLE h).op).hom.app U) x)
      (fun x : F.obj.obj (op (m, U.unop)) ↦
        F.obj.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
  /-- Morphisms are restricted without modifying their section maps. -/
  setsTower_map : ∀ {F G : Sheaf (coefficientSequenceTopology J) (Type r)}
    (f : F ⟶ G) (n : ℕ) (U : Cᵒᵖ),
    HEq (fun x ↦ (((setsTower.map f).app (op n)).hom.app U) x)
      (fun x : F.obj.obj (op (n, U.unop)) ↦ f.hom.app (op (n, U.unop)) x)
  /-- Direct image is inverse limit in sheaves of sets. -/
  directLimit : π.direct ≅ setsTower ⋙ lim
  /-- The geometric adjunction is the coordinate-wise constant/limit correspondence. -/
  adjunction_section : ∀ (H : Sheaf J (Type r))
    (F : Sheaf (coefficientSequenceTopology J) (Type r)) (a : π.inverse.obj H ⟶ F)
    (n : ℕ) (U : Cᵒᵖ) (x : H.obj.obj U),
    (eqToHom (setsTower_obj F n)).hom.app U
      ((limit.π (setsTower.obj F) (op n)).hom.app U
        ((directLimit.hom.app F).hom.app U (((π.adj.homEquiv H F) a).hom.app U x))) =
      a.hom.app (op (n, U.unop)) ((inverseUnderlying.inv.app H).app (op (n, U.unop)) x)

/-- Exact restriction to the limit ring, with actual transitions.
Source: Stacks 0940, 03D7 and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
structure SequenceModuleRestriction (b : Cone (rings.{c, v, r} J B τ))
    (g : SequenceSetProjection.{c, v, r} J B τ b) where
  /-- Restrict each component along the actual projection rho_n. -/
  restriction : Systems.{c, v, r} J B τ ⥤ (ℕᵒᵖ ⥤ Mod.{c, v, r} J b.pt)
  /-- Its object formula uses the existing evaluation and scalar restriction. -/
  restriction_obj : ∀ (M : Systems.{c, v, r} J B τ) (n : ℕ),
    (restriction.obj M).obj (op n) = (res.{c, v, r} (b.π.app (op n))).obj
      ((evaluation.{c, v, r} J B τ n).obj M)
  /-- The underlying additive transitions are unchanged. -/
  restriction_transition : ∀ (M : Systems.{c, v, r} J B τ)
    (m n : ℕ) (h : n ≤ m) (U : Cᵒᵖ),
    HEq (fun x ↦ (((restriction.obj M).map (homOfLE h).op).val.app U) x)
      (fun x : M.val.obj (op (m, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
  /-- System morphisms keep their original component maps. -/
  restriction_map : ∀ {M N : Systems.{c, v, r} J B τ} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
    HEq (fun x ↦ (((restriction.map f).app (op n)).val.app U) x)
      (fun x : M.val.obj (op (n, U.unop)) ↦ f.val.app (op (n, U.unop)) x)
  /-- Additivity and exactness, without a surjectivity condition on transitions. -/
  restriction_additive : restriction.Additive
  /-- Preservation of finite limits. -/
  restriction_limits : PreservesFiniteLimits restriction
  /-- Preservation of finite colimits. -/
  restriction_colimits : PreservesFiniteColimits restriction
  /-- The induced module direct image is the inverse limit of the restricted system. -/
  moduleDirect : g.π.modules ≅ restriction ⋙ lim
  /-- The module-limit identification is the coordinate map of the underlying set limit. -/
  moduleDirect_section : ∀ (M : Systems.{c, v, r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (x : (g.π.modules.obj M).val.obj U),
    (eqToHom (restriction_obj M n)).val.app U
      ((limit.π (restriction.obj M) (op n)).val.app U
        ((moduleDirect.hom.app M).val.app U x)) =
      (eqToHom (g.setsTower_obj
        ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, r} J B τ)).obj M) n)).hom.app U
        ((limit.π (g.setsTower.obj
          ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
            (systemRing.{c, v, r} J B τ)).obj M)) (op n)).hom.app U
          ((g.directLimit.hom.app
            ((completionUnderlying.{c, v, r} (coefficientSequenceTopology J)
              (systemRing.{c, v, r} J B τ)).obj M)).hom.app U
            ((g.π.underlying.hom.app M).hom.app U x)))

/-- The normalized simultaneous ordinary pullback.
Source: Stacks 0940, 03D7 and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
structure SequenceOrdinaryPullback (b : Cone (rings.{c, v, r} J B τ))
    (g : SequenceSetProjection.{c, v, r} J B τ b)
    (u : SequenceModuleRestriction.{c, v, r} J B τ b g) where
  /-- Ordinary ringed module pullback. -/
  extension : Mod.{c, v, r} J b.pt ⥤ Systems.{c, v, r} J B τ
  /-- Additivity of ordinary pullback. -/
  [extension_additive : extension.Additive]
  /-- This identifies extension with pi-star, by its defining module adjunction. -/
  moduleAdjunction : extension ⊣ g.π.modules
  /-- The recorded derived scalar-extension model at every actual rho_n. -/
  level : ∀ n : ℕ, ScalarData.{c, v, r} (b.π.app (op n))
  /-- The ordinary pullback evaluates to the sheafified change of rings. -/
  ordinaryEvaluation : ∀ n : ℕ,
    extension ⋙ evaluation.{c, v, r} J B τ n ≅ (level n).model.E
  /-- The comparison uses the ordinary tensor-insertion unit, fixing its normalization. -/
  ordinary_unit : ∀ (M : Mod.{c, v, r} J b.pt) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U),
    ((ordinaryEvaluation n).hom.app M).val.app U
      ((eqToHom (u.restriction_obj (extension.obj M) n)).val.app U
        ((limit.π (u.restriction.obj (extension.obj M)) (op n)).val.app U
          ((u.moduleDirect.hom.app (extension.obj M)).val.app U
            ((moduleAdjunction.unit.app M).val.app U x)))) =
      completionScalarSection.{c, v, r} J (b.π.app (op n)) (level n) M U 1 x
  /-- The one strict pullback system has transition 1 tensor q on pure tensors. -/
  ordinary_transition : ∀ (M : Mod.{c, v, r} J b.pt) (m n : ℕ) (h : n ≤ m)
    (U : Cᵒᵖ) (a : (B m).obj.obj U) (x : M.val.obj U),
    ((ordinaryEvaluation n).hom.app M).val.app U
      (((transition.{c, v, r} J B τ h).app (extension.obj M)).val.app U
        (((ordinaryEvaluation m).inv.app M).val.app U
          (completionScalarSection.{c, v, r} J (b.π.app (op m)) (level m) M U a x))) =
      completionScalarSection.{c, v, r} J (b.π.app (op n)) (level n) M U
        ((coefficientMap.{c, v, r} J B τ h).hom.app U a) x

attribute [instance] SequenceOrdinaryPullback.extension_additive

/-- The normalized simultaneous unbounded derived pullback.
Source: Stacks 0940, 03D7 and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
structure SequenceDerivedPullback (b : Cone (rings.{c, v, r} J B τ))
    (g : SequenceSetProjection.{c, v, r} J B τ b)
    (u : SequenceModuleRestriction.{c, v, r} J B τ b g)
    (p : SequenceOrdinaryPullback.{c, v, r} J B τ b g u) where
  /-- The single unbounded derived pullback, before evaluating at any level. -/
  derived : D.{c, v, r} J b.pt ⥤ DS.{c, v, r} J B τ
  /-- The natural left-derived comparison on all complexes. -/
  ε : completionLocalization.{c, v, r} J b.pt ⋙ derived ⟶
    p.extension.mapHomologicalComplex (.up ℤ) ⋙
      completionLocalization.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, r} J B τ)
  /-- The universal left-derived property of pi-star. -/
  universal : derived.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ))
  /-- Triangulated exactness on ordinary unbounded derived categories. -/
  triangulated : ∃ (_ : derived.CommShift ℤ), derived.IsTriangulated
  /-- The comparison is invertible on each flat-term K-flat complex, simultaneously. -/
  computes : ∀ (P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, r} (R := b.pt) P →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, r, r} (R := b.pt) (P.X i)) →
      IsIso (ε.app P)
  /-- Invariance of the entire strict complex under a quasi-isomorphism of resolutions. -/
  preserves : ∀ {P Q : CochainComplex (Mod.{c, v, r} J b.pt) ℤ} (f : P ⟶ Q),
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, r} (R := b.pt) P →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, r, r} (R := b.pt) (P.X i)) →
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, r} (R := b.pt) Q →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, r, r} (R := b.pt) (Q.X i)) →
    QuasiIso f → QuasiIso ((p.extension.mapHomologicalComplex (.up ℤ)).map f)
  /-- Evaluation comparison on all derived morphisms, not just object values. -/
  derivedEvaluation : ∀ n : ℕ, derived ⋙ e.{c, v, r} J B τ n ≅ (p.level n).T
  /-- Termwise form of the ordinary evaluation comparison. -/
  complexEvaluation : ∀ n : ℕ,
    p.extension.mapHomologicalComplex (.up ℤ) ⋙
      (evaluation.{c, v, r} J B τ n).mapHomologicalComplex (.up ℤ) ≅
        (p.level n).model.E.mapHomologicalComplex (.up ℤ)
  /-- The complex comparison has exactly the ordinary comparison in every degree. -/
  complexEvaluation_f : ∀ (n : ℕ) (P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ) (i : ℤ),
    ((complexEvaluation n).hom.app P).f i = (p.ordinaryEvaluation n).hom.app (P.X i)
  /-- The derived comparison is the localization of the specified simultaneous model. -/
  representative_square : ∀ (n : ℕ) (P : CochainComplex (Mod.{c, v, r} J b.pt) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, r} (R := b.pt) P)
    (_flatP : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, r, r} (R := b.pt) (P.X i)),
    (derivedEvaluation n).hom.app ((completionLocalization.{c, v, r} J b.pt).obj P) ≫
        (p.level n).model.ε.app P =
      (e.{c, v, r} J B τ n).map (ε.app P) ≫
        (Functor.mapDerivedCategoryFactors (evaluation.{c, v, r} J B τ n)).hom.app
          ((p.extension.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (completionLocalization.{c, v, r} J (B n)).map ((complexEvaluation n).hom.app P)

/-- The constant/limit projection with its ordinary and derived module models.
Source: Stacks 0940, 03D7 and 06YY
(blueprint: lem-pur-sequence-site-completion-projection). -/
structure SequenceCompletionProjection (b : Cone (rings.{c, v, r} J B τ)) where
  /-- Constant/limit geometric morphism and the projection ring map. -/
  geometric : SequenceSetProjection.{c, v, r} J B τ b
  /-- The exact functor retaining all additive transitions. -/
  restriction : SequenceModuleRestriction.{c, v, r} J B τ b geometric
  /-- One ordinary strict extension system, normalized on sheafified tensors. -/
  ordinary : SequenceOrdinaryPullback.{c, v, r} J B τ b geometric restriction
  /-- One derived functor, normalized before evaluation at any level. -/
  derived : SequenceDerivedPullback.{c, v, r} J B τ b geometric restriction ordinary

/-- The canonical sequence-site equivalence is exact, and the limit cone defines the
constant/limit ringed projection with the simultaneous K-flat reduction model.
Source: Stacks 0940, 06YY, 03D6, 03D7 and 03DB; Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-sequence-site-completion-projection).

Proof:
1. In the `def-coef-semilinear-system-models` realization, `Systems` is the very
   category of sequence-site modules, so `completionSystemEquivalence` retains all
   section data. `lem-pur-system-ringed-sequence-site` explains its identification
   with explicit strict systems by vertical restriction and horizontal transitions.
   The componentwise abelian structure of `def-pur-system-level-left-extension-basic`
   and equivalence exactness of `lem-weil-pbc-equivalence-injective-resolutions`
   give exactness.
2. Factor every product-site arrow into a vertical and a horizontal arrow. The sheaf
   equalizer at a fixed index is the base-site sheaf equalizer, giving `setsTower`.
3. Constant sequences are left adjoint to sectionwise inverse limit. The coordinate
   formulas are inverse and natural. `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`
   makes the limit a sheaf and shows constant sequences preserve finite limits.
4. The cone equations give the ring map with components rho_n. The induced module
   direct image has action b(x_n)=(rho_n(b)x_n); sectionwise module limits identify it
   with the inverse limit of actual scalar restrictions.
5. Apply `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` at every rho_n and on
   the sequence site. Its pure-tensor correspondence identifies ordinary pullback
   with the system (M tensor_B B_n), normalized by x mapping to 1 tensor x.
6. Apply `lem-weil-pbc-ringed-topoi-derived-pullback`, transporting through a small
   model in the coefficient universe if needed. `lem-pc-kflat-resolution` gives one
   flat-term K-flat P over B before any evaluation. The left-derived counit is
   invertible on P and sends quasi-isomorphisms between such P to quasi-isomorphisms.
   For p:P->K the representative is inv(derived(Q(p))) followed by epsilon_P.
7. Exact evaluation localizes termwise. `lem-pur-derived-change-of-rings` identifies
   its value with derived scalar extension, with the displayed representative square.
   Chain maps act by a tensor 1; compatibility with homotopies and inverted
   quasi-isomorphisms gives naturality on all localized morphisms.
8. For l>=m>=n the two ordinary transition composites send x tensor a to
   x tensor q_mn(q_lm(a))=x tensor q_ln(a). Sheafified pure tensors determine
   the maps. Equality indices give identities. Thus the single strict complex already
   has composing quotient maps before localization, including its differentials.
9. Restriction along rho_n keeps the additive transition: semilinearity and
   q_mn rho_m=rho_n make it B-linear. Exactness of scalar restriction and componentwise
   exactness in the source and tower category make this functor additive and exact. -/
theorem sequenceSiteCompletionProjection (b : Cone (rings.{c, v, r} J B τ))
    (_hb : IsLimit b) :
    PreservesFiniteLimits
      (completionSystemEquivalence.{c, v, r} J B τ).inverse ∧
    PreservesFiniteColimits
      (completionSystemEquivalence.{c, v, r} J B τ).inverse ∧
    Nonempty (SequenceCompletionProjection.{c, v, r} J B τ b) := by
  sorry

end WeilConjectures.SemilinearSections
