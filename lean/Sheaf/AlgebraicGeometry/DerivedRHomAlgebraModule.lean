/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategoryQCoherentAlgebra
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived internal Hom with its algebra module structure

Source: Stacks Project, Duality for Schemes, Section 48.11, Tags 0BUZ, 0BV0, 0BV1
(blueprint: def-pc-derived-rhom-algebra-module).

The natural algebra action is precomposition with multiplication. The derived functor
is the localization of termwise Hom after a functorial, degreewise injective K-injective
resolution. Its underlying object is the shared derived internal Hom.
-/

@[expose] public section

universe u w wB

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry

variable (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf)

/-- The section carrier of the shared internal Hom, on an open U.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable abbrev sheafAlgebraHomSections (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (U : (Opens Y)ᵒᵖ) :=
  (PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).obj U

/-- Multiplication by a restricted algebra section is additive and O-linear.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Distribute multiplication over addition. The O action is multiplication by the structure
map; commutativity and associativity move it past b. -/
theorem sheafAlgebraMul_linear (U : Opens Y) (b : B.right.obj.obj (op U))
    (W : (Over U)ᵒᵖ) :
    (∀ x y : B.toModule.val.obj (op W.unop.left),
      B.right.obj.map W.unop.hom.op b *
        (@id (B.right.obj.obj (op W.unop.left)) (x + y)) =
        B.right.obj.map W.unop.hom.op b *
          (@id (B.right.obj.obj (op W.unop.left)) x) + B.right.obj.map W.unop.hom.op b *
          (@id (B.right.obj.obj (op W.unop.left)) y)) ∧
    (∀ (r : Y.sheaf.obj.obj (op W.unop.left))
      (x : B.toModule.val.obj (op W.unop.left)),
      B.right.obj.map W.unop.hom.op b *
        (@id (B.right.obj.obj (op W.unop.left)) (r • x)) =
        r • (@id (B.toModule.val.obj (op W.unop.left))
          (B.right.obj.map W.unop.hom.op b *
            (@id (B.right.obj.obj (op W.unop.left)) x)))) := by
  dsimp [Scheme.CommAlgebraSheaf.toModule, SheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalars, PresheafOfModules.restrictScalarsObj,
    SheafOfModules.unit, PresheafOfModules.unit, ModuleCat.restrictScalars,
    ModuleCat.RestrictScalars.obj']
  constructor
  · intro x y
    change _ * (x + y : B.right.obj.obj (op W.unop.left)) = _
    exact mul_add _ _ _
  · intro r x
    let r' : B.right.obj.obj (op W.unop.left) := (B.hom.hom.app _).hom r
    let x' : B.right.obj.obj (op W.unop.left) := x
    let b' : B.right.obj.obj (op W.unop.left) := B.right.obj.map W.unop.hom.op b
    change b' * (r' * x') = r' * (b' * x')
    exact mul_left_comm _ _ _

/-- The component of multiplication by b on B restricted to U.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraMulApp (U : Opens Y) (b : B.right.obj.obj (op U))
    (W : (Over U)ᵒᵖ) :
    ((PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val).obj W ⟶
      ((PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val).obj W :=
  ModuleCat.ofHom
    { toFun := fun x ↦ B.right.obj.map W.unop.hom.op b *
          (@id (B.right.obj.obj (op W.unop.left)) x)
      map_add' := (sheafAlgebraMul_linear Y B U b W).1
      map_smul' := (sheafAlgebraMul_linear Y B U b W).2 }

/-- Multiplication components commute with restrictions.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Restriction is a ring map, so preserves products; functoriality identifies the two
restrictions of b. -/
theorem sheafAlgebraMul_naturality (U : Opens Y) (b : B.right.obj.obj (op U))
    {W V : (Over U)ᵒᵖ} (f : W ⟶ V) :
    ((PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val).map f ≫
      (ModuleCat.restrictScalars
        (((Over.forget U).op ⋙ Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map f).hom).map
        (sheafAlgebraMulApp Y B U b V) =
      sheafAlgebraMulApp Y B U b W ≫
        ((PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change B.right.obj.map V.unop.hom.op b *
    B.right.obj.map f.unop.left.op (@id (B.right.obj.obj (op W.unop.left)) x) =
    B.right.obj.map f.unop.left.op
      (B.right.obj.map W.unop.hom.op b * (@id (B.right.obj.obj (op W.unop.left)) x))
  rw [map_mul]
  have hb : B.right.obj.map f.unop.left.op (B.right.obj.map W.unop.hom.op b) =
      B.right.obj.map V.unop.hom.op b := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, Over.w]
  rw [hb]

/-- Multiplication by b on the first argument, on every open over U.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraMul (U : Opens Y) (b : B.right.obj.obj (op U)) :
    (PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val ⟶
      (PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val where
  app := sheafAlgebraMulApp Y B U b
  naturality := sheafAlgebraMul_naturality Y B U b

/-- The B(U) action on Hom is precomposition with multiplication by b.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable instance sheafAlgebraHomSMul (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (U : (Opens Y)ᵒᵖ) :
    SMul (B.right.obj.obj U) (sheafAlgebraHomSections Y B F U) where
  smul b φ := sheafAlgebraMul Y B U.unop b ≫ φ

/-- On every open over U the B-action is precomposition with multiplication.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Expand sheafAlgebraHomSMul, the composition of presheaf morphisms, and
sheafAlgebraMulApp. The composite evaluates φ at the product of the restriction of b
with x, exactly as asserted. -/
theorem sheafAlgebraHom_smul (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (U : (Opens Y)ᵒᵖ)
    (b : B.right.obj.obj U) (φ : sheafAlgebraHomSections Y B F U)
    (W : (Over U.unop)ᵒᵖ) (x : B.toModule.val.obj (op W.unop.left)) :
    (b • φ).app W x = φ.app W
      (B.right.obj.map W.unop.hom.op b * (@id (B.right.obj.obj (op W.unop.left)) x)) := by
  rfl

/-- The explicit action satisfies the module axioms.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Evaluate at every W and x. The unit and product axioms follow from commutative
multiplication in B; the four distributive and zero axioms follow from distributivity in B and
additivity of φ. -/
theorem sheafAlgebraHom_module_axioms (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (U : (Opens Y)ᵒᵖ) :
    (∀ φ : sheafAlgebraHomSections Y B F U, (1 : B.right.obj.obj U) • φ = φ) ∧
    (∀ (b c : B.right.obj.obj U) (φ : sheafAlgebraHomSections Y B F U),
      (b * c) • φ = b • c • φ) ∧
    (∀ (b : B.right.obj.obj U) (φ ψ : sheafAlgebraHomSections Y B F U),
      b • (φ + ψ) = b • φ + b • ψ) ∧
    (∀ b : B.right.obj.obj U, b • (0 : sheafAlgebraHomSections Y B F U) = 0) ∧
    (∀ (b c : B.right.obj.obj U) (φ : sheafAlgebraHomSections Y B F U),
      (b + c) • φ = b • φ + c • φ) ∧
    (∀ φ : sheafAlgebraHomSections Y B F U, (0 : B.right.obj.obj U) • φ = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [sheafAlgebraHom_smul, map_one, one_mul]
    rfl
  · intro b c φ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [sheafAlgebraHom_smul, map_mul, mul_assoc, id_eq]
    exact congrArg (fun z : B.right.obj.obj (op W.unop.left) ↦ φ.app W z)
      (mul_left_comm _ _ _)
  · intro b φ ψ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · intro b
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · intro b c φ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [sheafAlgebraHom_smul, map_add, add_mul, map_add]
    rfl
  · intro φ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [sheafAlgebraHom_smul, map_zero, zero_mul]
    rfl

/-- The B(U)-module structure with the explicitly defined scalar action.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable instance sheafAlgebraHomModule (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (U : (Opens Y)ᵒᵖ) :
    Module (B.right.obj.obj U) (sheafAlgebraHomSections Y B F U) where
  smul := (sheafAlgebraHomSMul Y B F U).smul
  one_smul := (sheafAlgebraHom_module_axioms Y B F U).1
  mul_smul := (sheafAlgebraHom_module_axioms Y B F U).2.1
  smul_add := (sheafAlgebraHom_module_axioms Y B F U).2.2.1
  smul_zero := (sheafAlgebraHom_module_axioms Y B F U).2.2.2.1
  add_smul := (sheafAlgebraHom_module_axioms Y B F U).2.2.2.2.1
  zero_smul := (sheafAlgebraHom_module_axioms Y B F U).2.2.2.2.2

/-- The existing Hom restrictions are semilinear for the B action.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The restriction of a morphism over U is its pullback to opens over V. The multiplier is the
restriction of b; functoriality of B restrictions identifies these actions. -/
theorem sheafAlgebraHom_restrict_smul (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))
    {U V : (Opens Y)ᵒᵖ} (f : U ⟶ V) (b : B.right.obj.obj U)
    (φ : sheafAlgebraHomSections Y B F U) :
    (PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).presheaf.map f (b • φ) =
      @SMul.smul _ (sheafAlgebraHomSections Y B F V)
        (sheafAlgebraHomSMul Y B F V) (B.right.obj.map f b)
        ((PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).presheaf.map f φ) := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let φ' := PresheafOfModules.restrictOverMap f.unop φ
  let b' : B.right.obj.obj (op W.unop.left) :=
    B.right.obj.map ((Over.map f.unop).obj W.unop).hom.op b
  let c' : B.right.obj.obj (op W.unop.left) :=
    B.right.obj.map W.unop.hom.op (B.right.obj.map f b)
  let x' : B.right.obj.obj (op W.unop.left) := x
  change φ'.app W (b' * x') = φ'.app W (c' * x')
  have hb : b' = c' := PresheafOfModules.overSections_coe_map_obj f.unop b W
  rw [hb]

/-- The Hom sheaf with B-module sections and the existing Hom restriction maps.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraHomObj (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj B.right) where
  val :=
    letI (U : (Opens Y)ᵒᵖ) :
        Module ((B.right.obj ⋙ forget₂ CommRingCat RingCat).obj U)
          ((PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).presheaf.obj U) :=
      sheafAlgebraHomModule Y B F U
    PresheafOfModules.ofPresheaf
    (R := B.right.obj ⋙ forget₂ CommRingCat RingCat)
    (PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).presheaf
    (fun {U V} f b φ ↦ sheafAlgebraHom_restrict_smul Y B F (U := U) (V := V) f b φ)
  isSheaf := (SheafOfModules.homObj.{u, u, u, u} (R := Y.sheaf) B.toModule F).isSheaf

/-- Postcomposition commutes with the B action.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Evaluate at W and x; both sides are g applied to φ evaluated at the product of the
restriction of b with x. -/
theorem sheafAlgebraHom_map_smul {F G : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)} (g : F ⟶ G)
    (U : (Opens Y)ᵒᵖ) (b : B.right.obj.obj U)
    (φ : sheafAlgebraHomSections Y B F U) :
    (PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val).app U (b • φ) =
      @SMul.smul _ (sheafAlgebraHomSections Y B G U)
        (sheafAlgebraHomSMul Y B G U) b
        ((PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val).app U φ) := by
  simp only [PresheafOfModules.homObjMap_app_apply]
  exact (Category.assoc _ _ _).symm

/-- The functor map is the existing postcomposition map with its B-linearity proof.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraHomMap {F G : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)} (g : F ⟶ G) :
    sheafAlgebraHomObj Y B F ⟶ sheafAlgebraHomObj Y B G where
  val := PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf
      (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map
      (PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val))
    (sheafAlgebraHom_map_smul Y B g)

/-- Postcomposition preserves identity and composition.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The underlying maps are homObjMap; its identity and composition laws imply the equalities
by extensionality of module morphisms. -/
theorem sheafAlgebraHom_functor_axioms :
    (∀ F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf),
      sheafAlgebraHomMap Y B (𝟙 F) = 𝟙 (sheafAlgebraHomObj Y B F)) ∧
    (∀ (F G H : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (f : F ⟶ G) (g : G ⟶ H),
      sheafAlgebraHomMap Y B (f ≫ g) =
        sheafAlgebraHomMap Y B f ≫ sheafAlgebraHomMap Y B g) := by
  constructor
  · intro F
    ext U φ
    change (PresheafOfModules.homObjMap (𝟙 B.toModule.val) (𝟙 F.val)).app U φ = φ
    rw [PresheafOfModules.homObjMap_id]
    rfl
  · intro F G H f g
    ext U φ
    change (PresheafOfModules.homObjMap (𝟙 B.toModule.val) (f.val ≫ g.val)).app U φ =
      (PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val).app U
        ((PresheafOfModules.homObjMap (𝟙 B.toModule.val) f.val).app U φ)
    simp only [PresheafOfModules.homObjMap_app_apply]
    simp

/-- The explicit algebra-valued Hom functor: sections are Hom and maps postcompose.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraHom : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf) ⥤ SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj B.right) where
  obj := sheafAlgebraHomObj Y B
  map := sheafAlgebraHomMap Y B
  map_id := (sheafAlgebraHom_functor_axioms Y B).1
  map_comp := fun f g ↦ (sheafAlgebraHom_functor_axioms Y B).2 _ _ _ f g

/-- The explicit Hom functor is additive.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: On every section postcomposition by f + g is the sum of postcomposition by f and g.
Extensionality gives additivity. -/
theorem sheafAlgebraHom_additive : (sheafAlgebraHom Y B).Additive := by
  constructor
  intro F G f g
  ext U φ
  change (PresheafOfModules.homObjMap (𝟙 B.toModule.val) (f.val + g.val)).app U φ =
    (PresheafOfModules.homObjMap (𝟙 B.toModule.val) f.val).app U φ +
      (PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val).app U φ
  simp only [PresheafOfModules.homObjMap_app_apply]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

attribute [instance] sheafAlgebraHom_additive

/-- The identity on Hom sections is O-linear after restriction of scalars.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The structure map sends r to its multiplication action on B. O-linearity of φ moves that
multiplier to the output, giving the existing Hom scalar action. -/
theorem sheafAlgebraHom_underlying_linear (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))
    (U : (Opens Y)ᵒᵖ) (r : Y.sheaf.obj.obj U)
    (φ : sheafAlgebraHomSections Y B F U) :
    (B.hom.hom.app U).hom r • φ =
      r • (φ : (PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).obj U) := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [sheafAlgebraHom_smul]
  change φ.app W (B.right.obj.map W.unop.hom.op ((B.hom.hom.app U).hom r) *
      (@id (B.right.obj.obj (op W.unop.left)) x)) =
    (Y.sheaf.obj.map W.unop.hom.op r) • φ.app W x
  have hr := congrArg (fun k ↦ k r) (congrArg CommRingCat.Hom.hom
    (B.hom.hom.naturality W.unop.hom.op))
  dsimp at hr
  rw [← hr]
  exact (φ.app W).hom.map_smul (Y.sheaf.obj.map W.unop.hom.op r) x

/-- Restricting the explicitly constructed Hom functor gives the existing O-module Hom.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The carriers, additive groups, restriction functions and postcomposition functions
are the same by construction. The O scalar action is also the same: O-linearity of each
Hom section identifies precomposition by multiplication by r with multiplication of its
output by r, as in sheafAlgebraHom_underlying_linear. Extensionality of Module structures,
module morphisms and functors, and proof irrelevance of their axioms, give equality. -/
theorem sheafAlgebraHomUnderlying_eq :
    sheafAlgebraHom Y B ⋙ SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom) =
      (SheafOfModules.homFunctor Y.sheaf).obj (op B.toModule) := by
  sorry

/-- The identity comparison, transported along equality of the constructed underlying
functor with the shared Hom functor. No Hom object, map or isomorphism is chosen.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraHomUnderlyingIso :
    sheafAlgebraHom Y B ⋙ SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom) ≅
      (SheafOfModules.homFunctor Y.sheaf).obj (op B.toModule) :=
  eqToIso (sheafAlgebraHomUnderlying_eq Y B)

/-- The functorial K-injective resolution in the Grothendieck abelian category of
O_Y-modules, using the canonical factorization construction.
Source: Stacks Project, Cohomology on Sites, Section 07A5, Theorem 079P
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraHomResolution :
    CochainComplex (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) ℤ :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) :=
    SheafOfModules.isGrothendieckAbelian _
  CochainComplex.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))

/-- The canonical natural resolution map into the preceding functor.
Source: Stacks Project, Cohomology on Sites, Section 07A5, Theorem 079P
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def toSheafAlgebraHomResolution :
    𝟭 (CochainComplex (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) ℤ) ⟶
      sheafAlgebraHomResolution Y :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) :=
    SheafOfModules.isGrothendieckAbelian _
  CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))

variable (hB : B.toModule.IsQuasicoherent)
  [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))]
  [HasDerivedCategory.{wB} (SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj B.right))]

/-- The resolution followed by termwise algebra-valued Hom inverts quasi-isomorphisms
after localization in D(B).
Source: Stacks Project, Section 48.11, Tag 0BV0; Cohomology on Sites, Lemma 0A95
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Naturality of M → I(M) and two-out-of-three make I(s) a quasi-isomorphism between
K-injective complexes for each quasi-isomorphism s. Apply quasiIso_homComplex_map with
both first complexes B[0] and the identity between them. The underlying termwise Hom
complex is Hom^•(B[0], I(M)); thus its map is a quasi-isomorphism. Quasi-isomorphisms of
B-modules are detected on underlying abelian sheaves, so Q_B inverts this map. -/
theorem sheafAlgebraHomResolution_inverts :
    (HomologicalComplex.quasiIso (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))
      (ComplexShape.up ℤ)).IsInvertedBy
      (sheafAlgebraHomResolution Y ⋙
        (sheafAlgebraHom Y B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) := by
  sorry

/-- Derived internal Hom with the natural B-module structure: localize termwise
Hom(B, I(M)), where I is the fixed degreewise injective K-injective resolution.
Source: Stacks Project, Section 48.11, Tags 0BV0 and 0BV1
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def derivedRHomAlgebraModule
    (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) (hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))]
    [HasDerivedCategory.{wB} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right))] :
    DerivedCategory (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj Y.sheaf)) ⥤
      sheafAlgebraDerivedCategory Y B hB :=
  Localization.lift
    (sheafAlgebraHomResolution Y ⋙
      (sheafAlgebraHom Y B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (sheafAlgebraHomResolution_inverts Y B) DerivedCategory.Q

/-- Computation on a representative, naturally in the entire complex M.
Source: Stacks Project, Section 48.11, Tag 0BV0
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The localization factorization isomorphism Localization.fac identifies Q followed
by the lifted functor with its defining functor M ↦ Q_B Hom(B, I(M)). -/
theorem derivedRHomAlgebraModule_comparison :
    Nonempty (DerivedCategory.Q ⋙ derivedRHomAlgebraModule Y B hB ≅
      sheafAlgebraHomResolution Y ⋙
        (sheafAlgebraHom Y B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) := by
  exact ⟨Localization.fac _ (sheafAlgebraHomResolution_inverts Y B) DerivedCategory.Q⟩

set_option linter.unusedSectionVars false in
/-- Restriction of algebra scalars preserves finite limits.
Source: Stacks Project, Section 48.11, Tag 0BV1
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The underlying abelian sheaf is unchanged. Finite limits carry the induced B action;
forgetting it gives the same universal cone in O-modules. -/
theorem sheafAlgebraRestrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)) := by
  let O := (sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat RingCat)).obj Y.sheaf
  let A := (sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat RingCat)).obj B.right
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).map B.hom)
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf O) := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf A)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf O)

attribute [instance] sheafAlgebraRestrictScalars_preservesFiniteLimits

set_option linter.unusedSectionVars false in
/-- Restriction of algebra scalars preserves finite colimits.
Source: Stacks Project, Section 48.11, Tag 0BV1
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The underlying abelian sheaf is unchanged. Finite colimits carry the induced B action;
forgetting it gives the same universal cone in O-modules. -/
theorem sheafAlgebraRestrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)) := by
  let O := (sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat RingCat)).obj Y.sheaf
  let A := (sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat RingCat)).obj B.right
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).map B.hom)
  have : PreservesFiniteColimits (SheafOfModules.toSheaf O) := inferInstance
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf O) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf A)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf O)

attribute [instance] sheafAlgebraRestrictScalars_preservesFiniteColimits

/-- Forgetting the algebra action recovers the recorded derived internal Hom, naturally
in K. The derived restriction of scalars is the exact functor mapDerivedCategory; the Hom
computation uses the same I as the definition above.
Source: Stacks Project, Section 48.11, Tag 0BV1
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Restriction of scalars is exact on sheaves of modules since kernels, images and
cokernels have the same underlying abelian sheaves. Its termwise functor therefore
induces mapDerivedCategory with its canonical factorization isomorphism.
Forgetting Hom(B, I(M)) gives
Hom^•(B[0], I(M)). Apply derivedInternalHom_comparison with this same resolution and
specialize its first variable to B[0]. Both resulting functors descend through Q;
full faithfulness of precomposition by a localization descends the natural isomorphism. -/
theorem derivedRHomAlgebraModule_underlying :
    Nonempty (derivedRHomAlgebraModule Y B hB ⋙
      (SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)).mapDerivedCategory ≅
        ((Functor.const (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)))).obj
          (op (DerivedCategory.Q.obj
            ((HomologicalComplex.single (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))
              (ComplexShape.up ℤ) 0).obj B.toModule)))).prod' (𝟭 _) ⋙
          derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf) := by
  sorry

end AlgebraicGeometry
