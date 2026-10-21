/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Sheaf.Paper.RingedTopoiTensorSections
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import all Sheaf.CategoryTheory.GeometricModuleTransport
import all Sheaf.CategoryTheory.GeometricModuleConstruction
import all Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction

/-! # Geometric two-isomorphisms and scalar balanced pairings

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL, balanced-pairing proof;
Sites, Tags 0H7J and 00YV (blueprint: lem-sfb-geometric-two-iso-scalar-pairing).

The small sites, coefficients and module sections share the explicitly bound universe.
The auxiliary presentations record precisely the stipulated normalized ordinary maps.
Finite expressions include the empty path and the iterated scalar/pullback maps themselves.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace CategoryTheory.GeometricScalar
open SheafOfModules SheafOfModules.RingedTensor

/-- The existing module category over the actual constant commutative ring sheaf.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
abbrev Modules {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : CommRingCat.{u}) [HasWeakSheafify J CommRingCat.{u}] :=
  SheafOfModules.{u} (ringSheaf ((constantSheaf J CommRingCat.{u}).obj A))

/-- The existing forgetful functor, with the constant coefficient displayed.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
abbrev underlyingModules {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : CommRingCat.{u}) [HasWeakSheafify J CommRingCat.{u}] :=
  underlying ((constantSheaf J CommRingCat.{u}).obj A)

/-- The underlying sheaf of the constant coefficient ring, using constant sheafification.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
abbrev coefficient {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : CommRingCat.{u}) [HasWeakSheafify J CommRingCat.{u}] :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
    ((constantSheaf J CommRingCat.{u}).obj A)

/-- The constant scalar summand, from the singleton constant sheaf to the ring sheaf.
It is induced by the scalar-labelled map of constant presheaves and the ring
sheafification unit, using the set-sheafification adjunction.
Source: Stacks Project, Sites, 0H7J; Modules on Sites, 03EL
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def scalarSection {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : CommRingCat.{u}) [HasWeakSheafify J CommRingCat.{u}] (r : A) :
    (constantSheaf J (Type u)).obj PUnit.{u+1} ⟶ coefficient J A :=
  ((sheafificationAdjunction J (Type u)).homEquiv _ _).symm
    ((Functor.const Cᵒᵖ).map (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r)) ≫
      Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A))
        (CategoryTheory.forget CommRingCat.{u}))

/-- Sheafified extension of scalars: the existing tensorFunctor, without a new tensor.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
abbrev extension {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {A B : CommRingCat.{u}} [HasWeakSheafify J CommRingCat.{u}] (a : A ⟶ B) :=
  tensorFunctor ((constantSheaf J CommRingCat.{u}).map a)

/-- The image of a scalar pure tensor under the actual module sheafification unit.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def extensionPure {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {A B : CommRingCat.{u}} [HasWeakSheafify J CommRingCat.{u}] (a : A ⟶ B)
    (M : Modules J A) (W : Cᵒᵖ)
    (b : ((constantSheaf J CommRingCat.{u}).obj B).obj.obj W) (m : M.val.obj W) :
    ((extension J a).obj M).val.obj W :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheaf ((constantSheaf J CommRingCat.{u}).obj B)).obj)).unit.app
      (changeOfRingsPresheaf.{u, u, u} ((constantSheaf J CommRingCat.{u}).map a) M)).app W)
        (b ⊗ₜ[((constantSheaf J CommRingCat.{u}).obj A).obj.obj W,
          (((constantSheaf J CommRingCat.{u}).map a).hom.app W).hom] m)

/-- A sheaf map is the universal scalar pairing when it has the actual pure-section formula.
This predicate tests every section, including locally varying coefficient sections.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def IsScalarPairing {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {A B : CommRingCat.{u}} [HasWeakSheafify J CommRingCat.{u}] (a : A ⟶ B)
    (M : Modules J A)
    (q : coefficient J B ⨯ (underlyingModules J A).obj M ⟶
      (underlyingModules J B).obj ((extension J a).obj M)) : Prop :=
  ∀ (W : Cᵒᵖ) (t : (coefficient J B ⨯ (underlyingModules J A).obj M).obj.obj W),
    q.hom.app W t = extensionPure J a M W
      ((prod.fst : coefficient J B ⨯ (underlyingModules J A).obj M ⟶
        coefficient J B).hom.app W t)
      ((prod.snd : coefficient J B ⨯ (underlyingModules J A).obj M ⟶
        (underlyingModules J A).obj M).hom.app W t)

/-- One specified geometric inverse image and its normalized scalar/pullback map.
The algebraic lifts are the dependency AlgebraicInverseImage, so all module operations
are transported on arbitrary generalized elements. The scalar-section equations
identify each coefficient comparison with the canonical coproduct comparison.
The last field is the generalized pure-tensor normalization of the stipulated map e.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
structure Step {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify K CommRingCat.{u}]
    {A B : CommRingCat.{u}} (a : A ⟶ B) where
  inverse : Sheaf J (Type u) ⥤ Sheaf K (Type u)
  direct : Sheaf K (Type u) ⥤ Sheaf J (Type u)
  adj : inverse ⊣ direct
  leftExact : PreservesFiniteLimits inverse
  point : inverse.obj ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≅
    (constantSheaf K (Type u)).obj PUnit.{u+1}
  left : AlgebraicInverseImage inverse
    ((constantSheaf J CommRingCat.{u}).obj A) ((constantSheaf K CommRingCat.{u}).obj A)
  right : AlgebraicInverseImage inverse
    ((constantSheaf J CommRingCat.{u}).obj B) ((constantSheaf K CommRingCat.{u}).obj B)
  left_constants : ∀ r : A,
    inverse.map (scalarSection J A r) ≫ left.ringUnderlying.hom =
      point.hom ≫ scalarSection K A r
  right_constants : ∀ r : B,
    inverse.map (scalarSection J B r) ≫ right.ringUnderlying.hom =
      point.hom ≫ scalarSection K B r
  comparison : extension J a ⋙ right.modules ≅ left.modules ⋙ extension K a
  normalized : ∀ (M : Modules J A) (Z : Sheaf J (Type u))
    (b : Z ⟶ coefficient J B) (m : Z ⟶ (underlyingModules J A).obj M)
    (z : Z ⟶ (underlyingModules J B).obj ((extension J a).obj M)),
    (∀ (W : Cᵒᵖ) (t : Z.obj.obj W),
      z.hom.app W t = extensionPure J a M W (b.hom.app W t) (m.hom.app W t)) →
    ∀ (W : Dᵒᵖ) (t : (inverse.obj Z).obj.obj W),
      (inverse.map z ≫ right.moduleUnderlying.inv.app ((extension J a).obj M) ≫
        (underlyingModules K B).map (comparison.hom.app M)).hom.app W t =
      extensionPure K a (left.modules.obj M) W
        ((inverse.map b ≫ right.ringUnderlying.hom).hom.app W t)
        ((inverse.map m ≫ left.moduleUnderlying.inv.app M).hom.app W t)

/-- A finite specified composite of geometric inverse images.
The nil constructor retains the identity path. Composition stores the actual steps;
its comparison below is their iterated normalized scalar/pullback comparison.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
inductive Path {A B : CommRingCat.{u}} (a : A ⟶ B) :
    {C D : Type u} → [SmallCategory C] → [SmallCategory D] →
    (J : GrothendieckTopology C) → (K : GrothendieckTopology D) →
    [HasWeakSheafify J CommRingCat.{u}] → [HasWeakSheafify K CommRingCat.{u}] →
    Type (u + 1)
  | nil {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
      [HasWeakSheafify J CommRingCat.{u}] : Path a J J
  | cons {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
      {J : GrothendieckTopology C} {K : GrothendieckTopology D}
      {H : GrothendieckTopology E} [HasWeakSheafify J CommRingCat.{u}]
      [HasWeakSheafify K CommRingCat.{u}] [HasWeakSheafify H CommRingCat.{u}]
      (s : Step J K a) (p : Path a K H) : Path a J H

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify K CommRingCat.{u}]
  {A B : CommRingCat.{u}} {a : A ⟶ B}

namespace Path

/-- The inverse functor of the specified path, composed in its given order.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def inverse :
    {C D : Type u} → [SmallCategory C] → [SmallCategory D] →
    {J : GrothendieckTopology C} → {K : GrothendieckTopology D} →
    [HasWeakSheafify J CommRingCat.{u}] → [HasWeakSheafify K CommRingCat.{u}] →
    Path a J K → Sheaf J (Type u) ⥤ Sheaf K (Type u)
  | _, _, _, _, _, _, _, _, @Path.nil _ _ _ _ _ _ _ => 𝟭 _
  | _, _, _, _, _, _, _, _, @Path.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s p => s.inverse ⋙ p.inverse

/-- The left functor of the specified path, composed in its given order.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def left :
    {C D : Type u} → [SmallCategory C] → [SmallCategory D] →
    {J : GrothendieckTopology C} → {K : GrothendieckTopology D} →
    [HasWeakSheafify J CommRingCat.{u}] → [HasWeakSheafify K CommRingCat.{u}] →
    Path a J K → Modules J A ⥤ Modules K A
  | _, _, _, _, _, _, _, _, @Path.nil _ _ _ _ _ _ _ => 𝟭 _
  | _, _, _, _, _, _, _, _, @Path.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s p => s.left.modules ⋙ p.left

/-- The right functor of the specified path, composed in its given order.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def right :
    {C D : Type u} → [SmallCategory C] → [SmallCategory D] →
    {J : GrothendieckTopology C} → {K : GrothendieckTopology D} →
    [HasWeakSheafify J CommRingCat.{u}] → [HasWeakSheafify K CommRingCat.{u}] →
    Path a J K → Modules J B ⥤ Modules K B
  | _, _, _, _, _, _, _, _, @Path.nil _ _ _ _ _ _ _ => 𝟭 _
  | _, _, _, _, _, _, _, _, @Path.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s p =>
    s.right.modules ⋙ p.right

/-- The canonical underlying-set identification for the left module composite.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def leftUnderlying :
    {C D : Type u} → [SmallCategory C] → [SmallCategory D] →
    {J : GrothendieckTopology C} → {K : GrothendieckTopology D} →
    [HasWeakSheafify J CommRingCat.{u}] → [HasWeakSheafify K CommRingCat.{u}] → (p : Path a J K) →
    p.left ⋙ underlyingModules K A ≅ underlyingModules J A ⋙ p.inverse
  | _, _, _, _, _, _, _, _, @Path.nil _ _ _ _ _ _ _ =>
    (Functor.leftUnitor _).trans (Functor.rightUnitor _).symm
  | _, _, _, _, _, _, _, _, @Path.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s p =>
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft s.left.modules p.leftUnderlying ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight s.left.moduleUnderlying p.inverse ≪≫ Functor.associator _ _ _

/-- The canonical underlying-set identification for the right module composite.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def rightUnderlying :
    {C D : Type u} → [SmallCategory C] → [SmallCategory D] →
    {J : GrothendieckTopology C} → {K : GrothendieckTopology D} →
    [HasWeakSheafify J CommRingCat.{u}] → [HasWeakSheafify K CommRingCat.{u}] → (p : Path a J K) →
    p.right ⋙ underlyingModules K B ≅ underlyingModules J B ⋙ p.inverse
  | _, _, _, _, _, _, _, _, @Path.nil _ _ _ _ _ _ _ =>
    (Functor.leftUnitor _).trans (Functor.rightUnitor _).symm
  | _, _, _, _, _, _, _, _, @Path.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s p =>
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft s.right.modules p.rightUnderlying ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight s.right.moduleUnderlying p.inverse ≪≫ Functor.associator _ _ _

/-- The iterated canonical constant-ring identification for A.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def leftCoefficient :
    {C D : Type u} → [SmallCategory C] → [SmallCategory D] →
    {J : GrothendieckTopology C} → {K : GrothendieckTopology D} →
    [HasWeakSheafify J CommRingCat.{u}] → [HasWeakSheafify K CommRingCat.{u}] → (p : Path a J K) →
    p.inverse.obj (coefficient J A) ≅ coefficient K A
  | _, _, _, _, _, _, _, _, @Path.nil _ _ _ _ _ _ _ => Iso.refl _
  | _, _, _, _, _, _, _, _, @Path.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s p =>
    p.inverse.mapIso s.left.ringUnderlying ≪≫ p.leftCoefficient

/-- The iterated canonical constant-ring identification for B.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def rightCoefficient :
    {C D : Type u} → [SmallCategory C] → [SmallCategory D] →
    {J : GrothendieckTopology C} → {K : GrothendieckTopology D} →
    [HasWeakSheafify J CommRingCat.{u}] → [HasWeakSheafify K CommRingCat.{u}] → (p : Path a J K) →
    p.inverse.obj (coefficient J B) ≅ coefficient K B
  | _, _, _, _, _, _, _, _, @Path.nil _ _ _ _ _ _ _ => Iso.refl _
  | _, _, _, _, _, _, _, _, @Path.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s p =>
    p.inverse.mapIso s.right.ringUnderlying ≪≫ p.rightCoefficient

/-- The expanded scalar/pullback map of a specified composite.
The cons formula first applies the first step comparison, then the remaining path
comparison. Associators are the ordinary module composition identifications.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
def comparison :
    {C D : Type u} → [SmallCategory C] → [SmallCategory D] →
    {J : GrothendieckTopology C} → {K : GrothendieckTopology D} →
    [HasWeakSheafify J CommRingCat.{u}] → [HasWeakSheafify K CommRingCat.{u}] → (p : Path a J K) →
    extension J a ⋙ p.right ≅ p.left ⋙ extension K a
  | _, _, _, _, _, _, _, _, @Path.nil _ _ _ _ _ _ _ =>
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm
  | _, _, _, _, _, _, _, _, @Path.cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s p =>
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight s.comparison p.right ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft s.left.modules p.comparison ≪≫
          (Functor.associator _ _ _).symm

end Path

section Proof



private lemma pathLimits (p : Path a J K) : PreservesFiniteLimits p.inverse := by
  induction p with
  | nil => change PreservesFiniteLimits (𝟭 _); infer_instance
  | cons s p ih =>
    exact @comp_preservesFiniteLimits _ _ _ _ _ _ s.inverse p.inverse s.leftExact ih

private lemma pathColimits (p : Path a J K) :
    PreservesColimitsOfSize.{u, u} p.inverse := by
  induction p with
  | nil => change PreservesColimitsOfSize (𝟭 _); infer_instance
  | cons s p ih =>
    have : PreservesColimitsOfSize.{u, u} s.inverse := s.adj.leftAdjoint_preservesColimits
    have := ih
    change PreservesColimitsOfSize (s.inverse ⋙ p.inverse)
    infer_instance

private lemma pathAddLeft (p : Path a J K) (M : Modules J A)
    (T : Sheaf J (Type u)) (x y z : T ⟶ (underlyingModules J A).obj M)
    (h : ∀ W t, z.hom.app W t =
      (show M.val.obj W from x.hom.app W t) + (show M.val.obj W from y.hom.app W t)) :
    ∀ W t, (p.inverse.map z ≫ p.leftUnderlying.inv.app M).hom.app W t =
      (show (p.left.obj M).val.obj W from
        (p.inverse.map x ≫ p.leftUnderlying.inv.app M).hom.app W t) +
      (show (p.left.obj M).val.obj W from
        (p.inverse.map y ≫ p.leftUnderlying.inv.app M).hom.app W t) := by
  induction p with
  | nil => simpa [Path.left, Path.inverse, Path.leftUnderlying] using h
  | cons s p ih =>
    have hh := ih (s.left.modules.obj M) (s.inverse.obj T)
      (s.inverse.map x ≫ s.left.moduleUnderlying.inv.app M)
      (s.inverse.map y ≫ s.left.moduleUnderlying.inv.app M)
      (s.inverse.map z ≫ s.left.moduleUnderlying.inv.app M)
      (s.left.moduleAdd M T x y z h)
    simpa [Path.left, Path.inverse, Path.leftUnderlying, Functor.map_comp, Category.assoc] using hh

private lemma pathSMulLeft (p : Path a J K) (M : Modules J A)
    (T : Sheaf J (Type u)) (r : T ⟶ coefficient J A)
    (x z : T ⟶ (underlyingModules J A).obj M)
    (h : ∀ W t, z.hom.app W t =
      (show ((constantSheaf J CommRingCat.{u}).obj A).obj.obj W from r.hom.app W t) •
        (show M.val.obj W from x.hom.app W t)) :
    ∀ W t, (p.inverse.map z ≫ p.leftUnderlying.inv.app M).hom.app W t =
      (show ((constantSheaf K CommRingCat.{u}).obj A).obj.obj W from
        (p.inverse.map r ≫ p.leftCoefficient.hom).hom.app W t) •
      (show (p.left.obj M).val.obj W from
        (p.inverse.map x ≫ p.leftUnderlying.inv.app M).hom.app W t) := by
  induction p with
  | nil => simpa [Path.left, Path.inverse, Path.leftUnderlying, Path.leftCoefficient] using h
  | cons s p ih =>
    have hh := ih (s.left.modules.obj M) (s.inverse.obj T)
      (s.inverse.map r ≫ s.left.ringUnderlying.hom)
      (s.inverse.map x ≫ s.left.moduleUnderlying.inv.app M)
      (s.inverse.map z ≫ s.left.moduleUnderlying.inv.app M)
      (s.left.moduleSMul M T r x z h)
    simpa [Path.left, Path.inverse, Path.leftUnderlying, Path.leftCoefficient,
      Functor.map_comp, Category.assoc] using hh

private lemma pathAddRight (p : Path a J K) (M : Modules J B)
    (T : Sheaf J (Type u)) (x y z : T ⟶ (underlyingModules J B).obj M)
    (h : ∀ W t, z.hom.app W t =
      (show M.val.obj W from x.hom.app W t) + (show M.val.obj W from y.hom.app W t)) :
    ∀ W t, (p.inverse.map z ≫ p.rightUnderlying.inv.app M).hom.app W t =
      (show (p.right.obj M).val.obj W from
        (p.inverse.map x ≫ p.rightUnderlying.inv.app M).hom.app W t) +
      (show (p.right.obj M).val.obj W from
        (p.inverse.map y ≫ p.rightUnderlying.inv.app M).hom.app W t) := by
  induction p with
  | nil => simpa [Path.right, Path.inverse, Path.rightUnderlying] using h
  | cons s p ih =>
    have hh := ih (s.right.modules.obj M) (s.inverse.obj T)
      (s.inverse.map x ≫ s.right.moduleUnderlying.inv.app M)
      (s.inverse.map y ≫ s.right.moduleUnderlying.inv.app M)
      (s.inverse.map z ≫ s.right.moduleUnderlying.inv.app M)
      (s.right.moduleAdd M T x y z h)
    simpa [Path.right, Path.inverse, Path.rightUnderlying,
      Functor.map_comp, Category.assoc] using hh

private lemma pathSMulRight (p : Path a J K) (M : Modules J B)
    (T : Sheaf J (Type u)) (r : T ⟶ coefficient J B)
    (x z : T ⟶ (underlyingModules J B).obj M)
    (h : ∀ W t, z.hom.app W t =
      (show ((constantSheaf J CommRingCat.{u}).obj B).obj.obj W from r.hom.app W t) •
        (show M.val.obj W from x.hom.app W t)) :
    ∀ W t, (p.inverse.map z ≫ p.rightUnderlying.inv.app M).hom.app W t =
      (show ((constantSheaf K CommRingCat.{u}).obj B).obj.obj W from
        (p.inverse.map r ≫ p.rightCoefficient.hom).hom.app W t) •
      (show (p.right.obj M).val.obj W from
        (p.inverse.map x ≫ p.rightUnderlying.inv.app M).hom.app W t) := by
  induction p with
  | nil =>
    simpa [Path.right, Path.inverse, Path.rightUnderlying, Path.rightCoefficient] using h
  | cons s p ih =>
    have hh := ih (s.right.modules.obj M) (s.inverse.obj T)
      (s.inverse.map r ≫ s.right.ringUnderlying.hom)
      (s.inverse.map x ≫ s.right.moduleUnderlying.inv.app M)
      (s.inverse.map z ≫ s.right.moduleUnderlying.inv.app M)
      (s.right.moduleSMul M T r x z h)
    simpa [Path.right, Path.inverse, Path.rightUnderlying, Path.rightCoefficient,
      Functor.map_comp, Category.assoc] using hh

private lemma extensionPure_map {M N : Modules J A} (f : M ⟶ N) (W : Cᵒᵖ)
    (b : ((constantSheaf J CommRingCat.{u}).obj B).obj.obj W) (m : M.val.obj W) :
    ((extension J a).map f).val.app W (extensionPure J a M W b m) =
      extensionPure J a N W b (f.val.app W m) := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (RingedTensor.ringSheaf ((constantSheaf J CommRingCat.{u}).obj B)).obj)).unit.naturality
    ((RingedTensor.tensorPresheafFunctor ((constantSheaf J CommRingCat.{u}).map a)).map f)
  exact (congrArg (fun k ↦ k.app W
    (b ⊗ₜ[((constantSheaf J CommRingCat.{u}).obj A).obj.obj W,
      (((constantSheaf J CommRingCat.{u}).map a).hom.app W).hom] m)) h).symm

private def pointTerminal (J : GrothendieckTopology C) :
    IsTerminal ((constantSheaf J (Type u)).obj PUnit.{u+1}) :=
  (Types.isTerminalPUnit.isTerminalObj (Functor.const Cᵒᵖ) _).isTerminalObj
    (presheafToSheaf J (Type u)) _

private def pathPoint (p : Path a J K) :
    p.inverse.obj ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u+1} := by
  have := pathLimits p
  exact ((pointTerminal J).isTerminalObj p.inverse _).uniqueUpToIso (pointTerminal K)

private lemma pathConstantsLeft (p : Path a J K) (r : A) :
    p.inverse.map (scalarSection J A r) ≫ p.leftCoefficient.hom =
      (pathPoint p).hom ≫ scalarSection K A r := by
  induction p with
  | nil =>
    rename_i C' hC J' hJ
    have hp : (pathPoint (Path.nil (a := a) J')).hom = 𝟙 _ :=
      (pointTerminal J').hom_ext _ _
    simp [Path.inverse, Path.leftCoefficient, hp]
  | cons s p ih =>
    have hp : (pathPoint (Path.cons s p)).hom =
        p.inverse.map s.point.hom ≫ (pathPoint p).hom :=
      (pointTerminal _).hom_ext _ _
    simp only [Path.inverse, Functor.comp_map, Path.leftCoefficient, Iso.trans_hom,
      Functor.mapIso_hom, ← Category.assoc, ← p.inverse.map_comp, s.left_constants]
    rw [p.inverse.map_comp, Category.assoc, ih]
    simp only [← Category.assoc, hp]

private lemma pathConstantsRight (p : Path a J K) (r : B) :
    p.inverse.map (scalarSection J B r) ≫ p.rightCoefficient.hom =
      (pathPoint p).hom ≫ scalarSection K B r := by
  induction p with
  | nil =>
    rename_i C' hC J' hJ
    have hp : (pathPoint (Path.nil (a := a) J')).hom = 𝟙 _ :=
      (pointTerminal J').hom_ext _ _
    simp [Path.inverse, Path.rightCoefficient, hp]
  | cons s p ih =>
    have hp : (pathPoint (Path.cons s p)).hom =
        p.inverse.map s.point.hom ≫ (pathPoint p).hom :=
      (pointTerminal _).hom_ext _ _
    simp only [Path.inverse, Functor.comp_map, Path.rightCoefficient, Iso.trans_hom,
      Functor.mapIso_hom, ← Category.assoc, ← p.inverse.map_comp, s.right_constants]
    rw [p.inverse.map_comp, Category.assoc, ih]
    simp only [← Category.assoc, hp]

omit [HasWeakSheafify J CommRingCat.{u}] in
private lemma coefficientPreserves :
    J.PreservesSheafification (forget CommRingCat.{u}) :=
  GrothendieckTopology.instPreservesSheafification _ _

attribute [local instance] coefficientPreserves

private lemma scalarSection_eq (J : GrothendieckTopology C) (A : CommRingCat.{u})
    [HasWeakSheafify J CommRingCat.{u}] (r : A) :
    scalarSection J A r =
      (constantSheaf J (Type u)).map (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r)) ≫
        ((constantCommuteCompose J (forget CommRingCat.{u})).app A).inv := by
  apply ((sheafificationAdjunction J (Type u)).homEquiv _ _).injective
  unfold scalarSection
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  ext t
  have hc := sheafComposeIso_hom_fac J (forget CommRingCat.{u})
    ((Functor.const Cᵒᵖ).obj A)
  have hn := toSheafify_naturality J ((Functor.const Cᵒᵖ).map
    (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r)))
  have hu :
      (((constantCommuteCompose J (forget CommRingCat.{u})).inv.app A).hom.app W)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type u))).app W r) =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app W r) := by
    have hc' := toSheafify_naturality J
      (Functor.constComp Cᵒᵖ A (forget CommRingCat.{u})).inv
    change (((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type u))) ≫
      (sheafifyMap J (Functor.constComp Cᵒᵖ A (forget CommRingCat.{u})).inv) ≫
      (sheafifyComposeIso J (forget CommRingCat.{u})
        ((Functor.const Cᵒᵖ).obj A)).hom).app W) r = _
    rw [← Category.assoc, ← hc', Category.assoc, hc]
    rfl
  have hn' := congrArg (fun k ↦ k.app W t) hn
  change ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app W r) =
    (((constantCommuteCompose J (forget CommRingCat.{u})).inv.app A).hom.app W)
      ((sheafifyMap J ((Functor.const Cᵒᵖ).map
        (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r)))).app W
          ((toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{u+1})).app W t))
  change ((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type u))).app W r) = _ at hn'
  exact hu.symm.trans (congrArg
    (((constantCommuteCompose J (forget CommRingCat.{u})).inv.app A).hom.app W) hn')

private def scalarCofan (R : Type u) : Cofan (fun _ : R ↦ PUnit.{u+1}) :=
  Cofan.mk R (fun r ↦ TypeCat.ofHom (fun _ ↦ r))

private def scalarCofanIsColimit (R : Type u) : IsColimit (scalarCofan R) :=
  Cofan.IsColimit.mk _ (fun s ↦ TypeCat.ofHom (fun r ↦ s.inj r PUnit.unit))
    (by intros; ext x; cases x; rfl)
    (by intro s f h; ext r; exact ConcreteCategory.congr_hom (h r) PUnit.unit)

private def mapScalarCofanIsColimit {E : Type*} [Category E]
    (F : Type u ⥤ E) [PreservesColimitsOfSize.{u, u} F] (R : Type u) :
    IsColimit (Cofan.mk (F.obj R)
      (fun r : R ↦ F.map (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r)))) :=
  isColimitCofanMkObjOfIsColimit F _ _ (scalarCofanIsColimit R)

omit [HasWeakSheafify K CommRingCat.{u}] in
private lemma coefficient_ext (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesColimitsOfSize.{u, u} F] (R : CommRingCat.{u})
    {X : Sheaf K (Type u)} {f g : F.obj (coefficient J R) ⟶ X}
    (h : ∀ r : R, F.map (scalarSection J R r) ≫ f =
      F.map (scalarSection J R r) ≫ g) : f = g := by
  have : PreservesColimitsOfSize.{u, u} (constantSheaf J (Type u)) := by
    dsimp [constantSheaf]; infer_instance
  apply (cancel_epi (F.map ((constantCommuteCompose J (forget CommRingCat.{u})).app R).inv)).mp
  apply Cofan.IsColimit.hom_ext
    (mapScalarCofanIsColimit (constantSheaf J (Type u) ⋙ F) R)
  intro r
  change F.map ((constantSheaf J (Type u)).map
      (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))) ≫ _ = _
  change F.map ((constantSheaf J (Type u)).map
      (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))) ≫ _ =
    F.map ((constantSheaf J (Type u)).map
      (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ r))) ≫ _
  simpa only [scalarSection_eq, F.map_comp, Category.assoc] using h r

private lemma coefficientTwoIsoLeft (p q : Path a J K) (θ : p.inverse ≅ q.inverse) :
    θ.hom.app (coefficient J A) ≫ q.leftCoefficient.hom = p.leftCoefficient.hom := by
  have := pathColimits p
  apply coefficient_ext p.inverse A
  intro r
  rw [← Category.assoc, θ.hom.naturality, Category.assoc, pathConstantsLeft,
    pathConstantsLeft]
  have hp : θ.hom.app ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≫
      (pathPoint q).hom = (pathPoint p).hom := (pointTerminal K).hom_ext _ _
  simp only [← Category.assoc, hp]

private lemma coefficientTwoIsoRight (p q : Path a J K) (θ : p.inverse ≅ q.inverse) :
    θ.hom.app (coefficient J B) ≫ q.rightCoefficient.hom = p.rightCoefficient.hom := by
  have := pathColimits p
  apply coefficient_ext p.inverse B
  intro r
  rw [← Category.assoc, θ.hom.naturality, Category.assoc, pathConstantsRight,
    pathConstantsRight]
  have hp : θ.hom.app ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≫
      (pathPoint q).hom = (pathPoint p).hom := (pointTerminal K).hom_ext _ _
  simp only [← Category.assoc, hp]

private lemma coefficientMapSection (r : A) :
    scalarSection J A r ≫ (sheafCompose J (forget CommRingCat.{u})).map
      ((constantSheaf J CommRingCat.{u}).map a) = scalarSection J B (a.hom r) := by
  rw [scalarSection_eq, scalarSection_eq]
  have h := (constantCommuteCompose J (forget CommRingCat.{u})).inv.naturality a
  dsimp only [Functor.comp_map] at h
  simp only [Iso.app_inv]
  rw [Category.assoc, ← h, ← Category.assoc, ← Functor.map_comp]
  rfl

private lemma pathCoefficientMap (p : Path a J K) :
    p.inverse.map ((sheafCompose J (forget CommRingCat.{u})).map
        ((constantSheaf J CommRingCat.{u}).map a)) ≫ p.rightCoefficient.hom =
      p.leftCoefficient.hom ≫ (sheafCompose K (forget CommRingCat.{u})).map
        ((constantSheaf K CommRingCat.{u}).map a) := by
  have := pathColimits p
  apply coefficient_ext p.inverse A
  intro r
  rw [← Category.assoc, ← p.inverse.map_comp, coefficientMapSection,
    pathConstantsRight, ← Category.assoc, pathConstantsLeft, Category.assoc,
    coefficientMapSection]

private theorem binaryOfGraph
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    {X Y Z : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (dX : F.obj X ⟶ A) (dY : F.obj Y ⟶ B) (dZ : F.obj Z ⟶ E)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ V, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ V p, b.hom.app V p =
      op' V ((prod.fst : A ⨯ B ⟶ A).hom.app V p)
        ((prod.snd : A ⨯ B ⟶ B).hom.app V p))
    (hgraph : ∀ (T : Sheaf J (Type u)) (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z),
      (∀ U p, z.hom.app U p = op U (x.hom.app U p) (y.hom.app U p)) →
      ∀ V p, (F.map z ≫ dZ).hom.app V p =
        op' V ((F.map x ≫ dX).hom.app V p) ((F.map y ≫ dY).hom.app V p)) :
    F.map a ≫ dZ = prodComparison F X Y ≫ prod.map dX dY ≫ b := by
  have h₁ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.fst =
      F.map prod.fst ≫ dX := by simp only [prod.map_fst, prodComparison_fst_assoc]
  have h₂ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.snd =
      F.map prod.snd ≫ dY := by simp only [prod.map_snd, prodComparison_snd_assoc]
  ext V p
  have h := hgraph (X ⨯ Y) prod.fst prod.snd a hs V p
  change (F.map a ≫ dZ).hom.app V p = b.hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p)
  rw [ht]
  have hh₁ := congrArg (fun k ↦ k.hom.app V p) h₁
  have hh₂ := congrArg (fun k ↦ k.hom.app V p) h₂
  change (prod.fst : A ⨯ B ⟶ A).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₁
  change (prod.snd : A ⨯ B ⟶ B).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₂
  rw [hh₁, hh₂]
  exact h


open SheafOfModules.GeometricConstruction

private def addOperation (J : GrothendieckTopology C) (A : CommRingCat.{u})
    [HasWeakSheafify J CommRingCat.{u}] (M : Modules J A) :=
  fromProd _ _ ≫ addition ((constantSheaf J CommRingCat.{u}).obj A) M

private def smulOperation (J : GrothendieckTopology C) (A : CommRingCat.{u})
    [HasWeakSheafify J CommRingCat.{u}] (M : Modules J A) :=
  fromProd _ _ ≫ action ((constantSheaf J CommRingCat.{u}).obj A) M

private lemma pathOperationsLeft (p : Path a J K) (M : Modules J A) :
    (p.inverse.map (addOperation J A M) ≫ p.leftUnderlying.inv.app M =
      prodComparison p.inverse _ _ ≫
        prod.map (p.leftUnderlying.inv.app M) (p.leftUnderlying.inv.app M) ≫
          addOperation K A (p.left.obj M)) ∧
    (p.inverse.map (smulOperation J A M) ≫ p.leftUnderlying.inv.app M =
      prodComparison p.inverse _ _ ≫
        prod.map p.leftCoefficient.hom (p.leftUnderlying.inv.app M) ≫
          smulOperation K A (p.left.obj M)) := by
  constructor
  · exact binaryOfGraph p.inverse _ _ _ _ _
      (fun W x y ↦ @Add.add (M.val.obj W) inferInstance x y)
      (fun W x y ↦ @Add.add ((p.left.obj M).val.obj W) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (pathAddLeft p M)
  · exact binaryOfGraph p.inverse _ _ _ _ _
      (fun W r x ↦ @SMul.smul _ (M.val.obj W) inferInstance r x)
      (fun W r x ↦ @SMul.smul _ ((p.left.obj M).val.obj W) inferInstance r x)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (pathSMulLeft p M)

private lemma pathOperationsRight (p : Path a J K) (M : Modules J B) :
    (p.inverse.map (addOperation J B M) ≫ p.rightUnderlying.inv.app M =
      prodComparison p.inverse _ _ ≫
        prod.map (p.rightUnderlying.inv.app M) (p.rightUnderlying.inv.app M) ≫
          addOperation K B (p.right.obj M)) ∧
    (p.inverse.map (smulOperation J B M) ≫ p.rightUnderlying.inv.app M =
      prodComparison p.inverse _ _ ≫
        prod.map p.rightCoefficient.hom (p.rightUnderlying.inv.app M) ≫
          smulOperation K B (p.right.obj M)) := by
  constructor
  · exact binaryOfGraph p.inverse _ _ _ _ _
      (fun W x y ↦ @Add.add (M.val.obj W) inferInstance x y)
      (fun W x y ↦ @Add.add ((p.right.obj M).val.obj W) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (pathAddRight p M)
  · exact binaryOfGraph p.inverse _ _ _ _ _
      (fun W r x ↦ @SMul.smul _ (M.val.obj W) inferInstance r x)
      (fun W r x ↦ @SMul.smul _ ((p.right.obj M).val.obj W) inferInstance r x)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (pathSMulRight p M)

omit [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify K CommRingCat.{u}] in
private lemma binaryConjugate
    {F G : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    [PreservesFiniteLimits F] (θ : F ≅ G)
    {X Y Z : Sheaf J (Type u)} {P Q R P' Q' R' : Sheaf K (Type u)}
    (x : P ≅ F.obj X) (y : Q ≅ F.obj Y) (z : R ≅ F.obj Z)
    (x' : P' ≅ G.obj X) (y' : Q' ≅ G.obj Y) (z' : R' ≅ G.obj Z)
    (b : X ⨯ Y ⟶ Z) (bP : P ⨯ Q ⟶ R) (bQ : P' ⨯ Q' ⟶ R')
    (hP : F.map b ≫ z.inv = prodComparison F X Y ≫ prod.map x.inv y.inv ≫ bP)
    (hQ : G.map b ≫ z'.inv = prodComparison G X Y ≫ prod.map x'.inv y'.inv ≫ bQ) :
    bP ≫ z.hom ≫ θ.hom.app Z ≫ z'.inv =
      prod.map (x.hom ≫ θ.hom.app X ≫ x'.inv)
        (y.hom ≫ θ.hom.app Y ≫ y'.inv) ≫ bQ := by
  apply (cancel_epi (prodComparison F X Y ≫ prod.map x.inv y.inv)).mp
  have h := congrArg (fun k ↦ k ≫ z.hom ≫ θ.hom.app Z ≫ z'.inv) hP
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  rw [θ.hom.naturality_assoc, hQ, prodComparison_natural_of_natTrans_assoc] at h
  simpa only [Category.assoc, prod.map_map_assoc, Iso.inv_hom_id_assoc] using h.symm

private lemma moduleTwoIsoLeft (p q : Path a J K) (θ : p.inverse ≅ q.inverse) :
    ∃ e : p.left ≅ q.left, ∀ M : Modules J A,
      (underlyingModules K A).map (e.hom.app M) ≫ q.leftUnderlying.hom.app M =
        p.leftUnderlying.hom.app M ≫ θ.hom.app ((underlyingModules J A).obj M) := by
  have := pathLimits p
  let n : p.left ⋙ underlyingModules K A ≅ q.left ⋙ underlyingModules K A :=
    p.leftUnderlying ≪≫ Functor.isoWhiskerLeft (underlyingModules J A) θ ≪≫
      q.leftUnderlying.symm
  have hn (M : Modules J A) : n.hom.app M =
      p.leftUnderlying.hom.app M ≫ θ.hom.app ((underlyingModules J A).obj M) ≫
        q.leftUnderlying.inv.app M := rfl
  have hadd (M : Modules J A) : addOperation K A (p.left.obj M) ≫ n.hom.app M =
      prod.map (n.hom.app M) (n.hom.app M) ≫ addOperation K A (q.left.obj M) := by
    exact binaryConjugate θ (p.leftUnderlying.app M) (p.leftUnderlying.app M)
      (p.leftUnderlying.app M) (q.leftUnderlying.app M) (q.leftUnderlying.app M)
      (q.leftUnderlying.app M) (addOperation J A M) _ _
      (pathOperationsLeft p M).1 (pathOperationsLeft q M).1
  have hsmul (M : Modules J A) : smulOperation K A (p.left.obj M) ≫ n.hom.app M =
      prod.map (𝟙 (coefficient K A)) (n.hom.app M) ≫
        smulOperation K A (q.left.obj M) := by
    have h := binaryConjugate θ p.leftCoefficient.symm (p.leftUnderlying.app M)
      (p.leftUnderlying.app M) q.leftCoefficient.symm (q.leftUnderlying.app M)
      (q.leftUnderlying.app M) (smulOperation J A M) _ _
      (pathOperationsLeft p M).2 (pathOperationsLeft q M).2
    simpa only [hn, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
      coefficientTwoIsoLeft, Iso.inv_hom_id] using h
  have ha (M : Modules J A) (W : Dᵒᵖ) (x y : (p.left.obj M).val.obj W) :
      (n.hom.app M).hom.app W (x + y) =
        (show (q.left.obj M).val.obj W from (n.hom.app M).hom.app W x) +
          (show (q.left.obj M).val.obj W from (n.hom.app M).hom.app W y) := by
    let t := sectionPair ((underlyingModules K A).obj (p.left.obj M))
      ((underlyingModules K A).obj (p.left.obj M)) W x y
    have h := congrArg (fun f ↦ f.hom.app W t) (hadd M)
    change (n.hom.app M).hom.app W
      (@Add.add ((p.left.obj M).val.obj W) inferInstance
        ((prod.fst : (underlyingModules K A).obj (p.left.obj M) ⨯
          (underlyingModules K A).obj (p.left.obj M) ⟶ _).hom.app W t)
        ((prod.snd : (underlyingModules K A).obj (p.left.obj M) ⨯
          (underlyingModules K A).obj (p.left.obj M) ⟶ _).hom.app W t)) =
      @Add.add ((q.left.obj M).val.obj W) inferInstance
        ((prod.fst : (underlyingModules K A).obj (q.left.obj M) ⨯
          (underlyingModules K A).obj (q.left.obj M) ⟶ _).hom.app W
            ((prod.map (n.hom.app M) (n.hom.app M)).hom.app W t))
        ((prod.snd : (underlyingModules K A).obj (q.left.obj M) ⨯
          (underlyingModules K A).obj (q.left.obj M) ⟶ _).hom.app W
            ((prod.map (n.hom.app M) (n.hom.app M)).hom.app W t)) at h
    erw [prodMap_fst_apply, prodMap_snd_apply] at h
    dsimp only [t] at h
    erw [sectionPair_fst, sectionPair_snd] at h
    exact h
  have hs (M : Modules J A) (W : Dᵒᵖ)
      (r : ((constantSheaf K CommRingCat.{u}).obj A).obj.obj W)
      (x : (p.left.obj M).val.obj W) : (n.hom.app M).hom.app W (r • x) =
        r • (show (q.left.obj M).val.obj W from (n.hom.app M).hom.app W x) := by
    let t := sectionPair (coefficient K A) ((underlyingModules K A).obj (p.left.obj M)) W r x
    have h := congrArg (fun f ↦ f.hom.app W t) (hsmul M)
    change (n.hom.app M).hom.app W
      (@SMul.smul (((constantSheaf K CommRingCat.{u}).obj A).obj.obj W)
        ((p.left.obj M).val.obj W) inferInstance
        ((prod.fst : coefficient K A ⨯ (underlyingModules K A).obj (p.left.obj M) ⟶
          coefficient K A).hom.app W t)
        ((prod.snd : coefficient K A ⨯ (underlyingModules K A).obj (p.left.obj M) ⟶
          (underlyingModules K A).obj (p.left.obj M)).hom.app W t)) =
      @SMul.smul (((constantSheaf K CommRingCat.{u}).obj A).obj.obj W)
        ((q.left.obj M).val.obj W) inferInstance
        ((prod.fst : coefficient K A ⨯ (underlyingModules K A).obj (q.left.obj M) ⟶
          coefficient K A).hom.app W
            ((prod.map (𝟙 (coefficient K A)) (n.hom.app M)).hom.app W t))
        ((prod.snd : coefficient K A ⨯ (underlyingModules K A).obj (q.left.obj M) ⟶
          (underlyingModules K A).obj (q.left.obj M)).hom.app W
            ((prod.map (𝟙 (coefficient K A)) (n.hom.app M)).hom.app W t)) at h
    erw [prodMap_fst_apply, prodMap_snd_apply] at h
    dsimp only [t] at h
    erw [sectionPair_fst, sectionPair_snd] at h
    exact h
  let η : p.left ⟶ q.left :=
    { app := fun M ↦ linearLift (n.hom.app M) (ha M) (hs M)
      naturality := fun {M N} f ↦ by
        apply (underlyingModules K A).map_injective
        change (underlyingModules K A).map (p.left.map f) ≫ n.hom.app N =
          n.hom.app M ≫ (underlyingModules K A).map (q.left.map f)
        exact n.hom.naturality f }
  have hi (M : Modules J A) : IsIso (η.app M) := by
    have : IsIso ((underlyingModules K A).map (η.app M)) := by
      change IsIso (n.hom.app M)
      infer_instance
    exact isIso_of_reflects_iso _ (underlyingModules K A)
  refine ⟨NatIso.ofComponents (fun M ↦ asIso (η.app M)) (fun f ↦ η.naturality f), ?_⟩
  intro M
  change n.hom.app M ≫ q.leftUnderlying.hom.app M = _
  rw [hn]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private lemma moduleTwoIsoRight (p q : Path a J K) (θ : p.inverse ≅ q.inverse) :
    ∃ e : p.right ≅ q.right, ∀ M : Modules J B,
      (underlyingModules K B).map (e.hom.app M) ≫ q.rightUnderlying.hom.app M =
        p.rightUnderlying.hom.app M ≫ θ.hom.app ((underlyingModules J B).obj M) := by
  have := pathLimits p
  let n : p.right ⋙ underlyingModules K B ≅ q.right ⋙ underlyingModules K B :=
    p.rightUnderlying ≪≫ Functor.isoWhiskerLeft (underlyingModules J B) θ ≪≫
      q.rightUnderlying.symm
  have hn (M : Modules J B) : n.hom.app M =
      p.rightUnderlying.hom.app M ≫ θ.hom.app ((underlyingModules J B).obj M) ≫
        q.rightUnderlying.inv.app M := rfl
  have hadd (M : Modules J B) : addOperation K B (p.right.obj M) ≫ n.hom.app M =
      prod.map (n.hom.app M) (n.hom.app M) ≫ addOperation K B (q.right.obj M) := by
    exact binaryConjugate θ (p.rightUnderlying.app M) (p.rightUnderlying.app M)
      (p.rightUnderlying.app M) (q.rightUnderlying.app M) (q.rightUnderlying.app M)
      (q.rightUnderlying.app M) (addOperation J B M) _ _
      (pathOperationsRight p M).1 (pathOperationsRight q M).1
  have hsmul (M : Modules J B) : smulOperation K B (p.right.obj M) ≫ n.hom.app M =
      prod.map (𝟙 (coefficient K B)) (n.hom.app M) ≫
        smulOperation K B (q.right.obj M) := by
    have h := binaryConjugate θ p.rightCoefficient.symm (p.rightUnderlying.app M)
      (p.rightUnderlying.app M) q.rightCoefficient.symm (q.rightUnderlying.app M)
      (q.rightUnderlying.app M) (smulOperation J B M) _ _
      (pathOperationsRight p M).2 (pathOperationsRight q M).2
    simpa only [hn, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
      coefficientTwoIsoRight, Iso.inv_hom_id] using h
  have ha (M : Modules J B) (W : Dᵒᵖ) (x y : (p.right.obj M).val.obj W) :
      (n.hom.app M).hom.app W (x + y) =
        (show (q.right.obj M).val.obj W from (n.hom.app M).hom.app W x) +
          (show (q.right.obj M).val.obj W from (n.hom.app M).hom.app W y) := by
    let t := sectionPair ((underlyingModules K B).obj (p.right.obj M))
      ((underlyingModules K B).obj (p.right.obj M)) W x y
    have h := congrArg (fun f ↦ f.hom.app W t) (hadd M)
    change (n.hom.app M).hom.app W
      (@Add.add ((p.right.obj M).val.obj W) inferInstance
        ((prod.fst : (underlyingModules K B).obj (p.right.obj M) ⨯
          (underlyingModules K B).obj (p.right.obj M) ⟶ _).hom.app W t)
        ((prod.snd : (underlyingModules K B).obj (p.right.obj M) ⨯
          (underlyingModules K B).obj (p.right.obj M) ⟶ _).hom.app W t)) =
      @Add.add ((q.right.obj M).val.obj W) inferInstance
        ((prod.fst : (underlyingModules K B).obj (q.right.obj M) ⨯
          (underlyingModules K B).obj (q.right.obj M) ⟶ _).hom.app W
            ((prod.map (n.hom.app M) (n.hom.app M)).hom.app W t))
        ((prod.snd : (underlyingModules K B).obj (q.right.obj M) ⨯
          (underlyingModules K B).obj (q.right.obj M) ⟶ _).hom.app W
            ((prod.map (n.hom.app M) (n.hom.app M)).hom.app W t)) at h
    erw [prodMap_fst_apply, prodMap_snd_apply] at h
    dsimp only [t] at h
    erw [sectionPair_fst, sectionPair_snd] at h
    exact h
  have hs (M : Modules J B) (W : Dᵒᵖ)
      (r : ((constantSheaf K CommRingCat.{u}).obj B).obj.obj W)
      (x : (p.right.obj M).val.obj W) : (n.hom.app M).hom.app W (r • x) =
        r • (show (q.right.obj M).val.obj W from (n.hom.app M).hom.app W x) := by
    let t := sectionPair (coefficient K B) ((underlyingModules K B).obj (p.right.obj M)) W r x
    have h := congrArg (fun f ↦ f.hom.app W t) (hsmul M)
    change (n.hom.app M).hom.app W
      (@SMul.smul (((constantSheaf K CommRingCat.{u}).obj B).obj.obj W)
        ((p.right.obj M).val.obj W) inferInstance
        ((prod.fst : coefficient K B ⨯ (underlyingModules K B).obj (p.right.obj M) ⟶
          coefficient K B).hom.app W t)
        ((prod.snd : coefficient K B ⨯ (underlyingModules K B).obj (p.right.obj M) ⟶
          (underlyingModules K B).obj (p.right.obj M)).hom.app W t)) =
      @SMul.smul (((constantSheaf K CommRingCat.{u}).obj B).obj.obj W)
        ((q.right.obj M).val.obj W) inferInstance
        ((prod.fst : coefficient K B ⨯ (underlyingModules K B).obj (q.right.obj M) ⟶
          coefficient K B).hom.app W
            ((prod.map (𝟙 (coefficient K B)) (n.hom.app M)).hom.app W t))
        ((prod.snd : coefficient K B ⨯ (underlyingModules K B).obj (q.right.obj M) ⟶
          (underlyingModules K B).obj (q.right.obj M)).hom.app W
            ((prod.map (𝟙 (coefficient K B)) (n.hom.app M)).hom.app W t)) at h
    erw [prodMap_fst_apply, prodMap_snd_apply] at h
    dsimp only [t] at h
    erw [sectionPair_fst, sectionPair_snd] at h
    exact h
  let η : p.right ⟶ q.right :=
    { app := fun M ↦ linearLift (n.hom.app M) (ha M) (hs M)
      naturality := fun {M N} f ↦ by
        apply (underlyingModules K B).map_injective
        change (underlyingModules K B).map (p.right.map f) ≫ n.hom.app N =
          n.hom.app M ≫ (underlyingModules K B).map (q.right.map f)
        exact n.hom.naturality f }
  have hi (M : Modules J B) : IsIso (η.app M) := by
    have : IsIso ((underlyingModules K B).map (η.app M)) := by
      change IsIso (n.hom.app M)
      infer_instance
    exact isIso_of_reflects_iso _ (underlyingModules K B)
  refine ⟨NatIso.ofComponents (fun M ↦ asIso (η.app M)) (fun f ↦ η.naturality f), ?_⟩
  intro M
  change n.hom.app M ≫ q.rightUnderlying.hom.app M = _
  rw [hn]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private lemma extensionPure_restrict (M : Modules J A) {W V : Cᵒᵖ} (i : W ⟶ V)
    (b : ((constantSheaf J CommRingCat.{u}).obj B).obj.obj W) (m : M.val.obj W) :
    ((extension J a).obj M).val.map i (extensionPure J a M W b m) =
      extensionPure J a M V (((constantSheaf J CommRingCat.{u}).obj B).obj.map i b)
        (M.val.map i m) := by
  have h := PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (RingedTensor.ringSheaf ((constantSheaf J CommRingCat.{u}).obj B)).obj)).unit.app
        (changeOfRingsPresheaf.{u, u, u} ((constantSheaf J CommRingCat.{u}).map a) M)) i
    (b ⊗ₜ[((constantSheaf J CommRingCat.{u}).obj A).obj.obj W,
      (((constantSheaf J CommRingCat.{u}).map a).hom.app W).hom] m)
  have ht := SheafOfModules.tensorRestriction_tmul
    ((constantSheaf J CommRingCat.{u}).map a) M i b m
  exact (congrArg
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (RingedTensor.ringSheaf ((constantSheaf J CommRingCat.{u}).obj B)).obj)).unit.app
        (changeOfRingsPresheaf.{u, u, u} ((constantSheaf J CommRingCat.{u}).map a) M)).app V)
    ht).symm.trans h |>.symm

private def extensionPairing (M : Modules J A) :
    coefficient J B ⨯ (underlyingModules J A).obj M ⟶
      (underlyingModules J B).obj ((extension J a).obj M) :=
  fromProd _ _ ≫
    ⟨{ app := fun W ↦ ↾(fun t ↦ extensionPure J a M W t.1 t.2)
       naturality := by
         intro W V i
         ext t
         exact (extensionPure_restrict M i t.1 t.2).symm }⟩

private lemma extensionPairing_spec (M : Modules J A) :
    IsScalarPairing J a M (extensionPairing M) := by
  intro W t
  rfl

private lemma pathNormalized (p : Path a J K) (M : Modules J A)
    (Z : Sheaf J (Type u)) (b : Z ⟶ coefficient J B)
    (m : Z ⟶ (underlyingModules J A).obj M)
    (z : Z ⟶ (underlyingModules J B).obj ((extension J a).obj M))
    (h : ∀ W t, z.hom.app W t = extensionPure J a M W
      (b.hom.app W t) (m.hom.app W t)) :
    ∀ W t, (p.inverse.map z ≫ p.rightUnderlying.inv.app ((extension J a).obj M) ≫
      (underlyingModules K B).map (p.comparison.hom.app M)).hom.app W t =
      extensionPure K a (p.left.obj M) W
        ((p.inverse.map b ≫ p.rightCoefficient.hom).hom.app W t)
        ((p.inverse.map m ≫ p.leftUnderlying.inv.app M).hom.app W t) := by
  induction p with
  | nil =>
    simpa [Path.left, Path.right, Path.inverse, Path.leftUnderlying, Path.rightUnderlying,
      Path.rightCoefficient, Path.comparison] using h
  | cons s p ih =>
    have hh := ih (s.left.modules.obj M) (s.inverse.obj Z)
      (s.inverse.map b ≫ s.right.ringUnderlying.hom)
      (s.inverse.map m ≫ s.left.moduleUnderlying.inv.app M)
      (s.inverse.map z ≫ s.right.moduleUnderlying.inv.app ((extension _ a).obj M) ≫
        (underlyingModules _ B).map (s.comparison.hom.app M))
      (s.normalized M Z b m z h)
    have hn := p.rightUnderlying.inv.naturality (s.comparison.hom.app M)
    simp only [Functor.map_comp, Category.assoc] at hh
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    erw [reassoc_of% hn] at hh
    simpa [Path.left, Path.right, Path.inverse, Path.comparison, Path.leftUnderlying,
      Path.rightUnderlying, Path.rightCoefficient, Functor.map_comp, Category.assoc] using hh

private lemma extension_hom_ext (M : Modules J A) (H : Modules J B)
    {f g : (extension J a).obj M ⟶ H}
    (h : ∀ W b m, f.val.app W (extensionPure J a M W b m) =
      g.val.app W (extensionPure J a M W b m)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (RingedTensor.ringSheaf ((constantSheaf J CommRingCat.{u}).obj B)).obj)
  change @Eq
    ((PresheafOfModules.sheafification
      (𝟙 (RingedTensor.ringSheaf ((constantSheaf J CommRingCat.{u}).obj B)).obj)).obj
        (changeOfRingsPresheaf.{u, u, u} ((constantSheaf J CommRingCat.{u}).map a) M) ⟶ H) f g
  apply (adj.homEquiv
    (changeOfRingsPresheaf.{u, u, u} ((constantSheaf J CommRingCat.{u}).map a) M) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact h W 1 m

private lemma extension_pairing_ext (M : Modules J A) (H : Modules J B)
    {f g : (extension J a).obj M ⟶ H}
    (h : extensionPairing M ≫ (underlyingModules J B).map f =
      extensionPairing M ≫ (underlyingModules J B).map g) : f = g := by
  apply extension_hom_ext M H
  intro W b m
  have hh := congrArg (fun k ↦ k.hom.app W (sectionPair _ _ W b m)) h
  change f.val.app W (extensionPure J a M W
    ((prod.fst : coefficient J B ⨯ (underlyingModules J A).obj M ⟶ _).hom.app W
      (sectionPair _ _ W b m))
    ((prod.snd : coefficient J B ⨯ (underlyingModules J A).obj M ⟶ _).hom.app W
      (sectionPair _ _ W b m))) = _ at hh
  change _ = g.val.app W (extensionPure J a M W
    ((prod.fst : coefficient J B ⨯ (underlyingModules J A).obj M ⟶ _).hom.app W
      (sectionPair _ _ W b m))
    ((prod.snd : coefficient J B ⨯ (underlyingModules J A).obj M ⟶ _).hom.app W
      (sectionPair _ _ W b m))) at hh
  simpa only [sectionPair_fst, sectionPair_snd] using hh

@[reassoc] private lemma pathPairing (p : Path a J K) (M : Modules J A) :
    p.inverse.map (extensionPairing M) ≫ p.rightUnderlying.inv.app ((extension J a).obj M) ≫
      (underlyingModules K B).map (p.comparison.hom.app M) =
        prodComparison p.inverse _ _ ≫
          prod.map p.rightCoefficient.hom (p.leftUnderlying.inv.app M) ≫
            extensionPairing (p.left.obj M) := by
  exact binaryOfGraph p.inverse _ _ _ _ _
    (fun W b m ↦ extensionPure J a M W b m)
    (fun W b m ↦ extensionPure K a (p.left.obj M) W b m)
    (extensionPairing_spec M) (extensionPairing_spec (p.left.obj M)) (pathNormalized p M)

private lemma pairing_naturality {M N : Modules J A} (f : M ⟶ N) :
    extensionPairing M ≫ (underlyingModules J B).map ((extension J a).map f) =
      prod.map (𝟙 (coefficient J B)) ((underlyingModules J A).map f) ≫
        extensionPairing N := by
  ext W t
  change ((extension J a).map f).val.app W
    (extensionPure J a M W
      ((prod.fst : coefficient J B ⨯ (underlyingModules J A).obj M ⟶ _).hom.app W t)
      ((prod.snd : coefficient J B ⨯ (underlyingModules J A).obj M ⟶ _).hom.app W t)) =
    extensionPure J a N W
      ((prod.fst : coefficient J B ⨯ (underlyingModules J A).obj N ⟶ _).hom.app W
        ((prod.map (𝟙 (coefficient J B)) ((underlyingModules J A).map f)).hom.app W t))
      ((prod.snd : coefficient J B ⨯ (underlyingModules J A).obj N ⟶ _).hom.app W
        ((prod.map (𝟙 (coefficient J B)) ((underlyingModules J A).map f)).hom.app W t))
  rw [prodMap_fst_apply, prodMap_snd_apply]
  exact extensionPure_map f W _ _

private lemma extensionZero : (extension J a).PreservesZeroMorphisms := by
  have := (RingedTensor.tensorAdjunction
    ((constantSheaf J CommRingCat.{u}).map a)).isLeftAdjoint
  infer_instance

private lemma pathZeroLeft (p : Path a J K) (M : Modules J A)
    (T : Sheaf J (Type u)) (z : T ⟶ (underlyingModules J A).obj M)
    (h : ∀ W t, (show M.val.obj W from z.hom.app W t) = 0) :
    ∀ W t, (show (p.left.obj M).val.obj W from
      (p.inverse.map z ≫ p.leftUnderlying.inv.app M).hom.app W t) = 0 := by
  induction p with
  | nil => simpa [Path.left, Path.inverse, Path.leftUnderlying] using h
  | cons s p ih =>
    have hh := ih (s.left.modules.obj M) (s.inverse.obj T)
      (s.inverse.map z ≫ s.left.moduleUnderlying.inv.app M) (s.left.moduleZero M T z h)
    simpa [Path.left, Path.inverse, Path.leftUnderlying, Functor.map_comp,
      Category.assoc] using hh

private lemma pathLeftZero (p : Path a J K) : p.left.PreservesZeroMorphisms := by
  refine ⟨?_⟩
  intro M N
  ext W x
  have h := pathZeroLeft p N ((underlyingModules J A).obj M)
    ((underlyingModules J A).map (0 : M ⟶ N)) (fun _ _ ↦ rfl) W
    ((p.leftUnderlying.hom.app M).hom.app W x)
  have hn := p.leftUnderlying.inv.naturality (0 : M ⟶ N)
  change p.inverse.map ((underlyingModules J A).map (0 : M ⟶ N)) ≫
    p.leftUnderlying.inv.app N = p.leftUnderlying.inv.app M ≫
      (underlyingModules K A).map (p.left.map (0 : M ⟶ N)) at hn
  rw [hn] at h
  have hi := congrArg (fun k ↦ k.hom.app W x) (p.leftUnderlying.hom_inv_id_app M)
  change (p.leftUnderlying.inv.app M).hom.app W
    ((p.leftUnderlying.hom.app M).hom.app W x) = x at hi
  change (p.left.map (0 : M ⟶ N)).val.app W
    ((p.leftUnderlying.inv.app M).hom.app W
      ((p.leftUnderlying.hom.app M).hom.app W x)) = 0 at h
  rw [hi] at h
  exact h

private lemma pathZeroRight (p : Path a J K) (M : Modules J B)
    (T : Sheaf J (Type u)) (z : T ⟶ (underlyingModules J B).obj M)
    (h : ∀ W t, (show M.val.obj W from z.hom.app W t) = 0) :
    ∀ W t, (show (p.right.obj M).val.obj W from
      (p.inverse.map z ≫ p.rightUnderlying.inv.app M).hom.app W t) = 0 := by
  induction p with
  | nil => simpa [Path.right, Path.inverse, Path.rightUnderlying] using h
  | cons s p ih =>
    have hh := ih (s.right.modules.obj M) (s.inverse.obj T)
      (s.inverse.map z ≫ s.right.moduleUnderlying.inv.app M) (s.right.moduleZero M T z h)
    simpa [Path.right, Path.inverse, Path.rightUnderlying, Functor.map_comp,
      Category.assoc] using hh

private lemma pathRightZero (p : Path a J K) : p.right.PreservesZeroMorphisms := by
  refine ⟨?_⟩
  intro M N
  ext W x
  have h := pathZeroRight p N ((underlyingModules J B).obj M)
    ((underlyingModules J B).map (0 : M ⟶ N)) (fun _ _ ↦ rfl) W
    ((p.rightUnderlying.hom.app M).hom.app W x)
  have hn := p.rightUnderlying.inv.naturality (0 : M ⟶ N)
  change p.inverse.map ((underlyingModules J B).map (0 : M ⟶ N)) ≫
    p.rightUnderlying.inv.app N = p.rightUnderlying.inv.app M ≫
      (underlyingModules K B).map (p.right.map (0 : M ⟶ N)) at hn
  rw [hn] at h
  have hi := congrArg (fun k ↦ k.hom.app W x) (p.rightUnderlying.hom_inv_id_app M)
  change (p.rightUnderlying.inv.app M).hom.app W
    ((p.rightUnderlying.hom.app M).hom.app W x) = x at hi
  change (p.right.map (0 : M ⟶ N)).val.app W
    ((p.rightUnderlying.inv.app M).hom.app W
      ((p.rightUnderlying.hom.app M).hom.app W x)) = 0 at h
  rw [hi] at h
  exact h

private lemma pathPairing_ext (p : Path a J K) (M : Modules J A) (H : Modules K B)
    {f g : p.right.obj ((extension J a).obj M) ⟶ H}
    (h : p.inverse.map (extensionPairing M) ≫
        p.rightUnderlying.inv.app ((extension J a).obj M) ≫ (underlyingModules K B).map f =
      p.inverse.map (extensionPairing M) ≫
        p.rightUnderlying.inv.app ((extension J a).obj M) ≫ (underlyingModules K B).map g) :
    f = g := by
  have := pathLimits p
  apply (cancel_epi (p.comparison.inv.app M)).mp
  apply extension_pairing_ext (p.left.obj M) H
  apply (cancel_epi (prodComparison p.inverse _ _ ≫
    prod.map p.rightCoefficient.hom (p.leftUnderlying.inv.app M))).mp
  have hf := congrArg (fun k ↦ k ≫
    (underlyingModules K B).map (p.comparison.inv.app M ≫ f)) (pathPairing p M)
  have hg := congrArg (fun k ↦ k ≫
    (underlyingModules K B).map (p.comparison.inv.app M ≫ g)) (pathPairing p M)
  simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app] at hf hg
  exact hf.symm.trans (h.trans hg)

private lemma scalarSquare (p q : Path a J K) (θ : p.inverse ≅ q.inverse)
    (θA : p.left ≅ q.left) (θB : p.right ≅ q.right)
    (hA : ∀ M, (underlyingModules K A).map (θA.hom.app M) ≫ q.leftUnderlying.hom.app M =
      p.leftUnderlying.hom.app M ≫ θ.hom.app ((underlyingModules J A).obj M))
    (hB : ∀ M, (underlyingModules K B).map (θB.hom.app M) ≫ q.rightUnderlying.hom.app M =
      p.rightUnderlying.hom.app M ≫ θ.hom.app ((underlyingModules J B).obj M))
    (M : Modules J A) :
    θB.hom.app ((extension J a).obj M) ≫ q.comparison.hom.app M =
      p.comparison.hom.app M ≫ (extension K a).map (θA.hom.app M) := by
  have ha : p.leftUnderlying.inv.app M ≫ (underlyingModules K A).map (θA.hom.app M) =
      θ.hom.app ((underlyingModules J A).obj M) ≫ q.leftUnderlying.inv.app M := by
    apply (cancel_mono (q.leftUnderlying.hom.app M)).mp
    simp only [Category.assoc, hA, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      ]
    erw [Category.comp_id]
  have hb : p.rightUnderlying.inv.app ((extension J a).obj M) ≫
      (underlyingModules K B).map (θB.hom.app ((extension J a).obj M)) =
      θ.hom.app ((underlyingModules J B).obj ((extension J a).obj M)) ≫
        q.rightUnderlying.inv.app ((extension J a).obj M) := by
    apply (cancel_mono (q.rightUnderlying.hom.app ((extension J a).obj M))).mp
    simp only [Category.assoc, hB, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      ]
    erw [Category.comp_id]
  apply pathPairing_ext p M
  simp only [Functor.map_comp]
  have hb' := congrArg (fun k ↦ p.inverse.map (extensionPairing M) ≫ k ≫
    (underlyingModules K B).map (q.comparison.hom.app M)) hb
  simp only [Category.assoc] at hb'
  rw [hb']
  have hn := θ.hom.naturality (extensionPairing (a := a) M)
  rw [← Category.assoc, ← Category.assoc, hn, Category.assoc, Category.assoc,
    pathPairing q M, prodComparison_natural_of_natTrans_assoc]
  have hp := congrArg (fun k ↦ k ≫
    (underlyingModules K B).map ((extension K a).map (θA.hom.app M))) (pathPairing p M)
  simp only [Category.assoc] at hp
  rw [hp]
  rw [pairing_naturality, prod.map_map_assoc, prod.map_map_assoc]
  simp only [coefficientTwoIsoRight, Category.comp_id, ha]

private lemma extensionPure_balance (M : Modules J A) (W : Cᵒᵖ)
    (r : ((constantSheaf J CommRingCat.{u}).obj A).obj.obj W)
    (b : ((constantSheaf J CommRingCat.{u}).obj B).obj.obj W) (m : M.val.obj W) :
    extensionPure J a M W ((((constantSheaf J CommRingCat.{u}).map a).hom.app W r) * b) m =
      extensionPure J a M W b (r • m) := by
  unfold extensionPure
  congr 1
  let := Module.compHom (((constantSheaf J CommRingCat.{u}).obj B).obj.obj W)
    (((constantSheaf J CommRingCat.{u}).map a).hom.app W).hom
  exact TensorProduct.smul_tmul r b m

end Proof

/-- The full scalar compatibility for two specified geometric presentations.

Proof, following the eight steps of the DAG node:
1. Naturality at the terminal and two product projections makes theta cartesian.
2. Express a constant ring as the coproduct of its scalar-labelled terminal summands.
The left adjoints preserve it (left-adjoint-preserves-colimits); naturality at each
inclusion and coproduct uniqueness fix the whole constant ring, and also its map a.
The constant-module result supplies the same normalized coproduct identification.
3. Naturality at addition, zero, negation and scalar action gives linear component
maps and linear inverses. Naturality on module maps gives the two module natural isos.
4. Apply theta naturality to the actual universal balanced pairing. The product
identity of step 1 gives the prequotient equation. Linearity gives the balancing
relation for b tensor theta(m).
5. Each stipulated comparison sends the inverse-image pairing to the target pairing
by its generalized normalization, with the entire product sheaf as test sheaf.
The two sides of the desired square therefore agree on that pairing. Cancel the
comparison and use tensor uniqueness (ringed-tensor-section-calculus). Existence of
the normalized tensor comparison is the construction dependency.
6. The actual extensionPure uses the module sheafification unit. The sectionwise
balanced map extends uniquely through module sheafification, so these are sheaf
equalities, even when a section is only locally a sum of pure tensors.
7. For a cons path the expanded comparison first carries the first inverse-image
pairing to the intermediate pairing and then to the final pairing. Hence it has
the same normalization. Induction, including the identity path, gives the square
for the iterated maps, with the ordinary associators displayed in Path.comparison.
8. Apply the square degreewise. Naturality at each differential makes the maps
chain maps; at each component of any chain map it gives complex naturality.
Source: Stacks Project, Modules on Sites, 03EK/03EL; Sites, 00YV and 0H7J
(blueprint: lem-sfb-geometric-two-iso-scalar-pairing). -/
theorem geometric_two_iso_scalar_pairing (p q : Path a J K) (θ : p.inverse ≅ q.inverse) :
    ∃ θA : p.left ≅ q.left, ∃ θB : p.right ≅ q.right,
      (∀ M : Modules J A,
        (underlyingModules K A).map (θA.hom.app M) ≫ q.leftUnderlying.hom.app M =
          p.leftUnderlying.hom.app M ≫ θ.hom.app ((underlyingModules J A).obj M)) ∧
      (∀ M : Modules J B,
        (underlyingModules K B).map (θB.hom.app M) ≫ q.rightUnderlying.hom.app M =
          p.rightUnderlying.hom.app M ≫ θ.hom.app ((underlyingModules J B).obj M)) ∧
      (θ.hom.app (coefficient J A) ≫ q.leftCoefficient.hom = p.leftCoefficient.hom) ∧
      (θ.hom.app (coefficient J B) ≫ q.rightCoefficient.hom = p.rightCoefficient.hom) ∧
      (p.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map
          ((constantSheaf J CommRingCat.{u}).map a)) ≫ p.rightCoefficient.hom =
        p.leftCoefficient.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map
            ((constantSheaf K CommRingCat.{u}).map a)) ∧
      (q.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map
          ((constantSheaf J CommRingCat.{u}).map a)) ≫ q.rightCoefficient.hom =
        q.leftCoefficient.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map
            ((constantSheaf K CommRingCat.{u}).map a)) ∧
      (∀ M : Modules J A,
        θB.hom.app ((extension J a).obj M) ≫ q.comparison.hom.app M =
          p.comparison.hom.app M ≫ (extension K a).map (θA.hom.app M)) ∧
      (∀ (M : Modules J A)
        (b : coefficient J B ⨯ (underlyingModules J A).obj M ⟶
          (underlyingModules J B).obj ((extension J a).obj M)),
        IsScalarPairing J a M b →
        (p.inverse.map b ≫ θ.hom.app ((underlyingModules J B).obj ((extension J a).obj M)) =
          θ.hom.app (coefficient J B ⨯ (underlyingModules J A).obj M) ≫ q.inverse.map b) ∧
        (θ.hom.app (coefficient J B ⨯ (underlyingModules J A).obj M) ≫
            prodComparison q.inverse _ _ =
          prodComparison p.inverse _ _ ≫
            prod.map (θ.hom.app (coefficient J B))
              (θ.hom.app ((underlyingModules J A).obj M)))) ∧
      (∀ (M : Modules J A) (W : Dᵒᵖ)
        (b : ((constantSheaf K CommRingCat.{u}).obj B).obj.obj W)
        (m : (p.left.obj M).val.obj W),
        ((extension K a).map (θA.hom.app M)).val.app W
          (extensionPure K a (p.left.obj M) W b m) =
            extensionPure K a (q.left.obj M) W b ((θA.hom.app M).val.app W m)) ∧
      (∀ (M : Modules J A) (W : Dᵒᵖ)
        (r : ((constantSheaf K CommRingCat.{u}).obj A).obj.obj W)
        (b : ((constantSheaf K CommRingCat.{u}).obj B).obj.obj W)
        (m : (p.left.obj M).val.obj W),
        extensionPure K a (q.left.obj M) W
            ((((constantSheaf K CommRingCat.{u}).map a).hom.app W r) * b)
            ((θA.hom.app M).val.app W m) =
          extensionPure K a (q.left.obj M) W b ((θA.hom.app M).val.app W (r • m))) ∧
      (∃ hF : (extension J a ⋙ p.right).PreservesZeroMorphisms,
        ∃ hL : (q.left ⋙ extension K a).PreservesZeroMorphisms,
        @NatTrans.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _ hF hL
            (Functor.whiskerLeft (extension J a) θB.hom ≫ q.comparison.hom)
            (ComplexShape.up ℤ) =
          @NatTrans.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _ hF hL
            (p.comparison.hom ≫ Functor.whiskerRight θA.hom (extension K a))
            (ComplexShape.up ℤ)) := by
  obtain ⟨θA, hA⟩ := moduleTwoIsoLeft p q θ
  obtain ⟨θB, hB⟩ := moduleTwoIsoRight p q θ
  refine ⟨θA, θB, hA, hB, coefficientTwoIsoLeft p q θ,
    coefficientTwoIsoRight p q θ, pathCoefficientMap p, pathCoefficientMap q,
    scalarSquare p q θ θA θB hA hB, ?_, ?_, ?_, ?_⟩
  · intro M b _
    exact ⟨θ.hom.naturality b, prodComparison_natural_of_natTrans θ.hom⟩
  · intro M W b m
    exact extensionPure_map (θA.hom.app M) W b m
  · intro M W r b m
    simpa only [map_smul] using
      extensionPure_balance (q.left.obj M) W r b ((θA.hom.app M).val.app W m)
  · have := extensionZero (J := J) (a := a)
    have := extensionZero (J := K) (a := a)
    have := pathRightZero p
    have := pathLeftZero q
    have hF : (extension J a ⋙ p.right).PreservesZeroMorphisms := inferInstance
    have hL : (q.left ⋙ extension K a).PreservesZeroMorphisms := inferInstance
    refine ⟨hF, hL, ?_⟩
    have h : Functor.whiskerLeft (extension J a) θB.hom ≫ q.comparison.hom =
        p.comparison.hom ≫ Functor.whiskerRight θA.hom (extension K a) := by
      apply NatTrans.ext
      funext M
      exact scalarSquare p q θ θA θB hA hB M
    exact congrArg (fun t ↦ NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)) h

end CategoryTheory.GeometricScalar
