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
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Mathlib.CategoryTheory.Adjunction.Limits

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
  sorry

end CategoryTheory.GeometricScalar
