/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Sheaf.Paper.RingedTopoiTensorComparisonData
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import WeilConjectures.SixFunctors.OpenClosed.Vanishing
import WeilConjectures.SixFunctors.OpenClosed.Points
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-!
# Closed constant coefficient tensors on the small étale site

Source: `literature/stacks-project/etale-cohomology.tex`, Tag 03Q1 (blueprint:
`lem-pur-etale-closed-constant-tensor`).

## Main definitions

* `closedConstantTensorMap`: multiplication after restriction to the intersection.
* `closedConstantSupportChange`: canonical maps comparing chosen fiber products.
* `closedConstantDerivedTensorMap`: multiplication through the flat degree-zero computation.
* `closedConstantDerivedPullbackMap`: inverse image on the degree-zero support model.

## Main statements

* `closedConstantModule_flat`: geometric-stalk flatness for every closed support.
* `closedConstantTensor`: invertibility and all ordinary and derived coherence clauses.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uB

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry
namespace Etale

open Scheme

attribute [local instance] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

/-- The constant module sheaf of a ring on a small étale site.
Source: `def-weil-pbc-constant-sheaf`; blueprint `def-weil-pbc-constant-sheaf`. -/
noncomputable def constantModuleSheaf (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- The ordinary direct image of the constant module along a scheme map.
Source: Stacks Tag 03QP(1); blueprint `def-weil-pbc-direct-image`. -/
noncomputable def closedConstantModule (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (lowerStar (ModuleCat.{u + 1} A) i).obj (constantModuleSheaf A C)

/-- The support morphism of the scheme-theoretic intersection of two closed subschemes.
Source: Stacks Tag 01JA; blueprint `def-pc-fibre-product`. -/
noncomputable def intersectionSupport {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) :
    pullback i j ⟶ X := pullback.fst i j ≫ i

/-- Scheme-theoretic intersections of closed immersions are closed immersions.
Source: base-change stability of closed immersions; blueprint
`lem-weil-pbc-closed-immersion-base-change`. -/
instance intersectionSupport_isClosedImmersion {C D X : Scheme.{u}}
    (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (intersectionSupport i j) := by
  dsimp [intersectionSupport]
  infer_instance

/-- Canonical restriction of constant sections to a closed intersection.
It is the mate of the constant-sheaf comparison under the inverse-image/direct-image
adjunction, with the pullback pasting comparison included. Source: Tag 03Q1(3);
blueprint `lem-weil-pbc-constant-module-pushforward-functoriality`. -/
noncomputable def closedConstantRestriction (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantModule A i ⟶ closedConstantModule A (intersectionSupport i j) :=
  constantModulePushforwardMap A (ModuleCat.of A A) i (intersectionSupport i j)
    (pullback.fst i j) (by simp [intersectionSupport, pullback.condition])

/-- The corresponding restriction from the second support to the same intersection.
Source: Tag 03Q1(3); blueprint `lem-weil-pbc-constant-module-pushforward-functoriality`. -/
noncomputable def closedConstantRestriction₂ (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantModule A j ⟶ closedConstantModule A (intersectionSupport i j) :=
  constantModulePushforwardMap A (ModuleCat.of A A) j (intersectionSupport i j)
    (pullback.snd i j) (by simp [intersectionSupport, pullback.condition])

/-- Pointwise multiplication on the constant module, transported through the sheaf tensor
unitors. Source: Stacks Tag 03EL; blueprint `def-pur-sheaf-tensor-product`. -/
noncomputable def constantModuleMultiplication (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    constantModuleSheaf A T ⊗ constantModuleSheaf A T ⟶ constantModuleSheaf A T :=
  (tensorIso (Iso.refl _) (Iso.refl _)).hom ≫ (λ_ _).hom

/-- The canonical ordinary tensor map, obtained from the two restriction maps and the lax
monoidal structure on direct image. This is the specified multiplication on local constants,
not an arbitrary morphism. Source: Tags 03EL and 03Q1; blueprint `def-pur-sheaf-tensor-product`. -/
noncomputable def closedConstantTensorMap (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantModule A i ⊗ closedConstantModule A j ⟶
      closedConstantModule A (intersectionSupport i j) :=
  tensorHom (closedConstantRestriction A i j) (closedConstantRestriction₂ A i j) ≫
    (Functor.LaxMonoidal.μ
      (lowerStar (ModuleCat.{u + 1} A) (intersectionSupport i j)) _ _) ≫
    (lowerStar (ModuleCat.{u + 1} A) (intersectionSupport i j)).map
      (constantModuleMultiplication A (pullback i j))

/-- The pullback-section map before taking its adjoint. It is defined by precomposition on
constant sections and the canonical lower-star composition comparison. Source: Tag 03Q1(3);
blueprint `lem-weil-pbc-constant-module-pushforward-functoriality`. -/
noncomputable def closedConstantPullbackMap (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    closedConstantModule A i ⟶
      (lowerStar (ModuleCat.{u + 1} A) v).obj
        (closedConstantModule A (pullback.fst v i)) := by
  let q := pullback.snd v i
  let f₂ : pullback v i ⟶ X := pullback.fst v i ≫ v
  have hq : q ≫ i = f₂ := pullback.condition.symm
  exact constantModulePushforwardMap A (ModuleCat.of A A) i f₂ q hq ≫
    (lowerStarComp (ModuleCat.{u + 1} A) (pullback.fst v i) v f₂ rfl).inv.app _

/-- The canonical section map from the constant module on the base to a closed direct image.
It is the recorded transition map for `𝟙 X` and `i`, hence carries the constant section to
its restriction. Source: Stacks Tag 03Q1(3); blueprint
`lem-weil-pbc-constant-module-pushforward-functoriality`. -/
noncomputable def closedConstantSectionMap (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    constantModuleSheaf A X ⟶ closedConstantModule A i :=
  (lowerStarId (ModuleCat.{u + 1} A) X).inv.app _ ≫
    constantModulePushforwardMap A (ModuleCat.of A A) (𝟙 X) i i (by simp)

/-- The canonical adjoint pullback map, defined as the mate of
`closedConstantPullbackMap`. Source: Tag 03Q1(3);
blueprint `prop-weil-pbc-inverse-image-modules-exact`. -/
noncomputable def closedConstantPullbackAdjoint (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    (upperStar (ModuleCat.{u + 1} A) v).obj (closedConstantModule A i) ⟶
      closedConstantModule A (pullback.fst v i) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ |>.symm
    (closedConstantPullbackMap A i v)

/-- Compatibility of the specified pullback adjoint with the canonical constant section.
The displayed constant-sheaf comparison is part of the equation, so this does not merely assert
that some section map exists. Source: Stacks Tag 03Q1(3); blueprint
`prop-weil-pbc-inverse-image-modules-exact`. -/
def closedConstantPullbackRestriction (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] : Prop :=
  (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).hom.app (ModuleCat.of A A) ≫
      closedConstantSectionMap A (pullback.fst v i) =
    (upperStar (ModuleCat.{u + 1} A) v).map (closedConstantSectionMap A i) ≫
      closedConstantPullbackAdjoint A i v


/-- Canonical change of support, contravariant in a morphism over the base.
Source: Stacks Tag 03Q1(3); (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantSupportChange (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    (g : D ⟶ C) (h : g ≫ i = j) : closedConstantModule A i ⟶ closedConstantModule A j :=
  constantModulePushforwardMap A (ModuleCat.of A A) i j g h

/-- The support identification for the identity pullback, induced by its universal lift.
Source: Stacks Tag 03Q1(3); (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantIdentitySupportMap (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) :
    closedConstantModule A (pullback.fst (𝟙 X) i) ⟶ closedConstantModule A i :=
  closedConstantSupportChange A _ _ (pullback.lift i (𝟙 C) (by simp)) (by simp)

/-- The canonical support comparison for successive base changes.
Source: Stacks Tag 03Q1(3); (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantCompositionSupportMap (A : Type (u + 1)) [CommRing A]
    {C X X' X'' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) (w : X'' ⟶ X') :
    closedConstantModule A (pullback.fst (w ≫ v) i) ⟶
      closedConstantModule A (pullback.fst w (pullback.fst v i)) :=
  closedConstantSupportChange A _ _
    (pullback.lift (pullback.fst w (pullback.fst v i))
      (pullback.snd w (pullback.fst v i) ≫ pullback.snd v i)
      (by
        rw [← Category.assoc, pullback.condition, Category.assoc,
          pullback.condition, Category.assoc]))
    (by simp)

/-- The support interchange map induced by the canonical pullback symmetry.
Source: Stacks Tag 03EL; (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantSymmetrySupportMap (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) :
    closedConstantModule A (intersectionSupport j i) ⟶
      closedConstantModule A (intersectionSupport i j) :=
  closedConstantSupportChange A _ _ (pullbackSymmetry i j).hom
    (by simp [intersectionSupport, pullback.condition])

/-- The reassociation of triple supports, given by the universal pullback lifts.
Source: Stacks Tag 03EL; (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantAssociativitySupportMap (A : Type (u + 1)) [CommRing A]
    {C D E X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X) :
    closedConstantModule A (intersectionSupport (intersectionSupport i j) k) ⟶
      closedConstantModule A (intersectionSupport i (intersectionSupport j k)) := by
  let a := pullback.fst i (intersectionSupport j k)
  let b := pullback.snd i (intersectionSupport j k)
  let g : pullback i (intersectionSupport j k) ⟶ pullback i j :=
    pullback.lift a (b ≫ pullback.fst j k)
    (by
      dsimp only [a, b]
      simpa only [intersectionSupport, Category.assoc] using
        (pullback.condition (f := i) (g := intersectionSupport j k)))
  let q : pullback i (intersectionSupport j k) ⟶
      pullback (intersectionSupport i j) k :=
    pullback.lift g (b ≫ pullback.snd j k)
    (by
      calc
        g ≫ intersectionSupport i j = a ≫ i := by simp [g, intersectionSupport]
        _ = b ≫ intersectionSupport j k := pullback.condition
        _ = (b ≫ pullback.snd j k) ≫ k := by
          simpa only [intersectionSupport, Category.assoc] using
            congrArg (fun f : pullback j k ⟶ X ↦ b ≫ f)
              (pullback.condition (f := j) (g := k)))
  exact closedConstantSupportChange A _ _ q
    (by simp [q, g, a, intersectionSupport])

/-- The base-change identification of an intersection, induced by the universal lifts.
Source: Stacks Tags 03Q1 and 03EL; (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantBaseChangeSupportMap (A : Type (u + 1)) [CommRing A]
    {C D X X' : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (v : X' ⟶ X) :
    closedConstantModule A (pullback.fst v (intersectionSupport i j)) ⟶
      closedConstantModule A (intersectionSupport (pullback.fst v i) (pullback.fst v j)) := by
  let a := pullback.fst (pullback.fst v i) (pullback.fst v j)
  let b := pullback.snd (pullback.fst v i) (pullback.fst v j)
  let g : pullback (pullback.fst v i) (pullback.fst v j) ⟶ pullback i j :=
    pullback.lift (a ≫ pullback.snd v i) (b ≫ pullback.snd v j)
    (by
      dsimp only [a, b]
      rw [Category.assoc, ← pullback.condition, ← Category.assoc,
        pullback.condition, Category.assoc, pullback.condition, Category.assoc])
  let q : pullback (pullback.fst v i) (pullback.fst v j) ⟶
      pullback v (intersectionSupport i j) :=
    pullback.lift (a ≫ pullback.fst v i) g
    (by
      dsimp only [g, intersectionSupport]
      rw [Category.assoc, pullback.lift_fst_assoc, Category.assoc, pullback.condition])
  exact closedConstantSupportChange A _ _ q
    (by simp [q, a, intersectionSupport])

/-- Identity and composition laws with canonical changes of support explicitly composed.
Source: Tag 03Q1(3); (blueprint: lem-pur-etale-closed-constant-tensor). -/
def closedConstantPullbackCoherence (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] : Prop :=
  closedConstantPullbackAdjoint A i (𝟙 X) ≫ closedConstantIdentitySupportMap A i =
    (upperStarId (ModuleCat.{u + 1} A) X).hom.app (closedConstantModule A i) ∧
  ∀ {X' X'' : Scheme.{u}} (v : X' ⟶ X) (w : X'' ⟶ X'),
    closedConstantPullbackAdjoint A i (w ≫ v) ≫
        closedConstantCompositionSupportMap A i v w =
      (upperStarComp (ModuleCat.{u + 1} A) w v).hom.app (closedConstantModule A i) ≫
        (upperStar (ModuleCat.{u + 1} A) w).map (closedConstantPullbackAdjoint A i v) ≫
        closedConstantPullbackAdjoint A (pullback.fst v i) w

/-- The normalized tensor pullback square with its canonical support comparison.
Source: Tag 03EL; (blueprint: lem-pur-etale-closed-constant-tensor). -/
def closedConstantTensorPullbackSquare (A : Type (u + 1)) [CommRing A]
    {C D X X' : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (v : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] : Prop :=
  (upperStar (ModuleCat.{u + 1} A) v).map (closedConstantTensorMap A i j) ≫
      closedConstantPullbackAdjoint A (intersectionSupport i j) v ≫
      closedConstantBaseChangeSupportMap A i j v =
    Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) v) _ _ ≫
      tensorHom (closedConstantPullbackAdjoint A i v) (closedConstantPullbackAdjoint A j v) ≫
      closedConstantTensorMap A (pullback.fst v i) (pullback.fst v j)

/-- Ordinary associativity and symmetry with explicit canonical support changes.
Source: Tags 03EL and 03Q1; (blueprint: lem-pur-etale-closed-constant-tensor). -/
def closedConstantTensorCoherence (A : Type (u + 1)) [CommRing A]
    {C D E X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k] : Prop :=
  tensorHom (closedConstantTensorMap A i j) (𝟙 _) ≫
      closedConstantTensorMap A (intersectionSupport i j) k ≫
      closedConstantAssociativitySupportMap A i j k =
    (α_ _ _ _).hom ≫ tensorHom (𝟙 _) (closedConstantTensorMap A j k) ≫
      closedConstantTensorMap A i (intersectionSupport j k) ∧
  (β_ _ _).hom ≫ closedConstantTensorMap A j i ≫
      closedConstantSymmetrySupportMap A i j = closedConstantTensorMap A i j

attribute [local irreducible] closedConstantModule closedConstantTensorMap
  closedConstantPullbackAdjoint

/-- Closed constant direct images are flat, including empty supports and the zero ring.
Source: Stacks Tags 03Q1 and 03PU; (blueprint: lem-pur-etale-closed-constant-tensor).
Proof: a geometric stalk is A on the closed support and zero off it. Tensoring thus
preserves short exact stalk sequences; exactness and conservativity of stalks reflect
this to sheaves. This is step 6 of the node's proof. -/
theorem closedConstantModule_flat (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ObjectProperty.flat (closedConstantModule A i) := by
  rw [closedConstantModule]
  have hfree : ObjectProperty.flat (ModuleCat.of A A) :=
    (ModuleCat.flat_iff_flat _).2 (inferInstance : Module.Flat A A)
  apply (flat_iff_forall_flat_sheafFiber_obj _).2
  intro Ω _ _ s
  apply ObjectProperty.prop_of_iso ObjectProperty.flat
    (((pointSmallEtale s).uliftSheafFiberIso (ModuleCat.{u + 1} A)).symm.app _)
  by_cases hs : s.base (IsLocalRing.closedPoint Ω) ∈ Set.range i.base
  · obtain ⟨t, ht, _⟩ := IsClosedImmersion.existsUnique_fac_of_field i s hs
    subst s
    let e := (lowerStarCompSheafFiberIso (ModuleCat.{u + 1} A) i t).app
      (constantModuleSheaf A C) ≪≫
      ((pointSmallEtale t).uliftSheafFiberIso (ModuleCat.{u + 1} A)).symm.app
        (constantModuleSheaf A C) ≪≫
      (pointSmallEtale t).ulift.{u + 1}.sheafFiberConstantSheafIso (ModuleCat.of A A)
    exact ObjectProperty.prop_of_iso ObjectProperty.flat e.symm hfree
  · let U := i.openComplement
    have hr : Set.range s.base ⊆ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      exact Scheme.range_base_subset_of_closedPoint_mem s hs
    let t := IsOpenImmersion.lift U.ι s hr
    have ht : t ≫ U.ι = s := IsOpenImmersion.lift_fac _ _ _
    have hz := isZero_upperStar_lowerStar_of_disjoint_range
      (ModuleCat.{u + 1} A) U.ι i
      (disjoint_range_of_range_eq_compl U.ι i
        i.range_eq_compl_range_openComplement_ι) (constantModuleSheaf A C)
    have hz' := (pointSmallEtale t).sheafFiber.map_isZero hz
    have e := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) U.ι t).app
      ((lowerStar (ModuleCat.{u + 1} A) i).obj (constantModuleSheaf A C))
    rw [ht] at e
    exact ObjectProperty.flat_of_isZero (hz'.of_iso e.symm)

/-- The degree-zero derived object associated to a supported constant module.
Source: Stacks Tag 06YQ; (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantDerivedModule (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.singleFunctor _ 0).obj (closedConstantModule A i)

/-- Apply an ordinary pairing after the canonical flat degree-zero tensor computation.
The coefficient category is left abstract while composing the two canonical arrows.
Source: Stacks Tag 06YQ; (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantFlatModelMap
    {B : Type uB} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X : Scheme.{u}} (L F G : Sheaf X.smallEtaleTopology B)
    (h : ObjectProperty.flat L) (f : L ⊗ F ⟶ G) :=
  (singleFunctorObjTensorIso (A := B) (X := X) L F h).hom ≫
    (DerivedCategory.singleFunctor _ 0).map f

/-- The canonical derived multiplication on the specified flat degree-zero model.
Source: Stacks Tag 06YQ; (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantDerivedTensorMap (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((DerivedCategory.singleFunctor _ 0).obj (closedConstantModule A i))).obj
        ((DerivedCategory.singleFunctor _ 0).obj (closedConstantModule A j)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        (closedConstantModule A (intersectionSupport i j)) :=
  closedConstantFlatModelMap (B := ModuleCat.{u + 1} A) (X := X)
    (closedConstantModule A i) (closedConstantModule A j)
    (closedConstantModule A (intersectionSupport i j))
    (closedConstantModule_flat A i) (closedConstantTensorMap A i j)

attribute [local irreducible] closedConstantDerivedTensorMap

/-- The derived pullback map of the same supported constant sheaf, using the canonical
commutation of exact inverse image with the single functor and the specified b map.
Source: Stacks Tag 03Q1(3); (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantDerivedPullbackMap (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor).obj
      ((DerivedCategory.singleFunctor _ 0).obj (closedConstantModule A i)) ⟶
        (DerivedCategory.singleFunctor _ 0).obj
          (closedConstantModule A (pullback.fst v i)) :=
  (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map (closedConstantPullbackAdjoint A i v)

attribute [local irreducible] closedConstantDerivedPullbackMap

/-- Map two arrows with the actual derived tensor bifunctor, without synthesizing a
second monoidal instance on the derived category.
Source: Stacks Tag 06YQ; (blueprint: lem-pur-etale-closed-constant-tensor). -/
noncomputable def closedConstantDerivedPairMap
    {B : Type uB} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) {K K' L L' : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensor B X).obj K).obj L ⟶ ((derivedTensor B X).obj K').obj L' :=
  ((derivedTensor B X).map f).app L ≫ ((derivedTensor B X).obj K').map g

/-- Derived associativity and symmetry for the specified canonical multiplication.
Source: Stacks Tags 06YQ and 03EL; (blueprint: lem-pur-etale-closed-constant-tensor). -/
structure ClosedConstantDerivedTensorCoherence (A : Type (u + 1)) [CommRing A]
    {C D E X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k] : Prop where
  associativity : CommSq
    (((derivedTensor (ModuleCat.{u + 1} A) X).map
      (closedConstantDerivedTensorMap A i j)).app _)
    (derivedTensorAssociator (ModuleCat.{u + 1} A) X _ _ _).hom
    (closedConstantDerivedTensorMap A (intersectionSupport i j) k ≫
      (DerivedCategory.singleFunctor _ 0).map (closedConstantAssociativitySupportMap A i j k))
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj _).map
      (closedConstantDerivedTensorMap A j k) ≫
        closedConstantDerivedTensorMap A i (intersectionSupport j k))
  symmetry : (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app _).app _) ≫
    closedConstantDerivedTensorMap A j i ≫
      (DerivedCategory.singleFunctor _ 0).map (closedConstantSymmetrySupportMap A i j) =
        closedConstantDerivedTensorMap A i j

/-- Derived pullback compatibility for the specified multiplication and b maps.
Source: Stacks Tags 06YQ and 03EL; (blueprint: lem-pur-etale-closed-constant-tensor). -/
structure ClosedConstantDerivedTensorPullbackSquare (A : Type (u + 1)) [CommRing A]
    {C D X X' : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (v : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] : Prop where
  commutes : CommSq
    (((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor).map
      (closedConstantDerivedTensorMap A i j))
    (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) v).app _).app _ ≫
      closedConstantDerivedPairMap X' (closedConstantDerivedPullbackMap A i v)
        (closedConstantDerivedPullbackMap A j v))
    (closedConstantDerivedPullbackMap A (intersectionSupport i j) v ≫
      (DerivedCategory.singleFunctor _ 0).map (closedConstantBaseChangeSupportMap A i j v))
    (closedConstantDerivedTensorMap A (pullback.fst v i) (pullback.fst v j))

/-- Closed constant tensors, canonical pullback adjoints, flatness, and all ordinary and
derived coherence clauses. The proof is intentionally postponed at stage 2.
(blueprint: lem-pur-etale-closed-constant-tensor).

The final two proposition structures state the derived associativity, symmetry and
pullback equalities, using `CommSq.w` for the associativity and pullback squares.

The proof follows nine steps: (1) construct the restriction maps by the constant-sheaf
adjunction; (2) compute supported and empty geometric stalks; (3) identify the adjoint
pullback map on stalks; (4) prove identity and composition by adjunction uniqueness;
(5) construct tensor multiplication from restriction and pointwise multiplication;
(6) prove flatness by the identity-or-zero stalk calculation;
(7) verify associativity and symmetry on pure tensors;
(8) verify the pullback square using the normalized lax/oplax tensor comparison; and
(9) pass to degree-zero K-flat derived tensors and their coherence. -/
theorem closedConstantTensor (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) {C D E : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i]
    (j : D ⟶ X) [IsClosedImmersion j]
    (k : E ⟶ X) [IsClosedImmersion k]
    {X' : Scheme.{u}} (v : X' ⟶ X) :
    IsIso (closedConstantPullbackAdjoint A i v) ∧
    IsIso (closedConstantPullbackAdjoint A j v) ∧
    IsIso (closedConstantPullbackAdjoint A (intersectionSupport i j) v) ∧
    closedConstantPullbackRestriction A i v ∧
    closedConstantPullbackRestriction A j v ∧
    closedConstantPullbackRestriction A (intersectionSupport i j) v ∧
    ObjectProperty.flat (closedConstantModule A i) ∧
    ObjectProperty.flat (closedConstantModule A j) ∧
    ObjectProperty.flat (closedConstantModule A (intersectionSupport i j)) ∧
    IsIso (closedConstantTensorMap A i j) ∧
    closedConstantTensorCoherence A i j k ∧
    closedConstantPullbackCoherence A i ∧
    closedConstantPullbackCoherence A j ∧
    closedConstantPullbackCoherence A (intersectionSupport i j) ∧
    closedConstantTensorPullbackSquare A i j v ∧
    IsIso (closedConstantDerivedTensorMap A i j) ∧
    ClosedConstantDerivedTensorCoherence A i j k ∧
    ClosedConstantDerivedTensorPullbackSquare A i j v := by
  sorry

end Etale
end AlgebraicGeometry
