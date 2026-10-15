/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Paper.ProfiniteTestObjectFunctor
import Sheaf.CategoryTheory.SiteMorphismComposition
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects

/-!
# The geometric inverse image from the profinite point

Source: RefactorInstruction.tex, Section 4, lem:XS and prop:pX, and Section 5,
eq:triangle and thm:alpha (blueprint: lem-weil-pbc-profinite-point-pullback).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The set inverse image is left Kan extension followed by sheafification.
Source: RefactorInstruction, prop:pX
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable abbrev profinitePointSetInverseImage :
    Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology specZ.{u}) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback profiniteToProEt (Type (u + 1))
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)

/-- Geometric inverse image from the profinite point, including the specified monoidal
comparison with the inverse image along every scheme morphism.

Source: RefactorInstruction, lem:XS, prop:pX, eq:triangle, thm:alpha
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (1) Apply the relative profinite test-object theorem at Spec Z to obtain finite
limits and covering preservation, identifying its maps with spectrum of precomposition.
(2) Apply the left-exact site inverse-image tensor theorem to obtain the sheafified Kan
extension adjunction, exactness and strong symmetric monoidality.
(3) The inverse-image composition comparison is the conjugate of the canonical
fibre-product comparison. Uniqueness of adjunction-compatible comparisons gives the
identity and associativity laws, and the site tensor theorem makes it monoidal.
(4) Whisker the comparison for h and the structure morphism by pointUpperStar and use
comp_toSpecZ. This is exactly upperStarFromPointComp, and is natural and monoidal.
(5) Apply it to ring operations to get the ring-sheaf isomorphism. The subsequent
coherence declarations record the identity, composition, linear, derived and square
clauses explicitly. -/
theorem profinite_point_pullback :
    (∀ S : Profinite.{u}, WeaklyEtale (toSpecZ (profiniteToScheme.obj S))) ∧
    PreservesFiniteLimits profiniteToProEt.{u} ∧
    CoverPreserving (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
      profiniteToProEt ∧
    (∀ F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1),
      profiniteToProEt.op.HasLeftKanExtension F) ∧
    (∀ F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1},
      profiniteToProEt.op.HasLeftKanExtension F) ∧
    Nonempty (profinitePointSetInverseImage.{u} ⊣
      profiniteToProEt.sheafPushforwardContinuous (Type (u + 1))
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)) ∧
    PreservesFiniteLimits profinitePointSetInverseImage.{u} ∧
    PreservesColimitsOfSize.{u + 1, u + 1} profinitePointSetInverseImage.{u} ∧
    PreservesFiniteLimits pointUpperStar.{u} ∧
    PreservesFiniteColimits pointUpperStar.{u} ∧
    Nonempty pointUpperStar.{u}.Monoidal ∧
    Nonempty pointUpperStar.{u}.Braided ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      NatTrans.IsMonoidal (upperStarFromPointComp f).hom) := by
  sorry

/-- The point comparisons satisfy identity and composition on abelian sheaves, hence
also on ring sheaves, since all their components preserve ring operations.
Source: RefactorInstruction, eq:triangle and thm:alpha
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (3) Transport inverse-image adjunctions to strictly composed right adjoints and
apply associativity of the unique conjugate comparison; identity follows by comparison
with the identity adjunction. (4) Whisker with pointUpperStar and use comp_toSpecZ.
(5) Naturality at addition, negation, zero, multiplication and one proves that these
same equations are equations of ring maps, not merely maps of underlying sheaves. -/
theorem profinite_point_pullback_coefficient_coherence :
    (∀ (X : Scheme.{u}) (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      (upperStarFromPointComp (𝟙 X)).hom.app Λ =
        (upperStarId Ab.{u + 1} X).hom.app ((upperStarFromPoint X).obj Λ)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      (upperStarComp Ab.{u + 1} f g).hom.app ((upperStarFromPoint Z).obj Λ) ≫
          (upperStar Ab.{u + 1} f).map ((upperStarFromPointComp g).hom.app Λ) ≫
          (upperStarFromPointComp f).hom.app Λ =
        (upperStarFromPointComp (f ≫ g)).hom.app Λ) := by
  sorry

/-- Abelian inverse-image composition is coherent, including both units and every
commutative square. The square map is explicitly the comparison through the common
composite, so it includes noncartesian squares and identity arrows.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tag 03CB
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (3) Fibre-product maps preserve both projections, so their associativity and unit
diagrams commute by the universal property. Conjugate these diagrams using the
inverse-image adjunctions; uniqueness of the conjugate comparison preserves the equations.
(8) For a square, compose the inverse-image comparison with the inverse comparison for
the other route after transporting along the equality of the two composite morphisms.
Both resulting point-comparison paths equal the comparison for that common morphism. -/
theorem profinite_point_pullback_abelian_coherence :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}),
      (upperStarComp Ab.{u + 1} (𝟙 X) f).hom.app M ≫
          (upperStarId Ab.{u + 1} X).hom.app ((upperStar Ab.{u + 1} f).obj M) =
        (eqToHom (congrArg (upperStar Ab.{u + 1}) (Category.id_comp f))).app M) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}),
      (upperStarComp Ab.{u + 1} f (𝟙 Y)).hom.app M ≫
          (upperStar Ab.{u + 1} f).map ((upperStarId Ab.{u + 1} Y).hom.app M) =
        (eqToHom (congrArg (upperStar Ab.{u + 1}) (Category.comp_id f))).app M) ∧
    (∀ (X Y Z W : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (M : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}),
      (upperStarComp Ab.{u + 1} (f ≫ g) h).hom.app M ≫
          (upperStarComp Ab.{u + 1} f g).hom.app ((upperStar Ab.{u + 1} h).obj M) =
        (eqToHom (congrArg (upperStar Ab.{u + 1}) (Category.assoc f g h))).app M ≫
          (upperStarComp Ab.{u + 1} f (g ≫ h)).hom.app M ≫
          (upperStar Ab.{u + 1} f).map ((upperStarComp Ab.{u + 1} g h).hom.app M)) ∧
    (∀ (X' X Y' Y : Scheme.{u}) (b : X' ⟶ X) (f : X ⟶ Y)
      (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : b ≫ f = f' ≫ g)
      (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      (upperStarComp Ab.{u + 1} b f).inv.app ((upperStarFromPoint Y).obj Λ) ≫
          (eqToHom (congrArg (upperStar Ab.{u + 1}) w)).app
            ((upperStarFromPoint Y).obj Λ) ≫
          (upperStarComp Ab.{u + 1} f' g).hom.app ((upperStarFromPoint Y).obj Λ) ≫
          (upperStar Ab.{u + 1} f').map ((upperStarFromPointComp g).hom.app Λ) ≫
          (upperStarFromPointComp f').hom.app Λ =
        (upperStar Ab.{u + 1} b).map ((upperStarFromPointComp f).hom.app Λ) ≫
          (upperStarFromPointComp b).hom.app Λ) := by
  sorry

open scoped CategoryTheory.Obj

/-- The identity comparison of module direct images is uniquely determined by the
identity comparison on underlying abelian sheaves.
Source: RefactorInstruction, Section 5, coherence of eq:triangle
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (5) condensedPushforwardHom_id identifies the scalar action with the identity
action through lowerStarId. (6) Hence that abelian identity map and its inverse are
linear. Faithfulness of forgetting the action proves uniqueness. -/
theorem existsUnique_profinitePointModuleDirectImageIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ∃! r : CondensedRing.lowerStar Λ (𝟙 X) ≅ 𝟭 _,
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
        (Mod.forget (condensedRingObj Λ X)).map (r.hom.app M) =
          (lowerStarId Ab.{u + 1} X).hom.app M.X := by
  sorry

/-- The canonical identity comparison of module direct images, selected by its unique
underlying map, not by a mere existence of an unrelated isomorphism.
Source: RefactorInstruction, Section 5, eq:triangle
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointModuleDirectImageIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    CondensedRing.lowerStar Λ (𝟙 X) ≅ 𝟭 _ :=
  (existsUnique_profinitePointModuleDirectImageIdentity Λ X).exists.choose

/-- The canonical identity comparison of module inverse images is the conjugate of
that of the direct images under the specified module adjunction.
Source: RefactorInstruction, Section 5, eq:triangle
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointModuleIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    CondensedRing.upperStar Λ (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 X))).symm
    (profinitePointModuleDirectImageIdentity Λ X).symm

/-- The scalar-extension pullback has the original exact abelian inverse image as its
underlying sheaf, via restriction along the inverse coefficient isomorphism.
Source: RefactorInstruction, thm:alpha; Stacks, Tags 03D2 and 03D8
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointModuleForgetPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStar Λ f ⋙ Mod.forget (condensedRingObj Λ X) ≅
      Mod.forget (condensedRingObj Λ Y) ⋙ upperStar Ab.{u + 1} f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)))
    (Mod.forget (condensedRingObj Λ X))

/-- The module comparison is the linear lift of the abelian comparison. Exactness
follows because extension of scalars along the coefficient isomorphism is an equivalence.
Source: RefactorInstruction, thm:alpha; Stacks, Tags 03D2 and 03D8
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (6) Apply inverse image to the module action and substitute the inverse coefficient
isomorphism in the scalar variable. The balanced maps r tensor m to alpha inverse(r)m
and m to 1 tensor m are inverse, giving profinitePointModuleForgetPullbackIso. Naturality
of the abelian composition comparison at the action makes it linear; its underlying map
is the equation below. Forgetting is faithful and creates kernels and sheafified cokernels,
so exactness and the abelian unit and associativity equations lift to modules. -/
theorem profinite_point_pullback_module_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      PreservesFiniteLimits (CondensedRing.upperStar Λ f) ∧
      PreservesFiniteColimits (CondensedRing.upperStar Λ f)) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      (Mod.forget (condensedRingObj Λ X)).map
          ((profinitePointModuleIdentity Λ X).hom.app
            ((CondensedRing.upperStar Λ f).obj M)) =
        (profinitePointModuleForgetPullbackIso Λ (𝟙 X)).hom.app
            ((CondensedRing.upperStar Λ f).obj M) ≫
          (upperStarId Ab.{u + 1} X).hom.app
            ((CondensedRing.upperStar Λ f).obj M).X) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
      (Mod.forget (condensedRingObj Λ X)).map
          ((CondensedRing.upperStarComp Λ f g).hom.app M) ≫
          (profinitePointModuleForgetPullbackIso Λ f).hom.app
            ((CondensedRing.upperStar Λ g).obj M) ≫
          (upperStar Ab.{u + 1} f).map
            ((profinitePointModuleForgetPullbackIso Λ g).hom.app M) =
        (profinitePointModuleForgetPullbackIso Λ (f ≫ g)).hom.app M ≫
          (upperStarComp Ab.{u + 1} f g).hom.app M.X) := by
  sorry

/-- Module inverse images satisfy both unit equations and associativity.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (6) Use the normalized linear lifts in profinite_point_pullback_module_comparison.
Apply the faithful forgetful functors and the corresponding abelian equations from step 3.
The coherence of coefficient maps in step 5 identifies all scalar actions. -/
theorem profinite_point_pullback_module_coherence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      (CondensedRing.upperStarComp Λ (𝟙 X) f).hom.app M ≫
          (profinitePointModuleIdentity Λ X).hom.app ((CondensedRing.upperStar Λ f).obj M) =
        (eqToHom (congrArg (CondensedRing.upperStar Λ) (Category.id_comp f))).app M) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      (CondensedRing.upperStarComp Λ f (𝟙 Y)).hom.app M ≫
          (CondensedRing.upperStar Λ f).map ((profinitePointModuleIdentity Λ Y).hom.app M) =
        (eqToHom (congrArg (CondensedRing.upperStar Λ) (Category.comp_id f))).app M) ∧
    (∀ (X Y Z W : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (M : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)),
      (CondensedRing.upperStarComp Λ (f ≫ g) h).hom.app M ≫
          (CondensedRing.upperStarComp Λ f g).hom.app ((CondensedRing.upperStar Λ h).obj M) =
        (eqToHom (congrArg (CondensedRing.upperStar Λ) (Category.assoc f g h))).app M ≫
          (CondensedRing.upperStarComp Λ f (g ≫ h)).hom.app M ≫
          (CondensedRing.upperStar Λ f).map ((CondensedRing.upperStarComp Λ g h).hom.app M)) := by
  sorry

/-- Monoidality of the canonical abelian inverse-image composition comparison.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (2) The sheafified Kan-extension inverse images have their canonical tensor
structures by the site inverse-image tensor theorem. (3) The composition comparison
is adjunction-compatible, so the monoidal comparison clause of that theorem applies.
Equivalently, conjugate the monoidal direct-image comparison and use the tensor mates. -/
@[instance]
theorem profinitePoint_isMonoidal_upperStarComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).hom := by
  sorry

/-- Monoidality of the canonical identity comparison of abelian inverse images.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (3) Compare the inverse-image identity adjunction with the identity adjunction.
The unit equation uniquely specifies upperStarId; the monoidal identity clause of the
site inverse-image tensor theorem says this same comparison is monoidal. -/
@[instance]
theorem profinitePoint_isMonoidal_upperStarId (X : Scheme.{u}) :
    NatTrans.IsMonoidal (upperStarId Ab.{u + 1} X).hom := by
  sorry

/-- The canonical ring-object composition comparison, obtained by lifting the abelian or
linear comparison through the existing functor on algebraic structures or localization.
Source: RefactorInstruction, eq:triangle and thm:alpha; Stacks, Tags 00YV and 05RU
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointRingComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar Ab.{u + 1} (f ≫ g)).mapMon ≅ (upperStar Ab.{u + 1} g).mapMon ⋙ (upperStar Ab.{u +
      1} f).mapMon :=
  Functor.mapMonNatIso (upperStarComp Ab.{u + 1} f g) ≪≫ Functor.mapMonCompIso

/-- The canonical ring-object identity comparison, using the existing lift of the
ordinary inverse-image identity and its normalization on the identity functor.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tags 00YV and 05RU
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointRingIdentity
    (X : Scheme.{u}) :
    (upperStar Ab.{u + 1} (𝟙 X)).mapMon ≅ 𝟭 (Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})) :=
  Functor.mapMonNatIso (upperStarId Ab.{u + 1} X) ≪≫ Functor.mapMonIdIso

/-- The ring-object inverse-image comparisons satisfy both units and associativity.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha; Stacks, Tag 05RU
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (5) Ring maps inherit the equations because forgetting multiplication is faithful.
(6) Module equations inherit them because forgetting the action is faithful.
(7) Apply the exact-functor derived factorization to the ordinary pullbacks. Naturality
at each differential makes the ordinary comparisons isomorphisms of complexes. The
localization universal property lifts them uniquely, preserves identity and composition,
and detects equality after precomposition with Q, so the degreewise unit and associativity
equations descend. (8) The two square routes are compared with the pullback of their common
composite; the same uniqueness identifies this comparison after localization. -/
theorem profinite_point_pullback_ring_coherence
    :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : Mon (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})),
      (profinitePointRingComp (𝟙 X) f).hom.app M ≫
          (profinitePointRingIdentity X).hom.app ((upperStar Ab.{u + 1} f).mapMon.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapMon)
          (Category.id_comp f))).app M) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : Mon (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})),
      (profinitePointRingComp f (𝟙 Y)).hom.app M ≫
          (upperStar Ab.{u + 1} f).mapMon.map ((profinitePointRingIdentity Y).hom.app M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapMon)
          (Category.comp_id f))).app M) ∧
    (∀ (X Y Z W : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (M : Mon (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})),
      (profinitePointRingComp (f ≫ g) h).hom.app M ≫
          (profinitePointRingComp f g).hom.app ((upperStar Ab.{u + 1} h).mapMon.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ W ↦ (upperStar Ab.{u + 1} k).mapMon)
          (Category.assoc f g h))).app M ≫
          (profinitePointRingComp f (g ≫ h)).hom.app M ≫
          (upperStar Ab.{u + 1} f).mapMon.map ((profinitePointRingComp g h).hom.app M)) := by
  sorry

/-- The canonical termwise derived composition comparison, obtained by lifting the abelian or
linear comparison through the existing functor on algebraic structures or localization.
Source: RefactorInstruction, eq:triangle and thm:alpha; Stacks, Tags 00YV and 05RU
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointAbelianDerivedComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar Ab.{u + 1} (f ≫ g)).mapDerivedCategory ≅
      (upperStar Ab.{u + 1} g).mapDerivedCategory ⋙ (upperStar Ab.{u + 1} f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Ab.{u + 1} f g) ≪≫
    Functor.mapDerivedCategoryCompIso (upperStar Ab.{u + 1} g) (upperStar Ab.{u + 1} f)

/-- The canonical termwise derived identity comparison, using the existing lift of the
ordinary inverse-image identity and its normalization on the identity functor.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tags 00YV and 05RU
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointAbelianDerivedIdentity
    (X : Scheme.{u}) :
    (upperStar Ab.{u + 1} (𝟙 X)).mapDerivedCategory ≅ 𝟭 (DerivedCategory (Sheaf
      (Scheme.ProEt.topology X) Ab.{u + 1})) :=
  Functor.mapDerivedCategoryNatIso (upperStarId Ab.{u + 1} X) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The termwise derived inverse-image comparisons satisfy both units and associativity.
The square clause identifies the derived square comparison with the unique descent of
the termwise ordinary comparison through the common composite.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha; Stacks, Tag 05RU
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (5) Ring maps inherit the equations because forgetting multiplication is faithful.
(6) Module equations inherit them because forgetting the action is faithful.
(7) Apply the exact-functor derived factorization to the ordinary pullbacks. Naturality
at each differential makes the ordinary comparisons isomorphisms of complexes. The
localization universal property lifts them uniquely, preserves identity and composition,
and detects equality after precomposition with Q, so the degreewise unit and associativity
equations descend. (8) The two square routes are compared with the pullback of their common
composite; the same uniqueness identifies this comparison after localization. -/
theorem profinite_point_pullback_abelianderived_coherence
    :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) Ab.{u
      + 1})),
      (profinitePointAbelianDerivedComp (𝟙 X) f).hom.app M ≫
          (profinitePointAbelianDerivedIdentity X).hom.app ((upperStar Ab.{u + 1}
            f).mapDerivedCategory.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapDerivedCategory)
          (Category.id_comp f))).app M) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) Ab.{u
      + 1})),
      (profinitePointAbelianDerivedComp f (𝟙 Y)).hom.app M ≫
          (upperStar Ab.{u + 1} f).mapDerivedCategory.map ((profinitePointAbelianDerivedIdentity
            Y).hom.app M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapDerivedCategory)
          (Category.comp_id f))).app M) ∧
    (∀ (X Y Z W : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (M : DerivedCategory (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})),
      (profinitePointAbelianDerivedComp (f ≫ g) h).hom.app M ≫
          (profinitePointAbelianDerivedComp f g).hom.app ((upperStar Ab.{u + 1}
            h).mapDerivedCategory.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ W ↦ (upperStar Ab.{u + 1} k).mapDerivedCategory)
          (Category.assoc f g h))).app M ≫
          (profinitePointAbelianDerivedComp f (g ≫ h)).hom.app M ≫
          (upperStar Ab.{u + 1} f).mapDerivedCategory.map ((profinitePointAbelianDerivedComp g
            h).hom.app M)) ∧
    (∀ (X' X Y' Y : Scheme.{u}) (b : X' ⟶ X) (f : X ⟶ Y)
      (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : b ≫ f = f' ≫ g) (M : DerivedCategory (Sheaf
        (Scheme.ProEt.topology Y) Ab.{u + 1})),
      (profinitePointAbelianDerivedComp b f).inv.app M ≫
          (eqToHom (congrArg (fun k : X' ⟶ Y ↦ (upperStar Ab.{u + 1} k).mapDerivedCategory)
            w)).app M ≫
          (profinitePointAbelianDerivedComp f' g).hom.app M =
        (Functor.mapDerivedCategoryCompIso (upperStar Ab.{u + 1} f) (upperStar Ab.{u + 1}
          b)).inv.app M ≫
          (Functor.mapDerivedCategoryNatIso
            ((upperStarComp Ab.{u + 1} b f).symm ≪≫
              eqToIso (congrArg (fun k : X' ⟶ Y ↦ (upperStar Ab.{u + 1} k)) w) ≪≫
              (upperStarComp Ab.{u + 1} f' g))).hom.app M ≫
          (Functor.mapDerivedCategoryCompIso (upperStar Ab.{u + 1} g) (upperStar Ab.{u + 1}
            f')).hom.app M) := by
  sorry

/-- The canonical termwise derived composition comparison, obtained by lifting the abelian or
linear comparison through the existing functor on algebraic structures or localization.
Source: RefactorInstruction, eq:triangle and thm:alpha; Stacks, Tags 00YV and 05RU
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointModuleDerivedComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CondensedRing.upperStar Λ (f ≫ g)).mapDerivedCategory ≅
      (CondensedRing.upperStar Λ g).mapDerivedCategory ⋙ (CondensedRing.upperStar Λ
        f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
    Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ g) (CondensedRing.upperStar Λ f)

/-- The canonical termwise derived identity comparison, using the existing lift of the
ordinary inverse-image identity and its normalization on the identity functor.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tags 00YV and 05RU
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointModuleDerivedIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    (CondensedRing.upperStar Λ (𝟙 X)).mapDerivedCategory ≅ 𝟭 (DerivedCategory (Mod (Sheaf
      (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  Functor.mapDerivedCategoryNatIso (profinitePointModuleIdentity Λ X) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The termwise derived inverse-image comparisons satisfy both units and associativity.
The square clause identifies the derived square comparison with the unique descent of
the termwise ordinary comparison through the common composite.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha; Stacks, Tag 05RU
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (5) Ring maps inherit the equations because forgetting multiplication is faithful.
(6) Module equations inherit them because forgetting the action is faithful.
(7) Apply the exact-functor derived factorization to the ordinary pullbacks. Naturality
at each differential makes the ordinary comparisons isomorphisms of complexes. The
localization universal property lifts them uniquely, preserves identity and composition,
and detects equality after precomposition with Q, so the degreewise unit and associativity
equations descend. (8) The two square routes are compared with the pullback of their common
composite; the same uniqueness identifies this comparison after localization. -/
theorem profinite_point_pullback_modulederived_coherence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y)
      Ab.{u + 1}) (condensedRingObj Λ Y))),
      (profinitePointModuleDerivedComp Λ (𝟙 X) f).hom.app M ≫
          (profinitePointModuleDerivedIdentity Λ X).hom.app ((CondensedRing.upperStar Λ
            f).mapDerivedCategory.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (CondensedRing.upperStar Λ k).mapDerivedCategory)
          (Category.id_comp f))).app M) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y)
      Ab.{u + 1}) (condensedRingObj Λ Y))),
      (profinitePointModuleDerivedComp Λ f (𝟙 Y)).hom.app M ≫
          (CondensedRing.upperStar Λ f).mapDerivedCategory.map
            ((profinitePointModuleDerivedIdentity Λ Y).hom.app M) =
        (eqToHom (congrArg (fun k : X ⟶ Y ↦ (CondensedRing.upperStar Λ k).mapDerivedCategory)
          (Category.comp_id f))).app M) ∧
    (∀ (X Y Z W : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ
        W))),
      (profinitePointModuleDerivedComp Λ (f ≫ g) h).hom.app M ≫
          (profinitePointModuleDerivedComp Λ f g).hom.app ((CondensedRing.upperStar Λ
            h).mapDerivedCategory.obj M) =
        (eqToHom (congrArg (fun k : X ⟶ W ↦ (CondensedRing.upperStar Λ k).mapDerivedCategory)
          (Category.assoc f g h))).app M ≫
          (profinitePointModuleDerivedComp Λ f (g ≫ h)).hom.app M ≫
          (CondensedRing.upperStar Λ f).mapDerivedCategory.map ((profinitePointModuleDerivedComp Λ
            g h).hom.app M)) ∧
    (∀ (X' X Y' Y : Scheme.{u}) (b : X' ⟶ X) (f : X ⟶ Y)
      (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : b ≫ f = f' ≫ g) (M : DerivedCategory (Mod (Sheaf
        (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))),
      (profinitePointModuleDerivedComp Λ b f).inv.app M ≫
          (eqToHom (congrArg (fun k : X' ⟶ Y ↦ (CondensedRing.upperStar Λ k).mapDerivedCategory)
            w)).app M ≫
          (profinitePointModuleDerivedComp Λ f' g).hom.app M =
        (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ f) (CondensedRing.upperStar
          Λ b)).inv.app M ≫
          (Functor.mapDerivedCategoryNatIso
            ((CondensedRing.upperStarComp Λ b f).symm ≪≫
              eqToIso (congrArg (fun k : X' ⟶ Y ↦ (CondensedRing.upperStar Λ k)) w) ≪≫
              (CondensedRing.upperStarComp Λ f' g))).hom.app M ≫
          (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ g)
            (CondensedRing.upperStar Λ f')).hom.app M) := by
  sorry

/-- The coefficient comparison is the ring lift of the stipulated point comparison.
Its component preserves both multiplication and addition because it is a morphism in
monoid objects of abelian sheaves; commutative rings remain commutative by braidedness.
Source: RefactorInstruction, Section 5, thm:alpha
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (5) Apply the monoidal natural isomorphism to a ring object. Naturality with
respect to every operation gives the ring map; the construction of mapMonNatIso gives
the asserted underlying component. Its inverse is also a ring map. The coefficient
identity and composition equations are the earlier abelian equations under a faithful
forgetful functor, so they hold as equations of ring maps as well. -/
theorem profinite_point_pullback_ring_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :
    (coefficientPullbackIso f Λ).hom.hom = (upperStarFromPointComp f).hom.app Λ.X := by
  sorry

/-- The module square comparison has precisely the underlying abelian square map
obtained via the common composite. The displayed normalization prevents an arbitrary
choice of an isomorphism between the two module pullbacks.
Source: RefactorInstruction, Section 5, eq:triangle and thm:alpha
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (8) Use the inverse of the linear composition comparison for the first route,
transport along the given equality of composite scheme maps, then use the comparison
for the second route. Step 6 identifies these maps after forgetting the module actions
with their abelian counterparts. Step 5 identifies both routes on coefficients with
the point comparison for the common morphism. This gives exactly the equation below. -/
theorem profinite_point_pullback_module_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} (b : X' ⟶ X) (f : X ⟶ Y)
    (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : b ≫ f = f' ≫ g)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (Mod.forget (condensedRingObj Λ X')).map
        ((CondensedRing.upperStarComp Λ b f).inv.app M ≫
          (eqToHom (congrArg (fun k : X' ⟶ Y ↦ CondensedRing.upperStar Λ k) w)).app M ≫
          (CondensedRing.upperStarComp Λ f' g).hom.app M) ≫
        (profinitePointModuleForgetPullbackIso Λ f').hom.app
          ((CondensedRing.upperStar Λ g).obj M) ≫
        (upperStar Ab.{u + 1} f').map
          ((profinitePointModuleForgetPullbackIso Λ g).hom.app M) =
      (profinitePointModuleForgetPullbackIso Λ b).hom.app
          ((CondensedRing.upperStar Λ f).obj M) ≫
        (upperStar Ab.{u + 1} b).map
          ((profinitePointModuleForgetPullbackIso Λ f).hom.app M) ≫
        (upperStarComp Ab.{u + 1} b f).inv.app M.X ≫
        (eqToHom (congrArg (upperStar Ab.{u + 1}) w)).app M.X ≫
        (upperStarComp Ab.{u + 1} f' g).hom.app M.X := by
  sorry

/-- The geometric set inverse image for an arbitrary scheme is the point inverse image
followed by the actual scheme inverse image along its structure morphism.
Source: RefactorInstruction, prop:pX and eq:triangle
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable abbrev profinitePointSetSchemeInverseImage (X : Scheme.{u}) :=
  profinitePointSetInverseImage.{u} ⋙
    Scheme.proEtaleSheafInverseImage (toSpecZ X) (Type (u + 1))

/-- Set inverse-image composition, conjugate to the canonical direct-image comparison.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tag 03CB
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointSetComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.proEtaleSheafInverseImage (f ≫ g) (Type (u + 1)) ≅
      Scheme.proEtaleSheafInverseImage g (Type (u + 1)) ⋙
        Scheme.proEtaleSheafInverseImage f (Type (u + 1)) :=
  ((conjugateIsoEquiv (Scheme.proEtaleSheafAdjunction (f ≫ g) (Type (u + 1)))
      ((Scheme.proEtaleSheafAdjunction g (Type (u + 1))).comp
        (Scheme.proEtaleSheafAdjunction f (Type (u + 1))))).symm
    (lowerStarComp (Type (u + 1)) f g).symm).symm

/-- Set inverse-image identity, conjugate to the canonical direct-image identity.
Source: RefactorInstruction, Section 5, eq:triangle; Stacks, Tag 03CB
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointSetIdentity (X : Scheme.{u}) :
    Scheme.proEtaleSheafInverseImage (𝟙 X) (Type (u + 1)) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (Scheme.proEtaleSheafAdjunction (𝟙 X) (Type (u + 1)))).symm
      (lowerStarId (Type (u + 1)) X).symm

/-- The set-level point comparison is composition followed by the structure-map equality.
Source: RefactorInstruction, Section 5, eq:triangle
(blueprint: lem-weil-pbc-profinite-point-pullback). -/
noncomputable def profinitePointSetSchemeComp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    profinitePointSetSchemeInverseImage Y ⋙
        Scheme.proEtaleSheafInverseImage f (Type (u + 1)) ≅
      profinitePointSetSchemeInverseImage X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft profinitePointSetInverseImage
    ((profinitePointSetComp f (toSpecZ Y)).symm ≪≫
      eqToIso (congrArg
        (fun k : X ⟶ specZ ↦ Scheme.proEtaleSheafInverseImage k (Type (u + 1)))
        (comp_toSpecZ f)))

/-- The geometric point comparisons are coherent already on sets.
Source: RefactorInstruction, prop:pX and Section 5, eq:triangle
(blueprint: lem-weil-pbc-profinite-point-pullback).

Proof: (2) The scheme base-change functors preserve finite limits and coverings, so their
inverse images and their composite with the point inverse image preserve finite limits.
(3) Conjugate the fibre-product identity and composition comparisons. Their diagrams
commute by uniqueness of maps preserving the projections; uniqueness of the conjugate
comparison carries these diagrams to inverse images. (4) Whisker with the point inverse
image and use the structure-map identity. (8) Both routes around a commutative square
therefore give the comparison for its common composite. -/
theorem profinite_point_pullback_set_coherence :
    (∀ X : Scheme.{u}, PreservesFiniteLimits (profinitePointSetSchemeInverseImage X)) ∧
    (∀ (X : Scheme.{u}) (F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
      (profinitePointSetSchemeComp (𝟙 X)).hom.app F =
        (profinitePointSetIdentity X).hom.app ((profinitePointSetSchemeInverseImage X).obj F)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
      (profinitePointSetComp f g).hom.app ((profinitePointSetSchemeInverseImage Z).obj F) ≫
          (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map
            ((profinitePointSetSchemeComp g).hom.app F) ≫
          (profinitePointSetSchemeComp f).hom.app F =
        (profinitePointSetSchemeComp (f ≫ g)).hom.app F) ∧
    (∀ (X' X Y' Y : Scheme.{u}) (b : X' ⟶ X) (f : X ⟶ Y)
      (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : b ≫ f = f' ≫ g)
      (F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
      (profinitePointSetComp b f).inv.app ((profinitePointSetSchemeInverseImage Y).obj F) ≫
          (eqToHom (congrArg
            (fun k : X' ⟶ Y ↦ Scheme.proEtaleSheafInverseImage k (Type (u + 1))) w)).app
              ((profinitePointSetSchemeInverseImage Y).obj F) ≫
          (profinitePointSetComp f' g).hom.app ((profinitePointSetSchemeInverseImage Y).obj F) ≫
          (Scheme.proEtaleSheafInverseImage f' (Type (u + 1))).map
            ((profinitePointSetSchemeComp g).hom.app F) ≫
          (profinitePointSetSchemeComp f').hom.app F =
        (Scheme.proEtaleSheafInverseImage b (Type (u + 1))).map
            ((profinitePointSetSchemeComp f).hom.app F) ≫
          (profinitePointSetSchemeComp b).hom.app F) := by
  sorry

end AlgebraicGeometry.ProEtale
