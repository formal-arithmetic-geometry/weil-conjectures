/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
import Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence

/-! # The cocycle calculation for an arbitrary abelian injective target

Source: Stacks Project, Tags 01F7 and 06XR.
(blueprint: new-abelian-counit-cocycle-calculation)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
attribute [local instance] AlgebraicGeometry.Scheme.Modules.instAddCommGroupH
attribute [local irreducible] abelianResolutionIso
attribute [local irreducible] Functor.rightDerivedObjIsoOfResolution
attribute [local irreducible] siteSectionsObjIso

/-- Abelian direct image, with the site categories fixed before instance search.
Source: Stacks, Tag 01F7. -/
abbrev abelianPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base

/-- The inverse-image/direct-image adjunction on the fixed site categories.
Source: Stacks, Tag 01F7. -/
def abelianAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    invImage f ⊣ abelianPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base

local instance cocycle_pushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abelianPushforward f).Additive :=
  ⟨by intros; ext U x; rfl⟩

/-- The common Ext-to-derived-sections part of the resolution comparisons.
Source: Stacks Project, Tags 03FD and 06XR. This is the composition of the
terminal-source Ext precomposition with the site-sections comparison. -/
@[irreducible]
def abelianExtSectionsIso (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
      ((abelianSections X).rightDerived p).obj
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) :=
  (Abelian.Ext.precompAddEquiv (terminalSourceIso X)
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p).toAddCommGrpIso ≪≫
    siteSectionsObjIso (Opens.grothendieckTopology X) ⊤
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) p

/-- Ext compared with sections of an abelian injective resolution of a module.
Source: Stacks Project, Tag 06XR. -/
@[irreducible]
def abelianInjectiveResolutionIso (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (R : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)) (p : ℕ) :
    AddCommGrpCat.of (H F p) ≅
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology p :=
  abelianExtSectionsIso X F p ≪≫
    (abelianSections X).rightDerivedObjIsoOfResolution R.ι
      (fun n ↦ Functor.rightAcyclic_of_injective (R.cocomplex.X n)) p

/- The canonical Ext comparison factors through the Hom-complex homology map.
This is the resolution-local normalization used by the cocycle calculation. -/
theorem abelian_ext_homology_comparison_formula
    {A : Type u} [Category.{u} A] [Abelian A] [HasExt.{u} A]
    [HasInjectiveResolutions A] (P F : A) (p : ℕ) :
    let I := injectiveResolution F
    let E := preadditiveCoyoneda.obj (op P)
    (extRightDerivedHomObjIso P F p).hom ≫ (I.isoRightDerivedObj E p).hom =
    (I.extAddEquivCohomologyClass (X := P) (n := p)).toAddCommGrpIso.hom ≫
      (CochainComplex.HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj P)
        I.cochainComplex (p : ℤ)).homologyIso.inv ≫
      HomologicalComplex.homologyMap (extRightDerivedHomComplexIso P I.cochainComplex).hom
        (p : ℤ) ≫
      HomologicalComplex.homologyMap
        (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat E).hom (p : ℤ) ≫
      (((E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
        ComplexShape.embeddingUpNat (rfl : (p : ℤ) = p)).hom := by
  dsimp only
  simp only [extRightDerivedHomObjIso,
    InjectiveResolution.isoRightDerivedObjCochainComplex,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, HomologicalComplex.homologyFunctor_map,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse-image/coefficient cocycle computation for abelian sheaves.
It asserts no comparison with a target module resolution.

Source: Stacks Project, Tag 01F7, Lemma 01F8 and equation 01F9; Tag 06XR.
(blueprint: new-abelian-counit-cocycle-calculation)

Proof: The section-acyclic source resolution computes Ext from the constant
integer sheaf by its Hom cocycles, identified with sections. Exact inverse image
sends a cocycle representing x to a cocycle representing mapFunctor(x), with
precomposition on the constant source given by constIso(f).symm. The augmentation
square for L ensures that postcomposition by L represents the coefficient map c.
Evaluation on the free integer generator identifies this Hom cocycle with the
section obtained from the adjoint of L. The adjunction unit gives this adjoint
as the unit followed by f_*L; the component equation for s then identifies its
sections with sections on X. Both identifications are additive chain maps and
therefore also preserve boundaries. Passing to homology gives the equality.
The source uses the given acyclic-resolution comparison. The injective target
uses the same canonical comparison for its augmentation; this agrees with its
usual injective-resolution computation by naturality of the identity comparison
lift to the chosen injective resolution, cancelling the inverse homology of that
lift. No comparison with a target module resolution is part of the argument.
The argument includes degree zero, zero sheaves and empty schemes. -/
theorem abelian_counit_cocycle_calculation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Y.Modules) (F : X.Modules) (J : InjectiveResolution A)
    (c : (invImage f).obj
      ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj A) ⟶
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F))
    (R : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F))
    (L : ((invImage f).mapHomologicalComplex (.up ℕ)).obj
      (((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex) ⟶ R.cocomplex)
    (hL : (HomologicalComplex.singleMapHomologicalComplex (invImage f) (.up ℕ) 0).inv.app
      ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj A) ≫
      ((invImage f).mapHomologicalComplex (.up ℕ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)) (.up ℕ) 0).inv.app A ≫
          ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).mapHomologicalComplex
            (.up ℕ)).map J.ι) ≫ L = (CochainComplex.single₀ _).map c ≫ R.ι)
    (s : abelianPushforward f ⋙ abelianSections Y ≅ abelianSections X)
    (hs : ∀ G, s.hom.app G = G.obj.map
      (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : Y.Opens)) ⟶ op (⊤ : X.Opens)))
    (p : ℕ) (x : H A p) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).map
      (((abelianSections Y).mapHomologicalComplex (.up ℕ)).map
        ((NatTrans.mapHomologicalComplex (abelianAdjunction f).unit (.up ℕ)).app
          (((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).mapHomologicalComplex
            (.up ℕ)).obj J.cocomplex) ≫
          ((abelianPushforward f).mapHomologicalComplex (.up ℕ)).map L) ≫
        (NatTrans.mapHomologicalComplex s.hom (.up ℕ)).app R.cocomplex))
      ((abelianResolutionIso Y J p).hom x) =
    (abelianInjectiveResolutionIso X F R p).hom
      (Sheaf.H.map c p (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
        ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj A) p x)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
