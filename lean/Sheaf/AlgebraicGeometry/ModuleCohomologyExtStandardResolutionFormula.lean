/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality

/-! # The fixed comparison on the chosen standard resolution

Source: Stacks Project, Tags 015E and 03FD.
(blueprint: new-module-cohomology-ext-standard-resolution-formula)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Computation only on Mathlib's fixed standard injective resolution, with no
change-of-resolution assertion.
Source: Stacks Project, Tag 015E (acyclic resolution computation) and Tag 03FD.
(blueprint: new-module-cohomology-ext-standard-resolution-formula)

Proof: Substitute hI, ha and hb, then unfold moduleCohomologyExtResolutionEquiv.
Its chosen resolution is exactly I = injectiveResolution F. The comparison a
is its module right-derived resolution isomorphism followed by inverse
exact-forgetting homology. Write c for the acyclic-resolution comparison in b,
d for siteSectionsObjIso and t for precompAddEquiv. Evaluating AddEquiv.trans
and the homomorphism of each composite gives t.symm (d.inv (c.inv (a.hom x))).
Iso.trans_inv gives the same expression for b.inv (a.hom x). The forgotten
augmentation is identical in the two constructions, and proof irrelevance
identifies its quasi-isomorphism proof with the supplied hι. No change of
resolution is used.
This calculation includes degree zero, zero coefficients and empty schemes. -/
theorem standard_resolution_formula
    (X : Scheme.{u}) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : InjectiveResolution F) (hI : I = injectiveResolution F)
    (hι : QuasiIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)) (.up ℕ) 0).inv.app F ≫
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapHomologicalComplex
          (.up ℕ)).map I.ι)) (p : ℕ)
    (a : (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) ≅
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology p)
    (b : AddCommGrpCat.of (H F p) ≅
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology p)
    (ha : a = (forget₂ _ AddCommGrpCat.{u}).mapIso
      (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p) ≪≫
        (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso
          (forget₂ _ AddCommGrpCat.{u})).symm)
    (hb : b = (by
      let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
      let ι := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app F ≫
        (T.mapHomologicalComplex (.up ℕ)).map I.ι
      haveI : QuasiIso ι := hι
      exact (Abelian.Ext.precompAddEquiv (terminalSourceIso X) (T.obj F) p).toAddCommGrpIso ≪≫
        siteSectionsObjIso (Opens.grothendieckTopology X) ⊤ (T.obj F) p ≪≫
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
          (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).rightDerivedObjIsoOfResolution ι
            (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n)) p))
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    moduleCohomologyExtResolutionEquiv X F p x = b.inv (a.hom x) := by sorry

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
