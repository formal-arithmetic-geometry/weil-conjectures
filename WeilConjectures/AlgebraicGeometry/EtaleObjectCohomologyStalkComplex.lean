/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution

/-! # Object cohomology stalks and section complexes

Source: Stacks Project, Cohomology on Sites, Tag 03F3; Etale Cohomology, Tag 09AX.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- Evaluate an etale sheaf on the given open objects and take its Zariski stalk.
-/
noncomputable abbrev etaleObjectStalkSections
    (X : Scheme.{u + 1}) (i : X.Opens ⥤ X.Etale) (x : X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      ((OpenNhds.inclusion (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op ⋙
        colim

instance (X : Scheme.{u + 1}) (i : X.Opens ⥤ X.Etale) (x : X) :
    (etaleObjectStalkSections X i x).Additive := inferInstance

/-- Object cohomology at a Zariski stalk is the homology of stalkwise sections of
an injective resolution. This does not assume strict henselianity.
Source: Stacks Project, Cohomology on Sites, Tag 03F3; Etale Cohomology, Tags 03XA and 09AX,
second and third sentences of the proof. -/
theorem etaleObjectCohomology_stalk_complex
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : X) :
    ∃ I : InjectiveResolution F,
      Nonempty
        (↑(colimit
          (((OpenNhds.inclusion (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op ⋙
            Sheaf.cohomologyPresheaf F q ⋙ AddCommGrpCat.uliftFunctor.{u + 2, w})) ≃+
          (((etaleObjectStalkSections X i x).mapHomologicalComplex (.up ℕ)).obj
            I.cocomplex).homology q) := by
  classical
  let I := injectiveResolution F
  let K := ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  let R := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
    ((OpenNhds.inclusion (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op ⋙ colim
  obtain ⟨e⟩ := objectCohomologyPresheaf_resolution X.smallEtaleTopology F I q
  refine ⟨I, ?_⟩
  let N := ((OpenNhds.inclusion
    (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op
  let d := colim.mapIso (Functor.isoWhiskerLeft N e)
  let h := (K.sc q).mapHomologyIso R
  let t := d ≪≫ (preservesColimitIso AddCommGrpCat.uliftFunctor (N ⋙ K.homology q)).symm
  let z := t ≪≫ AddCommGrpCat.uliftFunctor.mapIso h.symm
  exact ⟨z.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift⟩
