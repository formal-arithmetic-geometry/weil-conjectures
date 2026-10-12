/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact

/-! # Pullback on the Hom complexes of constant sheaves

Source: Stacks Project, Tag 06XR and Tag 01F8, equations 01F9 and 01FA.
-/

@[expose] public section

universe u v w w'
open CategoryTheory CochainComplex HomComplex Limits
namespace AlgebraicGeometry.SheafPullbackResolution
open Scheme Etale

set_option backward.defeqAttrib.useBackward true in
/-- Apply an additive functor to cochains, then compose with the two supplied maps. -/
noncomputable def homPullbackMap
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    (L : C ⥤ D) [L.Additive] {A : C} {A' : D} (α : A' ⟶ L.obj A)
    (K : CochainComplex C ℤ) (K' : CochainComplex D ℤ)
    (φ : (L.mapHomologicalComplex (.up ℤ)).obj K ⟶ K') :
    HomComplex ((singleFunctor _ 0).obj A) K ⟶
      HomComplex ((singleFunctor _ 0).obj A') K' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun a ↦ Cochain.fromSingleMk
        (α ≫ L.map (Cochain.fromSingleEquiv (zero_add n) a) ≫ φ.f n) (zero_add n)
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp] }
  comm' i j hij := by
    ext a
    obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
    change δ i j (Cochain.fromSingleMk
        (α ≫ L.map (Cochain.fromSingleEquiv (zero_add i)
          (Cochain.fromSingleMk a (zero_add i))) ≫ φ.f i) (zero_add i)) =
      Cochain.fromSingleMk (α ≫ L.map (Cochain.fromSingleEquiv (zero_add j)
        (δ i j (Cochain.fromSingleMk a (zero_add i)))) ≫ φ.f j) (zero_add j)
    rw [Cochain.fromSingleEquiv_fromSingleMk,
      Cochain.δ_fromSingleMk _ _ j j (zero_add j),
      Cochain.δ_fromSingleMk _ _ j j (zero_add j),
      Cochain.fromSingleEquiv_fromSingleMk, Functor.map_comp]
    congr 1
    simpa only [Category.assoc, Functor.mapHomologicalComplex_obj_d] using
      congrArg (fun f ↦ α ≫ L.map a ≫ f) (φ.comm i j)

/-- Ext pullback on the unevaluated Hom complex of a chosen injective resolution.
Source: Stacks Project, Tag 06XR; Tag 01F8, equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-ext-pullback-hom-complex)

Proof: Write a class as a cocycle into the chosen resolution, using the
Ext/resolution equivalence. Its inverse sends it to the roof whose right arrow
is the augmentation. Apply the exact inverse-image functor to the roof and
precompose with the constant-sheaf comparison. The supplied augmentation
homotopy makes the localized composite of the pulled-back augmentation and φ
identical to the target augmentation. Cancel that invertible augmentation.
The resulting roof is the class of the cochain obtained by applying inverse
image degreewise and composing with φ. This is homPullbackMap by its explicit
formula. Passing from cocycles modulo boundaries to the homology of the Hom
complex gives the square below. The argument includes degree zero and zero
objects; it uses no injectivity of the pulled-back resolution. -/
theorem extPullback_homComplex {X X' : Scheme.{u}} (g : X' ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (φ : ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℤ)).obj
      (injectiveResolution G).cochainComplex ⟶
      (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)).cochainComplex)
    (hφ : Nonempty (Homotopy
      (((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℤ)).map
        (injectiveResolution G).ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex
        (upperStar AddCommGrpCat.{u + 1} g) (.up ℤ) 0).hom.app G ≫
        (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)).ι'))) :
    let R := injectiveResolution G
    let R' := injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)
    R.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
        (leftHomologyData _ (injectiveResolution G).cochainComplex (q : ℤ)).homologyIso.inv ≫
        HomologicalComplex.homologyMap (homPullbackMap (upperStar AddCommGrpCat.{u + 1} g)
          ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).inv.app
            (AddCommGrpCat.of (ULift.{u + 1} ℤ))) _ _ φ) (q : ℤ) =
      AddCommGrpCat.ofHom (cohomologyMap g G q) ≫
        R'.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
        (leftHomologyData _
          (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G)).cochainComplex
          (q : ℤ)).homologyIso.inv := by sorry

end AlgebraicGeometry.SheafPullbackResolution
