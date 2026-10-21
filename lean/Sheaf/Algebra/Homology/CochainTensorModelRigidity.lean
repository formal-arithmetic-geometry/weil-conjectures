/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Rigidity of the cochain tensor model

Source: Stacks Project, Tags 013H, 06YS, 06YT and 06YU; blueprint
`def-wf-tensor-product`, first sentence
(blueprint: lem-sf-cochain-tensor-model-rigidity).

The helpers expose the given homotopy model and its comparisons, then write the four
arrows of the canonical cochain comparison. No resolutions are chosen functorially.

## Main statements

- `cochain_tensor_model_rigidity`: the specified representative comparison, normalized
  uniqueness of tensor models, and full faithfulness of restriction.
-/

@[expose] public section

universe u v w d e z

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option autoImplicit false
set_option synthInstance.maxSize 4096

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{w})
  [HasDerivedCategory.{d} (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))]

/-- The cochain representative property: precisely K-flatness and flatness in every degree.
Source: Stacks 06YS, 06YU (blueprint: lem-sf-cochain-tensor-model-rigidity). -/
def cochainTensorFlatRepresentatives : ObjectProperty (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :=
  fun K ↦ CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) K ∧
    ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (K.X n)

/-- The given homotopy representative subcategory from tensor descent. Its membership is
characterized by the exact same K-flat and degreewise flat predicates as the cochain property.
Source: Stacks 06YU (blueprint: lem-sf-cochain-tensor-model-rigidity). -/
noncomputable def cochainTensorHomotopyRepresentatives :
    ObjectProperty (HomotopyCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ)) :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0} J R).choose

/-- Restriction of the homotopy quotient to flat-term K-flat representatives. The membership
proof uses the characterization supplied by the existing descent theorem, not a new predicate.
Source: Stacks 013H, 06YU (blueprint: lem-sf-cochain-tensor-model-rigidity). -/
noncomputable def cochainTensorRepresentativeQuotient :
    (cochainTensorFlatRepresentatives J R).FullSubcategory ⥤
      (cochainTensorHomotopyRepresentatives J R).FullSubcategory :=
  (cochainTensorHomotopyRepresentatives J R).lift
    ((cochainTensorFlatRepresentatives J R).ι ⋙ HomotopyCategory.quotient _ (.up ℤ))
    (fun K ↦ ((site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0}
      J R).choose_spec.1 _).2 K.property)

/-- The cochain localization restricted to these representatives.
Source: Stacks 013H, 06YU (blueprint: lem-sf-cochain-tensor-model-rigidity). -/
noncomputable def cochainTensorRepresentativeLocalization :
    (cochainTensorFlatRepresentatives J R).FullSubcategory ⥤ DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :=
  (cochainTensorFlatRepresentatives J R).ι ⋙ DerivedCategory.Q

/-- The signed direct-sum total tensor on cochain complexes, using the existing sheaf tensor.
Source: Stacks 06YN, 06YU (blueprint: lem-sf-cochain-tensor-model-rigidity). -/
noncomputable def cochainTensorTotal : (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) ×
    (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) ⥤
    (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :=
  Functor.uncurry.obj ((curriedTensor (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

/-- The homotopy total tensor selected together with its comparison by the descent theorem.
Source: Stacks 06YU (blueprint: lem-sf-cochain-tensor-model-rigidity). -/
noncomputable def cochainTensorHomotopyTotal : (HomotopyCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ)) ×
    (HomotopyCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ)) ⥤
    (HomotopyCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ)) :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0}
    J R).choose_spec.2.2.1.choose

/-- The given comparison between homotopy tensor and the quotient of cochain tensor.
Source: Stacks 013H, 06YU (blueprint: lem-sf-cochain-tensor-model-rigidity). -/
noncomputable def cochainTensorHomotopyTotalComparison :
    ((HomotopyCategory.quotient (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ)).prod
      (HomotopyCategory.quotient (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ))) ⋙
      cochainTensorHomotopyTotal J R ≅
        cochainTensorTotal J R ⋙ HomotopyCategory.quotient (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (.up ℤ) :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0}
    J R).choose_spec.2.2.1.choose_spec.1.some

/-- The given representative comparison for the selected derived tensor model. The choices
are exactly the packet defining `siteDerivedTensorIndependentCoefficients`, with its comparison.
Source: Stacks 06YU (blueprint: lem-sf-cochain-tensor-model-rigidity). -/
noncomputable def cochainTensorHomotopyDerivedComparison :
    ((cochainTensorHomotopyRepresentatives J R).ι.prod
      (cochainTensorHomotopyRepresentatives J R).ι) ⋙
        cochainTensorHomotopyTotal J R ⋙ DerivedCategory.Qh ≅
    (((cochainTensorHomotopyRepresentatives J R).ι ⋙ DerivedCategory.Qh).prod
      ((cochainTensorHomotopyRepresentatives J R).ι ⋙ DerivedCategory.Qh)) ⋙
        siteDerivedTensorIndependentCoefficients J R :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, w, d, 0, 0}
    J R).choose_spec.2.2.1.choose_spec.2.choose_spec.some

/-- The four-arrow composite: Q→Qhπ, the cochain/homotopy tensor comparison, the given
homotopy representative comparison, and T applied to Qhπ→Q in both variables.
Source: Stacks 013H, 06YU (blueprint: lem-sf-cochain-tensor-model-rigidity). -/
noncomputable def cochainTensorRepresentativeArrow
    (X : (cochainTensorFlatRepresentatives J R).FullSubcategory ×
      (cochainTensorFlatRepresentatives J R).FullSubcategory) :
    DerivedCategory.Q.obj ((cochainTensorTotal J R).obj (X.1.obj, X.2.obj)) ⟶
      (siteDerivedTensorIndependentCoefficients J R).obj
        (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj X.2.obj) :=
  (DerivedCategory.quotientCompQhIso (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).inv.app
      ((cochainTensorTotal J R).obj (X.1.obj, X.2.obj)) ≫
    DerivedCategory.Qh.map ((cochainTensorHomotopyTotalComparison J R).inv.app
      (X.1.obj, X.2.obj)) ≫
    (cochainTensorHomotopyDerivedComparison J R).hom.app
      ((cochainTensorRepresentativeQuotient J R).obj X.1,
        (cochainTensorRepresentativeQuotient J R).obj X.2) ≫
    (siteDerivedTensorIndependentCoefficients J R).map
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).hom.app X.1.obj,
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).hom.app X.2.obj)

/-- The canonical cochain tensor comparison, its normalized uniqueness, and full faithfulness
of restriction along the product of the cochain representative localizations.
Source: Stacks 013H, 06YS, 06YT, 06YU; blueprint `def-wf-tensor-product`, first sentence
(blueprint: lem-sf-cochain-tensor-model-rigidity).

Proof:
1. The restricted quotient to the homotopy representative category is identity on objects
   and full on morphisms. A transformation on its product restriction descends componentwise:
   represent each homotopy class by a cochain map to check naturality. Restriction and this
   extension are inverse on every set of transformations, for any target category.
2. Apply the arbitrary-transformation descent clause of
   `lem-weil-pbc-site-derived-tensor-descent` to the homotopy representative localization.
   Combine its bijection with Step 1, and conjugate by `DerivedCategory.quotientCompQhIso`
   restricted to the cochain representatives. This gives the last clause below.
3. Compose Q→Qhπ, the inverse cochain/homotopy tensor comparison, the given homotopy
   representative comparison, and T applied to Qhπ→Q in both variables. Every arrow is a
   natural isomorphism, and its component is `cochainTensorRepresentativeArrow`.
   Both representative predicates and both tensors are literally those of the dependencies.
4. For r', full faithfulness lifts r⁻¹;r' and its inverse to transformations on D(R)×D(R).
   Faithfulness shows their composites are identities, so the lift is an isomorphism e.
   Its restriction gives r;e=r'. Any other compatible e has the same restriction after
   cancellation of r, so faithfulness proves equality. No functorial resolutions are used.
-/
theorem cochain_tensor_model_rigidity :
    ∃ r : (((cochainTensorFlatRepresentatives J R).ι.prod
        (cochainTensorFlatRepresentatives J R).ι) ⋙ cochainTensorTotal J R ⋙
          DerivedCategory.Q) ≅
      ((cochainTensorRepresentativeLocalization J R).prod
        (cochainTensorRepresentativeLocalization J R)) ⋙
          siteDerivedTensorIndependentCoefficients J R,
      (∀ X, r.hom.app X = cochainTensorRepresentativeArrow J R X) ∧
      (∀ (T' : (DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))) ×
        (DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))) ⥤
        (DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))))
        (r' : (((cochainTensorFlatRepresentatives J R).ι.prod
          (cochainTensorFlatRepresentatives J R).ι) ⋙ cochainTensorTotal J R ⋙
            DerivedCategory.Q) ≅
          ((cochainTensorRepresentativeLocalization J R).prod
            (cochainTensorRepresentativeLocalization J R)) ⋙ T'),
        ∃! e : siteDerivedTensorIndependentCoefficients J R ≅ T',
          r.hom ≫ Functor.whiskerLeft
            ((cochainTensorRepresentativeLocalization J R).prod
              (cochainTensorRepresentativeLocalization J R)) e.hom = r'.hom) ∧
      (∀ (E : Type e) (_ : Category.{z} E)
        (U V : (DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))) ×
        (DerivedCategory (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))) ⥤ E),
        Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft
          ((cochainTensorRepresentativeLocalization J R).prod
            (cochainTensorRepresentativeLocalization J R)) τ)) := by
  sorry

end SheafOfModules
