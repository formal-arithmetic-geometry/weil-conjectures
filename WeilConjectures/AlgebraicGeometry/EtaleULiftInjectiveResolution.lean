/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.Ulift

import WeilConjectures.AlgebraicGeometry.EtaleULiftInjective
import WeilConjectures.AlgebraicGeometry.EtaleULiftHomology

/-!
# Lifting an injective resolution on the small étale site

Source: Stacks Project, Injectives, Lemma 19.7.3, Tag 01DO;
Mathlib's small affine étale site equivalence and preservation of homology by ULift.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- An injective resolution can be lifted to the larger coefficient universe, and its evaluation
complexes are the lifts of the original evaluation complexes (Stacks, Tag 01DO). -/
theorem exists_etale_ulift_injectiveResolution
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (R : InjectiveResolution F) :
    ∃ S : InjectiveResolution
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F),
      ∀ U : X.Etale, Nonempty
        (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
            (op U)).mapHomologicalComplex
            (.up ℕ)).obj S.cocomplex ≅
          ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
            (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op U) ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex
                (.up ℕ)).obj R.cocomplex) := by
  let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  have : L.PreservesHomology := etale_ulift_preservesHomology X
  have : L.Additive := { map_add := fun {_ _ _ _} => rfl }
  let e := HomologicalComplex.singleMapHomologicalComplex L (.up ℕ) 0
  let S : InjectiveResolution (L.obj F) :=
    { cocomplex := (L.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
      injective := fun n => etale_ulift_injective X (R.cocomplex.X n)
      ι := (e.app F).inv ≫ (L.mapHomologicalComplex (.up ℕ)).map R.ι
      quasiIso := by
        dsimp [e]
        infer_instance }
  refine ⟨S, fun U => ⟨?_⟩⟩
  exact Iso.refl _

end AlgebraicGeometry.Scheme
