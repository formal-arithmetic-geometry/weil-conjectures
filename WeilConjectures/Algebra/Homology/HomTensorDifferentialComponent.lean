/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorDifferentialSummand
import WeilConjectures.Algebra.Homology.HomTensorSummandRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit

/-!
# Component of the iterated Hom differential after currying

## References

* [Stacks Project, Tag 0A5Y](https://stacks.math.columbia.edu/tag/0A5Y)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

private lemma homObjMap_add_first {A A' B : Mod} (f g : A' ⟶ A) :
    SheafOfModules.homObjMap (R := R) (f + g) (𝟙 B) =
      SheafOfModules.homObjMap (R := R) f (𝟙 B) +
        SheafOfModules.homObjMap (R := R) g (𝟙 B) :=
  SheafOfModules.hom_ext
    (PresheafOfModules.homObjMap_add_left (R := R.obj) f.val g.val (𝟙 B.val))

-- Rewriting the total-complex differential elaborates the dependent coproduct indices.
set_option synthInstance.maxSize 256 in
/-- The component of the iterated Hom differential after degreewise currying. -/
theorem homTensorDegreewiseMap_iteratedDifferential_component
    (K L M : CochainComplex Mod ℤ) (n t : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    (homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1) ≫
        homTensorDegreewiseMap R K L M (n + 1) ≫
          homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl =
      (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n t (t + n) rfl ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (T.X t)) (M.d (t + n) (t + (n + 1)))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R) (T.d t (t + 1)) (𝟙 (M.X (t + (n + 1))))) :=
  by
    let := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    apply homTensorSummandRestriction_ext R K L t
    intro p q h
    simpa only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
      SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      homObjMap_add_first, smul_add, ← sub_sub] using
      homTensorDegreewiseMap_iteratedDifferential_summand R K L M n t p q h

end CategoryTheory
