/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.YonedaDerivedExtComparison

/-! # The covariant functor of actual Yoneda extension classes

Source: Stacks Project, Derived Categories, Tags 06XU and 06XV, endpoint naturality
and Baer addition (blueprint: def-sfb-yoneda-ext-one-functor).

The objects are the existing quotients of short exact sequences. The recorded
normalized comparison transports the derived Ext action to these quotients;
its endpoint naturality identifies this action with pushout of extensions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Abelian

namespace CategoryTheory.YonedaDerivedExtComparison

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{max u v} A]

/-- The Baer group on the actual quotient of short extensions of `C` by `M`.
Source: Stacks 06XV and Homology 010I
(blueprint: def-sfb-yoneda-ext-one-functor). -/
def yonedaExtOneGroup (c : YonedaDerivedExtComparison A) (C M : A) :
    AddCommGrpCat.{max u v} :=
  @AddCommGrpCat.of (YonedaExtension.Classes M C 1) (c.classGroup M C 0)

/-- Pushout on short-extension classes, transported through the canonical normalized
comparison. Its endpoint naturality gives the geometric pushout action, and its
Baer clause gives additivity. Source: Stacks 06XU--06XV
(blueprint: def-sfb-yoneda-ext-one-functor). -/
def yonedaExtOneMap (c : YonedaDerivedExtComparison A) (C : A) {M N : A} (f : M ⟶ N) :
    c.yonedaExtOneGroup C M ⟶ c.yonedaExtOneGroup C N :=
  letI := c.classGroup M C 0
  letI := c.classGroup N C 0
  AddCommGrpCat.ofHom
    ((c.comparison N C 0).symm.toAddMonoidHom.comp
      (((extFunctorObj C 1).map f).hom.comp (c.comparison M C 0).toAddMonoidHom))

/-- The identity law needed to bundle the quotient action as a functor.
Source: Stacks 06XU, functoriality of pushout
(blueprint: def-sfb-yoneda-ext-one-functor).
Proof: apply injectivity of the normalized comparison, cancel its inverse, and use
`extFunctorObj.map_id`; transporting back gives the identity on the actual quotient. -/
theorem yonedaExtOneMap_id (c : YonedaDerivedExtComparison A) (C M : A) :
    c.yonedaExtOneMap C (𝟙 M) = 𝟙 (c.yonedaExtOneGroup C M) := by
  let := c.classGroup M C 0
  ext x
  change (c.comparison M C 0).symm
    (((extFunctorObj C 1).map (𝟙 M)) ((c.comparison M C 0) x)) = x
  rw [Functor.map_id]
  exact (c.comparison M C 0).symm_apply_apply x

/-- The composition law needed to bundle the quotient action as a functor.
Source: Stacks 06XU, functoriality of pushout
(blueprint: def-sfb-yoneda-ext-one-functor).
Proof: apply injectivity of the comparison at the target. The adjacent comparison
and inverse at the middle object cancel; `extFunctorObj.map_comp` then proves the
identity. This is also the associativity of pushout on endpoint-fixed classes. -/
theorem yonedaExtOneMap_comp (c : YonedaDerivedExtComparison A) (C : A)
    {M N P : A} (f : M ⟶ N) (g : N ⟶ P) :
    c.yonedaExtOneMap C (f ≫ g) = c.yonedaExtOneMap C f ≫ c.yonedaExtOneMap C g := by
  let := c.classGroup M C 0
  let := c.classGroup N C 0
  let := c.classGroup P C 0
  ext x
  change (c.comparison P C 0).symm
    (((extFunctorObj C 1).map (f ≫ g)) ((c.comparison M C 0) x)) =
      (c.comparison P C 0).symm
        (((extFunctorObj C 1).map g) ((c.comparison N C 0)
          ((c.comparison N C 0).symm
            (((extFunctorObj C 1).map f) ((c.comparison M C 0) x)))))
  rw [Functor.map_comp, AddCommGrpCat.comp_apply, AddEquiv.apply_symm_apply]

/-- The functor `M ↦ Ext¹_Yon(C,M)` with its Baer group and actual quotient carrier.
The arrow on `f : M ⟶ N` is pushout along `f`, by the naturality of the recorded
comparison. Source: Stacks 06XU--06XV and Homology 010I
(blueprint: def-sfb-yoneda-ext-one-functor). -/
def yonedaExtOneFunctor (c : YonedaDerivedExtComparison A) (C : A) :
    A ⥤ AddCommGrpCat.{max u v} where
  obj M := c.yonedaExtOneGroup C M
  map f := c.yonedaExtOneMap C f
  map_id M := c.yonedaExtOneMap_id C M
  map_comp f g := c.yonedaExtOneMap_comp C f g

end CategoryTheory.YonedaDerivedExtComparison
