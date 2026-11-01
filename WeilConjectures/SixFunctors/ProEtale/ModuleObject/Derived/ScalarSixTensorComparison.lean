/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat

/-! # The canonical tensor comparison for derived scalar extension

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/,
det-prop-scalar-six-tensor-hom.proof.md, clause (1), the K-flat tensor comparison;
also the scalar compatibility in fix-prop-projection-formula.proof.md
(blueprint: def-sf-condensed-scalar-tensor-comparison).

These are the existing scalar tensor constructions, moved from ScalarSixTensorHom
without changing their types or bodies. There is one strong monoidal instance and
one tensor comparison, for arbitrary coefficient maps and unbounded objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical strong monoidal structure on the existing scalar-change functor.
Its inverse tensorator is the K-flat derived tensor comparison; the unit comparison
is scalar extension of the regular module. This uses no flatness hypothesis on the map.
Source: blueprint det-prop-scalar-six-tensor-hom (1)
(blueprint: def-sf-condensed-scalar-tensor-comparison). -/
noncomputable instance scalarSixChangeMonoidal {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (X : Scheme.{u}) : (scalarSixChange a X).Monoidal :=
  letI := Mod.extendScalarsMonoidal
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  (Mod.extendScalars
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).leftDerivedFunctorMonoidal

/-- The natural tensor comparison on all unbounded derived objects. Its naturality,
associativity and both unit coherences are the fields of `scalarSixChangeMonoidal`.
Source: blueprint det-prop-scalar-six-tensor-hom (1)
(blueprint: def-sf-condensed-scalar-tensor-comparison). -/
def scalarSixTensorIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u})
    (K M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a X).obj (K ⊗ M) ≅
      (scalarSixChange a X).obj K ⊗ (scalarSixChange a X).obj M :=
  (Functor.Monoidal.μIso (scalarSixChange a X) K M).symm

end AlgebraicGeometry.ProEtale.CondensedRing
