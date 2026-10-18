/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Irreducible

/-!
# Birational quasi-modifications

Source: Temkin, *Stable modification of relative curves*, Proposition 3.2.6
(blueprint: def-trf-birational-quasi-modification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- An integral birational quasi-modification of a reduced target is separated and of finite
 type; its generic point maps to a component's generic point and the actual residue-field map
 is an isomorphism. On a reduced scheme the local ring at a component's generic point is a
 field, so this is exactly the induced function-field identification, with no arbitrary field
 isomorphism substituted for that of `f`.
 Source: Temkin, §3 opening conventions, pp. 13--14, and Proposition 3.2.6, pp. 16--17
 (blueprint: def-trf-birational-quasi-modification).
-/
def IsBirationalQuasiModification {Y Z : Scheme.{u}} [IsIntegral Y] [IsReduced Z]
    (f : Y ⟶ Z) : Prop :=
  IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
    closure ({f (genericPoint Y)} : Set Z) ∈ irreducibleComponents Z ∧
      IsIso (f.residueFieldMap (genericPoint Y))

end AlgebraicGeometry
