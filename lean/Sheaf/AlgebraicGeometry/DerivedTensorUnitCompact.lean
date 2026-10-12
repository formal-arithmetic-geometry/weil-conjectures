/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
public import Sheaf.CategoryTheory.CompactObject
import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Compactness of the derived structure sheaf

Source: Stacks Project, Tag 09M1, proof of Proposition
perfect-proposition-compact-is-perfect, first paragraph
(blueprint: lem-pc-derived-tensor-unit-compact).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The derived tensor unit is represented by a compact quasi-coherent object.
Source: Stacks Project, Tag 09M1, proof of Proposition
perfect-proposition-compact-is-perfect, first paragraph
(blueprint: lem-pc-derived-tensor-unit-compact).
Proof: The derived tensor unit is the structure sheaf in degree zero, since the
structure sheaf is flat; its cohomology is quasi-coherent. Let a be the structure
morphism to Spec(Z), using a universe lift of Z when necessary. It is quasi-compact
and quasi-separated. Derived pullback takes the structure sheaf of Spec(Z) to
that of X. The derived adjunction therefore identifies Hom(O_X,N) naturally with
Hom(O_Spec(Z),Ra_*N). Derived direct image preserves coproducts of quasi-coherent
objects. The affine derived equivalence identifies the latter Hom group with
H^0 of a complex of Z-modules. Direct sums in that derived category are represented
termwise; exactness of direct sums of modules shows H^0 preserves them. These
identifications are additive and natural, so on each summand the comparison is
composition with its coproduct inclusion. Thus the canonical Hom direct-sum map
is bijective, including the empty family. -/
theorem exists_compact_derivedTensorUnit (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∃ U : schemeDerivedQCohCategory X,
      Nonempty (U.obj ≅ 𝟙_ (schemeDerivedCategory X)) ∧ IsCompactObject U := by sorry

end AlgebraicGeometry
