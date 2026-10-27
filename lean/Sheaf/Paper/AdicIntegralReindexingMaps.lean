/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicRealizationFamilyData

/-! # Integral reindexing maps for one native realization comparison

This is the map-construction part of the common-stage integral descent argument.
Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-integral-reindexing-maps)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

/--
The balanced integral reindexing maps exist for every finite coefficient field.
The proof compares the finite quotient projections of the completed coefficient
sheaves, then localizes the resulting cochain comparison. It uses the coefficient
cartesian and finite-colimit statements, and the exact inverse-image tensor/Hom
comparison. The same construction works for identity and inverse scheme
isomorphisms and for zero complexes; no common-stage comparison is asserted here.
 (blueprint: lem-sf-adic-integral-reindexing-maps)
-/
theorem exists_integral_reindexing_maps (D : FiniteFieldDatum.{u})
    (d : ∀ T : GeometricSpace D, SpaceData l D T)
    (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (B : RingReindex l T.base.left g.hom (d T).realization (d U).realization) :
    letI := (d T).units
    letI := (d U).units
    Nonempty (∀ E, IntegralReindex l T.base.left g.hom B E) := by
  sorry

end WeilConjectures.AdicQbarRealization
