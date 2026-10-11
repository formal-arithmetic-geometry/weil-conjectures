/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.CategoryTheory.Subobject.Basic

/-! # Finite type quasi-coherent subalgebras

Source: Stacks Project, Properties, Tag 05JT and the definition preceding it
(blueprint: def-weil-pbc-finite-type-quasi-coherent-subalgebras).
-/

@[expose] public section

universe uB

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The inclusion-ordered set of quasi-coherent subalgebras of `A` of finite type.
Subobjects in the category of algebra sheaves encode subsheaves closed under the algebra
operations. Finite type means finite generation on every affine open, not finite generation
of the underlying module. Source: Stacks Project, Properties, Tag 05JT
(blueprint: def-weil-pbc-finite-type-quasi-coherent-subalgebras). -/
noncomputable abbrev CommAlgebraSheaf.finiteTypeQuasiCoherentSubalgebras
    {X : Scheme.{uB}} (A : X.CommAlgebraSheaf) :=
  {B : Subobject A //
    (CommAlgebraSheaf.toModule (B : X.CommAlgebraSheaf)).IsQuasicoherent ∧
      ∀ U : X.Opens, IsAffineOpen U →
        (((B : X.CommAlgebraSheaf).hom.hom.app (op U)).hom).FiniteType}

/-- The diagram sends a finite type quasi-coherent subalgebra to its algebra sheaf and an
inclusion to the corresponding algebra map. Source: Stacks Project, Properties, Tag 05JT
(blueprint: def-weil-pbc-finite-type-quasi-coherent-subalgebras). -/
noncomputable def CommAlgebraSheaf.finiteTypeQuasiCoherentSubalgebraDiagram
    {X : Scheme.{uB}} (A : X.CommAlgebraSheaf) :
    A.finiteTypeQuasiCoherentSubalgebras ⥤ X.CommAlgebraSheaf :=
  (show Monotone (fun B : A.finiteTypeQuasiCoherentSubalgebras ↦ B.val) from
    fun _ _ h ↦ h).functor ⋙ Subobject.underlying

end AlgebraicGeometry.Scheme
