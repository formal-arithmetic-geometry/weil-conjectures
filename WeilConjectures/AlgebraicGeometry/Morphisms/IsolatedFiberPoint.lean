/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Residue fields at isolated points of fibres

Source: Stacks Project, Morphisms, Lemmas 01TH and 01TG
(blueprint: `lem-weil-pbc-isolated-fibre-point-residue-finite`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- An isolated point of a fibre of a locally finite type morphism has finite residue
field extension. Source: Stacks Project, Morphisms, Lemma 01TH, (2) implies (1),
and Lemma 01TG (blueprint: `lem-weil-pbc-isolated-fibre-point-residue-finite`). -/
theorem finiteDimensional_residueField_of_isOpen_singleton_asFiber
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hx : IsOpen ({f.asFiber x} : Set (f.fiber (f x)))) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (S.residueField (f x)) (X.residueField x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have hq : (f.stalkMap x).hom.QuasiFinite :=
    (f.quasiFiniteAt_iff_isOpen_singleton_asFiber).mpr hx
  have hr : (X.residue x).hom.QuasiFinite :=
    RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ (X.residue_surjective x))
  have hc := hr.comp hq
  rw [← CommRingCat.hom_comp, ← residue_residueFieldMap] at hc
  have hi := RingHom.QuasiFinite.of_comp hc
  let : Algebra.QuasiFinite (S.residueField (f x)) (X.residueField x) := hi
  exact Module.Finite.of_quasiFinite

end AlgebraicGeometry.Scheme.Hom
