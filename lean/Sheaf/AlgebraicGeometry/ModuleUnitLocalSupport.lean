/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit

/-! # Local finite support for one section

Source: Stacks Project, Modules, Tags 01BB (first paragraph of the proof) and 01AH (2).
(blueprint: lem-weil-pbc-module-unit-local-support).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- A single section of a restricted free module sheaf locally has finite support.

Source: Stacks Project, Modules, Tags 01BB (first paragraph of the proof) and 01AH (2).
(blueprint: lem-weil-pbc-module-unit-local-support).

Proof: Express the free sheaf on I as the filtered colimit of its finite
sub-coproducts. The colimit property follows by assigning each basis index its
singleton stage and using compatibility on unions; equivalently use Mathlib's
finite-subcoproduct colimit construction. Restriction preserves that colimit,
and module_stalk_filtered_colimit says stalks preserve it. The germ at x of the
section defined by b therefore comes from some finite stage S. Represent this
lift germ by a section over a neighbourhood W of x inside U. Its image and the
section defined by b have equal germs, so shrink W until the sections agree.
The unit-section equivalence converts this lift and equality into a and the
required morphism equality. This argument uses only one germ and one shrinking;
it does not choose simultaneous neighbourhoods or assemble a finite free map.
For empty I the free target is zero: choose S empty and W = U. -/
theorem exists_unit_local_support
    (X : Scheme.{u}) (V U : X.Opens) (hUV : U ≤ V) (I : Type u)
    (b : unit ((moduleRings X.toRingedSpace).over U) ⟶
      (overMap (moduleRings X.toRingedSpace) (homOfLE hUV)).obj
        (free (R := (moduleRings X.toRingedSpace).over V) I)) (x : U) :
    ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧ ∃ (S : Finset I)
      (a : unit ((moduleRings X.toRingedSpace).over W) ⟶
        (overMap (moduleRings X.toRingedSpace) (homOfLE (hWU.trans hUV))).obj
          (free (R := (moduleRings X.toRingedSpace).over V) S)),
      a ≫ (overMap (moduleRings X.toRingedSpace) (homOfLE (hWU.trans hUV))).map
        (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : S → I)) =
      (overMap (moduleRings X.toRingedSpace) (homOfLE hWU)).map b := by sorry

end AlgebraicGeometry.Scheme.Modules
