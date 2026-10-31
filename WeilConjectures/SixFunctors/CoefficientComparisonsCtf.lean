/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ListedCoefficientCtf

/-! # Listed coefficient extension preserves bounded constructible finite-Tor complexes

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/sk-prop-scalar-six-ctf.md and its proof;
det-prop-scalar-six-ctf.md, clause (3).
(blueprint: det-sfb-coefficient-comparisons-ctf).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Ordinary derived extension along any listed coefficient map preserves Dctf.
The list includes nonflat finite ring maps, continuous integral-to-finite maps,
finite composites and identities. Both bounded constructibility and finite Tor
amplitude are retained on the same small pro-etale site.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/sk-prop-scalar-six-ctf.md and its proof;
det-prop-scalar-six-ctf.md, clause (3).
(blueprint: det-sfb-coefficient-comparisons-ctf).

Proof: Apply clause (3) of det-prop-scalar-six-ctf to the same scheme and
coefficient arrow. Its standing assumptions are exactly separated finite type
over a positive-characteristic field with characteristic different from ell.
The primitive maps in ListedCoefficientMap have the scalar-six presentations;
its composition constructor gives the same finite composites. Thus clause (3)
asserts both components of Dctf membership for the ordinary derived tensor
specified by scalarSixChange. For an identity, its canonical scalar unitor
identifies the derived tensor with K and gives the same conclusion directly.
No flatness or completion is used. -/
theorem coefficientComparisonsCtf (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    constantModelBoundedConstructible Λ'.X X.left ((scalarSixChange a X.left).obj K.obj) ∧
      DerivedCategory.finiteTorAmplitude _ ((scalarSixChange a X.left).obj K.obj) := by
  exact (listedCoefficientCtf ell a ha).2.2 k X K.obj K.property

end AlgebraicGeometry.ProEtale.CondensedRing
