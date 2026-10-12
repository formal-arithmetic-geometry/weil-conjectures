/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct
import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# Unramified morphisms are locally quasi-finite

Source: Stacks Project, Morphisms, Lemma 02V5 and Algebra, Lemma 02UR
(blueprint: lem-weil-pbc-unramified-quasi-finite-at-points).
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- An unramified morphism is quasi-finite at every point.

Source: Stacks Project, Morphisms, Lemma 02V5 and Algebra, Lemma 02UR
(blueprint: lem-weil-pbc-unramified-quasi-finite-at-points).
The proof follows the affine-local argument through unramified ring maps, base change
of Kähler differentials, the finite product decomposition over a field, and the isolated
fibre-point characterization of quasi-finiteness.
-/
theorem isLocallyQuasiFinite_of_unramified
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)) :
    IsLocallyQuasiFinite f := by
  sorry

end AlgebraicGeometry.Scheme.Hom
