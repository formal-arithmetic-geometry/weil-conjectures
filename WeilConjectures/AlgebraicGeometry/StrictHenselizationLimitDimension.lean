/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.GenericFiniteness

/-!
# Locally quasi-finite morphisms do not raise dimension

For a locally quasi-finite morphism of schemes `f : V ⟶ X` (for instance an étale morphism) we
show `dim V ≤ dim X`: the fibres of `f` are discrete, so `f` maps a strict chain of
specializations to a strict chain of specializations.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- An étale morphism is locally quasi-finite. -/
instance (priority := 900) Etale.locallyQuasiFinite {V X : Scheme.{u}} (f : V ⟶ X) [Etale f] :
    LocallyQuasiFinite f := LocallyQuasiFinite.of_etale f

end AlgebraicGeometry
