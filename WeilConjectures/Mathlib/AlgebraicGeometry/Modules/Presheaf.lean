/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# The base ring of a scheme over an affine scheme

A morphism of schemes `f : X ⟶ Spec R` induces a ring homomorphism `R →+* Γ(X, ⊤)`, along which
modules over the ring of sections of `X` become `R`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- The ring homomorphism `R →+* Γ(X, ⊤)` induced by a morphism of schemes `f : X ⟶ Spec R`.

The codomain is spelled as the ring of sections of the underlying sheaf of rings
`X.ringCatSheaf` rather than as `Γ(X, ⊤)`: the two carry the same ring structure, but only the
former is the literal ring over which `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)` takes
its values, and matching it is what lets `ModuleCat.restrictScalars` compose with that
evaluation. -/
noncomputable def baseRingHom (f : X ⟶ Spec R) : R →+* X.ringCatSheaf.obj.obj (op ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom

end AlgebraicGeometry.Scheme.Hom
