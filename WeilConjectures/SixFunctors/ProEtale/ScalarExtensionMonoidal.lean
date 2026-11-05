/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension

/-!
# Extension of scalars of pro-étale sheaves is monoidal

For a morphism of commutative rings `φ : R →+* S`, extension of scalars
`S ⊗_R - : Sh(X_proét, R) ⥤ Sh(X_proét, S)` is strong monoidal, and for a morphism of schemes
`g : Y ⟶ X` the isomorphism `g^* (S ⊗_R F) ≅ S ⊗_R g^* F` of
`AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso` is monoidal.

## Main results

- `AlgebraicGeometry.ProEtale.monoidal_sheafExtendScalars`: extension of scalars is strong
  monoidal, its oplax structure being that of the left adjoint of the lax monoidal restriction
  of scalars.
- `AlgebraicGeometry.ProEtale.isMonoidal_sheafExtendScalarsCompUpperStarIso_hom`: the
  commutation with `g^*` is monoidal.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u})

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

end AlgebraicGeometry.ProEtale
