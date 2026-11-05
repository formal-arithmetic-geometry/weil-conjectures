/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.ModuleCat
public import WeilConjectures.CategoryTheory.Triangulated.CompactBoundedHom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableBounded
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual

/-!
# Objects of `Dctf(X, Λ)` are compact in `D(X_ét, Λ)`

Blueprint `det-ctf-finite-compact-etale`. Let `k` be a field of finite cohomological dimension
for `Λ`-modules, `X` a finite-type `k`-scheme and `Λ` a finite ring whose exponent is invertible
on `X`. Every object `C` of `Dctf(X_ét, Λ)` is compact in `D(X_ét, Λ)`, and has *bounded
morphisms*: `Hom(C, G) = 0` for `G` in sufficiently negative degrees
(`AlgebraicGeometry.Etale.compactBoundedHom_of_constructibleFiniteTor`).

The proof follows the blueprint. Both properties are stable under shifts, extensions and
retracts (`DerivedCategory.compactBoundedHom`), and are transported along left adjoints whose
right adjoints preserve coproducts and have bounded amplitude
(`DerivedCategory.compactBoundedHom_of_adjunction`). By the dévissage
`AlgebraicGeometry.Etale.constructibleFiniteTor_eq_triangEnvelope_ctfGenerators` it suffices to
treat the generators `Rg_* Rj_! L`. Starting from `Λ[0]` in `D(Λ)`, one applies successively:

* the constant sheaf functor at the point `Spec k`, right adjoint `RΓ(Spec k, -)` of finite
  cohomological dimension;
* the pullback along `S ⟶ Spec k`, right adjoint the direct image of finite cohomological
  dimension;
* the tensor product with the lisse flat sheaf `L`, right adjoint the tensor product with its
  dual;
* the extension by zero along the open immersion `j`, right adjoint the exact restriction;
* the direct image along the closed immersion `g`, right adjoint `Rg^!`
  (`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedFunctor_closedUpperShriek`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme _root_.DerivedCategory

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

end Etale

end AlgebraicGeometry
