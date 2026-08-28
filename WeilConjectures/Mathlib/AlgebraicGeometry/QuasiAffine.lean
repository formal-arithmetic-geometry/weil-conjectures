/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Quasi-affineness consequences of Zariski's Main Theorem

Zariski's Main Theorem says that a separated, quasi-compact, locally quasi-finite morphism of
finite type `f : X ⟶ Y` factors as an open immersion into the relative normalization of `Y` in
`X` followed by an integral (in particular affine) morphism. We record the two consequences of
this that the Nagata compactification argument uses.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isAffineHom_of_locallyQuasiFinite`:
  such an `f` factors as an open immersion followed by an affine morphism.
* `AlgebraicGeometry.Scheme.IsQuasiAffine.of_locallyQuasiFinite`:
  the source of such an `f` is quasi-affine as soon as the target is.

Neither is an instance: the hypothesis list is long and `LocallyQuasiFinite` is not something
typeclass inference should be asked to discharge.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Zariski's Main Theorem**, in factorization form: a separated, quasi-compact, locally
quasi-finite morphism of finite type factors as an open immersion followed by an affine
morphism. The factorization is through the relative normalization `f.normalization`. -/
theorem Scheme.Hom.exists_isOpenImmersion_isAffineHom_of_locallyQuasiFinite
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    ∃ (W : Scheme.{u}) (j : X ⟶ W) (g : W ⟶ Y), IsOpenImmersion j ∧ IsAffineHom g ∧ j ≫ g = f :=
  ⟨f.normalization, f.toNormalization, f.fromNormalization, inferInstance, inferInstance,
    f.toNormalization_fromNormalization⟩

/-- If `f : X ⟶ Y` is separated, quasi-compact and locally quasi-finite of finite type and `Y` is
quasi-affine, then `X` is quasi-affine. Indeed, by Zariski's Main Theorem `f` factors as an open
immersion `X ⟶ f.normalization` followed by an affine morphism onto `Y`, so `f.normalization` is
quasi-affine, and `X` is a quasi-compact locally closed subscheme of it. -/
theorem Scheme.IsQuasiAffine.of_locallyQuasiFinite [Y.IsQuasiAffine]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    X.IsQuasiAffine :=
  have : f.normalization.IsQuasiAffine := .of_isAffineHom f.fromNormalization
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  .of_isImmersion f.toNormalization

end AlgebraicGeometry
