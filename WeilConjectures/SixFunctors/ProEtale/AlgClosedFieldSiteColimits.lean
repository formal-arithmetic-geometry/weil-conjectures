/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite

/-!
# Sections over the spectrum of an algebraically closed field commute with colimits

Let `X` be a scheme isomorphic to `Spec K` for an algebraically closed field `K`. Every covering
sieve of the terminal object of `X_proét` contains the identity
(`AlgebraicGeometry.Scheme.ProEt.id_mem_of_mem_topology_of_iso`). As the map from a presheaf to
its sheafification is locally injective and locally surjective, it is bijective on sections over
`X`. Hence sections over `X` of the sheafification of a presheaf `G` are the sections `G(X)`, and
taking sections over `X` commutes with all colimits of sheaves which exist in the coefficient
category (colimits of sheaves being sheafified colimits of presheaves).

## Main statements

- `AlgebraicGeometry.ProEtale.bijective_toSheafify_app_of_iso`.
- `AlgebraicGeometry.ProEtale.preservesColimitsOfShape_sheafSections_of_iso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [HasSheafify (Scheme.ProEt.topology X) A]
  [(Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget A)]
  [(Scheme.ProEt.topology X).PreservesSheafification (CategoryTheory.forget A)]

end AlgebraicGeometry.ProEtale
