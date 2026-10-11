/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-!
# Constructible generation on a finite-type scheme

Source: Stacks Project, Tag 03SA, part (3) (blueprint: lem-kun-03sa).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Every sheaf of modules on the small etale site of a scheme of finite type over a
field is a filtered colimit of constructible module sheaves. This is the finite-type
specialization of Stacks Project, Tag 03SA.

Proof: a scheme of finite type over a field is quasi-compact and quasi-separated.
The finite ring `Λ` is Noetherian. Apply the general filtered-colimit theorem
(`lem-weil-pbc-module-sheaf-colimit-constructible`, Stacks Tag 03SA(3)) to `X` and `Λ`.
It supplies a small filtered diagram of constructible module sheaves and a colimit
cocone with value `F`, exactly the conclusion (blueprint: lem-kun-03sa).
-/
theorem constructibleGeneration_finiteType
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (A : Type (u + 1)) (_ : SmallCategory A) (_ : IsFiltered A)
      (D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∀ a : A, Scheme.IsConstructibleEtaleModuleSheaf (D.obj a)) ∧
        ∃ ι : D ⟶ (Functor.const A).obj F,
          Nonempty (IsColimit (Cocone.mk F ι)) := sorry

end AlgebraicGeometry
