/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.Paper.DerivedHomMayerVietoris

/-!
# Finite type modules: images and extensions

Source: Stacks Project, Modules, Lemma 01B7 (blueprint:
lem-weil-pbc-module-finite-type-image-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSpace

/-- Images of finite type module sheaves and extensions of finite type module sheaves are
finite type (blueprint: lem-weil-pbc-module-finite-type-image-extension).

Source: Stacks Project, Modules, Lemma 01B7 (blueprint:
lem-weil-pbc-module-finite-type-image-extension).
Proof: for an epimorphism, push local finite generators along the map.  The image of a
morphism is the codomain of the induced epimorphism from its source to its image.  For a
short exact sequence, locally lift finitely many generators of the quotient and adjoin
finitely many generators of the subobject; the resulting sections generate the middle
object.  The local lifting and exactness arguments are those of the dependency nodes
`def-weil-pbc-module-finite-type-presentation`, `def-weil-pbc-exact-sequence`, and the
source's local lifting lemma.
-/
theorem finiteType_image_extension (X : RingedSpace.{u}) :
    (∀ {F G : SheafOfModules.{u} (moduleRings X)} (p : F ⟶ G),
      [Epi p] → [F.IsFiniteType] → G.IsFiniteType) ∧
    (∀ {F H : SheafOfModules.{u} (moduleRings X)} (φ : F ⟶ H),
      [F.IsFiniteType] → (Abelian.image φ).IsFiniteType) ∧
    (∀ (S : ShortComplex (SheafOfModules.{u} (moduleRings X))),
      S.ShortExact → [S.X₁.IsFiniteType] → [S.X₃.IsFiniteType] → S.X₂.IsFiniteType) := by
  sorry

end AlgebraicGeometry.RingedSpace
