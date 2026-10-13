/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Projection mates on shifted structure sheaves

Source: Stacks Project, Tag 08EU, final sentence of the proof.
(blueprint: lem-pc-qcqs-projection-mate-shifted-unit).
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- The supplied projection mate is invertible when the first factor is a shifted
structure sheaf. No quasi-compactness or quasi-coherence hypothesis is needed.
Source: Stacks Project, Tag 08EU, final sentence of the proof.
(blueprint: lem-pc-qcqs-projection-mate-shifted-unit).

Proof: derived pullback takes the structure sheaf to the structure sheaf and
commutes with shifts. Tensoring with O[k] identifies naturally with translation
by k. These identifications turn t(O[k],-) into a natural isomorphism between
the two shifted versions of pullback. The adjunction between pullback and direct
image induces an adjunction between their shifted versions; the canonical
pullback shift isomorphism induces the direct-image shift isomorphism by mates.
Under these isomorphisms the displayed projection mate is the adjunction
conjugate of the supplied comparison at O[k]. Conjugation preserves inverses,
as follows by inserting the unit/counit formulas and cancelling the two triangle
identities. Thus it is an isomorphism, for any p and t. Naturality in M,
obtained from naturality of t and the counit and the Hom equivalence, transports
the result along hM. For k = 0 this is the unit triangle calculation, modified
by an arbitrary natural automorphism of pullback and its conjugate; for empty
schemes every map here is the unique isomorphism of zero objects. -/
theorem qcqsProjectionMate_shiftedUnit_isIso (X Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedCategory Y) (L : schemeDerivedCategory X) (k : ℤ)
    (hM : Nonempty (M ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings Y.toRingedSpace)))⟦k⟧)) :
    IsIso (p.homEquiv (M ⊗ (schemeDerivedDirectImage f).obj L)
      ((derivedPullback f).obj M ⊗ L)
        (t.hom.app (M, (schemeDerivedDirectImage f).obj L) ≫
          (𝟙 ((derivedPullback f).obj M) ⊗ₘ p.counit.app L))) := by sorry

end AlgebraicGeometry
