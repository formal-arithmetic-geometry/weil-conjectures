/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Degreewise monomorphism in qcqs single-complex base change

Source: Stacks Project, Tag 0DJ9.
(blueprint: lem-pc-single-complex-qcqs-homology-mono).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The monomorphism part in one degree of the qcqs single-complex stalk criterion.

Source: Stacks Project, Tag 0DJ9, lemma-single-complex-base-change.
(blueprint: lem-pc-single-complex-qcqs-homology-mono).

Proof: Exact restriction to target opens detects the assertion, so restrict to
an affine new base mapping into an affine original base. The source is then
quasi-compact and quasi-separated. For an affine source open, translate
quasi-coherent derived objects into complexes of modules. The localized stalk
condition identifies the canonical comparison and makes it invertible in every
degree. Induct over quasi-compact source opens. In a union of two such opens,
the intersection is quasi-compact by quasi-separatedness. The two relative
Mayer--Vietoris triangles and the canonical comparison form a morphism of
triangles. Their long exact cohomology sequences propagate degreewise
invertibility from the two opens and their intersection to the union. The
quasi-compact-open induction principle reaches the whole source. The top-open
comparison is the original mate followed by direct image of phi. Retain its
monomorphism in degree n and descend from the target-open restriction. Zero
objects, empty schemes and negative degrees require no extra hypotheses. -/
theorem singleComplexBaseChange_homology_mono
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ) (n : ℤ) :
    Mono ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) n).map
        (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
          (schemeDerivedDirectImage f').map φ)) := by sorry

end AlgebraicGeometry
