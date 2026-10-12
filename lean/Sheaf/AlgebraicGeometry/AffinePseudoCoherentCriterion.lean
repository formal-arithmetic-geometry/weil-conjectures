/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.RingTheory.RingPseudoCoherentLocalizationGlue

/-! # Pseudo-coherence on an affine scheme

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.10.2, Tag 08E7,
pseudo-coherent clause (blueprint: lem-pc-affine-pseudo-coherent-criterion).
-/

@[expose] public section

universe u wA wX

open CategoryTheory

namespace AlgebraicGeometry

/-- The object obtained by associating sheaves termwise to a complex of `A`-modules on
`Spec A` is pseudo-coherent precisely when the module complex is quasi-isomorphic to a
bounded-above complex of finite free modules. The affine equivalence
`lem-pc-affine-qcoh-derived-equivalence` identifies this termwise construction with its
image in the quasi-coherent derived category.

Source: Stacks Project, Tag 08E7, Lemma 36.10.2, pseudo-coherent clause
(blueprint: lem-pc-affine-pseudo-coherent-criterion).

Proof:
1. Given a bounded-above finite free model, associate sheaves termwise, using
   `lem-pc-affine-qcoh-derived-equivalence`. The tilde functor sends A to the structure
   sheaf and preserves finite sums (`lem-weil-pbc-affine-tilde-gamma-adjunction`, part 4).
   The resulting complex is finite free and bounded above on the one-member cover.
   Apply `def-pur-pseudo-coherent-complex`.
2. Conversely, local pseudo-coherence gives bounded-above finite free models near every
   point. Quasi-compactness and the standard-open basis give a finite cover by D(f_i)
   refining these neighbourhoods, with the f_i generating the unit ideal.
3. Over D(f_i), restriction of tilde(M) is tilde(M localized at f_i), by
   `lem-weil-pbc-spec-module-tilde-sections`. Full faithfulness of tilde on free modules
   (`lem-weil-pbc-affine-tilde-gamma-adjunction`, parts 1 and 2) lifts the local model's
   differentials to module maps. The affine derived equivalence then identifies the
   localized module complex with this bounded-above finite free model.
4. Apply `lem-pc-ring-pseudo-coherent-localization-glue` to these finitely many
   localizations to obtain a bounded-above finite free model over A.
-/
theorem isPseudoCoherent_affine_iff (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    Scheme.IsPseudoCoherent (Spec (.of A))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M)) ↔
      DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj M) := by
  sorry

end AlgebraicGeometry
