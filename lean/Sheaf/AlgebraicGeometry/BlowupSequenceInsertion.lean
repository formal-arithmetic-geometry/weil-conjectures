/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.BlowupSequenceInsertionData
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.Density
import Sheaf.TraceFormula.ReducedSchemeImage

/-! # Canonical insertion into an ordinary blowup tower

Source: Temkin, Non-embedded Desingularization, Definition 4.2.2 and Lemmas 4.2.1,
4.2.3, 4.2.5, printed pp.28--29; §4.1.3 for image codimension and density
(blueprint: lem-per-blowup-sequence-insertion).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

open OrdinaryBlowupInsertion

/-- Insert a supported finite tower and extend the remaining centers by schematic closure.
The `Diagram` supplies the new suffix; its initial base is the terminal inserted scheme.
The fixed prefix, the fixed inserted segment and this suffix form the claimed tower.
Uniqueness is unique stagewise isomorphism preserving the ordered ideal centers.
The first center is the strict transform, and an induced tower on that center realizes
its successive blowups. If ambient centers lie in those transforms, the induced center
is identified with that ambient center itself. The final two clauses retain every stage
in flat base changes, including every center ideal and every empty center.

Source: Temkin Definition 4.2.2, Lemmas 4.2.1, 4.2.3, 4.2.5 and §4.1.3
(blueprint: lem-per-blowup-sequence-insertion).

Proof plan, following the node's seven steps:
1. Keep the prefix and append the given tower. The blowup-complement theorem
   `thm-nagata-global-blowup-complement` identifies its preserved open with the old one.
2. Induct along the old suffix. Take the kernel of restriction to the old center over
   the preserved open (`lemma-nagata-scheme-image-ideal-qc`). Its ideal is coherent on
   the Noetherian ambient scheme. Blow it up; properness and finite type preserve
   Noetherianness (`thm-nagata-global-blowup-proper`, `def-weil-proper-morphism`,
   `lem-weil-pbc-finite-type-over-noetherian`).
3. Flat base change of scheme images and blowups along the open immersion identifies
   the new open stages and ideals (`lem-sfb-scheme-image-flat-base-change`,
   `thm-nagata-blowup-flat-base-change`). The intrinsic kernels and the canonical
   blowup universal property give the unique isomorphisms, recursively.
4. Strict transform under an ambient blowup is the blowup in the pulled-back center
   (`lemma-nagata-strict-transform-ambient-closed`). Admissible blowups preserve the
   schematic density of the common open (`lemma-nagata-admissible-blowup-preserves-density`),
   so these transforms have exactly the kernel ideals used in the insertion. When an
   ambient center lies in the transform, its pullback is the same closed subscheme.
5. Apply `lem-trf-reduced-scheme-image` to the restricted reduced center.
6. Properness makes the center images closed. Both images are the closure of the common
   open image. Their generic points lie in the preserved open; composing the injective
   restrictions to that open and then to the local schemes over those generic points
   proves density for the replacement. The identical image has identical codimension.
7. Induct through both segments after a flat base change, whose stage maps stay flat
   (`lem-weil-pbc-flat-morphism-base-change`). Apply flat base change of kernel ideals
   and of blowups to obtain cartesian squares and equality of extended ideals at every
   stage. Unit ideals give identity blowups and are retained, not contracted. -/
theorem ordinaryBlowupSequence_insertion (X : Scheme.{u})
    (P : OrdinaryBlowupInsertion.Input X) :
    ∃ D : OrdinaryBlowupInsertion.Diagram P,
      (∀ E : OrdinaryBlowupInsertion.Diagram P,
        Nonempty (SuffixIso D E) ∧ Subsingleton (SuffixIso D E)) ∧
      (∀ h : P.position.val < P.old.length,
        D.firstNew h = P.transform h (Fin.last P.inserted.length) ∧
        ((∀ i : Fin P.inserted.length,
          P.transform h i.castSucc ≤ P.inserted.center i) →
        ∃ H : CenterTower P h,
          (∃ e : (D.firstNew h).subscheme ≅ H.tower.level (Fin.last H.tower.length),
            e.hom ≫ H.terminalMap = (D.firstNew h).subschemeι) ∧
          ∀ j : Fin H.tower.length,
            ∃ e : (H.tower.center j).subscheme ≅
                (P.inserted.center (Fin.cast H.length_eq j)).subscheme,
              e.hom ≫ (P.inserted.center (Fin.cast H.length_eq j)).subschemeι =
                (H.tower.center j).subschemeι ≫ H.map j.castSucc)) ∧
      (∀ i : Fin D.suffix.length,
        IsReduced (P.old.center
          (shiftCenter P.old.length P.position.val D.suffix.length D.length_eq i)).subscheme →
        IsReduced (D.suffix.center i).subscheme) ∧
      (∀ (i : Fin D.suffix.length) (e : ℕ),
        PureImageCodimension
          ((P.old.center
            (shiftCenter P.old.length P.position.val D.suffix.length D.length_eq i)).subschemeι ≫
            P.old.toBase
              (shiftLevel P.old.length P.position.val D.suffix.length D.length_eq i.castSucc)) e →
        DenseAboveGenericImage
          ((P.old.center
            (shiftCenter P.old.length P.position.val D.suffix.length D.length_eq i)).subschemeι ≫
            P.old.toBase
              (shiftLevel P.old.length P.position.val D.suffix.length D.length_eq i.castSucc)) →
        Set.range ((D.suffix.center i).subschemeι ≫ D.suffix.toBase i.castSucc ≫
          P.inserted.toBase (Fin.last P.inserted.length) ≫ P.old.toBase P.position) =
            Set.range ((P.old.center
              (shiftCenter P.old.length P.position.val D.suffix.length D.length_eq i)).subschemeι ≫
              P.old.toBase
                (shiftLevel P.old.length P.position.val D.suffix.length D.length_eq i.castSucc)) ∧
        PureImageCodimension
          ((D.suffix.center i).subschemeι ≫ D.suffix.toBase i.castSucc ≫
            P.inserted.toBase (Fin.last P.inserted.length) ≫ P.old.toBase P.position) e ∧
        DenseAboveGenericImage
          ((D.suffix.center i).subschemeι ≫ D.suffix.toBase i.castSucc ≫
            P.inserted.toBase (Fin.last P.inserted.length) ≫ P.old.toBase P.position)) ∧
      (∀ (Y : Scheme.{u}) [IsNoetherian Y] (f : Y ⟶ X) [Flat f],
        ∃ Q : OrdinaryBlowupInsertion.Input Y, Nonempty (InputPullback f P Q)) ∧
      (∀ (Y : Scheme.{u}) [IsNoetherian Y] (f : Y ⟶ X) [Flat f]
        (Q : OrdinaryBlowupInsertion.Input Y) (b : InputPullback f P Q),
        ∀ E : OrdinaryBlowupInsertion.Diagram Q,
          Nonempty (TowerPullback b.terminalMap D.suffix E.suffix)) := by
  sorry

end AlgebraicGeometry
