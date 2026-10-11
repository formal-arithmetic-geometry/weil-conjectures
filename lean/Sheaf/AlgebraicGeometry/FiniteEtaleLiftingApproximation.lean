/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.HenselianTerminology
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Finite étale lifting by henselian G-ring approximation

Source: Stacks Project, Fundamental Groups, proof of Lemma 0GS2, the essential-surjectivity
paragraph for a Noetherian G-ring (blueprint: lem-weil-pbc-finite-etale-lifting-approximation).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every finite étale cover of the closed fibre of a proper scheme over a henselian G-ring
lifts to a finite étale cover of the scheme, with an isomorphism over the closed fibre.
Source: Stacks Project, proof of Lemma 0GS2, Noetherian G-ring essential-surjectivity paragraph
(blueprint: lem-weil-pbc-finite-etale-lifting-approximation).

Proof (the eight steps of the DAG node):
1. Complete A at I. The completion is Noetherian, complete and henselian, and its quotient
   by the extended ideal is A/I. Base change Y to the completion; its closed fibre is Y₀.
   Use def-weil-pbc-adic-completion, lem-weil-pbc-adic-completion-mod-ideal,
   lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-complete-pair-henselian,
   lem-weil-pbc-proper-base-change and def-pc-fibre-product.
2. Lift V to the completed base using lem-weil-pbc-finite-etale-lifting-complete.
3. Express the completion as the directed union of its finitely generated A-subalgebras.
   They are finitely presented since A is Noetherian. Their spectra and the corresponding
   base changes of Y form inverse systems with the completed schemes as limits. Use
   def-weil-pbc-category-colimit, lem-weil-pbc-spec-colimit-limit,
   lem-weil-pbc-scheme-over-limit, lem-weil-pbc-proper-base-change,
   def-weil-proper-morphism and def-weil-pbc-scheme-conventions.
4. Descend the completed cover to a finitely presented morphism at a finite stage using
   thm-pd-spreading-out. Increase the stage until it is finite and étale using
   lem-weil-pbc-descend-finite and lem-weil-pbc-descend-etale; finiteness implies affine and
   quasi-compact, while étaleness implies locally finite presentation, as in
   def-weil-finite-integral-morphism, def-weil-etale-morphism and
   def-sbc-locally-finite-presentation. Base change preserves both properties by
   def-weil-pbc-finite-etale-category.
5. Present that algebra by finitely many generators and relations. Apply
   lem-weil-pbc-henselian-pair-approximation with N = 1 to its solution in the completion.
   This gives an A-algebra map from the stage to A agreeing modulo I with the completion
   map, using lem-weil-pbc-adic-completion-mod-ideal.
6. Pull the descended finite étale cover back along this map to obtain U over Y. Use
   def-pc-fibre-product and def-weil-pbc-finite-etale-category.
7. Paste the fibre squares. The agreement modulo I identifies the closed fibre of U with
   that of the completed cover, hence with V over Y₀. Use def-pc-fibre-product and
   lem-weil-pbc-adic-completion-mod-ideal.
8. Thus U is finite étale and its closed fibre is isomorphic to V, as required. -/
theorem exists_finiteEtale_lift_of_henselianPair_of_isGRing
    {A : Type u} [CommRing A] (hA : IsGRing A) (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y,
      Nonempty
        (Over.mk (pullback.snd U.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≅
          Over.mk V.hom) := by
  sorry

end AlgebraicGeometry.Scheme
