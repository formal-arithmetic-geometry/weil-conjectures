/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.FlatRelationCMOpen
import Sheaf.AlgebraicGeometry.RelationRestrictionQuotient
import Sheaf.AlgebraicGeometry.CohenMacaulayRelationPointSlice
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange

/-! # Slicing a flat equivalence relation

Source: Stacks Project, Bootstrap, Tag 0489 (lemma-slice-equivalence-relation)
(blueprint: lem-sfb-fppf-space-relation-slicing).

The coequalizer of the two Yoneda maps is the sectionwise quotient presheaf.
The two sheafifications are specified by their reflection universal properties;
the equation on quotient maps characterizes the isomorphism induced by `g`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A flat locally finitely presented equivalence relation admits a presentation with
flat, locally finitely presented, locally quasi-finite projections and the same fppf quotient.
Source: Stacks Project, Bootstrap, Tag 0489 (lemma-slice-equivalence-relation)
(blueprint: lem-sfb-fppf-space-relation-slicing).

Proof:
1. Apply lem-sfb-flat-relation-cm-open to find an open `W` of `V` on which the restricted
   relation has Cohen--Macaulay projections. Its saturation map to `V` is surjective,
   flat and locally finitely presented. By lem-sfb-relation-restriction-quotient,
   restriction to `W` preserves the fppf quotient.
2. At every finite type point `w` of `W`, use lem-sfb-cm-relation-point-slice to choose
   an affine slice `A_w → W` through `w`. The saturation `H_w = A_w ×[W] R_W → W`
   is flat, locally finitely presented and locally quasi-finite. The identity relation
   arrow at `w` shows that `w` belongs to its image.
3. Form `A = ∐ A_w` by lem-weil-pbc-scheme-coproduct-family, with induced map `g` to `W`.
   Restrict the relation to `D = (A ×[W] R_W) ×[W] A`. By def-pc-fibre-product, its
   sections are triples `(a,r,b)` with `t(r) = g(a)` and `s(r) = g(b)`. Injectivity
   and the equivalence-relation axioms follow from those of `R_W` on every test.
4. The saturation `H = A ×[W] R_W → W` is the disjoint union of the `H_w → W`.
   Every point has an open component neighbourhood, so the pointwise conditions of
   def-weil-flat-morphism, def-sbc-locally-finite-presentation and pqf-def-quasifinite
   give all three properties for `H → W`.
5. The first projection `D → A` is a base change of `H → W`. Use
   lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence (3),
   and lem-weil-pbc-separated-lqf-base-change (2) for its three properties.
   The involution reversing the unique relation arrow exchanges the projections,
   so the second projection has the same properties.
6. By lem-weil-pbc-flat-lfp-open, the image of `H → W` is open. It contains every
   finite type point by step 2, hence equals `W` by lem-sfb-finite-type-points-detect-open:
   a nonempty closed complement would contain a finite type point. Thus `H → W` is
   surjective and is an fppf cover by def-pc-fppf-site; no Jacobson assumption is needed.
7. Apply lem-sfb-relation-restriction-quotient again to get `A/D ≅ W/R_W`, and compose
   with step 1. Take `V' = A`, `R' = D`, and compose `g` with the open immersion into `V`.
   The projection maps to the original relation give `r`. The sheafification universal
   properties (def-weil-pbc-sheafification) and the quotient-map equation give exactly
   the induced isomorphism of fppf sheaves asserted here.
8. The finite type points form a subset of `W` in universe `u`. The slices, their
   coproduct and the finite fibre products remain in that universe, as required by
   def-weil-size-convention and lem-weil-pbc-scheme-coproduct-family. If `W` is empty,
   the index, slices, coproduct and relation are empty and the local conditions are vacuous.
-/
theorem exists_fppf_relation_slicing {S : Scheme.{u}} {V R : Over S}
    (s t : R ⟶ V)
    (hinj : ∀ T : Over S,
      Function.Injective (fun r : T ⟶ R ↦ (r ≫ s, r ≫ t)))
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Flat s.left] [Flat t.left]
    [LocallyOfFinitePresentation s.left] [LocallyOfFinitePresentation t.left] :
    ∃ (V' R' : Over S) (s' t' : R' ⟶ V') (g : V' ⟶ V) (r : R' ⟶ R)
      (F F' : Sheaf (Scheme.fppfTopology.over S) (Type u))
      (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
      (η' : coequalizer (yoneda.map s') (yoneda.map t') ⟶ F'.obj)
      (e : F' ≅ F),
      (∀ T : Over S,
        Function.Injective (fun a : T ⟶ R' ↦ (a ≫ s', a ≫ t'))) ∧
      (∀ T : Over S, Equivalence (fun a b : T ⟶ V' ↦
        ∃ q : T ⟶ R', q ≫ s' = a ∧ q ≫ t' = b)) ∧
      r ≫ s = s' ≫ g ∧ r ≫ t = t' ≫ g ∧
      Flat s'.left ∧ Flat t'.left ∧
      LocallyOfFinitePresentation s'.left ∧ LocallyOfFinitePresentation t'.left ∧
      Scheme.Hom.IsLocallyQuasiFinite s'.left ∧ Scheme.Hom.IsLocallyQuasiFinite t'.left ∧
      (∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
        Function.Bijective (fun k : F.obj ⟶ G.obj ↦ η ≫ k)) ∧
      (∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
        Function.Bijective (fun k : F'.obj ⟶ G.obj ↦ η' ≫ k)) ∧
      (coequalizer.π (yoneda.map s') (yoneda.map t') ≫ η') ≫ e.hom.hom =
        yoneda.map g ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) := by
  sorry

end AlgebraicGeometry
