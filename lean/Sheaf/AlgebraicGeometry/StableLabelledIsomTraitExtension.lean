/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.GroupTheory.Perm.Basic

import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction
import Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Unique extension of labelled stable isomorphisms over a trait

Source: the marked, persistently nodal log-canonical common-model argument in
literature/stacks-project/moduli-curves.tex, motivated by Tag 0E97
(lemma-unique-stable-model), and de Jong (1997), §3.8, pp. 608–609
(blueprint: lem-sfb-stable-labelled-isom-trait-extension).

The generic fibres are the iterated fibre products over `Spec R` and `Spec K`.
Isomorphisms in `Over` include the required compatibility with the base scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every generic isomorphism of stable pointed curves that respects a fixed permutation
of the labels extends uniquely over an arbitrary DVR. Markings are compared as morphisms.
No excellence, finite-type condition on the trait, generic smoothness or identity condition
on the isomorphism is imposed.
Source: marked log-canonical common-model argument, Stacks moduli-curves.tex,
Tag 0E97 (lemma-unique-stable-model) as motivation; de Jong (1997), §3.8, pp. 608–609
(blueprint: lem-sfb-stable-labelled-isom-trait-extension).

Proof:
1. Pull both families back to the trait and relabel the second by the given permutation.
   Projective-bundle affine presentations give finite-projective-space embeddings:
   an open containing the image of the trait's closed point pulls back to the whole trait.
   Use `lem-trf-projective-bundle-affine-presentations`,
   `lem-weil-pbc-closed-immersion-products`,
   `lem-weil-pbc-closed-immersion-base-change`, and
   `def-nagata-projective-space-base-change`. Flatness and finite presentation persist
   by `lem-weil-pbc-flat-morphism-base-change` and
   `lem-weil-pbc-qcqs-morphism-permanence`. Geometric fibres are unchanged by associativity
   of fibre products. Smooth markings stay smooth by
   `lem-sbc-smooth-relative-dimension-permanence` and `def-sbc-smooth-morphisms`.
2. The trait is Noetherian by `def-sc-discrete-valuation-ring`. Apply
   `lem-sfb-nodal-log-canonical-reconstruction`. On every normalized component the
   logarithmic dualizing degree is `2g - 2 + r`, positive by stability in genera zero,
   one and at least two. Thus each family is canonically the Proj of its log-canonical
   section algebra, including degree zero and the case of no markings.
3. By `lem-sfb-semistable-log-pluricanonical-lattices`, generic restriction is injective
   in every degree and the prescribed generic isomorphism identifies the section lattices.
   Compatibility with multiplication and units gives a graded unital R-algebra isomorphism.
4. Apply `prop-nagata-relative-proj-functoriality` contravariantly and conjugate by the
   reconstruction isomorphisms. Projectivity implies properness by
   `lem-kun-projective-implies-proper`. The fraction field is flat over R by
   `lem-weil-pbc-localization-flat`. Degree-zero flat base change for each tensor power
   (`lem-pc-flat-base-change-cohom`) identifies generic section algebras. Flat Proj base
   change and the chart formulas and isomorphism-naturality of
   `lem-sfb-proper-ample-section-proj-reconstruction` identify the generic restriction
   with the originally prescribed isomorphism.
5. The target is separated by properness. Flatness over the DVR makes multiplication
   by a uniformizer injective in local rings. Localization gives the geometrically
   reduced generic fibre, so the source is reduced. Every nonempty affine open meets
   the generic fibre, since otherwise the uniformizer would be nilpotent. Thus the
   generic fibre is dense. The trait itself is reduced with dense generic point.
6. Apply `lem-sfb-relative-separated-dominant-ext` first to the two maps from the trait
   obtained from each marked section, and then to any two extensions from the source
   curve. This proves the section equations and uniqueness. Relabel the target back.
   None of these steps requires the trait's generic point to map to a generic point
   of the original base. -/
theorem existsUnique_stable_labelled_isom_trait_extension
    {S W W' : Scheme.{u}} [IsLocallyNoetherian S]
    (f : W ⟶ S) (f' : W' ⟶ S) (n : ℕ)
    (s : Fin n → (S ⟶ W)) (s' : Fin n → (S ⟶ W'))
    (hs : ∀ i, s i ≫ f = 𝟙 S) (hs' : ∀ i, s' i ≫ f' = 𝟙 S)
    (hstable : IsStablePointedCurve f s hs) (hstable' : IsStablePointedCurve f' s' hs')
    (σ : Equiv.Perm (Fin n))
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (b : Spec (.of R) ⟶ S)
    (uK : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        ((Over.pullback b).obj (Over.mk f)) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        ((Over.pullback b).obj (Over.mk f')))
    (hmarks : ∀ i : Fin n,
      (pullback.snd f b).baseChangeSection
          (f.baseChangeSection (s i) (hs i) b)
          (f.baseChangeSection_snd (s i) (hs i) b)
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ uK.hom.left =
        (pullback.snd f' b).baseChangeSection
          (f'.baseChangeSection (s' (σ i)) (hs' (σ i)) b)
          (f'.baseChangeSection_snd (s' (σ i)) (hs' (σ i)) b)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    ∃! uR : (Over.pullback b).obj (Over.mk f) ≅ (Over.pullback b).obj (Over.mk f'),
      (∀ i : Fin n, f.baseChangeSection (s i) (hs i) b ≫ uR.hom.left =
        f'.baseChangeSection (s' (σ i)) (hs' (σ i)) b) ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapIso uR = uK := by
  sorry

end AlgebraicGeometry
