/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.SeparatedLqfBaseChange
import Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.QuasiFiniteIffFiniteFibres
import WeilConjectures.AlgebraicGeometry.NoetherNormalization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.RingTheory.ReducedIdealsZeroIntersection
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Finite etale thickenings after surjective affine base change

Source: Stacks Project, Etale Cohomology, Tag 095K, part (1),
`lemma-decompose-quasi-finite-morphism`
(blueprint: lem-weil-pbc-quasifinite-affine-etale-thickening-decomposition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-finite finitely presented morphism of affine schemes admits a surjective affine
base change on which the source has a finite etale closed subscheme with the same points.
Source: Stacks Project, Tag 095K (1), `lemma-decompose-quasi-finite-morphism`.
(blueprint: lem-weil-pbc-quasifinite-affine-etale-thickening-decomposition)

Proof:
1. Descend the finitely presented affine algebra and its quasi-finiteness to a finitely
   generated Z-subalgebra of the base ring (lem-kun-fp-algebra-descent and
   lem-weil-pbc-descend-quasifinite-affine). This gives a Noetherian affine model, using
   lem-weil-pbc-lfp-affine-opens-finite-presentation,
   lem-weil-pbc-finite-type-over-noetherian and lem-weil-pbc-fibre-product-affine-spectra.
2. Apply generic finiteness and Noetherian induction to partition that model into finitely
   many reduced locally closed affine strata on which the morphism is finite. Use
   lem-weil-pbc-separated-lqf-base-change, lem-pc-quasi-compact-base-change,
   pqf-lem-qf-locqf-qc, pqf-lem-qf-finitefibres,
   lem-weil-pbc-generic-finite-morphism-open-neighborhood, lem-zl-affine-partition,
   lem-sc-affine-noetherian-underlying-space and def-weil-pbc-scheme-reduction.
3. On each stratum apply lem-weil-pbc-finite-affine-section-cover. After a surjective finite
   locally free affine base change the finite source embeds in an affine scheme covered by
   finitely many closed sections. The new base is still Noetherian.
4. Refine the base by the Boolean atoms of the sections' intersections with the source and
   of their pairwise equalizers, then by reduced affine strata (lem-zl-affine-partition).
   Closed immersions survive base change (lem-weil-pbc-closed-immersion-base-change).
   Each intersection and equalizer is now either empty or the whole reduced stratum:
   lem-sc-reduced-ideals-zero-intersection makes its ideal zero in the latter case.
5. Choose one representative of each coinciding section contained in the source. They
   are disjoint and cover its points. The Chinese remainder theorem
   (lem-pc-crt-ideal-quotient-product) identifies their union with finitely many copies of
   the base and makes its inclusion a closed immersion surjective on points. This is
   def-sbc-first-order-thickening's general thickening notion. The composite is finite
   and etale by def-weil-finite-integral-morphism and lem-weil-pbc-scheme-coproduct-copies.
   Zero sections mean an empty source and the empty finite etale scheme.
6. Assemble the finitely many affine base strata by disjoint union
   (lem-weil-pbc-scheme-coproduct-family). It is affine, since a finite disjoint union of
   spectra is the spectrum of their product rings. The base map is surjective, the
   component closed immersions assemble to a thickening, and finiteness and etaleness
   hold on each open-and-closed component (def-weil-pbc-finite-etale-category).
7. Pull back to the original base. Affineness follows from
   lem-weil-pbc-fibre-product-affine-spectra. Surjectivity and closed immersion follow
   from lem-weil-pbc-surjective-base-change and lem-weil-pbc-closed-immersion-base-change;
   finite etaleness follows from the base change functor of
   def-weil-pbc-finite-etale-category. Reassociate the fibre products to obtain the result.
-/
theorem exists_affine_surjective_finite_etale_thickening_of_isQuasiFinite
    {V U : Scheme.{u}} [IsAffine V] [IsAffine U] (h : V ⟶ U)
    (hqf : Scheme.Hom.IsQuasiFinite h)
    (hfp : LocallyOfFinitePresentation h ∧ QuasiCompact h ∧ QuasiSeparated h) :
    ∃ (U' : Scheme.{u}) (_ : IsAffine U') (a : U' ⟶ U),
      Surjective a ∧ ∃ (Z : Scheme.{u}) (i : Z ⟶ pullback h a),
        IsThickening i ∧ IsFinite (i ≫ pullback.snd h a) ∧
          Etale (i ≫ pullback.snd h a) := by
  sorry

end AlgebraicGeometry
