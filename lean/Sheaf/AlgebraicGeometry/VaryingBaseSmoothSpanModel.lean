/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.FixedFamilyEtaleSpanDescent
import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import WeilConjectures.RingTheory.FiniteTypeIntGRing
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.PopescuSmoothing
import WeilConjectures.RingTheory.RegularComposition

/-!
# A smooth model for an étale span with a varying base map

Source: Stacks Project, More on Morphisms, Tag 0GDX,
`lemma-relative-map-approximation-pre`, second and third proof paragraphs
(blueprint: lem-trf-varying-base-smooth-span-model).

The helper is the canonical projection between the prescribed target pullbacks.
The theorem retains both target families, the actual arrows, and their residue maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical projection from the completed-base target to its smooth-stage model.
It preserves the projection to `X` and sends the base coordinate along `r`.
Source: Stacks Project, Tag 0GDX, second and third proof paragraphs
(blueprint: lem-trf-varying-base-smooth-span-model). -/
noncomputable def varyingBaseSpanProjection
    {X S V B : Scheme.{u}} (f : X ⟶ S) (q : V ⟶ S) (r : B ⟶ V)
    (β : B ⟶ S) (hr : r ≫ q = β) : pullback f β ⟶ pullback f q :=
  pullback.map f β f q (𝟙 X) r (𝟙 S)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id β).trans hr.symm)

/-- An affine finitely presented elementary étale span over a completed local base
has a smooth pointed model, including a factorization of the varying map to `Spec D`.
The chosen point `b` is required to be closed; the completed local ring is Noetherian
and local under the hypotheses, so this specifies precisely its unique closed point.
Finite presentation of the affine span sources is expressed by local finite presentation:
all their bases are affine, so quasi-compactness and quasi-separatedness are automatic.
The three equations involving `e.hom` express that `e` is over the completed base
and intertwines both actual base changes, by the universal property of pullbacks.

Source: Stacks Project, Tag 0GDX, `lemma-relative-map-approximation-pre`, second and
third proof paragraphs (blueprint: lem-trf-varying-base-smooth-span-model).

Proof:
1. The integers are Noetherian by lem-weil-pbc-finite-type-z-g-ring and
   def-weil-pbc-g-ring. The scheme finite type hypotheses give locally Noetherian
   bases by pqf-def-locnoeth and pqf-lem-locnoeth-lft. Their affine coordinate rings
   are Noetherian by pqf-lem-affine-open-locnoeth. Identify the stalk with the prime
   localization by lem-weil-pbc-affine-open-stalk-localization. Its Noetherianity is
   lem-weil-pbc-localization-noetherian, and that of its completion is
   lem-weil-pbc-adic-completion-noetherian.
2. By pqf-lem-lft-fp-locnoeth and lem-weil-pbc-lfp-affine-opens-finite-presentation,
   R and D are finitely presented over the integers. Thus R is a G-ring by
   lem-weil-pbc-finite-type-z-g-ring. The local completion map is regular by
   def-weil-pbc-g-ring, and localization is regular by lem-weil-pbc-localization-regular.
   Each composite fibre is a localization of a quotient of the Noetherian completion,
   hence Noetherian by lem-weil-pbc-surjective-image-noetherian and
   lem-weil-pbc-localization-noetherian. Apply lem-weil-pbc-regular-composition.
3. Apply lem-weil-pbc-popescu-smoothing to this regular map and reindex by
   lem-weil-pbc-filtered-category-directed-cofinal. The resulting nonempty directed
   system consists of smooth affine S-schemes. Its limit is the actual completed base
   with its canonical projections, by lem-weil-pbc-limit-affine-transition and
   lem-weil-pbc-morphism-affine-schemes-affine.
4. By lem-weil-pbc-local-completion-local-ring the canonical residue map from s to b
   is an isomorphism. At every stage it factors through the residue field of the
   image of b. The latter field injects into κ(b) and contains the surjective image
   of κ(s), so both maps in this factorization are isomorphisms.
5. The stages are qcqs by lem-weil-pbc-affine-scheme-qcqs. Apply
   lem-weil-pbc-finite-presentation-map-limit-factorization to lam over Spec ℤ.
   On the upper tail all maps to T factor lam; cones on this tail extend uniquely
   using common upper bounds, so it still has the same limit.
6. The affine families X and Y are finitely presented by pqf-lem-lft-fp-locnoeth and
   lem-weil-pbc-qcqs-morphism-permanence. Their pullbacks to the chosen stage are
   affine by lem-weil-pbc-fibre-product-affine-spectra and finitely presented by
   lem-weil-pbc-qcqs-morphism-permanence. Pullback uniqueness identifies their limit
   base changes with the prescribed targets, preserving all projections.
7. Apply lem-trf-fixed-family-etale-span-descent to these two fixed families and H.
   Step 4 gives its residue hypothesis. It descends both étale arrows to one later
   smooth affine stage and gives an isomorphism over B intertwining their pullbacks.
   The projection-preserving identifications of step 6 give the two displayed
   equations with varyingBaseSpanProjection by pullback uniqueness.
8. Project e⁻¹(h) to obtain the marked stage point. The same fixed-family descent
   gives both target residue comparisons, the source comparison, and the two
   elementary étale residue maps. Its point equations put all three points over
   r(b). Step 4 gives the two base residue isomorphisms, and step 5 gives lam'(r(b))=lam(b).
-/
theorem exists_varyingBase_smooth_span_model
    (R D : CommRingCat.{u}) (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y]
    (sZ : Spec R ⟶ Spec (.of (ULift.{u} ℤ)))
    (tZ : Spec D ⟶ Spec (.of (ULift.{u} ℤ)))
    [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    [LocallyOfFiniteType tZ] [QuasiCompact tZ]
    (f : X ⟶ Spec R) (g : Y ⟶ Spec D)
    [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType g] [QuasiCompact g]
    (s : Spec R)
    (b : Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
      ((Spec R).presheaf.stalk s))))
    (hb : IsClosed ({b} : Set (Spec (.of
      (AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
        ((Spec R).presheaf.stalk s))))))
    (lam : Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
      ((Spec R).presheaf.stalk s))) ⟶ Spec D)
    (H : Scheme.{u}) [IsAffine H]
    (p : H ⟶ Spec (.of
      (AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
        ((Spec R).presheaf.stalk s)))) [LocallyOfFinitePresentation p]
    (h : H) (hh : p h = b)
    (a : H ⟶ pullback f ((Spec.map (CommRingCat.ofHom
      (algebraMap ((Spec R).presheaf.stalk s)
        (AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
          ((Spec R).presheaf.stalk s)))) ≫ (Spec R).fromSpecStalk s)))
    (c : H ⟶ pullback g lam) [Etale a] [Etale c]
    (ha : a ≫ pullback.snd f ((Spec.map (CommRingCat.ofHom
      (algebraMap ((Spec R).presheaf.stalk s)
        (AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
          ((Spec R).presheaf.stalk s)))) ≫ (Spec R).fromSpecStalk s)) = p)
    (hc : c ≫ pullback.snd g lam = p)
    (haκ : IsIso (a.residueFieldMap h)) (hcκ : IsIso (c.residueFieldMap h)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Spec R), IsAffine V ∧ Smooth q ∧
      ∃ (r : Spec (.of
        (AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
          ((Spec R).presheaf.stalk s))) ⟶ V)
        (lam' : V ⟶ Spec D) (hr : r ≫ q = (Spec.map (CommRingCat.ofHom
          (algebraMap ((Spec R).presheaf.stalk s)
            (AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
              ((Spec R).presheaf.stalk s)))) ≫ (Spec R).fromSpecStalk s))
        (hlam : r ≫ lam' = lam) (H' : Scheme.{u}) (p' : H' ⟶ V),
        IsAffine H' ∧ LocallyOfFinitePresentation p' ∧
        ∃ (a' : H' ⟶ pullback f q) (c' : H' ⟶ pullback g lam'),
          Etale a' ∧ Etale c' ∧
          a' ≫ pullback.snd f q = p' ∧ c' ≫ pullback.snd g lam' = p' ∧
          ∃ e : pullback p' r ≅ H,
            e.hom ≫ p = pullback.snd p' r ∧
            e.hom ≫ a ≫ varyingBaseSpanProjection f q r ((Spec.map (CommRingCat.ofHom
              (algebraMap ((Spec R).presheaf.stalk s)
                (AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
                  ((Spec R).presheaf.stalk s)))) ≫ (Spec R).fromSpecStalk s)) hr =
              pullback.fst p' r ≫ a' ∧
            e.hom ≫ c ≫ varyingBaseSpanProjection g lam' r lam hlam =
              pullback.fst p' r ≫ c' ∧
            q (r b) = s ∧ lam' (r b) = lam b ∧
            p' ((e.inv ≫ pullback.fst p' r) h) = r b ∧
            pullback.snd f q (a' ((e.inv ≫ pullback.fst p' r) h)) = r b ∧
            pullback.snd g lam' (c' ((e.inv ≫ pullback.fst p' r) h)) = r b ∧
            IsIso (q.residueFieldMap (r b)) ∧ IsIso (r.residueFieldMap b) ∧
            IsIso (Scheme.Hom.residueFieldMap
              (varyingBaseSpanProjection f q r ((Spec.map (CommRingCat.ofHom
                (algebraMap ((Spec R).presheaf.stalk s)
                  (AdicCompletion (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk s))
                    ((Spec R).presheaf.stalk s)))) ≫ (Spec R).fromSpecStalk s)) hr) (a h)) ∧
            IsIso ((varyingBaseSpanProjection g lam' r lam hlam).residueFieldMap (c h)) ∧
            IsIso ((e.inv ≫ pullback.fst p' r).residueFieldMap h) ∧
            IsIso (a'.residueFieldMap ((e.inv ≫ pullback.fst p' r) h)) ∧
            IsIso (c'.residueFieldMap ((e.inv ≫ pullback.fst p' r) h)) := by
  sorry

end AlgebraicGeometry
