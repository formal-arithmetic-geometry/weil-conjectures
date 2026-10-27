/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.RingTheory.CompletionMapForLocalHom
import Sheaf.AlgebraicGeometry.CompletedLocalBaseChange
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.TraceFormula.IsomorphismCompletionApproximation
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompleteLocalGRing
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Localization.Submodule

/-! # An affine étale span over the completed local base

Source: Stacks Project, More on Morphisms, Tags 0GDX and 0CAV,
`lemma-relative-map-approximation-pre`, first proof paragraph, and
`lemma-isomorphism-approximation`.
(blueprint: lem-trf-completed-base-affine-etale-span)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A formal isomorphism over the completed base gives an affine elementary étale span.
The base points `s,t` are written as `f x,g y`. The completed-base point is the prime
obtained from the zero prime of the residue field by the first completion coordinate.
The scalar compatibility equation uses the canonical completion of `f.stalkMap x`;
its quotient coordinates determine it uniquely, so the choice is not arbitrary.
The base map B → S is written out as `Spec.map (algebraMap A Â) ≫ S.fromSpecStalk s`,
and X_B as its pullback along f.

Source: Stacks Project, Tags 0GDX (first proof paragraph) and 0CAV.
(blueprint: lem-trf-completed-base-affine-etale-span)

Proof:
1. Finite type over Spec ℤ makes S Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Its affine rings are Noetherian
   (pqf-lem-affine-open-locnoeth), and the stalk is their prime localization
   (lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-noetherian).
2. Completion is Noetherian and local and preserves the residue field
   (lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring).
   Module completeness (lem-weil-pbc-module-completion-complete) and equality of
   the extended maximal-ideal powers give completeness of this local ring. Apply
   lem-weil-pbc-complete-local-g-ring. Spec of the Noetherian completion is Noetherian.
3. Apply lem-trf-completed-local-base-change for the unique point xB and its completed
   stalk isomorphism. The fibre is Spec of κ(x) tensor κ(b) over κ(s)
   (lem-weil-pbc-fibre-product-points). Since κ(s) → κ(b) is an isomorphism this is
   Spec κ(x); lem-weil-pbc-fibre-product-point-residue-field gives the residue clause.
4. Both base changes are finite type (lem-sfb-finite-type-composition-base-change).
   Compose the inverse given formal isomorphism with the one in step 3. The resulting
   isomorphism is over the base stalk, which equals the complete local base ring.
   Apply lem-trf-isomorphism-completion-approximation with N = 2 to obtain the two
   elementary étale arrows over B.
5. Shrink their common source around the marked point to an affine open
   (lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink). Both arrows remain étale
   (lem-weil-pbc-etale-composition-cancellation), and open restriction preserves the
   marked stalk and its residue field. The structure map and marked point remain over B.
6. The structure map is locally finite type by the étale/unramified definitions and
   lem-weil-pbc-proper-fp-permanence. Over the Noetherian base it is locally finitely
   presented (pqf-lem-lft-fp-locnoeth). The base is separated
   (lem-weil-pbc-affine-source-morphism-separated). The affine source then makes its
   map affine (lem-weil-pbc-affine-source-separated-target-affine-morphism), hence
   quasi-compact and quasi-separated (lem-weil-pbc-affine-morphism-permanence).
-/
theorem completedBaseAffineEtaleSpan
    {X S Y T : Scheme.{u}} [IsAffine X] [IsAffine S] [IsAffine Y] [IsAffine T]
    (f : X ⟶ S) (g : Y ⟶ T)
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    (sZ : S ⟶ Spec (.of (ULift.{u} ℤ))) (tZ : T ⟶ Spec (.of (ULift.{u} ℤ)))
    [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    [LocallyOfFiniteType tZ] [QuasiCompact tZ]
    (x : X) (y : Y)
    (σ : T.presheaf.stalk (g y) →+*
      AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
        (S.presheaf.stalk (f x))) [IsLocalHom σ]
    (yB : pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk (g y)))
    (hyB : pullback.fst g (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk (g y)) yB = y)
    (hb : pullback.snd g (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk (g y)) yB =
      PrimeSpectrum.comap
        (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).toRingHom
        ⟨⊥, inferInstance⟩)
    (hformal : ∃ e :
        AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
        AdicCompletion
          (IsLocalRing.maximalIdeal
            ((pullback g (Spec.map (CommRingCat.ofHom σ) ≫
              T.fromSpecStalk (g y))).presheaf.stalk yB))
          ((pullback g (Spec.map (CommRingCat.ofHom σ) ≫
            T.fromSpecStalk (g y))).presheaf.stalk yB),
      e.toRingHom.comp
          (Classical.choose (RingHom.exists_adicCompletion_map_of_local (f.stalkMap x).hom)) =
        (algebraMap
          ((pullback g (Spec.map (CommRingCat.ofHom σ) ≫
            T.fromSpecStalk (g y))).presheaf.stalk yB)
          (AdicCompletion
            (IsLocalRing.maximalIdeal
              ((pullback g (Spec.map (CommRingCat.ofHom σ) ≫
                T.fromSpecStalk (g y))).presheaf.stalk yB))
            ((pullback g (Spec.map (CommRingCat.ofHom σ) ≫
              T.fromSpecStalk (g y))).presheaf.stalk yB))).comp
          (((pullback.snd g (Spec.map (CommRingCat.ofHom σ) ≫
            T.fromSpecStalk (g y))).stalkMap yB).hom.comp
            (StructureSheaf.toStalk
              (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
                (S.presheaf.stalk (f x)))
              ((pullback.snd g (Spec.map (CommRingCat.ofHom σ) ≫
                T.fromSpecStalk (g y))) yB)).hom)) :
    IsNoetherian
        (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
          (S.presheaf.stalk (f x))))) ∧
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))))) ≫ S.fromSpecStalk (f x)).residueFieldMap
        (PrimeSpectrum.comap
          (AdicCompletion.evalOneₐ
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).toRingHom
          ⟨⊥, inferInstance⟩)) ∧
      ∃ xB : pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))))) ≫ S.fromSpecStalk (f x)),
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))))) ≫ S.fromSpecStalk (f x)) xB = x ∧
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))))) ≫ S.fromSpecStalk (f x)) xB =
          PrimeSpectrum.comap
            (AdicCompletion.evalOneₐ
              (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).toRingHom
            ⟨⊥, inferInstance⟩ ∧
        (∀ z : pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))))) ≫ S.fromSpecStalk (f x)),
          pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))))) ≫ S.fromSpecStalk (f x)) z = x →
          pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))))) ≫ S.fromSpecStalk (f x)) z =
            PrimeSpectrum.comap
              (AdicCompletion.evalOneₐ
                (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).toRingHom
              ⟨⊥, inferInstance⟩ → z = xB) ∧
        IsIso ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))))) ≫ S.fromSpecStalk (f x))).residueFieldMap xB) ∧
        ∃ (H : Scheme.{u}) (h : H)
          (p : H ⟶ Spec (.of
            (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
              (S.presheaf.stalk (f x)))))
          (a : H ⟶ pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))))) ≫ S.fromSpecStalk (f x)))
          (c : H ⟶ pullback g (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk (g y))),
          IsAffine H ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p ∧
          p h = PrimeSpectrum.comap
            (AdicCompletion.evalOneₐ
              (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).toRingHom
            ⟨⊥, inferInstance⟩ ∧
          a ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (f x))
          (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
            (S.presheaf.stalk (f x))))) ≫ S.fromSpecStalk (f x)) = p ∧
          c ≫ pullback.snd g (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk (g y)) = p ∧
          Etale a ∧ Etale c ∧ a h = xB ∧ c h = yB ∧
          IsIso (a.residueFieldMap h) ∧ IsIso (c.residueFieldMap h) := by
  sorry

end AlgebraicGeometry
