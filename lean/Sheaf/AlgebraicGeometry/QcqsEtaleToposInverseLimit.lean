/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.QcqsEtaleLimitPresentation

import Sheaf.AlgebraicGeometry.QcqsEtaleLimitPresentationExists
import Sheaf.AlgebraicGeometry.QcqsEtalePresentationToposLimit
import Sheaf.AlgebraicGeometry.QcqsEtalePresentationComparison
import Sheaf.Paper.FinitarySiteEnoughPoints
import Sheaf.AlgebraicGeometry.EtaleToposPointsGeometric
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Sites.Finite

/-!
# Inverse limits of qcqs etale topoi

Source: Stacks Project, Sites, Tags 09YL, 0A35, 00YQ; ILO XX 4.4, printed p.373
(blueprint: lem-per-qcqs-etale-topos-inverse-limit).

All site and projection data are explicit in `QcqsEtaleLimit.Presentation`. The last clause
allows cofinal reindexing and a compatible isomorphism of scheme diagrams simultaneously.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private lemma presieve_canonical_family
    {C : Type (u + 1)} [SmallCategory C] {X : C} (R : Presieve X) :
    Presieve.ofArrows (fun k : R.uncurry ↦ k.val.1) (fun k ↦ k.val.2) = R := by
  apply le_antisymm
  · rintro Y f ⟨k⟩
    exact k.property
  · intro Y f hf
    exact .mk (⟨⟨Y, f⟩, hf⟩ : R.uncurry)

private lemma presentation_cover_finite
    {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}}
    (P : QcqsEtaleLimit.Presentation D) :
    P.cover ≤ Precoverage.finite P.colimit.pt := by
  intro X R hR
  obtain ⟨i, U, S, hU, hS, hmap⟩ := (P.cover_iff X R).mp hR
  subst X
  subst R
  change (S.map (P.colimit.ι.app (Opposite.op i)).toFunctor).uncurry.Finite
  let : Finite S.uncurry := ((P.stageCover_iff i U S).mp hS).1
  have hs : S.uncurry.Finite := Set.toFinite _
  apply (hs.image (fun f ↦
    ⟨(P.colimit.ι.app (Opposite.op i)).toFunctor.obj f.1,
      (P.colimit.ι.app (Opposite.op i)).toFunctor.map f.2⟩)).subset
  rintro ⟨Y, f⟩ hf
  cases hf with
  | of h => exact ⟨⟨_, _⟩, h, rfl⟩

private lemma finite_cover_site
    {C : Type (u + 1)} [SmallCategory C] [HasFiniteLimits C]
    (K : Precoverage C) (hf : K ≤ Precoverage.finite C)
    [K.HasIsos] [K.IsStableUnderFiniteComposition] [K.IsStableUnderFiniteBaseChange] :
    K.IsSiteForCoverings := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · intro X R T hR hT
    let : Finite R.uncurry := (hf X hR).to_subtype
    let U (i : R.uncurry) := i.val.1
    let f (i : R.uncurry) : U i ⟶ X := i.val.2
    let S (i : R.uncurry) := T (f i) i.property
    let (i : R.uncurry) : Finite (S i).uncurry :=
      (hf (U i) (hT _ _ i.property)).to_subtype
    have hR' : Presieve.ofArrows U f ∈ K X := by
      simpa only [U, f, presieve_canonical_family] using hR
    have hS (i : R.uncurry) :
        Presieve.ofArrows (fun j : (S i).uncurry ↦ j.val.1) (fun j ↦ j.val.2) ∈
          K (U i) := by
      rw [presieve_canonical_family]
      exact hT _ _ i.property
    have hc := Precoverage.IsStableUnderFiniteComposition.comp_mem_coverings
      (J := K) f hR' (fun i (j : (S i).uncurry) ↦ j.val.2) hS
    have he :
        Presieve.ofArrows (fun k : Σ i, (S i).uncurry ↦ k.2.val.1)
          (fun k ↦ k.2.val.2 ≫ f k.1) = R.bind (fun _ g hg ↦ T g hg) := by
      apply le_antisymm
      · rintro Y g ⟨⟨i, j⟩⟩
        exact ⟨_, _, _, i.property, j.property, rfl⟩
      · rintro Y g ⟨Z, a, b, hb, ha, rfl⟩
        exact .mk (⟨⟨⟨Z, b⟩, hb⟩, ⟨⟨Y, a⟩, ha⟩⟩ : Σ i, (S i).uncurry)
    rwa [he] at hc
  · intro A X U a ha Y b
    let R := Presieve.ofArrows U a
    let : Finite R.uncurry := (hf X ha).to_subtype
    have hc := Precoverage.IsStableUnderFiniteBaseChange.mem_coverings_of_isPullback
      (J := K) (fun k : R.uncurry ↦ k.val.2)
      (by simpa only [presieve_canonical_family] using ha) b
      (fun k ↦ pullback.snd k.val.2 b) (fun k ↦ pullback.fst k.val.2 b)
      (fun k ↦ (IsPullback.of_hasPullback k.val.2 b).flip)
    refine ⟨fun i ↦ pullback (a i) b, fun i ↦ pullback.snd _ _,
      fun i ↦ pullback.fst _ _, fun i ↦ (IsPullback.of_hasPullback _ _).flip, ?_⟩
    have he :
        Presieve.ofArrows (fun k : R.uncurry ↦ pullback k.val.2 b)
          (fun k ↦ pullback.snd k.val.2 b) =
        Presieve.ofArrows (fun i ↦ pullback (a i) b)
          (fun i ↦ pullback.snd (a i) b) := by
      apply le_antisymm
      · rintro Z g ⟨k⟩
        rcases k with ⟨⟨V, f⟩, hk⟩
        cases hk with
        | mk i => exact .mk i
      · rintro Z g ⟨i⟩
        exact .mk (⟨⟨U i, a i⟩, .mk i⟩ : R.uncurry)
    rwa [he] at hc

private lemma sets_isGrothendieckTopos :
    IsGrothendieckTopos.{u + 1} (Type (u + 1)) := by
  refine ⟨Discrete PUnit.{u + 2}, inferInstance, ⊥, ?_⟩
  exact ⟨(Functor.equiv : (Discrete PUnit.{u + 2} ⥤ Type (u + 1)) ≌
    Type (u + 1)).symm.trans
    ((Equivalence.congrLeft (Discrete.opposite PUnit.{u + 2})).symm.trans
      (sheafBotEquivalence _).symm)⟩

/-- The finite-cover colimit site presents the 2-limit of the small etale topoi,
with enough points represented by compatible geometric-point families.
Source: Stacks Project, Sites, Tags 09YL, 0A35, 00YQ; ILO XX 4.4, printed p.373
(blueprint: lem-per-qcqs-etale-topos-inverse-limit).

Proof:
1. In the qcqs etale subcategory, arrows and fibre products are qcqs, and scheme pullback
   preserves finite limits and finite jointly surjective covers. Use
   lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-etale-base-change-finite-limits,
   lem-weil-pbc-etale-base-change-continuous and lem-weil-pbc-etale-composition-cancellation.
   Finite affine refinements (lem-weil-pbc-etale-qcqs-cofinal-finite-coverings) and the dense
   comparison (lem-pc-fppf-dense-sheaf-equivalence) identify these sheaves with the full small
   etale topos. The inverse-image identification is
   lem-weil-pbc-sets-etale-inverse-image-exact.
2. Normalize identities and strictify by lem-coef-pseudofunctor-split-family-strictification,
   with empty incoming diagram. Evaluation transfers the finite covers and their sheaves.
3. Apply lem-weil-pbc-colimit-of-sites. Lift finite diagrams to stages. Its Hom calculation,
   lem-weil-pbc-filtered-colimit-categories and
   lem-weil-pbc-filtered-colimits-commute-finite-limits show that stagewise finite limits
   are limits in the colimit category. In particular images of terminal objects are terminal.
   Projection direct images are restriction of sections, with the displayed compatibility.
4. For a cone from E, restrict its inverse images to associated representables. By
   lem-per-lex-cover-functor-extension these are left exact cover-preserving functors;
   the site functor for each projection is U mapped to the associated image representable.
5. By lem-per-filtered-category-pseudococones glue these functors and their coherent
   comparisons. Finite limits and finite covers descend from stages, so
   lem-per-lex-cover-functor-extension extends the glued functor to an inverse image.
   These two equivalences also glue all natural transformations uniquely. Taking adjunction
   mates gives precisely the direct-image 2-morphisms used in `IsToposLimit`.
6. Specialize to E = Sets to factor every compatible geometric-point family. Apply
   lem-trf-finitary-site-enough-points to choose a conservative set of limit points.
   By lem-trf-etale-topos-points-geometric each projection of each such point is represented
   by an algebraically closed, hence separably closed, geometric point. Transporting the
   projection comparisons supplies the required cocycle without changing conservativity.
7. Final reindexing of the opposite site diagram and objectwise scheme isomorphisms give
   equivalent colimit sites by lem-per-filtered-category-pseudococones. Their finite
   topologies agree: each original stage maps to a reindexed stage. Dense comparison
   gives the sheaf equivalence. The full faithfulness of site extension identifies the
   projection inverse images and gives the unique invertible comparison 2-morphism.
   This also compares arbitrary choices of strictification. -/
theorem qcqs_etale_topos_inverse_limit
    (I : Type u) [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : I) (a : i ⟶ j), QuasiCompact (D.map a)]
    [∀ (i j : I) (a : i ⟶ j), QuasiSeparated (D.map a)] :
    ∃ P : QcqsEtaleLimit.Presentation D,
      QcqsEtaleLimit.IsToposLimit P.projections ∧
      (∀ q : QcqsEtaleLimit.GeometricPointCone D,
        Nonempty (QcqsEtaleLimit.Factorization P.projections q.cone)) ∧
      (∃ (T : Type (u + 1))
        (points : T → GeometricMorphism (Type (u + 1))
          (Sheaf P.cover.toGrothendieck (Type (u + 1)))),
        (∀ (t : T) (i : I), ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω)
          (s : Spec (.of Ω) ⟶ D.obj i),
          Nonempty ((P.projections.projection i).inverse ⋙ (points t).inverse ≅
            (Scheme.pointSmallEtale s).sheafFiber (A := Type (u + 1)))) ∧
        ∀ {F G : Sheaf P.cover.toGrothendieck (Type (u + 1))} (a : F ⟶ G),
          (∀ t : T, Function.Bijective ((points t).inverse.map a)) → IsIso a) ∧
      (∀ (J : Type u) [SmallCategory J] [IsCofiltered J]
        (r : J ⥤ I) [r.Initial] (D' : J ⥤ Scheme.{u}) (ε : D' ≅ r ⋙ D),
        Nonempty (QcqsEtaleLimit.Presentation D') ∧
          ∀ P' : QcqsEtaleLimit.Presentation D',
            ∃ c : QcqsEtaleLimit.Comparison P.projections P'.projections r ε,
              c.IsCanonical) := by
  classical
  obtain ⟨P⟩ := QcqsEtaleLimit.presentation_nonempty I D
  have hlimit := QcqsEtaleLimit.presentation_isToposLimit P
  let := P.finiteLimits
  let := P.coverIsos
  let := P.coverComposition
  let := P.coverBaseChange
  have hf := presentation_cover_finite P
  have hsite := finite_cover_site P.cover hf
  obtain ⟨T, points, hpoints⟩ := finitarySite_enoughPoints.{u + 1, u + 1, u + 1}
    P.cover hsite (by
      intro X A U f hcov
      let R := Presieve.ofArrows U f
      let : Finite R.uncurry := (hf X hcov).to_subtype
      refine ⟨R.uncurry, inferInstance, (fun k ↦ U k.property.idx),
        (fun k ↦ f k.property.idx), (fun k ↦ k.property.idx), ?_, ?_⟩
      · rwa [← Presieve.ofArrows_eq_ofArrows_uncurry f]
      · intro k
        exact ⟨𝟙 _, Category.id_comp _⟩)
  refine ⟨P, hlimit, ?_, ⟨T, points, ?_, hpoints⟩, ?_⟩
  · intro q
    exact hlimit.1 (Type (u + 1)) sets_isGrothendieckTopos q.cone
  · intro t i
    obtain ⟨Ω, field, closed, s, hs⟩ := Scheme.etaleToposPoint_isGeometric
      (D.obj i) ((points t).comp (P.projections.projection i))
    let := field
    let := closed
    exact ⟨Ω, field, inferInstance, s, hs⟩
  · intro J _ _ r _ D' ε
    let (j : J) : CompactSpace ((r ⋙ D).obj j) :=
      inferInstanceAs (CompactSpace (D.obj (r.obj j)))
    let (j : J) : QuasiSeparatedSpace ((r ⋙ D).obj j) :=
      inferInstanceAs (QuasiSeparatedSpace (D.obj (r.obj j)))
    let (j : J) : CompactSpace (D'.obj j) :=
      QuasiCompact.compactSpace_of_compactSpace (ε.hom.app j)
    let (j : J) : QuasiSeparatedSpace (D'.obj j) :=
      quasiSeparatedSpace_of_quasiSeparated (ε.hom.app j)
    let (j k : J) (a : j ⟶ k) : QuasiCompact (D'.map a) := inferInstance
    let (j k : J) (a : j ⟶ k) : QuasiSeparated (D'.map a) := inferInstance
    exact ⟨QcqsEtaleLimit.presentation_nonempty J D',
      fun P' ↦ QcqsEtaleLimit.presentation_comparison P P' r ε⟩

end AlgebraicGeometry
