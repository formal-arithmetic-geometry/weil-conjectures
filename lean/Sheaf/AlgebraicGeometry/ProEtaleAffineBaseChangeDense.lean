/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.AlgebraicGeometry.ProEtaleAffineBaseChangeEquivalence

/-! The affine ind-etale basis after a universal homeomorphism. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem covering_of_finite_jointly_surjective {S : Scheme.{u}}
    {W : S.AffineProEt} {ι : Type u} [Finite ι]
    (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ W)
    (hsurj : ∀ x : W.left, ∃ i, x ∈ Set.range (f i).left.base) :
    Sieve.generate (Presieve.ofArrows V f) ∈ AffineProEt.topology S W := by
  classical
  let E : W.left.Cover (Scheme.precoverage @WeaklyEtale) :=
    { I₀ := ι
      X := fun i ↦ (V i).left
      f := fun i ↦ (f i).left
      mem₀ := (Scheme.ofArrows_mem_precoverage_iff @WeaklyEtale).mpr
        ⟨hsurj, fun i ↦ inferInstance⟩ }
  have : ∀ i, AlgebraicGeometry.QuasiCompact (E.f i) := fun i ↦ by
    have : IsAffineHom (E.f i) := inferInstance
    infer_instance
  have : Finite E.I₀ := inferInstanceAs (Finite ι)
  have : QuasiCompactCover E.toPreZeroHypercover := QuasiCompactCover.of_finite
  let C := E.ofQuasiCompactCover
  apply Functor.mem_restrictedTopology_of_functorPushforward_mem
  apply ProEt.mem_topology_iff.mpr
  refine ⟨Presieve.ofArrows (fun i ↦ (AffineProEt.toProEt S).obj (V i))
    (fun i ↦ (AffineProEt.toProEt S).map (f i)), ?_, ?_⟩
  · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact C.mem₀
  · rintro Z _ ⟨i⟩
    exact ⟨V i, f i, 𝟙 _, Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i), by simp⟩

/-- Base change carries the affine ind-etale basis to a dense subsite with its original
covering topology.
Source: Stacks Project, Tag 09AB, `proetale-lemma-thickening`, and Tag 098X.
Proof: Use the proved equivalence of affine ind-etale categories. Composing it with
the dense affine-basis inclusion over X gives a cover-dense, fully faithful functor.
To reflect a covering sieve, choose a finite jointly surjective family in its pushforward.
Each arrow of this family factors through the pullback of an arrow of the original sieve.
The surjective base-change projections show that those original arrows are jointly
surjective. A finite jointly surjective family between affine basis objects is a
pro-etale cover: its arrows are weakly etale and affine, hence quasi-compact. It generates
a covering sieve contained in the original sieve. In the other direction, base change
and the original dense inclusion preserve coverings. This proves the required equivalence
of covering sieves. The argument includes the empty scheme and makes no finiteness
assumption on the universal homeomorphism.
(blueprint: lem-trf-proetale-affine-base-change-dense) -/
theorem proEtaleAffineBaseChange_isDenseSubsite {X Y : Scheme.{u}} [IsAffine Y]
    (r : X ⟶ Y) [IsUniversalHomeomorphism r] :
    (AffineProEt.toProEt Y ⋙ proEtaleBaseChange r).IsDenseSubsite
      (AffineProEt.topology Y) (ProEt.topology X) := by
  classical
  let F := proEtaleAffineBaseChange r
  have : F.IsEquivalence := proEtaleAffineBaseChange_isEquivalence r
  let G := F ⋙ AffineProEt.toProEt X
  have hG : G.IsCoverDense (ProEt.topology X) := by
    refine ⟨fun W ↦ (ProEt.topology X).superset_covering ?_
      ((AffineProEt.toProEt X).is_cover_of_isCoverDense (ProEt.topology X) W)⟩
    rintro Z g ⟨⟨V, a, b, hab⟩⟩
    let e := F.objObjPreimageIso V
    exact ⟨⟨F.objPreimage V, a ≫ (AffineProEt.toProEt X).map e.inv,
      (AffineProEt.toProEt X).map e.hom ≫ b, by
        rw [Category.assoc, ← Category.assoc
          ((AffineProEt.toProEt X).map e.inv), ← Functor.map_comp, e.inv_hom_id,
          (AffineProEt.toProEt X).map_id, Category.id_comp]
        exact hab⟩⟩
  change G.IsDenseSubsite (AffineProEt.topology Y) (ProEt.topology X)
  refine { isCoverDense' := hG, functorPushforward_mem_iff := ?_ }
  intro W T
  constructor
  · intro hT
    have hT' : T.functorPushforward F ∈ AffineProEt.topology X (F.obj W) := by
      apply Functor.mem_restrictedTopology_of_functorPushforward_mem
      rwa [← Sieve.functorPushforward_comp]
    obtain ⟨ι, hι, V, f, hf, hsurj⟩ :=
      AffineProEt.exists_finite_jointly_surjective_of_mem_topology hT'
    have := hι
    have hfac (i : ι) : ∃ (Z : Y.AffineProEt) (t : Z ⟶ W) (a : V i ⟶ F.obj Z),
        T t ∧ f i = a ≫ F.map t := hf i
    choose Z t a ht hta using hfac
    apply (AffineProEt.topology Y).superset_covering
      ((Sieve.generate_le_iff (Presieve.ofArrows Z t) T).mpr (by
        rintro Q _ ⟨i⟩
        exact ht i))
    apply covering_of_finite_jointly_surjective Z t
    intro y
    obtain ⟨x, hx⟩ := (pullback.fst W.hom r).surjective y
    obtain ⟨i, z, hz⟩ := hsurj x
    refine ⟨i, (pullback.fst (Z i).hom r) ((a i).left z), ?_⟩
    have hw : (F.map (t i)).left ≫ pullback.fst W.hom r =
        pullback.fst (Z i).hom r ≫ (t i).left := by
      dsimp [F, proEtaleAffineBaseChange, MorphismProperty.Over.pullback]
      exact pullback.lift_fst _ _ _
    calc
      (t i).left ((pullback.fst (Z i).hom r) ((a i).left z))
          = (pullback.fst W.hom r) ((F.map (t i)).left ((a i).left z)) := by
              exact (congrArg
                (fun k : pullback (Z i).hom r ⟶ W.left ↦ k ((a i).left z)) hw).symm
      _ = (pullback.fst W.hom r) ((f i).left z) := by
        rw [hta i]
        rfl
      _ = y := by rw [hz, hx]
  · intro hT
    change T.functorPushforward (AffineProEt.toProEt Y ⋙ proEtaleBaseChange r) ∈ _
    rw [Sieve.functorPushforward_comp]
    exact (proEtaleBaseChangeCoverPreserving r).cover_preserve
      ((Functor.IsDenseSubsite.coverPreserving
        (AffineProEt.topology Y) (ProEt.topology Y) (AffineProEt.toProEt Y)).cover_preserve hT)

end AlgebraicGeometry.Scheme
