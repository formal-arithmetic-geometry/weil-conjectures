/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentThickeningSystem
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.AlgebraicGeometry.ThickeningSystemsEquivalence
import WeilConjectures.AlgebraicGeometry.ThickeningSystemsCompletionComparison

/-! # The dictionary for coherent systems on infinitesimal thickenings

The natural evaluation isomorphisms specify the dictionary on both objects and morphisms.
The unit equations specify its transitions and the canonical restriction comparisons.
The indexing starts with X_0 = X × Spec(A/I).
X_n is spelled `pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))`,
j_n its `pullback.fst`, and I O_X `(Scheme.IdealSheafData.ofIdealTop (I.map
(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f`, as in
`quotientBaseChange_closedImmersion_ideal` and `grothendieck_existence`.

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0CYL](https://stacks.math.columbia.edu/tag/0CYL)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option autoImplicit false

private lemma support_eq_of_iso {Y : Scheme.{v}} {F G : Y.Modules} (e : F ≅ G) :
    {y : Y | ¬ Subsingleton (F.presheaf.stalk y)} =
      {y : Y | ¬ Subsingleton (G.presheaf.stalk y)} := by
  ext y
  let e' := ((Scheme.Modules.toPresheaf Y) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} y).mapIso e
  exact not_congr (Equiv.subsingleton_congr (Equiv.ofBijective e'.hom
    (ConcreteCategory.bijective_of_isIso e'.hom)))

private lemma support_proper_iff_of_iso {Y S : Scheme.{v}} (g : Y ⟶ S)
    [LocallyOfFiniteType g] {F G : Y.Modules} (e : F ≅ G) :
    Scheme.Modules.HasSupportProperOver g F ↔
      Scheme.Modules.HasSupportProperOver g G := by
  unfold Scheme.Modules.HasSupportProperOver
  rw [support_eq_of_iso e]

private lemma support_proper_closed_square {Y X S₀ S : Scheme.{v}}
    (j : Y ⟶ X) (g : Y ⟶ S₀) (f : X ⟶ S) (q : S₀ ⟶ S)
    [IsClosedImmersion j] [LocallyOfFiniteType g] [LocallyOfFiniteType f]
    [IsProper q] (hsq : j ≫ f = g ≫ q) (F : Y.Modules) (G : X.Modules)
    (hsupp : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} =
      j '' {y : Y | ¬ Subsingleton (F.presheaf.stalk y)}) :
    Scheme.Modules.HasSupportProperOver g F ↔
      Scheme.Modules.HasSupportProperOver f G := by
  classical
  constructor
  · rintro ⟨Z, hZ, hp⟩
    let t := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
    have ht : Set.range t.base = (Z : Set Y) := by
      simp [t]
    have : IsProper (t ≫ g) := hp
    have : IsProper ((t ≫ j) ≫ f) := by
      rw [Category.assoc, hsq, ← Category.assoc]
      infer_instance
    let W : TopologicalSpace.Closeds X :=
      ⟨j '' (Z : Set Y), j.isClosedEmbedding.isClosedMap _ Z.isClosed⟩
    refine ⟨W, ?_, ?_⟩
    · change j '' (Z : Set Y) = _
      rw [hZ, ← hsupp]
    · apply (Scheme.closed_subset_proper_over_base_properties f W).1.mpr
      refine ⟨_, t ≫ j, inferInstance, ?_, inferInstance⟩
      change Set.range (t ≫ j).base = j '' (Z : Set Y)
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ht]
  · rintro ⟨W, hW, hp⟩
    let Z : TopologicalSpace.Closeds Y :=
      ⟨j ⁻¹' (W : Set X), W.isClosed.preimage j.continuous⟩
    have hZ : (Z : Set Y) = {y : Y | ¬ Subsingleton (F.presheaf.stalk y)} := by
      change j ⁻¹' (W : Set X) = _
      rw [hW, hsupp, Set.preimage_image_eq _ j.isClosedEmbedding.injective]
    let t := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
    have ht : Set.range t.base = (Z : Set Y) := by simp [t]
    have htw : Set.range (t ≫ j).base = (W : Set X) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ht, hZ, ← hsupp, ← hW]
    have : IsProper ((t ≫ j) ≫ f) :=
      (Scheme.closed_subset_proper_over_base_properties f W).2.1.mp hp _ (t ≫ j) htw
    have : IsProper ((t ≫ g) ≫ q) := by
      rw [Category.assoc, ← hsq, ← Category.assoc]
      infer_instance
    exact ⟨Z, hZ, IsProper.of_comp (t ≫ g) q⟩

/-- The dictionary between coherent modules on `X` and formal coherent systems on the thickenings
`X_n = X ×_A Spec(A/I^(n+1))`, including its naturality and proper-support restriction. The
maps `i n` are the canonical transition maps, specified by their two projections, and `ai`,
`aj` are chosen tensor-pullback adjunctions. -/
theorem thickeningSystems_dictionary {A : Type v} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] (I : Ideal A)
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ,
      i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (hi₂ : ∀ n : ℕ,
      i n ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
      pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ≫
          Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))))
    (ai : ∀ n : ℕ, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (aj : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⊣
      Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1))))))) :
    ∃ hX : IsNoetherian X,
      (∀ n : ℕ, IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).ker =
            (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of
            A)).inv.hom)).comap f ^ (n + 1)) ∧
      ∃ (Φ : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) i ⥤
          @CoherentFormalModule X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f))
        (β : ∀ n : ℕ,
          Φ ⋙ ObjectProperty.ι (IsCoherentFormalModule ((Scheme.IdealSheafData.ofIdealTop (I.map
              (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)) ⋙
            (CategoryTheory.evaluation ℕᵒᵖ X.Modules).obj (op n) ≅
          CoherentThickeningSystem.evaluation (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))) i n ⋙
            Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1))))))),
        Φ.IsEquivalence ∧
        (∀ (M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) i) (n : ℕ),
          (((Φ.obj M).obj).map (homOfLE (Nat.le_succ n)).op) ≫ (β n).hom.app M =
          (β (n + 1)).hom.app M ≫
            (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
              ((ai n).homEquiv _ _ (M.comparison n).hom) ≫
            (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
              (M.term n) ≫
            (Scheme.Modules.pushforwardCongr (hi n)).hom.app (M.term n)) ∧
        ∃ (c : ∀ n : ℕ,
            Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙
              Scheme.Modules.tensorPullback (i n) ≅
            Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1)))))))
          (R : CoherentModules X ⥤ CoherentThickeningSystem (fun n ↦ pullback f (Spec.map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) i)
          (r : ∀ n : ℕ, R ⋙ CoherentThickeningSystem.evaluation (fun n ↦ pullback f (Spec.map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) i n ≅
            ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
              Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1)))))))
          (ρ : @completion X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f) ≅ R ⋙ Φ),
          (∀ (F : X.Modules) (n : ℕ),
            (aj (n + 1)).unit.app F ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
                ((ai n).unit.app
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforwardCongr (hi n)).hom.app
                ((Scheme.Modules.tensorPullback (i n)).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj F)) ≫
              (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((c n).hom.app F) =
            (aj n).unit.app F) ∧
          (∀ (F : CoherentModules X) (n : ℕ),
            ((R.obj F).comparison n).hom ≫ (r n).hom.app F =
              (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) ≫
                (c n).hom.app F.obj) ∧
          (∀ (F : CoherentModules X) (n : ℕ),
            formalModuleQuotientπ ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
                (CommRingCat.of A)).inv.hom)).comap f) (n + 1) F.obj ≫
              (ρ.hom.app F).hom.app (op n) ≫ (β n).hom.app (R.obj F) ≫
                (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                    (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((r n).hom.app F) =
            (aj n).unit.app F.obj) ∧
          (∀ F G : CoherentModules X,
            Function.Bijective (fun v : R.obj G ⟶ R.obj F ↦
              (ρ.hom.app G) ≫ Φ.map v ≫ (ρ.inv.app F))) ∧
          (∀ (F G : CoherentModules X) (v : G ⟶ F),
            (ρ.hom.app G) ≫ Φ.map (R.map v) ≫ (ρ.inv.app F) =
              (@completion X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
                  (CommRingCat.of A)).inv.hom)).comap f)).map v) ∧
          (∀ (F : CoherentModules X)
            (M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1)))))) i),
            ∃ b : (R.obj F ≅ M) ≃
              ((@completion X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
                  (CommRingCat.of A)).inv.hom)).comap f)).obj F ≅ Φ.obj M),
              ∀ e, b e = (ρ.app F) ≪≫ Φ.mapIso e) ∧
          (∀ F₀ : CoherentModules (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^
              (0 + 1)))))),
            {x : X | ¬ Subsingleton
              (((Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (0 + 1))))))).obj
                F₀.obj).presheaf.stalk x)} =
              (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))))) ''
                {x : ↥(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 +
                    1)))))) | ¬ Subsingleton (F₀.obj.presheaf.stalk x)} ∧
            (Scheme.Modules.HasSupportProperOver
              (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))))
              F₀.obj ↔
            Scheme.Modules.HasSupportProperOver f
              ((Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I ^ (0 + 1))))))).obj F₀.obj))) ∧
          (∀ M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))) i,
            Scheme.Modules.HasSupportProperOver
              (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))))
              (M.term 0) ↔
            Scheme.Modules.HasSupportProperOver f ((Φ.obj M).obj.obj (op 0))) := by
  classical
  have hX : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hgeom : (∀ n : ℕ, IsClosedImmersion (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).ker =
            (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of
            A)).inv.hom)).comap f ^ (n + 1)) := by
    intro n
    obtain ⟨hc, hk, _⟩ := quotientBaseChange_closedImmersion_ideal f (I ^ (n + 1))
    refine ⟨hc, hk.trans ?_⟩
    exact ((quotientBaseChange_extendedIdeal_mul_pow f).2 I (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))).symm
  obtain ⟨Φ, β, hΦ, ht⟩ := thickeningSystems_pushforward_equivalence f I i hi hi₂ ai aj hgeom
  obtain ⟨c, R, r, ρ, hu, hr, hρ⟩ :=
    thickeningSystems_completion_comparison f I i hi hi₂ ai aj hgeom Φ β ht
  have : Φ.IsEquivalence := hΦ
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨hX, hgeom, Φ, β, hΦ, ht, c, R, r, ρ, hu, hr, hρ, ?_, ?_, ?_, ?_, ?_⟩
  · intro F G
    exact ((Functor.FullyFaithful.ofFullyFaithful Φ).homEquiv.trans
      (Iso.homCongr (ρ.app G).symm (ρ.app F).symm)).bijective
  · intro F G v
    simpa only [Functor.comp_map, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id] using congrArg (fun k ↦ k ≫ ρ.inv.app F) (ρ.hom.naturality v).symm
  · intro F M
    refine ⟨(Functor.FullyFaithful.ofFullyFaithful Φ).isoEquiv.trans
      (Iso.isoCongrLeft (ρ.app F).symm), ?_⟩
    intro e
    simp [Iso.isoCongrLeft]
  · intro F₀
    have : IsClosedImmersion (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))))) := (hgeom 0).1
    have : IsNoetherian (pullback f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))))) :=
      isNoetherian_of_locallyOfFiniteType (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))))
    have hs := closedImmersion_coherent_support (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))))) F₀
    refine ⟨hs, ?_⟩
    exact support_proper_closed_square _ _ _ _ pullback.condition _ _ hs
  · intro M
    have : IsClosedImmersion (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))))) := (hgeom 0).1
    have : IsNoetherian (pullback f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))))) :=
      isNoetherian_of_locallyOfFiniteType (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))))
    have hs := closedImmersion_coherent_support (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))))
      ⟨M.term 0, M.coherent 0⟩
    exact (support_proper_closed_square _ _ _ _ pullback.condition _ _ hs).trans
      (support_proper_iff_of_iso f ((β 0).app M).symm)

end
end AlgebraicGeometry
