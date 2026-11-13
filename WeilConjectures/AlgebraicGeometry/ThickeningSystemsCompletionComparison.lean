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
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.CompletionFromRestriction
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Restriction of coherent modules and its canonical comparison with completion.

## References

* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option autoImplicit false

/-- Restriction of coherent modules and its canonical comparison with completion.
-/
theorem thickeningSystems_completion_comparison {A : Type v} [CommRing A] [IsNoetherianRing A]
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
          (I ^ (n + 1)))))))
    [hX : IsNoetherian X]
    (hgeom : (∀ n : ℕ, IsClosedImmersion (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).ker =
            (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of
            A)).inv.hom)).comap f ^ (n + 1)))
    (Φ : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
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
                (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (htransition : (∀ (M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) i) (n : ℕ),
          (((Φ.obj M).obj).map (homOfLE (Nat.le_succ n)).op) ≫ (β n).hom.app M =
          (β (n + 1)).hom.app M ≫
            (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
              ((ai n).homEquiv _ _ (M.comparison n).hom) ≫
            (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
              (M.term n) ≫
            (Scheme.Modules.pushforwardCongr (hi n)).hom.app (M.term n))) :
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
            (aj n).unit.app F.obj) := by
  let j := fun n : ℕ ↦ pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let e := fun n : ℕ ↦ Scheme.Modules.pushforwardComp (i n) (j (n + 1)) ≪≫
    Scheme.Modules.pushforwardCongr (hi n)
  let a := fun n : ℕ ↦ ((aj (n + 1)).comp (ai n)).ofNatIsoRight (e n)
  let c := fun n : ℕ ↦ (a n).leftAdjointUniq (aj n)
  have hc : ∀ (F : X.Modules) (n : ℕ),
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
            (aj n).unit.app F := by
    intro F n
    have h := (a n).unit_leftAdjointUniq_hom_app (aj n) F
    simpa [a, e, Adjunction.comp_unit_app, Category.assoc] using h
  have hcoh (F : CoherentModules X) (n : ℕ) :
      RingedSpace.IsCoherent _ ((Scheme.Modules.tensorPullback (j n)).obj F.obj) := by
    have hj : IsClosedImmersion (j n) := (hgeom n).1
    have : IsLocallyNoetherian (pullback f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) :=
      LocallyOfFiniteType.isLocallyNoetherian (j n)
    obtain ⟨hq, ht⟩ :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F.obj).mp F.property
    have : ((Scheme.Modules.pullback (j n)).obj F.obj).IsQuasicoherent := inferInstance
    have hqc : ((Scheme.Modules.tensorPullback (j n)).obj F.obj).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent
        (pullback f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))).ringCatSheaf).prop_of_iso
        (((aj n).leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction (j n))).app
          F.obj).symm inferInstance
    exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mpr
      ⟨hqc, (Scheme.Modules.tensorPullback_isFiniteType _ X (j n) F.obj).1⟩
  have hext {F G : CoherentThickeningSystem
      (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
      i} (u v : CoherentThickeningSystem.Hom F G) (h : u.app = v.app) : u = v := by
    cases u
    cases v
    cases h
    rfl
  let R : CoherentModules X ⥤ CoherentThickeningSystem
      (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
      i :=
    { obj := fun F ↦
        { term := fun n ↦ (Scheme.Modules.tensorPullback (j n)).obj F.obj
          coherent := hcoh F
          comparison := fun n ↦ (c n).app F.obj }
      map := fun u ↦
        { app := fun n ↦ (Scheme.Modules.tensorPullback (j n)).map u.hom
          compatibility := fun n ↦ ((c n).hom.naturality u.hom).symm }
      map_id := by
        intro F
        apply hext
        funext n
        exact (Scheme.Modules.tensorPullback (j n)).map_id F.obj
      map_comp := by
        intro F G H u v
        apply hext
        funext n
        exact (Scheme.Modules.tensorPullback (j n)).map_comp u.hom v.hom }
  let r : ∀ n : ℕ, R ⋙ CoherentThickeningSystem.evaluation _ i n ≅
      ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
        Scheme.Modules.tensorPullback (j n) := fun n ↦
    NatIso.ofComponents (fun F ↦ Iso.refl _)
      (by intros; simp [R, CoherentThickeningSystem.evaluation])
  have hr : ∀ (F : CoherentModules X) (n : ℕ),
      ((R.obj F).comparison n).hom ≫ (r n).hom.app F =
        (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) ≫
          (c n).hom.app F.obj := by
    intro F n
    simp [R, r, CoherentThickeningSystem.evaluation]
  obtain ⟨ρ, hρ⟩ := completion_from_restriction f I i hi hi₂ ai aj hgeom Φ β htransition
    c R r hc hr
  exact ⟨c, R, r, ρ, hc, hr, hρ⟩

end
end AlgebraicGeometry
