/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.SupportedThickeningDictionary
import WeilConjectures.AlgebraicGeometry.ClosedSupportedFormalAlgebraization
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceProper
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated

/-! # Algebraization of a system on a fixed proper closed subscheme

## References

* [Stacks Project, Tags 088E, 088F]
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Algebraization when one fixed proper closed subscheme annihilates the entire system.
No properness assumption on the first term is needed separately.
(Stacks, Theorem 088E, Proposition 088C, Lemma 087T and Remark 088F) -/
theorem grothendieckExistence_supported_system
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (ai : ∀ n : ℕ, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (aj : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⊣
      Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))))
    (F : ∀ n : ℕ, (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).Modules)
    (φ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).obj (F (n + 1)) ≅ F n)
    (hF : ∀ n : ℕ, RingedSpace.IsCoherent (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))).toRingedSpace (F n))
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j] [IsProper (j ≫ f)]
    (hkill : ∀ (n : ℕ) (V : X.Opens) (a : Γ(X, V)),
        a ∈ j.ker.idealOfOpens V →
        ∀ t : Γ((Scheme.Modules.pushforward (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj (F n), V),
          a • t = 0) :
    ∃ c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙
        Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))),
    (∀ (G : X.Modules) (n : ℕ),
      (aj (n + 1)).unit.app G ≫
        (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
          ((ai n).unit.app
            ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj G)) ≫
        (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
          ((Scheme.Modules.tensorPullback (i n)).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj G)) ≫
        (Scheme.Modules.pushforwardCongr (hi n)).hom.app
          ((Scheme.Modules.tensorPullback (i n)).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).obj G)) ≫
        (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((c n).hom.app G) =
      (aj n).unit.app G) ∧
    ∃ G : X.Modules, RingedSpace.IsCoherent X.toRingedSpace G ∧
    Scheme.Modules.HasSupportProperOver f G ∧
    ∃ ψ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅ F n,
    ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫ (φ n).hom = (c
      n).hom.app G ≫ (ψ n).hom := by
  classical
  obtain ⟨hX, M, hM, -, c, hcu, hψ⟩ :=
    supportedThickening_dictionary A I f i hi hp ai aj F φ hF Z j hkill
  let := hX
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType j
  let K : X.IdealSheafData :=
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f
  have he : (@completion Z (isNoetherian_of_locallyOfFiniteType j)
      (K.comap j)).IsEquivalence := by
    change (completion Z
      (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f).comap j)).IsEquivalence
    rw [← Scheme.IdealSheafData.comap_comp]
    exact grothendieck_existence_proper A I Z (j ≫ f)
  obtain ⟨GZ, hG, e⟩ := closedSupported_formal_algebraization j K he M hM
  let G : CoherentModules X := ⟨(Scheme.Modules.pushforward j).obj GZ.obj, hG⟩
  have hqZ := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    Z GZ.obj).mp GZ.property
  let := hqZ.1
  let := hqZ.2
  have hqG := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X G.obj).mp G.property
  let := hqG.1
  let := hqG.2
  have hproper : Scheme.Modules.HasSupportProperOver f G.obj := by
    apply (Scheme.Modules.module_support_proper_over_base f G.obj).2.1.mpr
    refine ⟨Z, j, inferInstance, inferInstance, ?_, GZ.obj,
      inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
    exact (Scheme.Modules.closedImmersion_pushforward_annihilated j).1 GZ.obj |>.2
  obtain ⟨ψ, hcompat⟩ := hψ G e
  exact ⟨c, hcu, G.obj, G.property, hproper, ψ, hcompat⟩

end AlgebraicGeometry
