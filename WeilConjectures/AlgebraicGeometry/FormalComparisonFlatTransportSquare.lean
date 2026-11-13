/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

import all WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.AlgebraicGeometry.FormalFlatQuotientMateData
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Flat transport squares for formal comparison maps

## References

* Stacks Project, Tags 088B, 0887, 02KH and 02N7
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport the quotient comparison and adjunction diagram under flat base change.
This statement does not take or construct a map from G to the completed direct image
(Stacks, Tag 088B; Tags 02KH and 0887). -/
theorem formalComparison_flat_transport_square
    {X Y S : Scheme.{u}} [IsNoetherian Y] [IsNoetherian S]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f] (g : S ⟶ Y) [Flat g]
    (I : S.IdealSheafData) (hI : J.comap g = I)
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) =
      (Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (G₀ : CoherentFormalModule S I) (F₀ : CoherentModules (pullback f g))
    (hD : RingedSpace.IsCoherent S.toRingedSpace
      ((Scheme.Modules.pushforward (pullback.snd f g)).obj F₀.obj))
    (hG : G₀.obj = G.obj ⋙ Scheme.Modules.tensorPullback g)
    (hF : F₀.obj = (Scheme.Modules.tensorPullback (pullback.fst f g)).obj F.obj) :
    let p := pullback.snd f g
    ∃ (adjR : Scheme.Modules.tensorPullback p ⊣ Scheme.Modules.pushforward p)
      (β₀ : G₀.obj ⋙ Scheme.Modules.tensorPullback p ≅
        formalCompletionSystem (I.comap p) F₀.obj)
      (κ₀ : formalCompletionSystem I ((Scheme.Modules.pushforward p).obj F₀.obj) ⟶
        formalCompletionSystem (I.comap p) F₀.obj ⋙ Scheme.Modules.pushforward p)
      (δ : ((completion S I).obj
          ⟨(Scheme.Modules.pushforward p).obj F₀.obj, hD⟩).obj ≅
        ((completion Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
            Scheme.Modules.tensorPullback g)
      (t : (formalCompletionSystem (J.comap f) F.obj ⋙
          Scheme.Modules.pushforward f) ⋙ Scheme.Modules.tensorPullback g ⟶
        formalCompletionSystem (I.comap p) F₀.obj ⋙ Scheme.Modules.pushforward p),
      (∀ n : ℕ, formalModuleQuotientπ I (n + 1)
          ((Scheme.Modules.pushforward p).obj F₀.obj) ≫ κ₀.app (op n) =
        (Scheme.Modules.pushforward p).map
          (formalModuleQuotientπ (I.comap p) (n + 1) F₀.obj)) ∧
      δ.hom ≫ Functor.whiskerRight κ (Scheme.Modules.tensorPullback g) ≫ t = κ₀ ∧
      (∀ n : ℕ, (eqToHom hG).app (op n) ≫
          (Scheme.Modules.tensorPullback g).map
            (adj.unit.app (G.obj.obj (op n)) ≫
              (Scheme.Modules.pushforward f).map (β.hom.app (op n))) ≫ t.app (op n) =
        adjR.unit.app (G₀.obj.obj (op n)) ≫
          (Scheme.Modules.pushforward p).map (β₀.hom.app (op n))) := by
  classical
  subst I
  obtain ⟨adjR, β₀, b, t, ht, hunit⟩ :=
    formal_flat_quotient_mate_data J f g (J.comap g) rfl adj G F β G₀ F₀ hG hF
  let H : CoherentModules Y := ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩
  let δ : formalCompletionSystem (J.comap g)
      ((Scheme.Modules.pushforward (pullback.snd f g)).obj F₀.obj) ≅
      formalCompletionSystem J H.obj ⋙ Scheme.Modules.tensorPullback g :=
    (formalCompletionFunctor (J.comap g)).mapIso b ≪≫
      (completionPullbackIso g J).app H
  have hδ (n : ℕ) : formalModuleQuotientπ (J.comap g) (n + 1)
      ((Scheme.Modules.pushforward (pullback.snd f g)).obj F₀.obj) ≫ δ.hom.app (op n) =
      b.hom ≫ (Scheme.Modules.tensorPullback g).map
        (formalModuleQuotientπ J (n + 1) H.obj) := by
    change formalModuleQuotientπ (J.comap g) (n + 1) _ ≫
      (formalCompletionMap (J.comap g) b.hom).app (op n) ≫
        (powerQuotientIso g J H.obj
          ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp
            H.property).1 (n + 1)).hom = _
    rw [← Category.assoc]
    rw [show formalModuleQuotientπ (J.comap g) (n + 1) _ ≫
        (formalCompletionMap (J.comap g) b.hom).app (op n) =
        b.hom ≫ formalModuleQuotientπ (J.comap g) (n + 1) _ from
      cokernel.π_desc _ _ _]
    rw [Category.assoc, powerQuotientIso_π]
  let κ₀ := δ.hom ≫ Functor.whiskerRight κ (Scheme.Modules.tensorPullback g) ≫ t
  refine ⟨adjR, β₀, κ₀, δ, t, ?_, rfl, hunit⟩
  intro n
  change formalModuleQuotientπ (J.comap g) (n + 1) _ ≫
    (δ.hom.app (op n) ≫ (Scheme.Modules.tensorPullback g).map (κ.app (op n))) ≫
      t.app (op n) = _
  rw [← Category.assoc, ← Category.assoc, hδ]
  calc
    _ = b.hom ≫ (Scheme.Modules.tensorPullback g).map
        (formalModuleQuotientπ J (n + 1) H.obj ≫ κ.app (op n)) ≫ t.app (op n) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [hκ]; exact ht n

end AlgebraicGeometry
