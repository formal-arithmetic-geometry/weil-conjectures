/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSplitResiduePoints
import WeilConjectures.AlgebraicGeometry.ElementaryLocalizeSplitPoints
import WeilConjectures.AlgebraicGeometry.FiniteDimensionalResidueFieldOfIsolatedFiberPoint
import WeilConjectures.AlgebraicGeometry.IsolatedFibrePointBaseChange

/-!
# Finite neighborhoods of multiple isolated fiber points after etale localization

Source: Stacks Project, More on Morphisms, Lemma 02LM.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For finitely many distinct isolated fiber points, an etale neighborhood makes their lifts
lie in finite open subschemes, with purely inseparable residue fields and no unlisted lifts
(Stacks, Tag 02LM). -/
theorem exists_etale_local_finite_multiple_points
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (n : ℕ) (x : Fin n → X) (hx : ∀ i, f (x i) = s)
    (hdistinct : Function.Injective x)
    (hisolated : ∀ i, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (u : U), Etale φ ∧ φ u = s ∧
      ∃ (m : Fin n → ℕ) (V : (i : Fin n) → Fin (m i) → (pullback f φ).Opens)
        (v : (i : Fin n) → (j : Fin (m i)) → (V i j).toScheme),
        (∀ (i : Fin n) (j : Fin (m i)),
          IsFinite ((V i j).ι ≫ pullback.snd f φ) ∧
          ∃ (hv : ((V i j).ι ≫ pullback.snd f φ) (v i j) = u),
            (∀ w : (V i j).toScheme,
              ((V i j).ι ≫ pullback.snd f φ) w = u → w = v i j) ∧
            (letI := ((U.residueFieldCongr hv.symm).hom ≫
              ((V i j).ι ≫ pullback.snd f φ).residueFieldMap (v i j)).hom.toAlgebra
             Module.Finite (U.residueField u) ((V i j).toScheme.residueField (v i j)) ∧
               IsPurelyInseparable (U.residueField u)
                 ((V i j).toScheme.residueField (v i j))) ∧
            ((V i j).ι ≫ pullback.fst f φ) (v i j) = x i) ∧
        Function.Injective
          (fun a : (i : Fin n) × Fin (m i) ↦ (V a.1 a.2).ι (v a.1 a.2)) ∧
        (∀ (i : Fin n) (w : ↥(pullback f φ)),
          pullback.snd f φ w = u → pullback.fst f φ w = x i →
            ∃ j : Fin (m i), w = (V i j).ι (v i j)) := by
  classical
  have hfinite (i : Fin n) :
      letI := (f.residueFieldMap (x i)).hom.toAlgebra
      Module.Finite (S.residueField (f (x i))) (X.residueField (x i)) :=
    f.finiteDimensional_residueField_of_isOpen_singleton_asFiber (x i) (hisolated i)
  obtain ⟨U, φ, u, hφ, hus, m, y, hyinj, hyx, hy, hex⟩ :=
    exists_etale_split_residue_points f s n x hx hfinite
  have hyisolated (i : Fin n) (j : Fin (m i)) :
      IsOpen ({(pullback.snd f φ).asFiber (y i j)} :
        Set ((pullback.snd f φ).fiber ((pullback.snd f φ) (y i j)))) := by
    apply isolated_fiber_point_base_change f φ (y i j)
    exact Eq.rec (motive := fun z _ ↦
      IsOpen ({f.asFiber z} : Set (f.fiber (f z)))) (hisolated i) (hyx i j).symm
  have hinj : Function.Injective (fun a : (i : Fin n) × Fin (m i) ↦ y a.1 a.2) := by
    intro a b hab
    change y a.1 a.2 = y b.1 b.2 at hab
    have hi : a.1 = b.1 := hdistinct
      ((hyx a.1 a.2).symm.trans ((congrArg (pullback.fst f φ) hab).trans (hyx b.1 b.2)))
    cases a with
    | mk i j =>
      cases b with
      | mk i' j' =>
        dsimp at hi hab ⊢
        subst i'
        have hj := hyinj i hab
        subst j'
        rfl
  obtain ⟨U', ψ, u', hψ, hψu, V, v, hpts, hvij, hex'⟩ :=
    exists_elementary_localize_split_points f φ u n x m y hyx hy hyisolated hinj hex
  have : Etale φ := hφ
  have : Etale ψ := hψ
  refine ⟨U', ψ ≫ φ, u', inferInstance, ?_, m, V, v, hpts, hvij, hex'⟩
  change φ (ψ u') = s
  rw [hψu, hus]

end AlgebraicGeometry
