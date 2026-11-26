/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData

/-!
# Replacing the prime component of a glueing datum

Given a glueing datum `Y` and an `S`-linear map `h : Q → Y.M'` that is bijective on every
chart, we construct a glueing datum with prime component `Q` and a morphism to `Y` whose
chart components are bijective.

## Implementation details

The new datum keeps the chart modules and overlap maps of `Y`; each comparison isomorphism is
composed with the localization of `h`. The square identity uses naturality of the
interchange isomorphism with respect to `h`. No flatness or quotient hypothesis is used.

## References

* [Stacks, Tag 0ALK], proof of part (1)
* [Stacks, Tag 05EL]
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

private noncomputable def localEndHom {R : Type u} [CommRing R]
    (r : R) (M : ModuleCat.{w} R) :
    Module.End R M →+* Module.End R (localize r M) where
  toFun := IsLocalizedModule.map (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
  map_one' := IsLocalizedModule.map_id _ _
  map_mul' h k := IsLocalizedModule.map_comp' _ _ _ _ k h
  map_zero' := map_zero _
  map_add' := map_add _

private theorem localEndHom_scalar {R : Type u} [CommRing R]
    (r : R) (M : ModuleCat.{w} R) (a : R) :
    localEndHom r M (algebraMap R (Module.End R M) a) =
      algebraMap R (Module.End R (localize r M)) a := by
  ext x
  induction x using LocalizedModule.induction_on with
  | _ m t =>
    change IsLocalizedModule.map (Submonoid.powers r)
      (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ M)
      (algebraMap R (Module.End R M) a) (LocalizedModule.mk m t) =
      a • LocalizedModule.mk m t
    rw [IsLocalizedModule.map_LocalizedModules]
    exact (LocalizedModule.smul'_mk a m t).symm

private theorem localize_units {R : Type u} [CommRing R]
    (r : R) (M : ModuleCat.{w} R) (a : R)
    (h : IsUnit (algebraMap R (Module.End R M) a)) :
    IsUnit (algebraMap R (Module.End R (localize r M)) a) := by
  rw [← localEndHom_scalar]
  exact h.map (localEndHom r M)

private theorem localMap_mk {R : Type u} [CommRing R]
    (r : R) {M N : ModuleCat.{w} R} (h : M →ₗ[R] N)
    (m : M) (s : Submonoid.powers r) :
    localMap r h (LocalizedModule.mk m s) = LocalizedModule.mk (h m) s :=
  IsLocalizedModule.map_LocalizedModules _ h m s

private theorem localMap_comp {R : Type u} [CommRing R]
    (r : R) {M N P : ModuleCat.{w} R} (h : M →ₗ[R] N) (k : N →ₗ[R] P) :
    localMap r (k.comp h) = (localMap r k).comp (localMap r h) :=
  IsLocalizedModule.map_comp' (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) N)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) P) h k

private theorem localMap_id {R : Type u} [CommRing R] (r : R) (M : ModuleCat.{w} R) :
    localMap r (LinearMap.id : M →ₗ[R] M) = LinearMap.id :=
  IsLocalizedModule.map_id _ _

private theorem swap_mk_one {R : Type u} [CommRing R]
    (r s : R) (M : ModuleCat.{w} R) (m : M) :
    swap r s M (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1 :=
  (exists_swap r s M).exists.choose_spec m

private theorem swap_naturality {R : Type u} [CommRing R]
    (r s : R) {M N : ModuleCat.{w} R} (h : M →ₗ[R] N) :
    (swap r s N).comp (localMap s (localMap r h)) =
      (localMap r (localMap s h)).comp (swap r s M) := by
  apply IsLocalizedModule.ext (Submonoid.powers s)
    (LocalizedModule.mkLinearMap (Submonoid.powers s) (localize r M))
    (fun t => localize_units r (localize s N) t
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap _ N) t))
  apply IsLocalizedModule.ext (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
    (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap _ (localize s N)))
  ext m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
  rw [localMap_mk, localMap_mk, swap_mk_one, swap_mk_one, localMap_mk, localMap_mk]

private theorem extendMapR_id {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (M : ModuleCat.{w} R) :
    extendMapR φ (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext x
  simp [extendMapR, extendMap, restrictMap]

/-- A map invertible on every chart gives a new glueing datum and a morphism to
 the old datum that is invertible on its chart components. -/
theorem exists_replace_prime_to
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) {t : ℕ} (f : Fin t → R)
    (Y : Data.{u, v, max u v w} φ f) (Q : ModuleCat.{max u v w} S)
    (h : Q →ₗ[S] Y.M')
    (hloc : ∀ i : Fin t, Function.Bijective
      (localMap (f i) (restrictMap φ h))) :
    ∃ X : Data.{u, v, max u v w} φ f,
      ∃ (a : X ⟶ Y) (e : X.M' ≃ₗ[S] Q),
        a.prime = h.comp e.toLinearMap ∧
        ∀ i : Fin t, Function.Bijective (a.chart i) := by
  classical
  let e (i : Fin t) := LinearEquiv.ofBijective
    (localMap (f i) (restrictMap φ h)) (hloc i)
  let X : Data.{u, v, max u v w} φ f :=
    { M' := Q
      M := Y.M
      alpha := fun i => (e i).trans (Y.alpha i)
      alpha_smul := by
        intro i s x
        change Y.alpha i
          (localMap (f i) (restrictMap φ h) ((localizedSModule φ (f i) Q).smul s x)) =
          s • Y.alpha i (localMap (f i) (restrictMap φ h) x)
        rw [localMap_smul]
        exact Y.alpha_smul i s _
      alpha_overlap := Y.alpha_overlap
      square := by
        intro i j
        change (extendMapR φ (Y.alpha_overlap i j).toLinearMap).comp
            ((compare φ (f j) (piece (f i) (Y.M i))).comp
              (localMap (f j) ((Y.alpha i).toLinearMap.comp
                (localMap (f i) (restrictMap φ h))))) =
          (compare φ (f i) (piece (f j) (Y.M j))).comp
            ((localMap (f i) ((Y.alpha j).toLinearMap.comp
              (localMap (f j) (restrictMap φ h)))).comp
                (swap (f i) (f j) (restrict φ Q)))
        rw [localMap_comp, localMap_comp]
        calc
          _ = ((extendMapR φ (Y.alpha_overlap i j).toLinearMap).comp
              ((compare φ (f j) (piece (f i) (Y.M i))).comp
                (localMap (f j) (Y.alpha i).toLinearMap))).comp
                  (localMap (f j) (localMap (f i) (restrictMap φ h))) := by
                    simp only [LinearMap.comp_assoc]
          _ = _ := by
            rw [Y.square]
            simp only [LinearMap.comp_assoc]
            rw [← swap_naturality]
      cocycle := Y.cocycle }
  let a : X ⟶ Y :=
    { prime := h
      chart := fun _ => LinearMap.id
      prime_compat := by
        intro i
        change (Y.alpha i).toLinearMap.comp (localMap (f i) (restrictMap φ h)) =
          (extendMapR φ (LinearMap.id : piece (f i) (Y.M i) →ₗ[R] _)).comp
            ((Y.alpha i).toLinearMap.comp (localMap (f i) (restrictMap φ h)))
        rw [extendMapR_id, LinearMap.id_comp]
      chart_compat := by
        intro i j
        change (Y.alpha_overlap i j).toLinearMap.comp
          (localMap (f j) (LinearMap.id : piece (f i) (Y.M i) →ₗ[R] _)) =
          (localMap (f i) (LinearMap.id : piece (f j) (Y.M j) →ₗ[R] _)).comp
            (Y.alpha_overlap i j).toLinearMap
        rw [localMap_id, localMap_id, LinearMap.comp_id, LinearMap.id_comp] }
  exact ⟨X, a, LinearEquiv.refl S Q, by simp [a], fun _ => Function.bijective_id⟩

end FormalGlueing
