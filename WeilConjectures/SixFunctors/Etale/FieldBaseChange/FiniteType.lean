/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Noetherian
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality

/-!
# Base change along `X ×_K S ⟶ S` for morphisms of finite type `K`-schemes

Let `K` be a field, `Λ` a finite ring whose exponent is invertible in `K`, `X` a Noetherian
`K`-scheme and `γ : T ⟶ S` a separated morphism of schemes of finite type over `K`. For a
constructible sheaf `F` of `Λ`-modules on `T`, the base-change maps of the cartesian square

```
X ×_K T --e--> T
   |           |
   h           γ
   v           v
X ×_K S --p--> S
```

are isomorphisms in every degree
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_finiteType`). Factor `γ` as an open
immersion `j : T ⟶ T̄` followed by a proper `T̄ ⟶ S` (Nagata). Deligne's generic base change
theorem over the base `Spec K`, whose only nonempty open is everything, says that `Rj_* F`
commutes with the base change along `X ×_K T̄ ⟶ T̄`; the proper base change theorem says that
`R(T̄ ⟶ S)_*` commutes with the base change along `X ×_K S ⟶ S`; and the base-change maps of a
vertical composite of squares compose.

This is the finite-type case of blueprint `lem-kun-0f1i`, replacing the open-immersion lemma
`lem-kun-0f1h` of the blueprint by Deligne's theorem.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Vertical pasting, at an object**, for a pasted square whose left vertical map is only equal
to the composite `f' ≫ e'`: the derived base change map of the pasted square at `K` is an
isomorphism as soon as the one of the upper square is an isomorphism at `K` and the one of the
lower square is an isomorphism at `Rf_* K`. -/
lemma Etale.isIso_derivedBaseChangeMapPlus_app_paste_vert_of_eq {X' X Y' Y Z' Z : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z}
    {k : Z' ⟶ Z} {f'' : X' ⟶ Z'} (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k)
    (sq : CommSq g' f'' (f ≫ e) k) (hf'' : f'' = f' ≫ e')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h₁ : IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁).app K))
    (h₂ : IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂).app
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj K))) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app K) := by
  subst hf''
  exact Etale.isIso_derivedBaseChangeMapPlus_app_paste_vert sq₁ sq₂ sq K h₁ h₂

/-- Base change along `X ×_K S ⟶ S` for a separated morphism `γ : T ⟶ S` of schemes of finite
type over a field `K`, a Noetherian `K`-scheme `X` and a constructible sheaf of `Λ`-modules,
`Λ` finite with exponent invertible in `K`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_finiteType [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X S T X' Y : Scheme.{u}} [IsNoetherian X]
    (aX : X ⟶ Spec (.of K)) (aS : S ⟶ Spec (.of K)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (γ : T ⟶ S) [LocallyOfFiniteType γ] [QuasiCompact γ] [IsSeparated γ]
    (b : X' ⟶ X) (p : X' ⟶ S) (_hb : IsPullback b p aX aS)
    (e : Y ⟶ T) (h : Y ⟶ X') (sq : IsPullback e h γ p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf F] (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := ⟨⟩
  obtain ⟨⟨T', g, i, rfl, hg, hi⟩⟩ :=
    (nagataCompactification_of_isNoetherian γ).nonempty_compactification
  have sq₂ := IsPullback.of_hasPullback g p
  have sqX : IsPullback (pullback.fst g p) (pullback.snd g p ≫ b) (g ≫ aS) aX :=
    (sq₂.flip.paste_horiz _hb).flip
  let f' : Y ⟶ pullback g p := pullback.lift (e ≫ i) h (by rw [Category.assoc, sq.w])
  have hf' : h = f' ≫ pullback.snd g p := (pullback.lift_snd _ _ _).symm
  have sq₁ : IsPullback e f' i (pullback.fst g p) :=
    IsPullback.of_bot (hf' ▸ sq) (pullback.lift_fst _ _ _).symm sq₂
  -- Deligne's generic base change over `Spec K`, whose nonempty opens are everything
  obtain ⟨U, ⟨x, hx⟩, hD⟩ :=
    Etale.exists_hasConstructibleDirectImageBaseChangeOn Λ (𝟙 (Spec (.of K))) (g ≫ aS) i F
  have hU : Set.range aX ⊆ U := by
    rintro _ ⟨y, rfl⟩
    have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rwa [Subsingleton.elim (aX y) x]
  have h₁ := (Etale.isIso_derivedBaseChangeMap_app_ι_obj_iff _ _ _).1
    ((NatTrans.isIso_app_iff_of_iso _ ((DerivedCategory.Plus.singleFunctorιIso _ 0).app F)).2
      (hD X aX hU _ _ (pullback.fst g p) (pullback.snd g p ≫ b) e f' sqX sq₁).2)
  -- proper base change for `g`
  have h₂ := Etale.isIso_baseChange_of_isProper_of_torsionHomology Λ sq₂
    ((i)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ _ isAddTorsion_of_finite _)
  have := Etale.isIso_derivedBaseChangeMapPlus_app_paste_vert_of_eq Λ sq₁.toCommSq
    sq₂.toCommSq sq.toCommSq hf' _ h₁ h₂
  rw [Etale.isIso_baseChangeHomologyMap_iff, Etale.baseChange_eq_derivedBaseChangeMapPlus]
  infer_instance

end AlgebraicGeometry
