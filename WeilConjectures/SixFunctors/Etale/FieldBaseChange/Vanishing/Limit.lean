/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.FiniteType
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.LimitSquares
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.Vanishing.ConstantSheaf

/-!
# Base change for limits of morphisms of finite type schemes over a field

Let `K` be a field, `X` an affine scheme of finite type over `K`, and let `t : T ⟶ S` be the
limit of a compatible cofiltered system `g_j : T_j ⟶ S_j` of morphisms of affine schemes of
finite type over `K`, with affine transition morphisms. Then the base-change maps of the square

```
Y ----e---> T
|           |
h           t
v           v
X ×_K S --> S
```

at the constant sheaf `Λ/dΛ` are isomorphisms
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_constantModSheaf_of_isLimit`): the
base-change maps of the finite-type stages are isomorphisms
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_finiteType`), hence so is the one of
the limit (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Base change for the limit `t : T ⟶ S` of a cofiltered system `g_j : T_j ⟶ S_j` of
morphisms of affine schemes of finite type over a field `K`, along `X ×_K S ⟶ S` with `X` affine
of finite type over `K`, at the constant sheaf `Λ/dΛ`. -/
theorem Etale.isIso_baseChangeHomologyMap_constantModSheaf_of_isLimit [Finite Λ] {K : Type u}
    [Field K] [HasInvertibleExponent Λ (Spec (.of K))]
    {J : Type u} [SmallCategory J] [IsCofiltered J] (DT DS : J ⥤ Scheme.{u})
    (hDT : ∀ j, IsAffine (DT.obj j)) (hDS : ∀ j, IsAffine (DS.obj j))
    (hDTmap : ∀ {i j : J} (φ : i ⟶ j), IsAffineHom (DT.map φ))
    (hDSmap : ∀ {i j : J} (φ : i ⟶ j), IsAffineHom (DS.map φ))
    (tT : DT ⟶ (Functor.const J).obj (Spec (.of K)))
    (tS : DS ⟶ (Functor.const J).obj (Spec (.of K)))
    (htT : ∀ j, LocallyOfFiniteType (tT.app j)) (htS : ∀ j, LocallyOfFiniteType (tS.app j))
    (g : DT ⟶ DS) (hg : ∀ j, g.app j ≫ tS.app j = tT.app j)
    (cT : Cone DT) (hcT : IsLimit cT) (cS : Cone DS) (hcS : IsLimit cS)
    [IsAffine cT.pt] [IsAffine cS.pt]
    (aS : cS.pt ⟶ Spec (.of K)) (haS : ∀ j, cS.π.app j ≫ tS.app j = aS)
    (t : cT.pt ⟶ cS.pt) (ht : ∀ j, cT.π.app j ≫ g.app j = t ≫ cS.π.app j)
    {X X' Y : Scheme.{u}} [IsAffine X] (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX]
    (b : X' ⟶ X) (p : X' ⟶ cS.pt) (hb : IsPullback b p aX aS)
    (e : Y ⟶ cT.pt) (h : Y ⟶ X') (sq : IsPullback e h t p) (d : ℕ) (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q (Etale.constantModSheaf Λ cT.pt d)) := by
  have haT (j : J) : cT.π.app j ≫ tT.app j = t ≫ aS := by
    rw [← hg, reassoc_of% ht, haS]
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : IsNoetherian X := ⟨⟩
  have : QuasiCompact t := inferInstance
  have : QuasiSeparated t := inferInstance
  have (i j : J) (φ : i ⟶ j) : IsAffineHom ((Over.lift DT tT).map φ).left := hDTmap φ
  have (i j : J) (φ : i ⟶ j) : IsAffineHom ((Over.lift DS tS).map φ).left := hDSmap φ
  have (j : J) : IsAffine ((Over.lift DT tT).obj j).left := hDT j
  have (j : J) : IsAffine ((Over.lift DS tS).obj j).left := hDS j
  rw [← Etale.isIso_baseChangeHomologyMap_iff_of_iso Λ sq q
    (Etale.upperStarConstantModSheafIso Λ (t ≫ aS) d)]
  refine Etale.isIso_baseChangeHomologyMap_of_isLimit Λ aX (Over.lift DS tS)
    (Over.liftCone DS tS cS aS haS) (hcS.ofIsoLimit (Cone.ext (Iso.refl _) (by simp)))
    (Over.lift DT tT) (Over.liftCone DT tT cT (t ≫ aS) haT)
    (hcT.ofIsoLimit (Cone.ext (Iso.refl _) (by simp))) g.app (fun φ ↦ g.naturality φ) t ht
    (fun j ↦ pullback.fst aX (tS.app j)) (fun j ↦ pullback.snd aX (tS.app j))
    (fun j ↦ IsPullback.of_hasPullback aX (tS.app j))
    (fun j ↦ pullback.fst (g.app j) (pullback.snd aX (tS.app j)))
    (fun j ↦ pullback.snd (g.app j) (pullback.snd aX (tS.app j)))
    (fun j ↦ IsPullback.of_hasPullback _ _) b p hb e h sq
    (Etale.constantModSheaf Λ (Spec (.of K)) d) q fun j ↦ ?_
  have := htS j
  have : LocallyOfFiniteType (g.app j) := by
    have : LocallyOfFiniteType (g.app j ≫ tS.app j) := hg j ▸ htT j
    exact locallyOfFiniteType_of_comp (g.app j) (tS.app j)
  have : Scheme.IsConstructibleSheaf ((((Over.lift DT tT).obj j).hom)^*[ModuleCat.{u + 1} Λ].obj
      (Etale.constantModSheaf Λ (Spec (.of K)) d)) :=
    Scheme.IsConstructibleSheaf.upperStar _ _
  exact Etale.isIso_baseChangeHomologyMap_of_finiteType Λ aX (tS.app j) (g.app j) _ _
    (IsPullback.of_hasPullback aX (tS.app j)) _ _ (IsPullback.of_hasPullback _ _) _ q

end AlgebraicGeometry
