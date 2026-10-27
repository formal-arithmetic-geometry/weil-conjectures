/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalOplax

/-!

# The monoidal structure of the derived pullback on module objects over `Λ`

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback `Lf^* = L((f)^*⟦Λ⟧) : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` is strong monoidal for
the derived tensor products `- ⊗ᴸ_{Λ} -` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`:
```
m_{K,L} : Lf^* (K ⊗ᴸ_{Λ_Y} L) ≅ Lf^* K ⊗ᴸ_{Λ_X} Lf^* L,    Lf^* Λ_Y ≅ Λ_X.
```
This comparison is the input of the derived projection morphisms, hence of Verdier duality and
Poincaré duality.

The pullback `f^*` of module objects over `Λ` is strong monoidal for the relative tensor products
(`ProEtale.CondensedRing.monoidal_upperStar`), with comparison isomorphisms
`μ : f^* M ⊗_{Λ_X} f^* N ≅ f^* (M ⊗_{Λ_Y} N)`. The comparison `m` is constructed from `μ`
(`ProEtale.CondensedRing.leftDerivedUpperStarTensorIso`) in three steps:

1. **Complexes.** For complexes `A` and `B` of module objects over `Λ_Y`, `μ` applied degreewise
   gives a map of complexes `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` for the total tensor product of
   complexes (`ProEtale.CondensedRing.upperStarTensorComplexHom`): on the summand
   `f^* A^p ⊗ f^* B^q` of degree `n = p + q` it is `μ` followed by the inclusion of
   `f^* (A^p ⊗ B^q)` into `f^* ((A ⊗ B)^n)`.
2. **Homotopy category.** Composing with the lax structure `Qh A' ⊗ᴸ Qh B' ⟶ Qh (A' ⊗ B')` of
   the localization `Qh : K(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X})`, this gives a natural transformation of
   bifunctors `Qh (f^* A) ⊗ᴸ Qh (f^* B) ⟶ Qh (f^* (A ⊗ B))` on the homotopy category of
   `Mod_{Λ_Y}` (`ProEtale.CondensedRing.upperStarTensorCounit`).
3. **Derived categories.** The bifunctor `(K, L) ↦ Lf^* K ⊗ᴸ Lf^* L` on `D(Mod_{Λ_Y})`, with the
   transformation of step 2 precomposed with the counits of `Lf^*`, is a left derived bifunctor
   of `(A, B) ↦ Qh (f^* (A ⊗ B))` (`ProEtale.CondensedRing.isLeftDerivedFunctor₂_upperStarTensor`).
   The bifunctor `(K, L) ↦ Lf^* (K ⊗ᴸ L)` receives a canonical transformation to the same
   bifunctor, so the universal property of left derived bifunctors
   (`Functor.leftDerived₂Lift`) gives the comparison
   `m : Lf^* (- ⊗ᴸ -) ⟶ Lf^* - ⊗ᴸ Lf^* -` (`ProEtale.CondensedRing.leftDerivedUpperStarTensor`),
   characterized by its compatibility with the counits.

The unit comparison `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso` is
`Lf^* (Qh 𝟙) ≅ Qh (f^* 𝟙) ≅ Qh 𝟙`: the counit of `Lf^*`, an isomorphism since `f^*` is exact,
followed by the unit comparison of `monoidal_upperStar` in degree `0`. Together with the inverse
of `m` as tensorator, it makes `Lf^*` strong monoidal
(`ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`).

## Proofs

- `ProEtale.CondensedRing.upperStarTensorComplexHom_comm`: the degreewise comparison is a section
  of the comparison induced by the comonoidal structure `δ` of `f^*`, which commutes with the
  differentials and is an isomorphism; so `upperStarTensorComplexHom` is its inverse
  (`ProEtale.CondensedRing.upperStarTensorComplexHom_eq_inv`) and is natural.
- `ProEtale.CondensedRing.isLeftDerivedFunctor₂_upperStarTensor` and
  `ProEtale.CondensedRing.isIso_leftDerivedUpperStarTensor` are computed on pairs of K-flat
  complexes, `f^*` preserving K-flat complexes
  (`ProEtale.CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj`): on such a pair the
  counits of `Lf^*` and the lax structure of `Qh` are isomorphisms.
- The coherences of `monoidal_leftDerivedUpperStar` are those of the oplax monoidal structure
  `ProEtale.CondensedRing.leftDerivedUpperStarOplaxMonoidal` with comonoidal structure `m`,
  obtained from `CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare'` by checking them on
  K-flat complexes; its counit is `leftDerivedUpperStarUnitIso`
  (`ProEtale.CondensedRing.leftDerivedUpperStarOplaxMonoidal_η`).

## Main definitions

- `ProEtale.CondensedRing.leftDerivedUpperStarTensor`: the comparison
  `Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L`, as a natural transformation of bifunctors.
- `ProEtale.CondensedRing.leftDerivedUpperStarTensorIso`: the comparison isomorphism.
- `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso`: the unit comparison `Lf^* 𝟙 ≅ 𝟙`.
- `ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`: the strong monoidal structure on `Lf^*`.

-/


set_option Elab.async false

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The counit of the oplax monoidal structure `leftDerivedUpperStarOplaxMonoidal` is the unit
comparison `leftDerivedUpperStarUnitIso`. -/
lemma leftDerivedUpperStarOplaxMonoidal_η :
    letI := leftDerivedUpperStarOplaxMonoidal Λ f
    Functor.OplaxMonoidal.η L((f)^*⟦Λ⟧) = (leftDerivedUpperStarUnitIso Λ f).hom := by
  let := leftDerivedUpperStarOplaxMonoidal Λ f
  have hY : Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology Y)
      Ab.{u + 1}) (condensedRingObj Λ Y))) = 𝟙 _ := rfl
  have hX : Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology X)
      Ab.{u + 1}) (condensedRingObj Λ X))) = 𝟙 _ := rfl
  have := DerivedCategory.isIso_ε_Qh
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  change L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.ε DerivedCategory.Qh) ≫
      (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (𝟙_ _) ≫
        DerivedCategory.Qh.map (Functor.OplaxMonoidal.η ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ))) ≫
          CategoryTheory.inv (Functor.LaxMonoidal.ε DerivedCategory.Qh) = _
  simp only [hY, hX, CategoryTheory.Functor.map_id, IsIso.inv_id, Category.id_comp]
  rw [Functor.mapHomotopyCategory_η, Functor.mapCochainComplex_η]
  erw [Category.comp_id]
  rfl

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The derived pullback `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` on module objects over `Λ` is
strong monoidal for the derived tensor products, with tensorator the inverse of
`leftDerivedUpperStarTensorIso` and unit comparison `leftDerivedUpperStarUnitIso`. -/
noncomputable instance monoidal_leftDerivedUpperStar : L((f)^*⟦Λ⟧).Monoidal :=
  letI := leftDerivedUpperStarOplaxMonoidal Λ f
  haveI (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
      IsIso (Functor.OplaxMonoidal.δ L((f)^*⟦Λ⟧) K L) :=
    inferInstanceAs (IsIso (((leftDerivedUpperStarTensor Λ f).app K).app L))
  haveI : IsIso (Functor.OplaxMonoidal.η L((f)^*⟦Λ⟧)) := by
    rw [leftDerivedUpperStarOplaxMonoidal_η]
    infer_instance
  have hμ (K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
      (((leftDerivedUpperStarTensorIso Λ f).app K).app L).symm =
        (asIso (Functor.OplaxMonoidal.δ L((f)^*⟦Λ⟧) K L)).symm := by
    ext
    exact (IsIso.inv_eq_of_hom_inv_id
      (((leftDerivedUpperStarTensorIso Λ f).app K).app L).hom_inv_id).symm
  have hε : (leftDerivedUpperStarUnitIso Λ f).symm =
      (asIso (Functor.OplaxMonoidal.η L((f)^*⟦Λ⟧))).symm := by
    ext
    refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
    rw [leftDerivedUpperStarOplaxMonoidal_η, Iso.symm_hom, Iso.hom_inv_id]
  Functor.CoreMonoidal.toMonoidal
    { εIso := (leftDerivedUpperStarUnitIso Λ f).symm
      μIso K L := (((leftDerivedUpperStarTensorIso Λ f).app K).app L).symm
      μIso_hom_natural_left φ L :=
        NatTrans.congr_app ((leftDerivedUpperStarTensorIso Λ f).inv.naturality φ) L
      μIso_hom_natural_right K ψ :=
        ((leftDerivedUpperStarTensorIso Λ f).inv.app K).naturality ψ
      associativity K L M := by
        rw [hμ, hμ, hμ, hμ]
        exact (Functor.CoreMonoidal.ofOplaxMonoidal L((f)^*⟦Λ⟧)).associativity K L M
      left_unitality K := by
        rw [hμ, hε]
        exact (Functor.CoreMonoidal.ofOplaxMonoidal L((f)^*⟦Λ⟧)).left_unitality K
      right_unitality K := by
        rw [hμ, hε]
        exact (Functor.CoreMonoidal.ofOplaxMonoidal L((f)^*⟦Λ⟧)).right_unitality K }

end AlgebraicGeometry.ProEtale.CondensedRing
