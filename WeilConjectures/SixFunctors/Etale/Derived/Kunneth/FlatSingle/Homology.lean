/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.TensorSingle
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The homology sheaves of the base change map for a pushforward tensored with a sheaf

Fix a commutative square `h ≫ f' = e ≫ g`, `p : X' ⟶ X` and a sheaf `𝓕` on `T`, and put
`N = Lf'^* Rg_* 𝓕[0]`. For a sheaf `𝓖` on `X` and `q : ℤ`, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`) at `(Lp^* 𝓖[0], 𝓕[0])` induces on `Hᵠ` a map

`Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N) ⟶ Hᵠ(Lp^* 𝓖[0] ⊗ᴸ N) ⟶ Hᵠ(Rh_*(Lh^* Lp^* 𝓖[0] ⊗ᴸ Le^* 𝓕[0]))
  ⟶ Hᵠ(Rh_*((h^* p^* 𝓖 ⊗ e^* 𝓕)[0]))`

natural in `𝓖` (`AlgebraicGeometry.Etale.tensorBaseChangeHomologyMap`). Its source and target are
functors of `𝓖` which, for `𝓖` killed by the Jacobson radical, are computed by underived tensor
products, and for `𝓖` flat it is the map induced on `Hᵠ` by the base change map.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X X' S' T Y : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X')
  (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
  (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The complex `N = Lf'^* Rg_* 𝓕[0]` on `X'`. -/
noncomputable abbrev tensorBaseChangeComplex :
    DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  L((f')^*[ModuleCat.{u + 1} Λ]).obj (R((g)_*[ModuleCat.{u + 1} Λ]).obj
    ((DerivedCategory.singleFunctor _ 0).obj 𝓕))

/-- The source `𝓖 ↦ Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N)` of the degree-`q` base change map. -/
noncomputable def tensorBaseChangeHomologySource (q : ℤ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[ModuleCat.{u + 1} Λ]) ⋙
    (-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).flip.obj
      ((DerivedCategory.TStructure.t.truncLE q).obj (tensorBaseChangeComplex Λ f' g 𝓕)) ⋙
    DerivedCategory.homologyFunctor _ q

/-- The target `𝓖 ↦ Hᵠ(Rh_*((h^* p^* 𝓖 ⊗ e^* 𝓕)[0]))` of the degree-`q` base change map. -/
noncomputable def tensorBaseChangeHomologyTarget (q : ℤ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (p)^*[ModuleCat.{u + 1} Λ] ⋙ (h)^*[ModuleCat.{u + 1} Λ] ⋙
    tensorRight ((e)^*[ModuleCat.{u + 1} Λ].obj 𝓕) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
    R((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.homologyFunctor _ q

variable [Etale.UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]

set_option maxHeartbeats 1000000 in
/-- The degree-`q` base change map
`Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N) ⟶ Hᵠ(Rh_*((h^* p^* 𝓖 ⊗ e^* 𝓕)[0]))`, natural in the sheaf `𝓖` on `X`:
the truncation `τ^{≤q} N ⟶ N`, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMapLeft`) and the comparison of the derived and the
underived tensor products (`AlgebraicGeometry.Etale.singleFunctorTensorToSingle`). -/
noncomputable def tensorBaseChangeHomologyMap (q : ℤ) :
    tensorBaseChangeHomologySource Λ p f' g 𝓕 q ⟶ tensorBaseChangeHomologyTarget Λ p h e 𝓕 q :=
  let M := ModuleCat.{u + 1} Λ
  let H := DerivedCategory.homologyFunctor (Sheaf X'.smallEtaleTopology M) q
  let ι : tensorBaseChangeHomologySource Λ p f' g 𝓕 q ⟶
      DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[M]) ⋙
        (-⊗ᴸ-(X')[M]).flip.obj (tensorBaseChangeComplex Λ f' g 𝓕) ⋙ H :=
    Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[M]))
      (Functor.whiskerRight ((-⊗ᴸ-(X')[M]).flip.map
        ((DerivedCategory.TStructure.t.truncLEι q).app (tensorBaseChangeComplex Λ f' g 𝓕))) H)
  let τ : DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[M]) ⋙
        (-⊗ᴸ-(X')[M]).flip.obj (tensorBaseChangeComplex Λ f' g 𝓕) ⋙ H ⟶
      (DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[M]) ⋙ L((h)^*[M])) ⋙
        (-⊗ᴸ-(Y)[M]).flip.obj (L((e)^*[M]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) ⋙
          R((h)_*[M]) ⋙ H :=
    Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[M]))
      (Functor.whiskerRight (tensorBaseChangeMapLeft M h e f' g w
        ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) H)
  let a : DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology M) 0 ⋙ L((p)^*[M]) ⋙
        L((h)^*[M]) ≅
      (p)^*[M] ⋙ (h)^*[M] ⋙ DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology M) 0 :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (singleFunctorCompLeftDerivedUpperStarIso M p) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (singleFunctorCompLeftDerivedUpperStarIso M h)
  let b : (-⊗ᴸ-(Y)[M]).flip.obj (L((e)^*[M]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) ≅
      tensorRight ((DerivedCategory.singleFunctor _ 0).obj ((e)^*[M].obj 𝓕)) :=
    (-⊗ᴸ-(Y)[M]).flip.mapIso ((singleFunctorCompLeftDerivedUpperStarIso M e).app 𝓕)
  let θ₁ : (DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[M]) ⋙ L((h)^*[M])) ⋙
        (-⊗ᴸ-(Y)[M]).flip.obj (L((e)^*[M]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) ⋙
          R((h)_*[M]) ⋙ H ⟶
      ((p)^*[M] ⋙ (h)^*[M]) ⋙ (DerivedCategory.singleFunctor _ 0 ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj ((e)^*[M].obj 𝓕))) ⋙
          R((h)_*[M]) ⋙ H :=
    Functor.whiskerRight a.hom _ ≫
      Functor.whiskerLeft ((p)^*[M] ⋙ (h)^*[M] ⋙ DerivedCategory.singleFunctor _ 0)
        (Functor.whiskerRight b.hom (R((h)_*[M]) ⋙ H))
  let θ₂ : ((p)^*[M] ⋙ (h)^*[M]) ⋙ (DerivedCategory.singleFunctor _ 0 ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj ((e)^*[M].obj 𝓕))) ⋙
          R((h)_*[M]) ⋙ H ⟶ tensorBaseChangeHomologyTarget Λ p h e 𝓕 q :=
    Functor.whiskerLeft ((p)^*[M] ⋙ (h)^*[M])
      (Functor.whiskerRight (singleFunctorTensorToSingle ((e)^*[M].obj 𝓕)) (R((h)_*[M]) ⋙ H))
  ι ≫ τ ≫ θ₁ ≫ θ₂

end Etale

end AlgebraicGeometry
