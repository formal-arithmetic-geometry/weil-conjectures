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


/-- The truncation part `Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N) ⟶ Hᵠ(Lp^* 𝓖[0] ⊗ᴸ N)` of the degree-`q` base
change map. -/
noncomputable def tensorBaseChangeHomologyTrunc (q : ℤ) :
    tensorBaseChangeHomologySource Λ p f' g 𝓕 q ⟶
      DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[ModuleCat.{u + 1} Λ]) ⋙
        (-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).flip.obj (tensorBaseChangeComplex Λ f' g 𝓕) ⋙
          DerivedCategory.homologyFunctor _ q :=
  Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0)
    (Functor.whiskerLeft L((p)^*[ModuleCat.{u + 1} Λ])
      (Functor.whiskerRight ((-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).flip.map
        ((DerivedCategory.TStructure.t.truncLEι q).app (tensorBaseChangeComplex Λ f' g 𝓕)))
        (DerivedCategory.homologyFunctor _ q)))

/-- The base change part `Hᵠ(Lp^* 𝓖[0] ⊗ᴸ N) ⟶ Hᵠ(Rh_*(Lh^* Lp^* 𝓖[0] ⊗ᴸ Le^* 𝓕[0]))` of the
degree-`q` base change map. -/
noncomputable def tensorBaseChangeHomologyBaseChange (q : ℤ) :
    DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[ModuleCat.{u + 1} Λ]) ⋙
        (-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).flip.obj (tensorBaseChangeComplex Λ f' g 𝓕) ⋙
          DerivedCategory.homologyFunctor _ q ⟶
      DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[ModuleCat.{u + 1} Λ]) ⋙
        (L((h)^*[ModuleCat.{u + 1} Λ]) ⋙
          (-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).flip.obj (L((e)^*[ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) ⋙ R((h)_*[ModuleCat.{u + 1} Λ])) ⋙
          DerivedCategory.homologyFunctor _ q :=
  Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0)
    (Functor.whiskerLeft L((p)^*[ModuleCat.{u + 1} Λ])
      (Functor.whiskerRight (tensorBaseChangeMapLeft (ModuleCat.{u + 1} Λ) h e f' g w
        ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) (DerivedCategory.homologyFunctor _ q)))

/-- The derived tensor product with a fixed object in the second variable is `tensorRight`. -/
noncomputable def derivedTensorFlipObjIsoTensorRight {Z : Scheme.{u}}
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (-⊗ᴸ-(Z)[ModuleCat.{u + 1} Λ]).flip.obj K ≅ tensorRight K :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp [derivedTensor])

/-- The identification `Hᵠ(Rh_*(Lh^* Lp^* 𝓖[0] ⊗ᴸ Le^* 𝓕[0])) ≅ Hᵠ(Rh_*(h^* p^* 𝓖[0] ⊗ᴸ e^* 𝓕[0]))`
of the derived pullbacks of sheaves with the underived ones. -/
noncomputable def tensorBaseChangeHomologyPullbackIso (q : ℤ) :
    DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[ModuleCat.{u + 1} Λ]) ⋙
        (L((h)^*[ModuleCat.{u + 1} Λ]) ⋙
          (-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).flip.obj (L((e)^*[ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) ⋙ R((h)_*[ModuleCat.{u + 1} Λ])) ⋙
          DerivedCategory.homologyFunctor _ q ≅
      (p)^*[ModuleCat.{u + 1} Λ] ⋙ (h)^*[ModuleCat.{u + 1} Λ] ⋙
        (DerivedCategory.singleFunctor _ 0 ⋙ tensorRight ((DerivedCategory.singleFunctor _ 0).obj
          ((e)^*[ModuleCat.{u + 1} Λ].obj 𝓕))) ⋙
          R((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.homologyFunctor _ q :=
  let M := ModuleCat.{u + 1} Λ
  let H := DerivedCategory.homologyFunctor (Sheaf X'.smallEtaleTopology M) q
  let sX := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology M) 0
  let sX' := DerivedCategory.singleFunctor (Sheaf X'.smallEtaleTopology M) 0
  let sY := DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology M) 0
  let Φ := (-⊗ᴸ-(Y)[M]).flip.obj (L((e)^*[M]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓕))
  let Ψ := tensorRight (sY.obj ((e)^*[M].obj 𝓕))
  let b : Φ ≅ Ψ := (-⊗ᴸ-(Y)[M]).flip.mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso M e).app 𝓕) ≪≫
    derivedTensorFlipObjIsoTensorRight Λ _
  let rest := (Φ ⋙ R((h)_*[M])) ⋙ H
  -- `sX ⋙ Lp^* ⋙ (Lh^* ⋙ Φ ⋙ Rh_*) ⋙ H ≅ sX ⋙ Lp^* ⋙ Lh^* ⋙ rest`
  let i₁ : sX ⋙ L((p)^*[M]) ⋙ (L((h)^*[M]) ⋙ Φ ⋙ R((h)_*[M])) ⋙ H ≅
      sX ⋙ L((p)^*[M]) ⋙ L((h)^*[M]) ⋙ rest :=
    Functor.isoWhiskerLeft sX (Functor.isoWhiskerLeft L((p)^*[M])
      (Functor.associator L((h)^*[M]) (Φ ⋙ R((h)_*[M])) H))
  let i₂ : sX ⋙ L((p)^*[M]) ⋙ L((h)^*[M]) ⋙ rest ≅ (p)^*[M] ⋙ sX' ⋙ L((h)^*[M]) ⋙ rest :=
    (Functor.associator sX L((p)^*[M]) (L((h)^*[M]) ⋙ rest)).symm ≪≫
      Functor.isoWhiskerRight (singleFunctorCompLeftDerivedUpperStarIso M p) _ ≪≫
      Functor.associator (p)^*[M] sX' (L((h)^*[M]) ⋙ rest)
  let i₃ : (p)^*[M] ⋙ sX' ⋙ L((h)^*[M]) ⋙ rest ≅ (p)^*[M] ⋙ (h)^*[M] ⋙ sY ⋙ rest :=
    Functor.isoWhiskerLeft (p)^*[M]
      ((Functor.associator sX' L((h)^*[M]) rest).symm ≪≫
        Functor.isoWhiskerRight (singleFunctorCompLeftDerivedUpperStarIso M h) rest ≪≫
        Functor.associator (h)^*[M] sY rest)
  let i₄ : sY ⋙ rest ≅ (sY ⋙ Ψ) ⋙ R((h)_*[M]) ⋙ H :=
    Functor.isoWhiskerLeft sY (Functor.associator Φ R((h)_*[M]) H) ≪≫
      (Functor.associator sY Φ (R((h)_*[M]) ⋙ H)).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft sY b) (R((h)_*[M]) ⋙ H)
  i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ Functor.isoWhiskerLeft (p)^*[M] (Functor.isoWhiskerLeft (h)^*[M] i₄)

/-- The comparison `Hᵠ(Rh_*(h^* p^* 𝓖[0] ⊗ᴸ e^* 𝓕[0])) ⟶ Hᵠ(Rh_*((h^* p^* 𝓖 ⊗ e^* 𝓕)[0]))` of the
derived and the underived tensor products. -/
noncomputable def tensorBaseChangeHomologyComparison (q : ℤ) :
    (p)^*[ModuleCat.{u + 1} Λ] ⋙ (h)^*[ModuleCat.{u + 1} Λ] ⋙
        (DerivedCategory.singleFunctor _ 0 ⋙ tensorRight ((DerivedCategory.singleFunctor _ 0).obj
          ((e)^*[ModuleCat.{u + 1} Λ].obj 𝓕))) ⋙
          R((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.homologyFunctor _ q ⟶
      tensorBaseChangeHomologyTarget Λ p h e 𝓕 q :=
  Functor.whiskerLeft (p)^*[ModuleCat.{u + 1} Λ]
    (Functor.whiskerLeft (h)^*[ModuleCat.{u + 1} Λ]
      (Functor.whiskerRight (singleFunctorTensorToSingle ((e)^*[ModuleCat.{u + 1} Λ].obj 𝓕))
        (R((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.homologyFunctor _ q) ≫
      (Functor.associator _ _ _).hom))

/-- The degree-`q` base change map
`Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N) ⟶ Hᵠ(Rh_*((h^* p^* 𝓖 ⊗ e^* 𝓕)[0]))`, natural in the sheaf `𝓖` on `X`:
the truncation `τ^{≤q} N ⟶ N`, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMapLeft`) and the comparison of the derived and the
underived tensor products (`AlgebraicGeometry.Etale.singleFunctorTensorToSingle`). -/
noncomputable def tensorBaseChangeHomologyMap (q : ℤ) :
    tensorBaseChangeHomologySource Λ p f' g 𝓕 q ⟶ tensorBaseChangeHomologyTarget Λ p h e 𝓕 q :=
  tensorBaseChangeHomologyTrunc Λ p f' g 𝓕 q ≫
    tensorBaseChangeHomologyBaseChange Λ p h e f' g w 𝓕 q ≫
      (tensorBaseChangeHomologyPullbackIso Λ p h e 𝓕 q).hom ≫
        tensorBaseChangeHomologyComparison Λ p h e 𝓕 q

end Etale

end AlgebraicGeometry
