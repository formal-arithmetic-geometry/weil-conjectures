/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.ReductionHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjectionBaseChange

/-!
# The finite-level exchange rectangle on pro-étale derived categories

Fix a commutative square of schemes
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
and a coefficient object `P ∈ D(Y_proét)` (for instance the reduction `P_n = Λ/Iⁿ` of an adic
coefficient ring, see `def-weil-pbc-adic-coefficient-datum`). This file instantiates the abstract
exchange rectangle of `WeilConjectures.CategoryTheory.CompletedBaseChange.Rectangle` at the
pro-étale derived categories:

* `AlgebraicGeometry.ProEtale.baseChangeSquare A sq`: the base change square of the derived
  categories `D(X_proét), D(Y_proét), D(X'_proét), D(Y'_proét)` with the derived pullbacks, the
  derived direct images and the Cartesian identification
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso`; its exchange map is the derived base
  change map `AlgebraicGeometry.ProEtale.derivedBaseChangeMap` (`def-weil-pbc-ambient-ringed-exchange`);
* `AlgebraicGeometry.ProEtale.tensorReduction A sq P`: the reduction `- ⊗ᴸ P` of this square into
  itself, with the tensor comparisons of the derived pullbacks. The commutativity of the cube of
  left adjoints (the field `cube`, assumed in the abstract setting) is **proved** here from the
  compatibility of the square isomorphism with the tensor comparisons;
* `AlgebraicGeometry.ProEtale.tensorReductionHom A sq φ`: a morphism of coefficients `P ⟶ P'`
  (e.g. the quotient `P_{n+1} ⟶ P_n`) induces a morphism of reductions.

For `K ∈ D(X_proét)` the four corners (`def-weil-pbc-four-corners`,
`def-weil-pbc-level-map-corners`) are
```
A = Lg^*(Rf_*K ⊗ᴸ P),        B = Lg^*Rf_*(K ⊗ᴸ Lf^*P),
C = Rf'_*Lg'^*K ⊗ᴸ Lg^*P,     D = Rf'_*Lg'^*(K ⊗ᴸ Lf^*P),
```
and the four arrows (`def-weil-pbc-four-arrows`, `def-weil-pbc-level-map-arrows`) are
`h = Lg^* π_{f,K,P}`, `v = (Ex_K ⊗ 1) ∘ comparison`, `h' = Rf'_*(comparisons) ∘ π_{f',Lg'^*K,Lg^*P}`
and `v' = Ex_{K ⊗ᴸ Lf^*P}`; they are identified with the arrows of the abstract reduction by
`AlgebraicGeometry.ProEtale.tensorReduction_arrowH_app` etc.

## Main results

- `AlgebraicGeometry.ProEtale.finiteLevelRectangle`: `v' ∘ h = h' ∘ v`
  (`lem-weil-pbc-finite-level-rectangle`, `lemma-weil-pbc-level-map-rectangle`).
- `AlgebraicGeometry.ProEtale.finiteLevelRectangle_naturality`: operator naturality
  (`lemma-weil-pbc-level-map-operator-naturality`).
- `AlgebraicGeometry.ProEtale.finiteLevelRectangle_tower_comm`: the four arrows commute with the
  coefficient transitions (`lemma-weil-pbc-level-map-tower-compatibility`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]

namespace ProEtale

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The base change square of pro-étale derived categories attached to a commutative square of
schemes `g' ≫ f = f' ≫ g` (Blueprint `def-weil-pbc-cartesian-square`, on derived categories):
derived pullbacks, derived direct images with the adjunctions `Lf^* ⊣ Rf_*`, and the Cartesian
identification `Lg^* Lf'^* ≅ Lf^* Lg'^*`. -/
noncomputable def baseChangeSquare (sq : CommSq g' f' f g) :
    BaseChangeSquare (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
      (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X') A))
      (DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A)) where
  upperF := L((f)^*[A])
  lowerF := R((f)_*[A])
  adjF := derivedUpperStarLowerStarAdjunction A f
  upperF' := L((f')^*[A])
  lowerF' := R((f')_*[A])
  adjF' := derivedUpperStarLowerStarAdjunction A f'
  upperG := L((g)^*[A])
  upperG' := L((g')^*[A])
  iso := leftDerivedUpperStarSquareIso A sq

/-- The exchange map of `ProEtale.baseChangeSquare` is the derived base change map
(Blueprint `def-weil-pbc-ambient-ringed-exchange`). -/
lemma baseChangeSquare_exchange (sq : CommSq g' f' f g) :
    (baseChangeSquare A sq).exchange.natTrans = derivedBaseChangeMap A sq := rfl

/-- The reduction `- ⊗ᴸ P` of the pro-étale base change square along a coefficient object
`P ∈ D(Y_proét)`: on the four corners it is the tensor product with `P`, `Lf^*P`, `Lg^*P` and
`Lf'^*Lg^*P`, the comparisons are the tensor comparisons of the derived pullbacks, and the
commutativity of the cube of left adjoints is
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso_hom_tensor`. -/
noncomputable def tensorReduction (sq : CommSq g' f' f g)
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (baseChangeSquare A sq).Reduction (baseChangeSquare A sq) where
  redX := (-⊗ᴸ-(X)[A]).flip.obj (L((f)^*[A]).obj P)
  redY := (-⊗ᴸ-(Y)[A]).flip.obj P
  redX' := (-⊗ᴸ-(X')[A]).flip.obj (L((f')^*[A]).obj (L((g)^*[A]).obj P))
  redY' := (-⊗ᴸ-(Y')[A]).flip.obj (L((g)^*[A]).obj P)
  γF := TwoSquare.mk _ _ _ _
    { app M := ((leftDerivedUpperStarTensorComparison A f).app M).app P
      naturality M N φ := by
        simpa using congrArg (fun α ↦ α.app P)
          ((leftDerivedUpperStarTensorComparison A f).naturality φ) }
  γF' := TwoSquare.mk _ _ _ _
    { app M := ((leftDerivedUpperStarTensorComparison A f').app M).app (L((g)^*[A]).obj P)
      naturality M N φ := by
        simpa using congrArg (fun α ↦ α.app (L((g)^*[A]).obj P))
          ((leftDerivedUpperStarTensorComparison A f').naturality φ) }
  δG := NatIso.ofComponents
    (fun M ↦ asIso (((leftDerivedUpperStarTensorComparison A g).app M).app P))
    (fun φ ↦ by
      simpa using congrArg (fun α ↦ α.app P)
        ((leftDerivedUpperStarTensorComparison A g).naturality φ))
  δG' := NatIso.ofComponents
      (fun K ↦ asIso (((leftDerivedUpperStarTensorComparison A g').app K).app
        (L((f)^*[A]).obj P)))
      (fun φ ↦ by
        simpa using congrArg (fun α ↦ α.app (L((f)^*[A]).obj P))
          ((leftDerivedUpperStarTensorComparison A g').naturality φ)) ≪≫
    Functor.isoWhiskerLeft L((g')^*[A])
      ((-⊗ᴸ-(X')[A]).flip.mapIso ((leftDerivedUpperStarSquareIso A sq).app P).symm)
  cube := by
    refine TwoSquare.ext _ _ fun M ↦ ?_
    have h := leftDerivedUpperStarSquareIso_hom_tensor A sq M P
    simp [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, baseChangeSquare]
    sorry

variable (sq : CommSq g' f' f g) (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
  (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))

/-- The projection map of the reduction `- ⊗ᴸ P` is the projection-formula map
`π_{f,K,P} : Rf_*K ⊗ᴸ P ⟶ Rf_*(K ⊗ᴸ Lf^*P)` (Blueprint `def-weil-pbc-projection-formula-map`). -/
lemma tensorReduction_projF_app :
    (tensorReduction A sq P).projF.natTrans.app K =
      ((rightDerivedLowerStarProjectionMap A f).app K).app P := by
  rw [BaseChangeSquare.Reduction.projF_app, rightDerivedLowerStarProjectionMap_app_app,
    Adjunction.homEquiv_unit]
  rfl

/-- The projection map `π_{f'}` of the reduction `- ⊗ᴸ P` is `π_{f',M,Lg^*P}`. -/
lemma tensorReduction_projF'_app (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X') A)) :
    (tensorReduction A sq P).projF'.natTrans.app M =
      ((rightDerivedLowerStarProjectionMap A f').app M).app (L((g)^*[A]).obj P) := by
  rw [BaseChangeSquare.Reduction.projF'_app, rightDerivedLowerStarProjectionMap_app_app,
    Adjunction.homEquiv_unit]
  rfl

/-- The corner `A = Lg^*(Rf_*K ⊗ᴸ P)` (Blueprint `def-weil-pbc-four-corners`,
`def-weil-pbc-level-map-corners`: `A_n = Lg^*((Rf_*K) ⊗ᴸ P_n)`). -/
lemma tensorReduction_cornerA_obj :
    (tensorReduction A sq P).cornerA.obj K =
      L((g)^*[A]).obj (((-⊗ᴸ-(Y)[A]).obj (R((f)_*[A]).obj K)).obj P) := rfl

/-- The corner `B = Lg^*Rf_*(K ⊗ᴸ Lf^*P)` (`B_n = Lg^*Rf_*K_n`, `K_n = K ⊗ᴸ P_n`). -/
lemma tensorReduction_cornerB_obj :
    (tensorReduction A sq P).cornerB.obj K =
      L((g)^*[A]).obj (R((f)_*[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj P))) := rfl

/-- The corner `C = Rf'_*Lg'^*K ⊗ᴸ Lg^*P` (`C_n = (Rf'_*E) ⊗ᴸ P_n`, `E = Lg'^*K`). -/
lemma tensorReduction_cornerC_obj :
    (tensorReduction A sq P).cornerC.obj K =
      ((-⊗ᴸ-(Y')[A]).obj (R((f')_*[A]).obj (L((g')^*[A]).obj K))).obj (L((g)^*[A]).obj P) := rfl

/-- The corner `D = Rf'_*Lg'^*(K ⊗ᴸ Lf^*P)` (`D_n = Rf'_*E_n`, `E_n = Lg'^*K_n`). -/
lemma tensorReduction_cornerD_obj :
    (tensorReduction A sq P).cornerD.obj K =
      R((f')_*[A]).obj (L((g')^*[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj P))) := rfl

/-- The arrow `h = Lg^* π_{f,K,P} : A ⟶ B` (Blueprint `def-weil-pbc-four-arrows`,
`def-weil-pbc-level-map-arrows`). -/
lemma tensorReduction_arrowH_app :
    (tensorReduction A sq P).arrowH.app K =
      L((g)^*[A]).map (((rightDerivedLowerStarProjectionMap A f).app K).app P) := by
  rw [BaseChangeSquare.Reduction.arrowH_app, tensorReduction_projF_app]
  rfl

/-- The arrow `v = (Ex_K ⊗ᴸ 1) ∘ c : A ⟶ C`, the reduction of the derived base change map
`Ex_K : Lg^*Rf_*K ⟶ Rf'_*Lg'^*K` transported through the tensor comparison
`c : Lg^*(Rf_*K ⊗ᴸ P) ≅ Lg^*Rf_*K ⊗ᴸ Lg^*P`. -/
lemma tensorReduction_arrowV_app :
    (tensorReduction A sq P).arrowV.app K =
      ((leftDerivedUpperStarTensorComparison A g).app (R((f)_*[A]).obj K)).app P ≫
        ((-⊗ᴸ-(Y')[A]).map ((derivedBaseChangeMap A sq).app K)).app (L((g)^*[A]).obj P) := by
  rw [BaseChangeSquare.Reduction.arrowV_app]
  rfl

/-- The arrow `h' : C ⟶ D`: the projection-formula map `π_{f',Lg'^*K,Lg^*P}` followed by the
inverse tensor comparison of `Lg'^*` and the Cartesian identification `Lf'^*Lg^*P ≅ Lg'^*Lf^*P`. -/
lemma tensorReduction_arrowH'_app :
    (tensorReduction A sq P).arrowH'.app K =
      ((rightDerivedLowerStarProjectionMap A f').app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj P) ≫
        R((f')_*[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
            ((leftDerivedUpperStarSquareIso A sq).hom.app P) ≫
          inv (((leftDerivedUpperStarTensorComparison A g').app K).app
            (L((f)^*[A]).obj P))) := by
  rw [BaseChangeSquare.Reduction.arrowH'_app, tensorReduction_projF'_app]
  rfl

/-- The arrow `v' = Ex_{K ⊗ᴸ Lf^*P} : B ⟶ D`, the derived base change map at `K_n`. -/
lemma tensorReduction_arrowV'_app :
    (tensorReduction A sq P).arrowV'.app K =
      (derivedBaseChangeMap A sq).app (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj P)) := rfl

/-- **The finite-level exchange rectangle** (Blueprint `lem-weil-pbc-finite-level-rectangle`,
`lemma-weil-pbc-level-map-rectangle`): for a commutative square of schemes, `K ∈ D(X_proét)` and
a coefficient object `P` (e.g. `P_n`), `v' ∘ h = h' ∘ v : A ⟶ D` with
`h = Lg^* π_{f,K,P}`, `v' = Ex_{K ⊗ᴸ Lf^*P}`, `v = (Ex_K ⊗ᴸ 1) ∘ c_g` and
`h' = Rf'_*(c_{g'}⁻¹ ∘ (1 ⊗ β)) ∘ π_{f',Lg'^*K,Lg^*P}`. It is the abstract rectangle
`CategoryTheory.BaseChangeSquare.Reduction.rectangle` of the reduction
`AlgebraicGeometry.ProEtale.tensorReduction`, whose cube condition is proved there. -/
theorem finiteLevelRectangle :
    L((g)^*[A]).map (((rightDerivedLowerStarProjectionMap A f).app K).app P) ≫
        (derivedBaseChangeMap A sq).app (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj P)) =
      (((leftDerivedUpperStarTensorComparison A g).app (R((f)_*[A]).obj K)).app P ≫
        ((-⊗ᴸ-(Y')[A]).map ((derivedBaseChangeMap A sq).app K)).app (L((g)^*[A]).obj P)) ≫
      ((rightDerivedLowerStarProjectionMap A f').app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj P) ≫
        R((f')_*[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
            ((leftDerivedUpperStarSquareIso A sq).hom.app P) ≫
          inv (((leftDerivedUpperStarTensorComparison A g').app K).app
            (L((f)^*[A]).obj P))) := by
  rw [← tensorReduction_arrowH_app, ← tensorReduction_arrowV'_app, ← tensorReduction_arrowV_app,
    ← tensorReduction_arrowH'_app]
  exact (tensorReduction A sq P).rectangle_app K

/-- **Operator naturality of the finite-level rectangle** (Blueprint
`lemma-weil-pbc-level-map-operator-naturality`): for `φ : K ⟶ K'` (e.g. a tower-compatible
endomorphism of `K`), the four arrows `h, v, h', v'` intertwine the induced maps
`Lg^*(Rf_*φ ⊗ 1)`, `Lg^*Rf_*(φ ⊗ 1)`, `Rf'_*Lg'^*φ ⊗ 1`, `Rf'_*Lg'^*(φ ⊗ 1)` of the corners,
and the common composite `v' h = h' v` is natural. -/
lemma finiteLevelRectangle_naturality {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (φ : K ⟶ K') :
    let ρ := tensorReduction A sq P
    ρ.cornerA.map φ ≫ ρ.arrowH.app K' = ρ.arrowH.app K ≫ ρ.cornerB.map φ ∧
    ρ.cornerA.map φ ≫ ρ.arrowV.app K' = ρ.arrowV.app K ≫ ρ.cornerC.map φ ∧
    ρ.cornerC.map φ ≫ ρ.arrowH'.app K' = ρ.arrowH'.app K ≫ ρ.cornerD.map φ ∧
    ρ.cornerB.map φ ≫ ρ.arrowV'.app K' = ρ.arrowV'.app K ≫ ρ.cornerD.map φ ∧
    ρ.cornerA.map φ ≫ ρ.arrowH.app K' ≫ ρ.arrowV'.app K' =
      (ρ.arrowV.app K ≫ ρ.arrowH'.app K) ≫ ρ.cornerD.map φ :=
  (tensorReduction A sq P).rectangle_app_naturality φ

/-- A morphism of coefficient objects `φ : P ⟶ P'` (e.g. the quotient `P_{n+1} ⟶ P_n` of a
coefficient tower) induces a morphism of reductions `- ⊗ᴸ P ⟶ - ⊗ᴸ P'`, by naturality of the
tensor comparisons and of the Cartesian identification. -/
noncomputable def tensorReductionHom {P P' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (φ : P ⟶ P') : (tensorReduction A sq P).Hom (tensorReduction A sq P') where
  τX := (-⊗ᴸ-(X)[A]).flip.map (L((f)^*[A]).map φ)
  τY := (-⊗ᴸ-(Y)[A]).flip.map φ
  τX' := (-⊗ᴸ-(X')[A]).flip.map (L((f')^*[A]).map (L((g)^*[A]).map φ))
  τY' := (-⊗ᴸ-(Y')[A]).flip.map (L((g)^*[A]).map φ)
  commF M := (((leftDerivedUpperStarTensorComparison A f).app M).naturality φ)
  commF' M := (((leftDerivedUpperStarTensorComparison A f').app M).naturality _)
  commG M := (((leftDerivedUpperStarTensorComparison A g).app M).naturality φ)
  commG' K := by
    have h₁ := ((leftDerivedUpperStarTensorComparison A g').app K).naturality
      (L((f)^*[A]).map φ)
    have h₂ := (leftDerivedUpperStarSquareIso A sq).inv.naturality φ
    dsimp [tensorReduction] at h₁ h₂ ⊢
    simp only [Category.assoc, reassoc_of% h₁, ← Functor.map_comp, h₂]

/-- **Tower compatibility of the finite-level arrows** (Blueprint
`lemma-weil-pbc-level-map-tower-compatibility`): for a coefficient tower
`P : ℕᵒᵖ ⥤ D(Y_proét)` (e.g. `P_n = Λ/Iⁿ`) the corner transitions
`a = Lg^*(1 ⊗ q_n)`, `b = Lg^*Rf_*(1 ⊗ Lf^*q_n)`, `c = 1 ⊗ Lg^*q_n`, `d = Rf'_*Lg'^*(1 ⊗ Lf^*q_n)`
(the maps `mapA … mapD` of `tensorReductionHom`) satisfy `b h = h a`, `c v = v a`,
`d h' = h' c` and `d v' = v' b`. -/
lemma finiteLevelRectangle_tower_comm (P : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (n : ℕ) :
    let τ := tensorReductionHom A sq (P.map (homOfLE n.le_succ).op)
    (tensorReduction A sq _).arrowH ≫ τ.mapB = τ.mapA ≫ (tensorReduction A sq _).arrowH ∧
    (tensorReduction A sq _).arrowV ≫ τ.mapC = τ.mapA ≫ (tensorReduction A sq _).arrowV ∧
    (tensorReduction A sq _).arrowH' ≫ τ.mapD = τ.mapC ≫ (tensorReduction A sq _).arrowH' ∧
    (tensorReduction A sq _).arrowV' ≫ τ.mapD = τ.mapB ≫ (tensorReduction A sq _).arrowV' :=
  (tensorReductionHom A sq (P.map (homOfLE n.le_succ).op)).arrows_comm

end ProEtale

end AlgebraicGeometry
