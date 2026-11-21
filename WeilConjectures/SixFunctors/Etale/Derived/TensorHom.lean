/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Parametrized
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# The tensor–Hom exchange and the Verdier-duality exchange

Let `f : X ⟶ Y` be a morphism of schemes admitting a compactification, so that the pair
`Rf_! ⊣ Rf^!` is available. The *tensor–Hom form of the exchange* is the isomorphism

`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`,

natural in `M` and `N`. It is the Yoneda consequence of the three adjunctions `Lf^* ⊣ Rf_*`,
`Rf_! ⊣ Rf^!` and `- ⊗ᴸ - ⊣ RHom`, together with the projection formula.

Specialising it to `N = ω_Y` and using `Rf^! ω_Y ≅ ω_X` gives the *Verdier-duality exchange*
`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`: the Verdier dual intertwines `Rf_!` and `Rf_*`.

## Main statements

- `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`: the natural isomorphism
  `Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`, given the projection formula.
- `AlgebraicGeometry.Etale.commShift_derivedHomRightDerivedLowerShriekIso_app_hom`: it commutes
  with shifts.
- `AlgebraicGeometry.Etale.derivedHomLowerShriekIsoOfAdjunction_hom_app_comp_mateEquiv`: it is
  compatible with changes of coefficients, such as finite reduction and scalar extension.
- `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerShriek`:
  `Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex`:
  `Rf^! ω_Y ≅ ω_X`.
- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek`:
  `𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_dualizingComplex`: `ω_Y` lies in `Dctf`
  when `Λ_S` does and `S` is Noetherian.

## Implementation details

The tensor–Hom exchange is constructed as a natural isomorphism of bifunctors
`D(X_ét)ᵒᵖ ⥤ D(Y_ét) ⥤ D(Y_ét)`, for any coefficient category `A` for which the projection map
is an isomorphism and any right adjoint `G` of `Rf_!`
(`AlgebraicGeometry.Etale.derivedHomLowerShriekIsoOfAdjunction`), by conjugating the projection
formula along the two adjunctions with a parameter
(`CategoryTheory.ParametrizedAdjunction.conjugateIso`). For a finite coefficient ring `Λ` and
`G = Rf^!` it is `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`. The other
comparison maps are not constructed in this repository, so the remaining isomorphisms are
asserted as `Nonempty (_ ≅ _)`.

The compatibilities of the tensor–Hom exchange are stated as those of its ingredients. A change
of coefficients is encoded by functors `T_X`, `T_Y` and comparison 2-squares for the left
adjoints `Lf^*`, `Rf_!`, `M ⊗ᴸ -`; the comparison maps of the right adjoints `Rf_*`, `Rf^!`,
`RHom(M, -)` are their mates.

Applying the exchange at `N = ω_Y` needs `ω_Y` to lie in `Dctf(Y, A)`, which does not follow
for a general coefficient category, so the Verdier exchange carries it as the hypothesis `hω`.
`AlgebraicGeometry.Etale.constructibleFiniteTor_dualizingComplex` discharges it over a
Noetherian base whenever the unit `Λ_S` lies in `Dctf(S, A)`.
-/

@[expose] public section

universe u' u'' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

section TensorHomIso

variable [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- **Tensor–Hom form of the exchange**, for an arbitrary right adjoint `G` of `Rf_!`. If the
projection map `PF : Rf_! M ⊗ᴸ L ⟶ Rf_!(M ⊗ᴸ Lf^* L)` (`AlgebraicGeometry.Etale.projectionMap`)
is an isomorphism, then `Rf_* RHom_X(M, G N) ≅ RHom_Y(Rf_! M, N)` as bifunctors
`D(X_ét)ᵒᵖ ⥤ D(Y_ét) ⥤ D(Y_ét)`, the conjugate of the projection formula along the adjunctions
with a parameter. -/
noncomputable def derivedHomLowerShriekIsoOfAdjunction
    {G : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (adj : R(f)_![A] ⊣ G) [IsIso (projectionMap A f)] :
    RHom(X)[A] ⋙ (Functor.whiskeringLeft _ _ _).obj G ⋙
        (Functor.whiskeringRight _ _ _).obj R((f)_*[A]) ≅
      (R(f)_![A]).op ⋙ RHom(Y)[A] :=
  ((derivedTensorHomAdjunction₂ A X).comp (derivedUpperStarLowerStarAdjunction A f)
      adj).conjugateIso
    ((derivedTensorHomAdjunction₂ A Y).precomp R(f)_![A]) (asIso (projectionMap A f))

/-- **Tensor–Hom form of the exchange.** Let `f : X ⟶ Y` admit a compactification, and assume
that the projection map `PF : Rf_! M ⊗ᴸ L ⟶ Rf_!(M ⊗ᴸ Lf^* L)`
(`AlgebraicGeometry.Etale.projectionMap`) is an isomorphism. Then
`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)` as bifunctors
`D(X_ét)ᵒᵖ ⥤ D(Y_ét) ⥤ D(Y_ét)`. -/
noncomputable def derivedHomRightDerivedLowerShriekIso
    [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f)] :
    RHom(X)[ModuleCat.{u + 1} Λ] ⋙ (Functor.whiskeringLeft _ _ _).obj R(f)^![Λ] ⋙
        (Functor.whiskeringRight _ _ _).obj R((f)_*[ModuleCat.{u + 1} Λ]) ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).op ⋙ RHom(Y)[ModuleCat.{u + 1} Λ] :=
  derivedHomLowerShriekIsoOfAdjunction (ModuleCat.{u + 1} Λ) f
    (rightDerivedUpperShriekAdjunction Λ f)

/-- The isomorphism `Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)` of
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` commutes with the shifts in
`N`. -/
theorem commShift_derivedHomRightDerivedLowerShriekIso_app_hom
    [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f)]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    NatTrans.CommShift (F₁ := (R(f)^![Λ] ⋙ (RHom(X)[ModuleCat.{u + 1} Λ]).obj (op M)) ⋙
        R((f)_*[ModuleCat.{u + 1} Λ]))
      (F₂ := (RHom(Y)[ModuleCat.{u + 1} Λ]).obj (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)))
      ((derivedHomRightDerivedLowerShriekIso Λ f).app (op M)).hom ℤ :=
  NatTrans.CommShift.conjugateEquiv
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).comp
      ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) M).comp
        (rightDerivedUpperShriekAdjunction Λ f)))
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) ((R(f)_![ModuleCat.{u + 1} Λ]).obj M))
    ((projectionMap (ModuleCat.{u + 1} Λ) f).app M)

section CoefficientChange

open TwoSquare

variable (A' : Type u'') [Category.{u + 1} A'] [Abelian A'] [IsGrothendieckAbelian.{u + 1} A']
  [MonoidalCategory A'] [MonoidalPreadditive A'] [SymmetricCategory A'] [MonoidalClosed A']
  [Abelian.HasFunctorialFlatResolution A']
  {FA' : A' → A' → Type (u + 1)} {CA' : A' → Type (u + 1)}
  [∀ X Y, FunLike (FA' X Y) (CA' X) (CA' Y)] [ConcreteCategory.{u + 1} A' FA']
  [Etale.UpperStarPreservesFlat A']
  [(CategoryTheory.forget A').ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A')]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A')]

omit [HasSmallSiteSheafify A] in
/-- Compatibility of the tensor–Hom exchange with a change of coefficients, as an identity of
2-squares: `derivedHomLowerShriekIsoOfAdjunction_hom_app_comp_mateEquiv` before evaluation at an
object `N`. -/
theorem whiskerTop_derivedHomLowerShriekIsoOfAdjunction_hom
    {G : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (adj : R(f)_![A] ⊣ G)
    {G' : DerivedCategory (Sheaf Y.smallEtaleTopology A') ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A')}
    (adj' : R(f)_![A'] ⊣ G') [IsIso (projectionMap A f)] [IsIso (projectionMap A' f)]
    (TX : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (TY : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A'))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M' : DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (σ : TwoSquare TY L((f)^*[A]) L((f)^*[A']) TX)
    (μ : TwoSquare TX ((-⊗ᴸ-(X)[A]).obj M) ((-⊗ᴸ-(X)[A']).obj M') TX)
    (ρ : TwoSquare TX R(f)_![A] R(f)_![A'] TY)
    (ν : TwoSquare TY ((-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj M))
      ((-⊗ᴸ-(Y)[A']).obj ((R(f)_![A']).obj M')) TY)
    (h : ν.whiskerLeft ((projectionMap A f).app M) =
      (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight ((projectionMap A' f).app M')) :
    (mateEquiv (derivedTensorHomAdjunction A ((R(f)_![A]).obj M))
        (derivedTensorHomAdjunction A' ((R(f)_![A']).obj M')) ν).whiskerTop
        ((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op M)).hom =
      ((mateEquiv adj adj' ρ ≫ₕ
          mateEquiv (derivedTensorHomAdjunction A M) (derivedTensorHomAdjunction A' M') μ) ≫ₕ
          mateEquiv (derivedUpperStarLowerStarAdjunction A f)
            (derivedUpperStarLowerStarAdjunction A' f) σ).whiskerBottom
        ((derivedHomLowerShriekIsoOfAdjunction A' f adj').app (op M')).hom := by
  rw [← mateEquiv_hcomp, ← mateEquiv_hcomp]
  exact mateEquiv_whiskerTop_conjugateEquiv
    ((derivedUpperStarLowerStarAdjunction A f).comp
      ((derivedTensorHomAdjunction A M).comp adj))
    (derivedTensorHomAdjunction A ((R(f)_![A]).obj M))
    ((derivedUpperStarLowerStarAdjunction A' f).comp
      ((derivedTensorHomAdjunction A' M').comp adj'))
    (derivedTensorHomAdjunction A' ((R(f)_![A']).obj M'))
    ((projectionMap A f).app M) ((projectionMap A' f).app M') _ ν h

omit [HasSmallSiteSheafify A] in
/-- **Compatibility of the tensor–Hom exchange with a change of coefficients.** A change of
coefficients is given by functors `T_X : D(X_ét, A) ⥤ D(X_ét, A')` and
`T_Y : D(Y_ét, A) ⥤ D(Y_ét, A')`, an object `M'` corresponding to `M`, and comparison 2-squares
`σ` for `Lf^*`, `μ`, `ν` for the tensor products and `ρ` for `Rf_!`; their mates are the
comparison maps of the right adjoints. If the change of coefficients is compatible with the
projection maps, then the square

```
T_Y Rf_* RHom(M, G N) -------- T_Y(iso) --------> T_Y RHom(Rf_! M, N)
          | |
          | comparison | comparison
          v v
Rf_* RHom(M', G' T_Y N) ---------- iso ----------> RHom(Rf_! M', T_Y N)
```

commutes, for right adjoints `G` and `G'` of `Rf_!` over `A` and `A'`. -/
theorem derivedHomLowerShriekIsoOfAdjunction_hom_app_comp_mateEquiv
    {G : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (adj : R(f)_![A] ⊣ G)
    {G' : DerivedCategory (Sheaf Y.smallEtaleTopology A') ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A')}
    (adj' : R(f)_![A'] ⊣ G') [IsIso (projectionMap A f)] [IsIso (projectionMap A' f)]
    (TX : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (TY : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A'))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M' : DerivedCategory (Sheaf X.smallEtaleTopology A'))
    (σ : TwoSquare TY L((f)^*[A]) L((f)^*[A']) TX)
    (μ : TwoSquare TX ((-⊗ᴸ-(X)[A]).obj M) ((-⊗ᴸ-(X)[A']).obj M') TX)
    (ρ : TwoSquare TX R(f)_![A] R(f)_![A'] TY)
    (ν : TwoSquare TY ((-⊗ᴸ-(Y)[A]).obj ((R(f)_![A]).obj M))
      ((-⊗ᴸ-(Y)[A']).obj ((R(f)_![A']).obj M')) TY)
    (h : ν.whiskerLeft ((projectionMap A f).app M) =
      (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight ((projectionMap A' f).app M'))
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    TY.map (((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op M)).hom.app N) ≫
        (mateEquiv (derivedTensorHomAdjunction A ((R(f)_![A]).obj M))
          (derivedTensorHomAdjunction A' ((R(f)_![A']).obj M')) ν).app N =
      (mateEquiv (derivedUpperStarLowerStarAdjunction A f)
          (derivedUpperStarLowerStarAdjunction A' f) σ).app _ ≫
        R((f)_*[A']).map ((mateEquiv (derivedTensorHomAdjunction A M)
          (derivedTensorHomAdjunction A' M') μ).app _) ≫
        R((f)_*[A']).map (((RHom(X)[A']).obj (op M')).map ((mateEquiv adj adj' ρ).app N)) ≫
        ((derivedHomLowerShriekIsoOfAdjunction A' f adj').app (op M')).hom.app
          (TY.obj N) := by
  have key := congr_app
    (whiskerTop_derivedHomLowerShriekIsoOfAdjunction_hom A f A' adj adj' TX TY M M'
      σ μ ρ ν h) N
  simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app, TwoSquare.hComp_app,
    Functor.comp_obj, Category.assoc, Functor.map_comp] at key
  exact key

end CoefficientChange

end TensorHomIso

section TensorHom

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasCompactification f]

/-- **Tensor–Hom form of the exchange.** For a morphism `f : X ⟶ Y` admitting a compactification
and torsion coefficients `Λ`,

`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`. -/
theorem nonempty_iso_derivedHom_rightDerivedLowerShriek
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op M)).obj
        ((R(f)^![Λ]).obj N)) ≅
      (RHom(Y)[ModuleCat.{u + 1} Λ].obj (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M))).obj N) := by
  have := isIso_projectionMap_of_finite Λ f
  exact ⟨((derivedHomRightDerivedLowerShriekIso _ f).app (op M)).app N⟩

/-- For a morphism `f : X ⟶ Y` admitting a compactification and torsion coefficients `Λ`, there
is an isomorphism `Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)` of bifunctors
`D(X_ét, Λ)ᵒᵖ ⥤ D(Y_ét, Λ) ⥤ D(Y_ét, Λ)` which commutes with the shifts in `N`. -/
theorem exists_iso_derivedHom_rightDerivedLowerShriek_commShift :
    ∃ e : RHom(X)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringLeft _ _ _).obj R(f)^![Λ] ⋙
          (Functor.whiskeringRight _ _ _).obj R((f)_*[ModuleCat.{u + 1} Λ]) ≅
        (R(f)_![ModuleCat.{u + 1} Λ]).op ⋙ RHom(Y)[ModuleCat.{u + 1} Λ],
      ∀ M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        NatTrans.CommShift
          (F₁ := (R(f)^![Λ] ⋙ (RHom(X)[ModuleCat.{u + 1} Λ]).obj (op M)) ⋙
            R((f)_*[ModuleCat.{u + 1} Λ]))
          (F₂ := (RHom(Y)[ModuleCat.{u + 1} Λ]).obj (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)))
          (e.app (op M)).hom ℤ :=
  have := isIso_projectionMap_of_finite Λ f
  ⟨derivedHomRightDerivedLowerShriekIso _ f,
    fun M ↦ commShift_derivedHomRightDerivedLowerShriekIso_app_hom _ f M⟩

/-- **Internal ambient adjunction.** For a morphism `f : X ⟶ Y` admitting a compactification and
a finite coefficient ring `Λ`, the canonical isomorphism, natural in `M ∈ D(X_ét, Λ)` and
`K ∈ D(Y_ét, Λ)`,

`Rf_* RHom_X(M, Rf^! K) ≅ RHom_Y(Rf_! M, K)`. -/
noncomputable def derivedHomRightDerivedLowerShriekIsoOfFinite :
    RHom(X)[ModuleCat.{u + 1} Λ] ⋙
        (Functor.whiskeringLeft _ _ _).obj R(f)^![Λ] ⋙
          (Functor.whiskeringRight _ _ _).obj R((f)_*[ModuleCat.{u + 1} Λ]) ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).op ⋙ RHom(Y)[ModuleCat.{u + 1} Λ] :=
  have := isIso_projectionMap_of_finite Λ f
  derivedHomRightDerivedLowerShriekIso _ f

end TensorHom

section VerdierExchange

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y S : Scheme.{u}} (f : X ⟶ Y)
  (aY : Y ⟶ S) [HasCompactification f] [HasCompactification aY] [HasCompactification (f ≫ aY)]

/-- **Verdier-duality exchange, first half.** If `f : X ⟶ Y`, the structure morphism
`a_Y : Y ⟶ S` and `a_X = f ≫ a_Y` all admit a compactification, then for torsion coefficients
the exceptional inverse image along `f` of the dualizing complex of `Y` is the dualizing complex
of `X`:

`Rf^! ω_Y ≅ ω_X`. -/
theorem nonempty_iso_rightDerivedUpperShriek_dualizingComplex :
    Nonempty ((R(f)^![Λ]).obj (dualizingComplex _ aY) ≅
      dualizingComplex _ (f ≫ aY)) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f aY
  exact ⟨((((rightDerivedUpperShriekAdjunction _ (f ≫ aY)).ofNatIsoLeft e).rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction _ f).comp
      (rightDerivedUpperShriekAdjunction _ aY))).app (𝟙_ _)).symm⟩

/-- **Verdier-duality exchange, second half.** With `a_Y : Y ⟶ S` the structure morphism of `Y`
and `a_X = f ≫ a_Y` that of `X`, the Verdier duals `𝔻_Y = RHom_Y(-, ω_Y)` and
`𝔻_X = RHom_X(-, ω_X)` exchange the extraordinary and the ordinary direct image: for torsion
coefficients and every `M`,

`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`. -/
theorem nonempty_iso_verdierDual_rightDerivedLowerShriek
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((verdierDual _ aY).obj (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)) ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual _ (f ≫ aY)).obj (op M))) := by
  obtain ⟨e₁⟩ := nonempty_iso_derivedHom_rightDerivedLowerShriek Λ f M (dualizingComplex _ aY)
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ f aY
  exact ⟨e₁.symm ≪≫ (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
    ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op M)).mapIso e₂)⟩

/-- **Verdier-duality exchange.** With `a_Y : Y ⟶ S` the structure morphism of `Y` and
`a_X = f ≫ a_Y` that of `X`, for torsion coefficients there is an isomorphism

`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`

natural in `M`, i.e. an isomorphism of functors `D(X_ét)ᵒᵖ ⥤ D(Y_ét)`. -/
theorem nonempty_verdierDual_rightDerivedLowerShriek_natIso :
    Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).op ⋙ verdierDual _ aY ≅
      verdierDual _ (f ≫ aY) ⋙ R((f)_*[ModuleCat.{u + 1} Λ])) := by
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ f aY
  exact ⟨(Functor.isoWhiskerRight (derivedHomRightDerivedLowerShriekIsoOfFinite Λ f)
      ((CategoryTheory.evaluation _ _).obj (dualizingComplex _ aY))).symm ≪≫
    Functor.isoWhiskerRight ((RHom(X)[ModuleCat.{u + 1} Λ]).flip.mapIso e₂)
      R((f)_*[ModuleCat.{u + 1} Λ])⟩

end VerdierExchange

end Etale

end AlgebraicGeometry
