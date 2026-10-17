/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OverProper
public import WeilConjectures.TraceFormula.Correspondence

/-!

# Proper pushforward of a correspondence

Let `c = (C, c₁, c₂, u)` be an endocorrespondence of `(X, K)`. A *proper pushforward diagram*
`(f, g) : (C, c) ⟶ (D, b)` (blueprint `def-trf-coefficient-pushforward`) consists of a proper
morphism `f : X ⟶ Y`, a second support `b = (b₁, b₂) : D ⟶ Y × Y` and a proper morphism
`g : C ⟶ D` with `g ≫ bᵢ = cᵢ ≫ f`
(`ProEtale.CondensedRing.Correspondence.ProperPushforwardDiagram`). No cartesian condition on
the leg squares is imposed. With `K' = Rf_* K`, the *coefficient pushforward* of `u` is
```
[f, g]_! u = δ ∘ Rg_* u ∘ γ : Lb₂^* K' ⟶ Rb₁^! K',
```
where
* the *ordinary half* `γ : Lb₂^* K' ⟶ Rg_* Lc₂^* K` is the unit of `Lg^* ⊣ Rg_*`, followed by
  the pullback composition `Lg^* Lb₂^* ≅ L(g ≫ b₂)^* = L(c₂ ≫ f)^* ≅ Lc₂^* Lf^*` and the counit of
  `Lf^* ⊣ Rf_*` (`ProperPushforwardDiagram.pushforwardCoeffUnit`);
* the *exceptional half* `δ : Rg_* Rc₁^! K ⟶ Rb₁^! K'` is the adjoint for `Rb₁_! ⊣ Rb₁^!` of
  `Rb₁_! Rg_* Rc₁^! K ≅ Rb₁_! Rg_! Rc₁^! K ≅ Rf_! Rc₁_! Rc₁^! K ⟶ Rf_! K ≅ Rf_* K`
  (`ProperPushforwardDiagram.pushforwardCoeffCounit`).

This gives a correspondence `(D, b₁, b₂, [f, g]_! u)` of `(Y, Rf_* K)`
(`ProperPushforwardDiagram.pushforward`).

## The induced map of fixed loci

The relations `g ≫ bᵢ = cᵢ ≫ f` induce `h : Fix(c) ⟶ Fix(b)`, the restriction of `g`
(`ProperPushforwardDiagram.fixMap`). It factors as
```
Fix(c) --κ--> C ×_D Fix(b) --π--> Fix(b)
```
with `π` the base change of `g` and `κ` a base change of the relative diagonal
`X ⟶ X ×_Y X` (`ProperPushforwardDiagram.isPullback_fixMapFactor`), hence a closed immersion;
so `h` is proper (`ProperPushforwardDiagram.isProper_fixMap`, blueprint
`lem-trf-fixed-map-proper`), and so is `q = f × f` (`ProperPushforwardDiagram.isProper_prodMap`).

## Maps along proper morphisms

For the kernel maps of a proper pushforward diagram (blueprint
`def-trf-kernel-pushforward-maps`) we construct the trace `τ_f : Rf_* ω_X ⟶ ω_Y`
(`lowerStarDualizingComplexTrace`) and the multiplication
`μ_f : Rf_* M ⊗ Rf_* N ⟶ Rf_* (M ⊗ N)` (`lowerStarTensorMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Maps along proper morphisms -/

section ProperMaps

variable (ℓ) {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The *trace along a proper morphism* `τ_f : Rf_* ω_X ⟶ ω_Y` (blueprint
`def-trf-kernel-pushforward-maps`, item 2):
```
Rf_* ω_X ≅ Rf_! ω_X ≅ Rf_! Rf^! ω_Y --ε--> ω_Y,
```
using `Rf_! ≅ Rf_*` for the proper `f`, the composition isomorphism `Rf^! ω_Y ≅ ω_X`
(`dualizingComplexComp`) and the counit of `Rf_! ⊣ Rf^!`. -/
noncomputable def lowerStarDualizingComplexTrace (f : X ⟶ Y) [IsProper f.left] :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (dualizingComplex ℓ X) ⟶ dualizingComplex ℓ Y :=
  (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app _ ≫
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map
      (dualizingComplexComp ℓ f).inv ≫
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app _

/-- The *multiplication* `μ_f : Rf_* M ⊗ Rf_* N ⟶ Rf_* (M ⊗ N)` (blueprint
`def-trf-kernel-pushforward-maps`, item 3): the adjoint for `Lf^* ⊣ Rf_*` of
```
Lf^* (Rf_* M ⊗ Rf_* N) ≅ Lf^* Rf_* M ⊗ Lf^* Rf_* N --ε ⊗ ε--> M ⊗ N,
```
the monoidal structure of `Lf^*` followed by the counits. -/
noncomputable def lowerStarTensorMap (f : X ⟶ Y)
    (M N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M ⊗
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj N ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj (M ⊗ N) :=
  (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f).homEquiv
    _ _
    (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
        _ _ ≫
      ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
          f).counit.app M ⊗ₘ
        (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
          f).counit.app N))

end ProperMaps

namespace Correspondence

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-! ### Proper pushforward diagrams -/

variable (c : Correspondence ℓ K) (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- A *proper pushforward diagram* `(f, g) : (C, c) ⟶ (D, b)` of an endocorrespondence `c` of
`(X, K)` to a scheme `Y` (blueprint `def-trf-coefficient-pushforward`): a proper morphism
`f : X ⟶ Y`, a separated `k`-scheme of finite type `D` with morphisms `b₁, b₂ : D ⟶ Y`, and a
proper morphism `g : C ⟶ D` with `g ≫ bᵢ = cᵢ ≫ f`. No cartesian condition is imposed on the
leg squares. -/
structure ProperPushforwardDiagram where
  /-- the proper morphism `f : X ⟶ Y`. -/
  f : X ⟶ Y
  [isProper_f : IsProper f.left]
  /-- the support `D` of the target correspondence. -/
  D : Over (Spec (.of k))
  [locallyOfFiniteType : LocallyOfFiniteType D.hom]
  [quasiCompact : QuasiCompact D.hom]
  [isSeparated : IsSeparated D.hom]
  /-- the exceptional leg `b₁ : D ⟶ Y`. -/
  b₁ : D ⟶ Y
  /-- the ordinary leg `b₂ : D ⟶ Y`. -/
  b₂ : D ⟶ Y
  /-- the proper morphism `g : C ⟶ D`. -/
  g : c.C ⟶ D
  [isProper_g : IsProper g.left]
  w₁ : g ≫ b₁ = c.c₁ ≫ f
  w₂ : g ≫ b₂ = c.c₂ ≫ f

namespace ProperPushforwardDiagram

attribute [instance] isProper_f isProper_g locallyOfFiniteType quasiCompact isSeparated

variable {c Y} (P : c.ProperPushforwardDiagram Y)

/-- The pushforward coefficient `K' = Rf_* K` of a proper pushforward diagram. -/
noncomputable abbrev coeff : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ P.f).obj K

/-- The *ordinary half* `γ : Lb₂^* K' ⟶ Rg_* Lc₂^* K` of the coefficient pushforward (blueprint
`def-trf-coefficient-pushforward`, item 1):
```
Lb₂^* K' --η_g--> Rg_* Lg^* Lb₂^* K' ≅ Rg_* L(g ≫ b₂)^* K' = Rg_* L(c₂ ≫ f)^* K'
  ≅ Rg_* Lc₂^* Lf^* Rf_* K --Rg_* Lc₂^* ε_f--> Rg_* Lc₂^* K.
```
-/
noncomputable def pushforwardCoeffUnit :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.b₂).obj P.coeff ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ P.g).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K) :=
  (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      P.g).unit.app _ ≫
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ P.g).map
      ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ P.g P.b₂).inv.app _ ≫
        eqToHom (by rw [P.w₂]) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂ P.f).hom.app _ ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            P.f).counit.app K))

/-- The *exceptional half* `δ : Rg_* Rc₁^! K ⟶ Rb₁^! K'` of the coefficient pushforward
(blueprint `def-trf-coefficient-pushforward`, item 2): the adjoint for `Rb₁_! ⊣ Rb₁^!` of
```
Rb₁_! Rg_* Rc₁^! K ≅ Rb₁_! Rg_! Rc₁^! K ≅ R(g ≫ b₁)_! Rc₁^! K = R(c₁ ≫ f)_! Rc₁^! K
  ≅ Rf_! Rc₁_! Rc₁^! K --Rf_! ε_{c₁}--> Rf_! K ≅ Rf_* K,
```
using `Rg_! ≅ Rg_*`, `Rf_! ≅ Rf_*` for the proper `g`, `f` and the composition isomorphisms of
the lower shriek. -/
noncomputable def pushforwardCoeffCounit :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ P.g).obj
        ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.c₁).obj K) ⟶
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ P.b₁).obj P.coeff :=
  (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ P.b₁).homEquiv _ _
    ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ P.b₁).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ P.g).inv.app _) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ P.g P.b₁).inv.app _ ≫
      eqToHom (by rw [P.w₁]) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ c.c₁ P.f).hom.app _ ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ P.f).map
        ((boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
          c.c₁).counit.app K) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ P.f).hom.app K)

/-- The *coefficient pushforward* `[f, g]_! u = δ ∘ Rg_* u ∘ γ : Lb₂^* K' ⟶ Rb₁^! K'` of the
coefficient map of `c` along a proper pushforward diagram (blueprint
`def-trf-coefficient-pushforward`, item 3). -/
noncomputable def pushforwardCoeff :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ P.b₂).obj P.coeff ⟶
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ P.b₁).obj P.coeff :=
  P.pushforwardCoeffUnit ≫
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ P.g).map c.u ≫
    P.pushforwardCoeffCounit

/-- The *proper pushforward* `(D, b₁, b₂, [f, g]_! u)` of the correspondence `c`, a
correspondence of `(Y, Rf_* K)` (blueprint `def-trf-coefficient-pushforward`). -/
noncomputable def pushforward : Correspondence ℓ P.coeff where
  C := P.D
  c₁ := P.b₁
  c₂ := P.b₂
  u := P.pushforwardCoeff

end ProperPushforwardDiagram

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
