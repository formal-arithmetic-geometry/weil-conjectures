/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs

/-!
# Correspondences, global operators and Borel-Moore integration

A correspondence from `(X, K)` to `(Y, L)` is a pair of legs `c = (c₁, c₂) : C ⟶ Y × X`
together with a coefficient map `u : c₂^* K ⟶ c₁^! L`. When `X = Y` and `K = L` it is an
*endocorrespondence*, its fixed scheme `Fix(c)` is the locus where the two legs agree, and
when the ordinary leg `c₂` is proper it induces a *global operator* on compactly supported
cohomology.

A *Borel-Moore section* on a geometric scheme `T` is a map `A_T ⟶ ω_T`; it can be pushed
forward along a proper morphism, and integrated when `T` is proper over the base.

## Main definitions

- `AlgebraicGeometry.ProEtale.Correspondence`: a correspondence and its supported class.
- `AlgebraicGeometry.ProEtale.Correspondence.fix`, `fixι`, `fixStr`: the fixed scheme of an
  endocorrespondence, its inclusion into the support and its structure morphism.
- `AlgebraicGeometry.ProEtale.Correspondence.toProd`,
  `AlgebraicGeometry.ProEtale.Correspondence.toProdSwap`,
  `AlgebraicGeometry.ProEtale.Correspondence.intersection`,
  `AlgebraicGeometry.ProEtale.Correspondence.intersectionStr`: the support map
  `c : C ⟶ Y × X`, its swapped form on an opposite correspondence, and the intersection
  support `E(C, D) = C ×_{Y × X} D` of an opposite pair.
- `AlgebraicGeometry.ProEtale.Correspondence.ofEnd`: the diagonal endocorrespondence
  attached to an endomorphism of the coefficient complex.
- `AlgebraicGeometry.ProEtale.Correspondence.globalOperator`: the global operator
  `T_c(u)` on compactly supported cohomology.
- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMooreSections`: the Borel-Moore
  sections `A_T ⟶ ω_T` of a geometric scheme.
- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMooreRestrict`: the restriction of a
  Borel-Moore section along an open immersion.
- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMoorePushforward`,
  `AlgebraicGeometry.ProEtale.GeometricOperations.integral`: the pushforward and the
  integral of a Borel-Moore section.

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMoorePushforward_id`: pushing forward
  along the identity gives the section back.

## Implementation notes

`globalOperator`, `borelMooreRestrict`, `borelMoorePushforward`, `integral` and the
coefficient map of `ofEnd` are defined as composites of the adjunctions of the pro-étale
functors and the comparison data of the package
`AlgebraicGeometry.ProEtale.GeometricOperations`:

* `ofEndCoeff` uses `leftDerivedUpperStarId` and `GeometricOperations.upperShriekId`,
  hence the field `lowerShriekId`;
* `globalOperator` uses the fields `properComparison` and `lowerShriekComp`, transported
  along `c₁ ≫ a_X = a_C = c₂ ≫ a_X` by `rightDerivedLowerShriekCongr`;
* `borelMooreRestrict` uses the fields `upperStarUnit`, `openPurity` and `dualizingComp`;
* `borelMoorePushforward` uses the fields `upperStarUnit`, `properComparison` and
  `dualizingComp`, and `integral` is the pushforward along `a_T : T ⟶ s` followed by
  `dualizingBase`.

The integral takes its values in `End (A_s)`, which is the coefficient ring by the
normalisation `GeometricOperations.dualizingBase : ω_s ≅ A_s`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s : Scheme.{u}}

/-- A correspondence from `(X, K)` to `(Y, L)`: a geometric scheme `C` over the base `s`,
two legs `c₁ : C ⟶ Y`, `c₂ : C ⟶ X` over `s` — the blueprint's `c = (c₁, c₂) : C ⟶ Y × X`,
`c₂` being the *ordinary-pullback* leg — and a coefficient map `u : c₂^* K ⟶ c₁^! L`:

```
            C
          ↙   ↘
       c₁       c₂
      ↙           ↘
     Y             X          u : Lc₂^* K ⟶ c₁^! L
      ↘     ↓a_C  ↙
       a_Y  ↓  a_X
          ↘ ↓ ↙
            s
```

A class supported on `i : T ⟶ Z` is an element of `Hom(Ri_! A_T, P)`; tensor-hom, the
projection formula and exceptional adjunction identify such classes with coefficient maps,
so the supported class `[u]` carries the same information as `u` and is not separate data
(blueprint: `sk-d-corr`). -/
structure Correspondence {X Y : Scheme.{u}} (aX : X ⟶ s) (aY : Y ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) where
  /-- the support `C` of the correspondence. -/
  supp : Scheme.{u}
  /-- the structure morphism `a_C : C ⟶ s`. -/
  str : supp ⟶ s
  /-- the exceptional leg `c₁ : C ⟶ Y`. -/
  fst : supp ⟶ Y
  /-- the ordinary-pullback leg `c₂ : C ⟶ X`. -/
  snd : supp ⟶ X
  /-- `c₁` is a morphism over `s`. -/
  fst_comp : fst ≫ aY = str
  /-- `c₂` is a morphism over `s`. -/
  snd_comp : snd ≫ aX = str
  /-- `c₁` admits a compactification, so that `c₁^!` is available. -/
  [hasCompactification_fst : HasCompactification fst]
  /-- the coefficient map `u : c₂^* K ⟶ c₁^! L`. -/
  coeff : ((upperStar A snd).leftDerivedFunctor).obj K ⟶
    (rightDerivedUpperShriek A fst).obj L

attribute [instance] Correspondence.hasCompactification_fst

namespace Correspondence

variable {X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}

/-- The fixed scheme `Fix(c) = C ×_{X × X, c, Δ_X} X` of an endocorrespondence: the locus
where the two legs agree, realised as their equalizer (part of blueprint `sk-d-corr`). -/
noncomputable def fix (c : Correspondence aX aX K K) : Scheme.{u} :=
  equalizer c.fst c.snd

/-- The inclusion `Fix(c) ⟶ C` of the fixed scheme into the support
(part of blueprint `sk-d-corr`). -/
noncomputable def fixι (c : Correspondence aX aX K K) : c.fix ⟶ c.supp :=
  equalizer.ι c.fst c.snd

/-- The structure morphism `Fix(c) ⟶ s` of the fixed scheme
(part of blueprint `sk-d-corr`). -/
noncomputable def fixStr (c : Correspondence aX aX K K) : c.fix ⟶ s :=
  c.fixι ≫ c.str

/-- The support map `c = (c₁, c₂) : C ⟶ Y × X` of a correspondence
(part of blueprint `sk-d-corr`). -/
noncomputable def toProd (c : Correspondence aX aY K L) : c.supp ⟶ pullback aY aX :=
  pullback.lift c.fst c.snd (c.fst_comp.trans c.snd_comp.symm)

/-- The support map `d̄ = τ d : D ⟶ Y × X` of an opposite correspondence, obtained from
`d = (d₁, d₂) : D ⟶ X × Y` by the exchange of factors
(part of blueprint `sk-d-corr`). -/
noncomputable def toProdSwap (d : Correspondence aY aX L K) : d.supp ⟶ pullback aY aX :=
  pullback.lift d.snd d.fst (d.snd_comp.trans d.fst_comp.symm)

/-- The intersection support `E(C, D) = C ×_{Y × X} D` of an opposite pair
(part of blueprint `sk-d-pairing`). -/
noncomputable def intersection (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K) : Scheme.{u} :=
  pullback c.toProd d.toProdSwap

/-- The structure morphism `E(C, D) ⟶ s` of the intersection support
(part of blueprint `sk-d-pairing`). -/
noncomputable def intersectionStr (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K) : c.intersection d ⟶ s :=
  pullback.fst c.toProd d.toProdSwap ≫ c.str

/-- The fixed scheme is the pullback of the support map along the diagonal:

```
  Fix(c) ──fixι──▶ C
     │             │
  fixι ≫ c₁        │ c = (c₁, c₂)
     ▼             ▼
     X ────Δ_X───▶ X ×_s X
```

is Cartesian, the equalizer of `c₁` and `c₂` being `C ×_{X × X} X`
(part of blueprint `sk-d-corr`). -/
lemma isPullback_fixι_toProd (c : Correspondence aX aX K K) :
    IsPullback c.fixι (c.fixι ≫ c.fst) c.toProd (pullback.diagonal aX) :=
  isPullback_equalizer_ι_diagonal c.fst c.snd _

/-- The inclusion `Fix(c) ⟶ C` of the fixed scheme is the base change of the diagonal of
`aX` along the support map `c : C ⟶ X × X` (`isPullback_fixι_toProd`). The diagonal is a
closed immersion when `aX` is separated, so `Fix(c) ⟶ C` then admits a compactification. -/
instance hasCompactification_fixι [IsSeparated aX] (c : Correspondence aX aX K K) :
    HasCompactification c.fixι :=
  .of_isPullback c.isPullback_fixι_toProd.flip

/-- The structure morphism of the intersection support `E(C, D)` factors through the first
projection of `Y × X`: the diagram

```
  E(C, D) ──pr₁──▶ C ────c────▶ Y ×_s X
                   │               │
               a_C │               │ pr₁
                   ▼               ▼
                   s ◀────a_Y───── Y
```

commutes, since `c ≫ pr₁ = c₁` and `c₁ ≫ a_Y = a_C`. -/
lemma pullback_fst_toProd_fst_comp_eq_intersectionStr (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K) :
    pullback.fst c.toProd d.toProdSwap ≫ c.toProd ≫ pullback.fst aY aX ≫ aY =
      c.intersectionStr d := by
  simp [intersectionStr, toProd, c.fst_comp]

/-- The structure morphism of the fixed scheme factors through the support map and the first
projection of `X × X`: `fixι ≫ c ≫ pr₁ ≫ a_X = a_{Fix(c)}`, since `c ≫ pr₁ = c₁` and
`c₁ ≫ a_X = a_C`. -/
lemma fixι_toProd_fst_comp_eq_fixStr (c : Correspondence aX aX K K) :
    c.fixι ≫ c.toProd ≫ pullback.fst aX aX ≫ aX = c.fixStr := by
  simp [fixStr, toProd, c.fst_comp]

variable [DerivedBraiding A]

/-- The coefficient map of `AlgebraicGeometry.ProEtale.Correspondence.ofEnd`: the
endomorphism `v` read through the comparisons `L(𝟙)^* K ≃ K ≃ 𝟙^! K`. -/
noncomputable def ofEndCoeff (G : GeometricOperations A s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    ((upperStar A (𝟙 X)).leftDerivedFunctor).obj K ⟶
      (rightDerivedUpperShriek A (𝟙 X)).obj K :=
  (leftDerivedUpperStarId A X).hom.app K ≫ v ≫ (G.upperShriekId X).inv.app K

/-- The coefficient map of the diagonal identity `ofEnd G aX K (𝟙 K)` is the comparison
`L(𝟙)^* K ≃ K ≃ 𝟙^! K`. -/
@[simp]
lemma ofEndCoeff_id (G : GeometricOperations A s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ofEndCoeff G K (𝟙 K) =
      (leftDerivedUpperStarId A X).hom.app K ≫ (G.upperShriekId X).inv.app K := by
  simp [ofEndCoeff]

/-- The endocorrespondence on `(X, K)` with support `X`, support map the diagonal `Δ_X`,
identity legs, and coefficient map induced by `v : K ⟶ K`. For `v = 𝟙 K` this is the
blueprint's *diagonal identity* (part of blueprint `sk-d-corr`). -/
noncomputable def ofEnd (G : GeometricOperations A s) (aX : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    Correspondence aX aX K K where
  supp := X
  str := aX
  fst := 𝟙 X
  snd := 𝟙 X
  fst_comp := Category.id_comp aX
  snd_comp := Category.id_comp aX
  coeff := ofEndCoeff G K v

/-- The support map of `ofEnd G aX K v` is the diagonal of `aX`. -/
@[simp]
lemma ofEnd_toProd (G : GeometricOperations A s) (aX : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    (ofEnd G aX K v).toProd = pullback.diagonal aX :=
  rfl

/-- The swapped support map of `ofEnd G aX K v` is the diagonal of `aX`. -/
@[simp]
lemma ofEnd_toProdSwap (G : GeometricOperations A s) (aX : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    (ofEnd G aX K v).toProdSwap = pullback.diagonal aX :=
  rfl

/-- The support map of `ofEnd G aX K v` is the diagonal of `aX`, a closed immersion when
`aX` is separated, so it admits a compactification. -/
instance hasCompactification_toProd_ofEnd (G : GeometricOperations A s) (aX : X ⟶ s)
    [IsSeparated aX] (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    HasCompactification (ofEnd G aX K v).toProd := by
  rw [ofEnd_toProd]
  infer_instance

/-- The swapped support map of `ofEnd G aX K v` is the diagonal of `aX`, a closed immersion
when `aX` is separated, so it admits a compactification. -/
instance hasCompactification_toProdSwap_ofEnd (G : GeometricOperations A s) (aX : X ⟶ s)
    [IsSeparated aX] (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    HasCompactification (ofEnd G aX K v).toProdSwap := by
  rw [ofEnd_toProdSwap]
  infer_instance

instance isIso_fixι_ofEnd (G : GeometricOperations A s) (aX : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    IsIso (ofEnd G aX K v).fixι :=
  inferInstanceAs (IsIso (equalizer.ι (𝟙 X) (𝟙 X)))

/-- The structure morphism of `ofEnd G aX K v` is `aX`, so it admits a compactification
when `aX` does. -/
instance hasCompactification_str_ofEnd (G : GeometricOperations A s) (aX : X ⟶ s)
    [HasCompactification aX] (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (v : K ⟶ K) : HasCompactification (ofEnd G aX K v).str :=
  inferInstanceAs (HasCompactification aX)

instance isProper_fixStr_ofEnd (G : GeometricOperations A s) (aX : X ⟶ s) [IsProper aX]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    IsProper (ofEnd G aX K v).fixStr :=
  inferInstanceAs (IsProper ((ofEnd G aX K v).fixι ≫ aX))

/-- `c₂ ≫ a_X = a_C` admits a compactification when `a_C` does. -/
instance hasCompactification_snd_comp (c : Correspondence aX aY K L)
    [HasCompactification c.str] : HasCompactification (c.snd ≫ aX) :=
  c.snd_comp ▸ inferInstance

/-- `c₁ ≫ a_Y = a_C` admits a compactification when `a_C` does. -/
instance hasCompactification_fst_comp (c : Correspondence aX aY K L)
    [HasCompactification c.str] : HasCompactification (c.fst ≫ aY) :=
  c.fst_comp ▸ inferInstance

/-- The first half of the global operator, `RΓ_c(X, K) ⟶ RΓ_c(C, c₂^* K)`: the composite

```
  Ra_{X!} K ──η──▶ Ra_{X!} Rc₂_* c₂^* K ≅ Ra_{X!} Rc₂_! c₂^* K ≅ Ra_{C!} c₂^* K
```

of the unit of `c₂^* ⊣ Rc₂_*`, the proper identification `Rc₂_* = Rc₂_!` and the
composition `Ra_{X!} Rc₂_! ≃ R(c₂ ≫ a_X)_! = Ra_{C!}` (part of blueprint `sk-d-operator`). -/
noncomputable def globalOperatorUnit (G : GeometricOperations A s)
    (c : Correspondence aX aY K L) [HasCompactification aX] [IsProper c.snd]
    [HasCompactification c.str] :
    (rightDerivedLowerShriek A aX).obj K ⟶
      (rightDerivedLowerShriek A c.str).obj (((upperStar A c.snd).leftDerivedFunctor).obj K) :=
  (rightDerivedLowerShriek A aX).map
      ((derivedUpperStarLowerStarAdjunction A c.snd).unit.app K) ≫
    (rightDerivedLowerShriek A aX).map ((G.properComparison c.snd).inv.app _) ≫
    (G.lowerShriekComp c.snd aX).hom.app _ ≫
    (rightDerivedLowerShriekCongr A c.snd_comp).hom.app _

/-- The second half of the global operator, `RΓ_c(C, c₁^! L) ⟶ RΓ_c(Y, L)`: the composite

```
  Ra_{C!} c₁^! L ≅ Ra_{Y!} Rc₁_! c₁^! L ──ε──▶ Ra_{Y!} L
```

of the composition `Ra_{C!} = R(c₁ ≫ a_Y)_! ≃ Ra_{Y!} Rc₁_!` and the counit of
`Rc₁_! ⊣ c₁^!` (part of blueprint `sk-d-operator`). -/
noncomputable def globalOperatorCounit (G : GeometricOperations A s)
    (c : Correspondence aX aY K L) [HasCompactification aY] [HasCompactification c.str] :
    (rightDerivedLowerShriek A c.str).obj ((rightDerivedUpperShriek A c.fst).obj L) ⟶
      (rightDerivedLowerShriek A aY).obj L :=
  (rightDerivedLowerShriekCongr A c.fst_comp.symm).hom.app _ ≫
    (G.lowerShriekComp c.fst aY).inv.app _ ≫
    (rightDerivedLowerShriek A aY).map ((rightDerivedUpperShriekAdjunction A c.fst).counit.app L)

/-- The global operator of an endocorrespondence `(C, c, u)` on `(X, K)` whose ordinary leg
`c₂` is proper: the composite

```
  RΓ_c(X, K) ──η──▶ RΓ_c(X, Rc₂_* c₂^* K) ≅ RΓ_c(C, c₂^* K) ──u──▶ RΓ_c(C, c₁^! K)
             ≅ RΓ_c(X, Rc₁_! c₁^! K) ──ε──▶ RΓ_c(X, K)
```

of the unit of `c₂^* ⊣ Rc₂_*`, the proper identification `Rc₂_* = Rc₂_!` and the counit of
`Rc₁_! ⊣ c₁^!`, acting on compactly supported cohomology `RΓ_c(X, K) = Ra_{X!} K`
(blueprint: `sk-d-operator`). -/
noncomputable def globalOperator (G : GeometricOperations A s)
    (c : Correspondence aX aX K K) [HasCompactification aX] [IsProper c.snd]
    [HasCompactification c.str] :
    (rightDerivedLowerShriek A aX).obj K ⟶ (rightDerivedLowerShriek A aX).obj K :=
  globalOperatorUnit G c ≫ (rightDerivedLowerShriek A c.str).map c.coeff ≫
    globalOperatorCounit G c

end Correspondence

namespace GeometricOperations

variable [DerivedBraiding A] (G : GeometricOperations A s)

/-- The *Borel-Moore sections* `A_T ⟶ ω_T` of a geometric scheme `a : T ⟶ s`
(part of blueprint `sk-d-integral`). -/
abbrev borelMooreSections {T : Scheme.{u}} (a : T ⟶ s) :=
  𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) A)) ⟶ G.dualizing a

/-- The restriction `j^* α : A_B ⟶ ω_B` of a Borel-Moore section `α : A_E ⟶ ω_E` along an
open immersion `j : B ⟶ E`: the composite

`A_B ≃ Lj^* A_E ⟶ Lj^* ω_E ≃ j^! ω_E ≃ ω_B`

of `GeometricOperations.upperStarUnit`, open-immersion purity and the dualizing
composition (part of blueprint `sk-d-local-term`). An open immersion need not admit a
compactification, so `[HasCompactification j]` is a hypothesis: `openPurity` needs it. -/
noncomputable def borelMooreRestrict {E B : Scheme.{u}} {aE : E ⟶ s} (j : B ⟶ E)
    [IsOpenImmersion j] [HasCompactification j] (α : G.borelMooreSections aE) :
    G.borelMooreSections (j ≫ aE) :=
  (G.upperStarUnit j).inv ≫ ((upperStar A j).leftDerivedFunctor).map α ≫
    (G.openPurity j).inv.app _ ≫ (G.dualizingComp j aE).hom

/-- The pushforward of a Borel-Moore section `α : A_T ⟶ ω_T` along a proper `h : T ⟶ T'`
over `s`: the composite

```
  A_{T'} ──η──▶ Rh_* Lh^* A_{T'} ≅ Rh_* A_T ──α──▶ Rh_* ω_T ≅ Rh_! ω_T ≅ Rh_! h^! ω_{T'}
         ──ε──▶ ω_{T'}
```

of the unit of `h^* ⊣ Rh_*`, the proper identification `Rh_* = Rh_!`, the dualizing
composition `h^! ω_{T'} ≃ ω_T` and the counit of `Rh_! ⊣ h^!`
(blueprint: `sk-d-integral`). -/
noncomputable def borelMoorePushforward {T T' : Scheme.{u}} (h : T ⟶ T') (a : T' ⟶ s)
    [HasCompactification h] [IsProper h] (α : G.borelMooreSections (h ≫ a)) :
    G.borelMooreSections a :=
  (derivedUpperStarLowerStarAdjunction A h).unit.app (𝟙_ _) ≫
    ((lowerStar A h).rightDerivedFunctor).map ((G.upperStarUnit h).hom ≫ α) ≫
    (G.properComparison h).inv.app _ ≫
    (rightDerivedLowerShriek A h).map (G.dualizingComp h a).inv ≫
    (rightDerivedUpperShriekAdjunction A h).counit.app (G.dualizing a)

/-- Pushing a Borel-Moore section forward along the identity gives the section back, up to
the transport `ω_{𝟙 ≫ a} = ω_a`. -/
lemma borelMoorePushforward_id {T : Scheme.{u}} (a : T ⟶ s)
    (α : G.borelMooreSections (𝟙 T ≫ a)) :
    G.borelMoorePushforward (𝟙 T) a α = α ≫ (G.dualizingCongr (Category.id_comp a)).hom := by
  set c := (conjugateEquiv (derivedUpperStarLowerStarAdjunction A (𝟙 T)) Adjunction.id)
    (leftDerivedUpperStarId A T).inv
  have hc := c.naturality
  have h₁ := unit_conjugateEquiv (derivedUpperStarLowerStarAdjunction A (𝟙 T)) Adjunction.id
    (leftDerivedUpperStarId A T).inv (𝟙_ _)
  have h₂ := conjugateEquiv_counit Adjunction.id (rightDerivedUpperShriekAdjunction A (𝟙 T))
    (G.lowerShriekId T).hom (G.dualizing a)
  have h₃ : (((conjugateIsoEquiv Adjunction.id (rightDerivedUpperShriekAdjunction A (𝟙 T)))
      (G.lowerShriekId T)).symm.app (G.dualizing a)).inv =
      ((conjugateEquiv Adjunction.id (rightDerivedUpperShriekAdjunction A (𝟙 T)))
        (G.lowerShriekId T).hom).app (G.dualizing a) := rfl
  have h₄ := (G.lowerShriekId T).inv.naturality
    (eqToHom (congrArg G.dualizing (Category.id_comp a)))
  dsimp at hc h₁ h₂
  dsimp only [Functor.id_obj, Functor.id_map] at h₄
  simp only [borelMoorePushforward, G.properComparison_id, G.dualizingComp_id,
    upperStarUnit_hom_id, Iso.trans_inv, NatTrans.comp_app, conjugateIsoEquiv_apply_inv,
    eqToIso.inv, Functor.map_comp, Category.assoc, dualizingCongr]
  rw [reassoc_of% (hc α), reassoc_of% (hc ((leftDerivedUpperStarId A T).hom.app (𝟙_ _))),
    reassoc_of% h₁, h₃, h₂, ← reassoc_of% h₄]
  simp

/-- The integral `∫_T α ∈ A` of a Borel-Moore section over a geometric scheme `T` that is
proper over the base: the pushforward of `α` along `a_T`, read in `End (A_s) = A` through
`GeometricOperations.dualizingBase` (part of blueprint `sk-d-integral`). -/
noncomputable def integral {T : Scheme.{u}} (a : T ⟶ s) [HasCompactification a]
    [IsProper a] (α : G.borelMooreSections a) :
    End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))) :=
  G.borelMoorePushforward a (𝟙 s)
      (α ≫ (G.dualizingCongr (Category.comp_id a).symm).hom) ≫
    G.dualizingBase.hom

end GeometricOperations

end AlgebraicGeometry.ProEtale
