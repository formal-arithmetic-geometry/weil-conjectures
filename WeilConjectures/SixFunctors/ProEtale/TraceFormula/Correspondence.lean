/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
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

## Implementation notes

`globalOperator`, `borelMooreRestrict`, `borelMoorePushforward`, `integral` and the
coefficient map of `ofEnd` are defined as composites of the adjunctions of the pro-étale
functors and the comparison data of the package
`AlgebraicGeometry.ProEtale.GeometricOperations`:

* `ofEndCoeff` uses `leftDerivedUpperStarId` and `GeometricOperations.upperShriekIdIso`,
  hence the field `lowerShriekId`;
* `globalOperator` uses the fields `properComparison` and `lowerShriekComp`, transported
  along `c₁ ≫ a_X = a_C = c₂ ≫ a_X` by `lowerShriekCongr`;
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
where the two legs agree, realised as their equaliser (part of blueprint `sk-d-corr`). -/
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

/-- The coefficient map of `AlgebraicGeometry.ProEtale.Correspondence.ofEnd`: the
endomorphism `v` read through the comparisons `L(𝟙)^* K ≃ K ≃ 𝟙^! K`. -/
noncomputable def ofEndCoeff (G : GeometricOperations A s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    ((upperStar A (𝟙 X)).leftDerivedFunctor).obj K ⟶
      (rightDerivedUpperShriek A (𝟙 X)).obj K :=
  (leftDerivedUpperStarId A X).hom.app K ≫ v ≫ (G.upperShriekIdIso X).hom.app K

/-- The coefficient map of the diagonal identity `ofEnd G aX K (𝟙 K)` is the comparison
`L(𝟙)^* K ≃ K ≃ 𝟙^! K`. -/
@[simp]
lemma ofEndCoeff_id (G : GeometricOperations A s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ofEndCoeff G K (𝟙 K) =
      (leftDerivedUpperStarId A X).hom.app K ≫ (G.upperShriekIdIso X).hom.app K := by
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

instance isIso_fixι_ofEnd (G : GeometricOperations A s) (aX : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    IsIso (ofEnd G aX K v).fixι :=
  inferInstanceAs (IsIso (equalizer.ι (𝟙 X) (𝟙 X)))

instance hasCompactification_str_ofEnd (G : GeometricOperations A s) (aX : X ⟶ s)
    [HasCompactification aX] (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (v : K ⟶ K) : HasCompactification (ofEnd G aX K v).str :=
  inferInstanceAs (HasCompactification aX)

instance isProper_fixStr_ofEnd (G : GeometricOperations A s) (aX : X ⟶ s) [IsProper aX]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (v : K ⟶ K) :
    IsProper (ofEnd G aX K v).fixStr :=
  inferInstanceAs (IsProper ((ofEnd G aX K v).fixι ≫ aX))

instance hasCompactification_snd_comp (c : Correspondence aX aY K L)
    [HasCompactification c.str] : HasCompactification (c.snd ≫ aX) := by
  rw [c.snd_comp]
  infer_instance

instance hasCompactification_fst_comp (c : Correspondence aX aY K L)
    [HasCompactification c.str] : HasCompactification (c.fst ≫ aY) := by
  rw [c.fst_comp]
  infer_instance

/-- The first half `RΓ_c(X, K) ⟶ RΓ_c(X, Rc₂_* c₂^* K) ≃ RΓ_c(C, c₂^* K)` of the global
operator: the unit of `c₂^* ⊣ Rc₂_*`, the proper identification `Rc₂_* = Rc₂_!` and the
composition `Ra_{X!} Rc₂_! ≃ Ra_{C!}`. -/
noncomputable def globalOperatorUnit (G : GeometricOperations A s)
    (c : Correspondence aX aX K K) [HasCompactification aX] [IsProper c.snd]
    [HasCompactification c.str] :
    (rightDerivedLowerShriek A aX).obj K ⟶
      (rightDerivedLowerShriek A c.str).obj (((upperStar A c.snd).leftDerivedFunctor).obj K) :=
  (rightDerivedLowerShriek A aX).map
      ((derivedUpperStarLowerStarAdjunction A c.snd).unit.app K) ≫
    (rightDerivedLowerShriek A aX).map ((G.properComparison c.snd).inv.app _) ≫
    (G.lowerShriekComp c.snd aX ≪≫ lowerShriekCongr c.snd_comp).hom.app _

/-- The second half `RΓ_c(C, c₁^! K) ≃ RΓ_c(X, Rc₁_! c₁^! K) ⟶ RΓ_c(X, K)` of the global
operator: the composition `Ra_{C!} ≃ Ra_{X!} Rc₁_!` and the counit of `Rc₁_! ⊣ c₁^!`. -/
noncomputable def globalOperatorCounit (G : GeometricOperations A s)
    (c : Correspondence aX aX K K) [HasCompactification aX] [HasCompactification c.str] :
    (rightDerivedLowerShriek A c.str).obj ((rightDerivedUpperShriek A c.fst).obj K) ⟶
      (rightDerivedLowerShriek A aX).obj K :=
  (lowerShriekCongr c.fst_comp.symm ≪≫
      (G.lowerShriekComp c.fst aX).symm).hom.app _ ≫
    (rightDerivedLowerShriek A aX).map ((rightDerivedUpperShriekAdjunction A c.fst).counit.app K)

/-- The global operator of an endocorrespondence `(C, c, u)` on `(X, K)` whose ordinary leg
`c₂` is proper: the composite

`T_c(u) : RΓ_c(X, K) ⟶ RΓ_c(X, Rc₂_* c₂^* K) ≃ RΓ_c(C, c₂^* K) ⟶ RΓ_c(C, c₁^! K)
  ≃ RΓ_c(X, Rc₁_! c₁^! K) ⟶ RΓ_c(X, K)`

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

variable (G : GeometricOperations A s)

/-- The *Borel-Moore sections* `A_T ⟶ ω_T` of a geometric scheme `a : T ⟶ s`
(part of blueprint `sk-d-integral`). -/
abbrev borelMooreSections {T : Scheme.{u}} (a : T ⟶ s) :=
  𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) A)) ⟶ G.dualizing a

/-- The restriction `j^* α : A_B ⟶ ω_B` of a Borel-Moore section `α : A_E ⟶ ω_E` along an
open immersion `j : B ⟶ E`: the composite

`A_B ≃ Lj^* A_E ⟶ Lj^* ω_E ≃ j^! ω_E ≃ ω_B`

of `GeometricOperations.upperStarUnit`, open-immersion purity and the dualizing
composition (part of blueprint `sk-d-local-term`). -/
noncomputable def borelMooreRestrict {E B : Scheme.{u}} {aE : E ⟶ s} (j : B ⟶ E)
    [IsOpenImmersion j] [HasCompactification j] (α : G.borelMooreSections aE) :
    G.borelMooreSections (j ≫ aE) :=
  (G.upperStarUnit j).inv ≫ ((upperStar A j).leftDerivedFunctor).map α ≫
    (G.openPurity j).inv.app _ ≫ (G.dualizingComp j aE).hom

/-- The pushforward of a Borel-Moore section `α : A_T ⟶ ω_T` along a proper `h : T ⟶ T'`
over `s`: the composite

`A_{T'} ⟶ Rh_* A_T ⟶ Rh_* ω_T ≃ Rh_! h^! ω_{T'} ⟶ ω_{T'}`

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

/-- The integral `∫_T α ∈ A` of a Borel-Moore section over a geometric scheme `T` that is
proper over the base: the pushforward of `α` along `a_T`, read in `End (A_s) = A` through
`GeometricOperations.dualizingBase` (part of blueprint `sk-d-integral`). -/
noncomputable def integral {T : Scheme.{u}} (a : T ⟶ s) [HasCompactification a]
    [IsProper a] (α : G.borelMooreSections a) :
    End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))) :=
  G.borelMoorePushforward a (𝟙 s)
      (α ≫ eqToHom (congrArg G.dualizing (Category.comp_id a).symm)) ≫
    G.dualizingBase.hom

end GeometricOperations

end AlgebraicGeometry.ProEtale
