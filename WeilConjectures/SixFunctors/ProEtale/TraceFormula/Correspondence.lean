/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Constructions
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
- `AlgebraicGeometry.ProEtale.Correspondence.ofGraph`: the graph endocorrespondence `(1, g)`
  of an `s`-endomorphism `g : X ⟶ X`, with a coefficient map `Lg^* K ⟶ K`.
- `AlgebraicGeometry.ProEtale.Correspondence.globalOperator`: the global operator
  `T_c(u)` on compactly supported cohomology.
- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMooreSections`: the Borel-Moore
  sections `A_T ⟶ ω_T` of a geometric scheme.
- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMoorePushforward`,
  `AlgebraicGeometry.ProEtale.GeometricOperations.integral`: the pushforward and the
  integral of a Borel-Moore section.

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMoorePushforward_id`: pushing forward
  along the identity gives the section back.

## Implementation notes

`globalOperator`, `borelMoorePushforward`, `integral` and the
coefficient map of `ofEnd` are defined as composites of the adjunctions of the pro-étale
functors and the comparison data of the package
`AlgebraicGeometry.ProEtale.GeometricOperations`:

* `ofEndCoeff` uses `leftDerivedUpperStarId` and `GeometricOperations.upperShriekId`,
  hence the field `lowerShriekId`;
* `globalOperator` uses the fields `properComparison` and `lowerShriekComp`, transported
  along `c₁ ≫ a_X = a_C = c₂ ≫ a_X` by `rightDerivedLowerShriekCongr`;
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
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {s : Scheme.{u}}

/-- The classes supported on a morphism `i : T ⟶ Z` with values in `P ∈ D(Z, A)`: the group
`H_T^0(Z, P) = Hom(Ri_! A_T, P)`. The map `i` is part of the data; it need not be an
immersion, and different maps with the same image give different groups
(blueprint: `def-trf-supported-class`). -/
abbrev SupportedClass {T Z : Scheme.{u}} (i : T ⟶ Z) [HasCompactification i]
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) : Type (u + 1) :=
  (rightDerivedLowerShriek A i).obj (𝟙_ _) ⟶ P

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

/-- The two legs agree on the fixed scheme: `c₂ ∘ i_F = c₁ ∘ i_F`, and this common composite is
the projection `d : Fix(c) ⟶ X` (part of blueprint `prop-trf-fixed-square-cartesian`). -/
@[reassoc]
lemma fixι_snd (c : Correspondence aX aX K K) : c.fixι ≫ c.snd = c.fixι ≫ c.fst :=
  (equalizer.condition c.fst c.snd).symm

/-- The identity `Δ_X ∘ d = c ∘ i_F` of the fixed square, where `d = c₁ ∘ i_F`
(part of blueprint `prop-trf-fixed-square-cartesian`). -/
@[reassoc]
lemma fixι_fst_diagonal (c : Correspondence aX aX K K) :
    (c.fixι ≫ c.fst) ≫ pullback.diagonal aX = c.fixι ≫ c.toProd :=
  c.isPullback_fixι_toProd.w.symm

/-- The inclusion `Fix(c) ⟶ C` of the fixed scheme is the base change of the diagonal of
`aX` along the support map `c : C ⟶ X × X` (`isPullback_fixι_toProd`). The diagonal is a
closed immersion when `aX` is separated, so `Fix(c) ⟶ C` then admits a compactification. -/
instance hasCompactification_fixι [IsSeparated aX] (c : Correspondence aX aX K K) :
    HasCompactification c.fixι :=
  .of_isPullback c.isPullback_fixι_toProd.flip

/-- The inclusion `Fix(c) ⟶ C` of the fixed scheme is a closed immersion when `aX` is
separated, being the base change of the diagonal of `aX` along the support map. -/
instance isClosedImmersion_fixι [IsSeparated aX] (c : Correspondence aX aX K K) :
    IsClosedImmersion c.fixι :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) c.isPullback_fixι_toProd.flip
    (inferInstanceAs (IsClosedImmersion (pullback.diagonal aX)))

/-- The fixed scheme of an endocorrespondence on a geometric scheme with geometric support is
geometric. -/
instance isGeometric_fixStr [IsSeparated aX] (c : Correspondence aX aX K K) [IsGeometric c.str] :
    IsGeometric c.fixStr :=
  inferInstanceAs (IsGeometric (c.fixι ≫ c.str))

/-- The trace-class source `𝓗_c = RHom(Lc₂^* K, Rc₁^! L) ∈ D(C, A)` of a correspondence; for
an endocorrespondence of `(X, K)` it is `RHom(Lc₂^* K, Rc₁^! K)`
(blueprint: `def-trf-trace-class-source`). -/
noncomputable abbrev traceClassSource (c : Correspondence aX aY K L) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology c.supp) A) :=
  (ihom (((upperStar A c.snd).leftDerivedFunctor).obj K)).obj
    ((rightDerivedUpperShriek A c.fst).obj L)

/-- The mate `ũ : A_C ⟶ 𝓗_c` of the coefficient map `u : Lc₂^* K ⟶ Rc₁^! L`: its image under
the tensor-hom adjunction `Hom(A_C, RHom(Lc₂^* K, Rc₁^! L)) ≃ Hom(Lc₂^* K, Rc₁^! L)` of
`CategoryTheory.MonoidalClosed.curryHomEquiv'` (blueprint: `def-trf-trace-class-source`). -/
noncomputable def mate (c : Correspondence aX aY K L) :
    𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology c.supp) A)) ⟶ c.traceClassSource :=
  curry' c.coeff

/-- The tensor-hom adjunction identifies the mate `ũ` with the coefficient map `u`
(blueprint: `def-trf-trace-class-source`). -/
@[simp]
lemma uncurry'_mate (c : Correspondence aX aY K L) : uncurry' c.mate = c.coeff :=
  uncurry'_curry' _

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

end Correspondence

namespace Correspondence

variable [DerivedBraiding A] {X : Scheme.{u}}

/-- The coefficient map of `AlgebraicGeometry.ProEtale.Correspondence.ofEnd`: the
endomorphism `v` read through the comparisons `L(𝟙)^* K ≃ K ≃ 𝟙^! K`, for `K ∈ Dᵇctf(X)`. -/
noncomputable def ofEndCoeff (G : GeometricOperations A s) (aX : X ⟶ s) [IsGeometric aX]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : G.ctf X K) (v : K ⟶ K) :
    ((upperStar A (𝟙 X)).leftDerivedFunctor).obj K ⟶
      (rightDerivedUpperShriek A (𝟙 X)).obj K :=
  (leftDerivedUpperStarId A X).hom.app K ≫ v ≫ (G.upperShriekIdIso X (.id aX) K hK).hom

/-- The coefficient map of the diagonal identity `ofEnd G aX K hK (𝟙 K)` is the comparison
`L(𝟙)^* K ≃ K ≃ 𝟙^! K`. -/
@[simp]
lemma ofEndCoeff_id (G : GeometricOperations A s) (aX : X ⟶ s) [IsGeometric aX]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : G.ctf X K) :
    ofEndCoeff G aX K hK (𝟙 K) =
      (leftDerivedUpperStarId A X).hom.app K ≫ (G.upperShriekIdIso X (.id aX) K hK).hom := by
  simp [ofEndCoeff]

/-- The endocorrespondence on `(X, K)` with support `X`, support map the diagonal `Δ_X`,
identity legs, and coefficient map induced by `v : K ⟶ K`, for `K ∈ Dᵇctf(X)`. For `v = 𝟙 K`
this is the blueprint's *diagonal identity* (part of blueprint `sk-d-corr`). -/
noncomputable def ofEnd (G : GeometricOperations A s) (aX : X ⟶ s) [IsGeometric aX]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : G.ctf X K) (v : K ⟶ K) :
    Correspondence aX aX K K where
  supp := X
  str := aX
  fst := 𝟙 X
  snd := 𝟙 X
  fst_comp := Category.id_comp aX
  snd_comp := Category.id_comp aX
  coeff := ofEndCoeff G aX K hK v

variable (G : GeometricOperations A s) (aX : X ⟶ s) [IsGeometric aX]
  (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : G.ctf X K) (v : K ⟶ K)

/-- The support map of `ofEnd G aX K hK v` is the diagonal of `aX`. -/
@[simp]
lemma ofEnd_toProd : (ofEnd G aX K hK v).toProd = pullback.diagonal aX :=
  rfl

/-- The swapped support map of `ofEnd G aX K hK v` is the diagonal of `aX`. -/
@[simp]
lemma ofEnd_toProdSwap : (ofEnd G aX K hK v).toProdSwap = pullback.diagonal aX :=
  rfl

/-- The support map of `ofEnd G aX K hK v` is the diagonal of `aX`, a closed immersion as `aX`
is separated, so it admits a compactification. -/
instance hasCompactification_toProd_ofEnd :
    HasCompactification (ofEnd G aX K hK v).toProd := by
  rw [ofEnd_toProd]
  infer_instance

/-- The swapped support map of `ofEnd G aX K hK v` is the diagonal of `aX`, a closed immersion
as `aX` is separated, so it admits a compactification. -/
instance hasCompactification_toProdSwap_ofEnd :
    HasCompactification (ofEnd G aX K hK v).toProdSwap := by
  rw [ofEnd_toProdSwap]
  infer_instance

instance isIso_fixι_ofEnd : IsIso (ofEnd G aX K hK v).fixι :=
  inferInstanceAs (IsIso (equalizer.ι (𝟙 X) (𝟙 X)))

/-- The structure morphism of `ofEnd G aX K hK v` is `aX`, so it admits a compactification
when `aX` does. -/
instance hasCompactification_str_ofEnd [HasCompactification aX] :
    HasCompactification (ofEnd G aX K hK v).str :=
  inferInstanceAs (HasCompactification aX)

/-- The structure morphism of `ofEnd G aX K hK v` is `aX`, which is geometric. -/
instance isGeometric_str_ofEnd : IsGeometric (ofEnd G aX K hK v).str :=
  inferInstanceAs (IsGeometric aX)

instance isProper_fixStr_ofEnd [IsProper aX] : IsProper (ofEnd G aX K hK v).fixStr :=
  inferInstanceAs (IsProper ((ofEnd G aX K hK v).fixι ≫ aX))

/-- Paired with the diagonal endocorrespondence `ofEnd G aX K hK v` (support `X`, swapped
support map `Δ_X`), an endocorrespondence `c` has intersection support
`E(C, X) = C ×_{X × X, c, Δ_X} X`, which is its fixed scheme `Fix(c)`; for `v = 𝟙 K` this is
the pairing of `c` with the identity correspondence
(blueprint: `def-trf-correspondence-between-pairs`). -/
noncomputable def intersectionOfEndIso (c : Correspondence aX aX K K) :
    c.intersection (ofEnd G aX K hK v) ≅ c.fix :=
  c.isPullback_fixι_toProd.isoPullback.symm

/-- Under `E(C, X) ≅ Fix(c)`, the inclusion of the fixed scheme into `C` is the first
projection of `E(C, X)`. -/
@[reassoc (attr := simp)]
lemma intersectionOfEndIso_hom_fixι (c : Correspondence aX aX K K) :
    (intersectionOfEndIso G aX K hK v c).hom ≫ c.fixι =
      pullback.fst c.toProd (ofEnd G aX K hK v).toProdSwap :=
  c.isPullback_fixι_toProd.isoPullback_inv_fst

/-- Under `E(C, X) ≅ Fix(c)`, the projection `d : Fix(c) ⟶ X` is the second projection of
`E(C, X)`. -/
@[reassoc (attr := simp)]
lemma intersectionOfEndIso_hom_fixι_fst (c : Correspondence aX aX K K) :
    (intersectionOfEndIso G aX K hK v c).hom ≫ c.fixι ≫ c.fst =
      pullback.snd c.toProd (ofEnd G aX K hK v).toProdSwap :=
  c.isPullback_fixι_toProd.isoPullback_inv_snd

/-- Under `E(C, X) ≅ Fix(c)`, the structure morphisms of the two supports agree. -/
@[reassoc (attr := simp)]
lemma intersectionOfEndIso_hom_fixStr (c : Correspondence aX aX K K) :
    (intersectionOfEndIso G aX K hK v c).hom ≫ c.fixStr =
      c.intersectionStr (ofEnd G aX K hK v) := by
  rw [fixStr, intersectionOfEndIso_hom_fixι_assoc, intersectionStr]

/-- The projection `d = c₁ ∘ i_F : Fix(c) ⟶ X` of the fixed scheme admits a compactification:
`i_F` is a closed immersion and `c₁` is a compactifiable morphism of geometric schemes. -/
instance hasCompactification_fixι_fst (c : Correspondence aX aX K K) [IsGeometric c.str] :
    HasCompactification (c.fixι ≫ c.fst) :=
  have : QuasiCompact c.fst := (IsGeometricHom.mk c.fst_comp).quasiCompact
  .of_isClosedImmersion c.fixι c.fst

/-- The composition law for the exceptional inverse image in the fixed square

```
  Fix(c) ──i_F──▶ C
     │            │
   d │            │ c = (c₁, c₂)
     ▼            ▼
     X ───Δ_X───▶ X ×_s X
```

(Cartesian by `isPullback_fixι_toProd`): as `d = c₁ ∘ i_F`, it gives `Rd^! ≃ Ri_F^! Rc₁^!` on
`Dᵇctf`, the adjoint form of `R(c₁ i_F)_! ≃ Rc₁_! Ri_{F!}`
(blueprint: `prop-trf-fixed-square-cartesian`). -/
noncomputable def fixUpperShriekIso (c : Correspondence aX aX K K) [IsGeometric c.str] :
    G.upperShriekCtf (c.fixι ≫ c.fst)
        ((IsGeometricHom.mk (aX := c.fixStr) (aY := c.str) rfl).comp (.mk c.fst_comp)) ≅
      G.upperShriekCtf c.fst (.mk c.fst_comp) ⋙
        G.upperShriekCtf c.fixι (.mk (aX := c.fixStr) (aY := c.str) rfl) :=
  G.upperShriekComp c.fixι c.fst _ _ _

/-- The graph endocorrespondence `(1, g)` on `(X, K)` of an endomorphism `g : X ⟶ X` over
`s`, for `K ∈ Dᵇctf(X)`: support `X`, exceptional leg `𝟙 X`, ordinary-pullback leg `g`, and
coefficient map `v : Lg^* K ⟶ K` read through `K ≃ 𝟙^! K`,

```
            X
          ↙   ↘
       𝟙         g              v : Lg^* K ⟶ K ≃ 𝟙^! K
      ↙           ↘
     X             X
```

For `g = 𝟙 X` this is `ofEnd` up to the identification `L(𝟙)^* K ≃ K`
(part of blueprint `sk-d-corr`). -/
noncomputable def ofGraph (g : X ⟶ X) (hg : g ≫ aX = aX)
    (v : ((upperStar A g).leftDerivedFunctor).obj K ⟶ K) :
    Correspondence aX aX K K where
  supp := X
  str := aX
  fst := 𝟙 X
  snd := g
  fst_comp := Category.id_comp aX
  snd_comp := hg
  coeff := v ≫ (G.upperShriekIdIso X (.id aX) K hK).hom

variable (g : X ⟶ X) (hg : g ≫ aX = aX) (w : ((upperStar A g).leftDerivedFunctor).obj K ⟶ K)

/-- The structure morphism of `ofGraph G aX K hK g hg w` is `aX`, so it admits a
compactification when `aX` does. -/
instance hasCompactification_str_ofGraph [HasCompactification aX] :
    HasCompactification (ofGraph G aX K hK g hg w).str :=
  inferInstanceAs (HasCompactification aX)

/-- The structure morphism of `ofGraph G aX K hK g hg w` is `aX`, which is geometric. -/
instance isGeometric_str_ofGraph : IsGeometric (ofGraph G aX K hK g hg w).str :=
  inferInstanceAs (IsGeometric aX)

/-- The support map `(𝟙, g) : X ⟶ X ×_s X` of `ofGraph G aX K hK g hg w` is the graph
`X ⟶ X ×_s X` of `g`, a section of the first projection, followed by the identification
of `X ×_{g ≫ a_X, s, a_X} X` with `X ×_s X` along `g ≫ a_X = a_X`. -/
lemma ofGraph_toProd_eq :
    (ofGraph G aX K hK g hg w).toProd =
      pullback.lift (𝟙 X) g (Category.id_comp (g ≫ aX)) ≫ (pullback.congrHom hg rfl).hom := by
  apply pullback.hom_ext <;> simp [toProd, ofGraph]

/-- The support map `(𝟙, g) : X ⟶ X ×_s X` of `ofGraph G aX K hK g hg w` is a section of the
first projection, hence a closed immersion as `aX` is separated. -/
instance isClosedImmersion_toProd_ofGraph :
    IsClosedImmersion (ofGraph G aX K hK g hg w).toProd := by
  rw [ofGraph_toProd_eq]
  -- instance search does not find this factor inside the composite, only when it is stated
  -- on its own
  have : IsClosedImmersion (pullback.lift (𝟙 X) g (Category.id_comp (g ≫ aX))) :=
    inferInstance
  infer_instance

end Correspondence

namespace Correspondence

variable [DerivedBraiding A] {X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}

/-- `c₂ ≫ a_X = a_C` admits a compactification when `a_C` does. -/
instance hasCompactification_snd_comp (c : Correspondence aX aY K L)
    [HasCompactification c.str] : HasCompactification (c.snd ≫ aX) :=
  c.snd_comp ▸ inferInstance

/-- `c₁ ≫ a_Y = a_C` admits a compactification when `a_C` does. -/
instance hasCompactification_fst_comp (c : Correspondence aX aY K L)
    [HasCompactification c.str] : HasCompactification (c.fst ≫ aY) :=
  c.fst_comp ▸ inferInstance

/-- The first half of the global operator, `RΓ_c(X, K) ⟶ RΓ_c(C, c₂^* K)`, for `K ∈ Dᵇctf(X)`
on geometric schemes: the composite

```
  Ra_{X!} K ──η──▶ Ra_{X!} Rc₂_* c₂^* K ≅ Ra_{X!} Rc₂_! c₂^* K ≅ Ra_{C!} c₂^* K
```

of the unit of `c₂^* ⊣ Rc₂_*`, the proper identification `Rc₂_* = Rc₂_!` and the
composition `Ra_{X!} Rc₂_! ≃ R(c₂ ≫ a_X)_! = Ra_{C!}` (part of blueprint `sk-d-operator`). -/
noncomputable def globalOperatorUnit (G : GeometricOperations A s)
    (c : Correspondence aX aY K L) (hK : G.ctf X K) [IsGeometric aX] [IsGeometric c.str]
    [HasCompactification aX] [IsProper c.snd] [HasCompactification c.str] :
    (rightDerivedLowerShriek A aX).obj K ⟶
      (rightDerivedLowerShriek A c.str).obj (((upperStar A c.snd).leftDerivedFunctor).obj K) :=
  (rightDerivedLowerShriek A aX).map
      ((derivedUpperStarLowerStarAdjunction A c.snd).unit.app K) ≫
    (rightDerivedLowerShriek A aX).map
      ((G.properComparison c.snd (.mk c.snd_comp)).inv.app
        ⟨_, G.ctf_upperStar c.snd (.mk c.snd_comp) hK⟩).hom ≫
    ((G.lowerShriekComp c.snd aX (.mk c.snd_comp) (.of_isGeometric aX)
      (.mk (aX := c.str) (aY := 𝟙 s) (by rw [Category.comp_id, c.snd_comp]))).hom.app
        ⟨_, G.ctf_upperStar c.snd (.mk c.snd_comp) hK⟩).hom ≫
    (rightDerivedLowerShriekCongr A c.snd_comp).hom.app _

/-- The second half of the global operator, `RΓ_c(C, c₁^! L) ⟶ RΓ_c(Y, L)`, for
`L ∈ Dᵇctf(Y)` on geometric schemes: the composite

```
  Ra_{C!} c₁^! L ≅ Ra_{Y!} Rc₁_! c₁^! L ──ε──▶ Ra_{Y!} L
```

of the composition `Ra_{C!} = R(c₁ ≫ a_Y)_! ≃ Ra_{Y!} Rc₁_!` and the counit of
`Rc₁_! ⊣ c₁^!` (part of blueprint `sk-d-operator`). -/
noncomputable def globalOperatorCounit (G : GeometricOperations A s)
    (c : Correspondence aX aY K L) (hL : G.ctf Y L) [IsGeometric aY] [IsGeometric c.str]
    [HasCompactification aY] [HasCompactification c.str] :
    (rightDerivedLowerShriek A c.str).obj ((rightDerivedUpperShriek A c.fst).obj L) ⟶
      (rightDerivedLowerShriek A aY).obj L :=
  (rightDerivedLowerShriekCongr A c.fst_comp.symm).hom.app _ ≫
    ((G.lowerShriekComp c.fst aY (.mk c.fst_comp) (.of_isGeometric aY)
      (.mk (aX := c.str) (aY := 𝟙 s) (by rw [Category.comp_id, c.fst_comp]))).inv.app
        ⟨_, G.ctf_upperShriek c.fst (.mk c.fst_comp) hL⟩).hom ≫
    (rightDerivedLowerShriek A aY).map (G.exceptionalCounit c.fst (.mk c.fst_comp) L hL)

/-- The global operator of an endocorrespondence `(C, c, u)` on `(X, K)` with `K ∈ Dᵇctf(X)`,
on a geometric scheme `X`, whose ordinary leg `c₂` is proper: the composite
```
  RΓ_c(X, K) ──η──▶ RΓ_c(X, Rc₂_* c₂^* K) ≅ RΓ_c(C, c₂^* K) ──u──▶ RΓ_c(C, c₁^! K)
             ≅ RΓ_c(X, Rc₁_! c₁^! K) ──ε──▶ RΓ_c(X, K)
```
of the unit of `c₂^* ⊣ Rc₂_*`, the proper identification `Rc₂_* = Rc₂_!` and the counit of
`Rc₁_! ⊣ c₁^!`, acting on compactly supported cohomology `RΓ_c(X, K) = Ra_{X!} K`
(blueprint: `sk-d-operator`). -/
noncomputable def globalOperator (G : GeometricOperations A s)
    (c : Correspondence aX aX K K) (hK : G.ctf X K) [IsGeometric aX] [IsGeometric c.str]
    [HasCompactification aX] [IsProper c.snd] [HasCompactification c.str] :
    (rightDerivedLowerShriek A aX).obj K ⟶ (rightDerivedLowerShriek A aX).obj K :=
  globalOperatorUnit G c hK ≫ (rightDerivedLowerShriek A c.str).map c.coeff ≫
    globalOperatorCounit G c hK

end Correspondence

namespace GeometricOperations

variable [DerivedBraiding A] (G : GeometricOperations A s)

/-- The *Borel-Moore sections* `A_T ⟶ ω_T` of a geometric scheme `a : T ⟶ s`
(part of blueprint `sk-d-integral`). -/
abbrev borelMooreSections {T : Scheme.{u}} (a : T ⟶ s) :=
  𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) A)) ⟶ G.dualizing a

/-- The pushforward of a Borel-Moore section `α : A_T ⟶ ω_T` along a proper `h : T ⟶ T'`
of geometric schemes over `s`: the composite
```
  A_{T'} ──η──▶ Rh_* Lh^* A_{T'} ≅ Rh_* A_T ──α──▶ Rh_* ω_T ≅ Rh_! ω_T ≅ Rh_! h^! ω_{T'}
         ──ε──▶ ω_{T'}
```
of the unit of `h^* ⊣ Rh_*`, the proper identification `Rh_* = Rh_!`, the dualizing
composition `h^! ω_{T'} ≃ ω_T` and the counit of `Rh_! ⊣ h^!`
(blueprint: `sk-d-integral`). -/
noncomputable def borelMoorePushforward {T T' : Scheme.{u}} (h : T ⟶ T') (a : T' ⟶ s)
    [IsGeometric a] [IsGeometric (h ≫ a)] [HasCompactification h] [IsProper h]
    (α : G.borelMooreSections (h ≫ a)) :
    G.borelMooreSections a :=
  (derivedUpperStarLowerStarAdjunction A h).unit.app (𝟙_ _) ≫
    ((lowerStar A h).rightDerivedFunctor).map ((G.upperStarUnit h).hom ≫ α) ≫
    ((G.properComparison h (.mk (aY := a) rfl)).inv.app
      ⟨G.dualizing (h ≫ a), G.ctf_dualizing (h ≫ a)⟩).hom ≫
    (rightDerivedLowerShriek A h).map (G.dualizingComp h a).inv ≫
    G.exceptionalCounit h (.mk (aY := a) rfl) (G.dualizing a) (G.ctf_dualizing a)

/-- Pushing a Borel-Moore section forward along the identity gives the section back, up to
the transport `ω_{𝟙 ≫ a} = ω_a`. -/
lemma borelMoorePushforward_id {T : Scheme.{u}} (a : T ⟶ s) [IsGeometric a]
    (α : G.borelMooreSections (𝟙 T ≫ a)) :
    G.borelMoorePushforward (𝟙 T) a α = α ≫ (G.dualizingCongr (Category.id_comp a)).hom := by
  set c := (conjugateEquiv (derivedUpperStarLowerStarAdjunction A (𝟙 T)) Adjunction.id)
    (leftDerivedUpperStarId A T).inv
  have hc := c.naturality
  have h₁ := unit_conjugateEquiv (derivedUpperStarLowerStarAdjunction A (𝟙 T)) Adjunction.id
    (leftDerivedUpperStarId A T).inv (𝟙_ _)
  have h₂ := congrArg (·.hom) (conjugateEquiv_counit Adjunction.id
    (G.exceptionalAdjunction (𝟙 T) (.id a)) (G.lowerShriekId T (.id a)).hom
    ⟨G.dualizing a, G.ctf_dualizing a⟩)
  have h₄ := congrArg (·.hom)
    ((G.lowerShriekId T (.id a)).inv.naturality (X := ⟨G.dualizing (𝟙 T ≫ a), G.ctf_dualizing _⟩)
      (Y := ⟨G.dualizing a, G.ctf_dualizing a⟩)
      (ObjectProperty.homMk (eqToHom (congrArg G.dualizing (Category.id_comp a)))))
  dsimp at hc h₁ h₂ h₄
  have h₂' : (rightDerivedLowerShriek A (𝟙 T)).map
      ((conjugateEquiv Adjunction.id (G.exceptionalAdjunction (𝟙 T) (.id a))
        (G.lowerShriekId T (.id a)).hom).app ⟨G.dualizing a, G.ctf_dualizing a⟩).hom ≫
      ((G.exceptionalAdjunction (𝟙 T) (.id a)).counit.app ⟨G.dualizing a, G.ctf_dualizing a⟩).hom =
      ((G.lowerShriekId T (.id a)).hom.app ⟨G.dualizing a, G.ctf_dualizing a⟩).hom := by
    rw [← Category.comp_id ((G.lowerShriekId T (.id a)).hom.app _).hom]
    exact h₂
  have h₄' : eqToHom (congrArg G.dualizing (Category.id_comp a)) ≫
      ((G.lowerShriekId T (.id a)).inv.app ⟨G.dualizing a, G.ctf_dualizing a⟩).hom =
      ((G.lowerShriekId T (.id a)).inv.app ⟨G.dualizing (𝟙 T ≫ a), G.ctf_dualizing _⟩).hom ≫
        (rightDerivedLowerShriek A (𝟙 T)).map
          (eqToHom (congrArg G.dualizing (Category.id_comp a))) :=
    h₄
  simp only [borelMoorePushforward, G.properComparison_id_inv_app_hom, G.dualizingComp_id,
    upperStarUnit_hom_id, Iso.trans_inv, eqToIso.inv, Functor.map_comp, Category.assoc,
    dualizingCongr,
    GeometricCoefficients.exceptionalCounit,
    conjugateIsoEquiv_apply_inv, Functor.mapIso_inv, Iso.symm_inv,
    conjugateIsoEquiv_apply_hom, ObjectProperty.ι_map, Iso.app_inv]
  rw [reassoc_of% (hc α), reassoc_of% (hc ((leftDerivedUpperStarId A T).hom.app (𝟙_ _))),
    reassoc_of% h₁]
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.id_comp,
    Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% h₄', h₂',
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
  simp

/-- The integral `∫_T α ∈ A` of a Borel-Moore section over a geometric scheme `T` that is
proper over the base: the pushforward of `α` along `a_T`, read in `End (A_s) = A` through
`GeometricOperations.dualizingBase` (part of blueprint `sk-d-integral`). -/
noncomputable def integral {T : Scheme.{u}} (a : T ⟶ s) [IsGeometric a] [HasCompactification a]
    [IsProper a] (α : G.borelMooreSections a) :
    End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))) :=
  G.borelMoorePushforward a (𝟙 s)
      (α ≫ (G.dualizingCongr (Category.comp_id a).symm).hom) ≫
    G.dualizingBase.hom

end GeometricOperations

end AlgebraicGeometry.ProEtale
