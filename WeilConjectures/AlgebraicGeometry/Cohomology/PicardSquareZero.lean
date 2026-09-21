/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Pullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.Units
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Line bundles on a square-zero thickening

Let `W` be a scheme and let `I` be a quasi-coherent ideal sheaf on `W` with `I² = 0`, so that
the closed immersion `i : W₀ = V(I) ⟶ W` it cuts out is a *square-zero thickening*. The
truncated exponential sequence

`1 ⟶ I ⟶ 𝒪_W^× ⟶ i_* 𝒪_{W₀}^× ⟶ 1`,

whose first map is `a ↦ 1 + a` — a homomorphism precisely because `I² = 0` — gives on
cohomology the five-term exact sequence

`Γ(W, 𝒪^×) ⟶ Γ(W₀, 𝒪^×) ⟶ H¹(W, I) ⟶ Pic W ⟶ Pic W₀`,

and this sequence is natural in the thickening:

```
Γ(W, 𝒪)ˣ ──▶ Γ(W₀, 𝒪)ˣ ──δ──▶ H¹(W, I) ──▶ Pic W ──▶ Pic W₀
    │             │               │            │          │
    ▼             ▼               ▼            ▼          ▼
Γ(W', 𝒪)ˣ ─▶ Γ(W₀', 𝒪)ˣ ─δ'─▶ H¹(W', I') ─▶ Pic W' ─▶ Pic W₀'
```

That is the content of this file. It is what turns a vanishing statement about `H¹(W, I)`
into the statement that a line bundle on `W` is determined by its restriction to `W₀`, which
is how the theorem of the cube deforms a trivialisation along an infinitesimal neighbourhood.

Everything is stated for `I` regarded as a sheaf of `𝒪_W`-modules
(`AlgebraicGeometry.Scheme.IdealSheafData.toModules`), so the third term is `H¹(W, I)` rather
than the blueprint's `H¹(W₀, I)`; the two agree, because the pushforward along a closed
immersion is exact and preserves cohomology, and `H¹(W, I)` is the one of the two that can be
written down with what is available.

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.unitsToH1` — the connecting homomorphism
  `Γ(W₀, 𝒪^×) ⟶ H¹(W, I)`.
- `AlgebraicGeometry.Scheme.IdealSheafData.h1ToPic` — the map `H¹(W, I) ⟶ Pic W`.
- `AlgebraicGeometry.Scheme.IdealSheafData.hMap` — the map `H^k(W, I) ⟶ H^k(W', I')` induced
  by a morphism `g : W' ⟶ W` and a comparison morphism `g^* I ⟶ I'`, and
  `AlgebraicGeometry.Scheme.IdealSheafData.hMapOfComapLe`, its value at the canonical
  comparison morphism.
- `AlgebraicGeometry.Scheme.IdealSheafData.h1Map` — the vertical map
  `H¹(W, I) ⟶ H¹(W', I')` of the naturality ladder, the degree-one case of `hMap` written
  multiplicatively, and `AlgebraicGeometry.Scheme.IdealSheafData.h1MapOfComapLe`, its value at
  the canonical comparison morphism `g^* I ⟶ I'`.

## Main statements

The exactness statements and the two squares of the ladder that involve the connecting maps
are part of `prop:cube-picard-square-zero` of the blueprint
(`27_theorem_of_the_cube.tex`) and are `sorry` by design; see the implementation notes.

- `AlgebraicGeometry.Scheme.IdealSheafData.range_unitsMap_subschemeι_eq_ker`,
  `range_unitsToH1_eq_ker` and `range_h1ToPic_eq_ker` — exactness of the five-term sequence at
  its three middle terms `Γ(W₀, 𝒪^×)`, `H¹(W, I)` and `Pic W`. This is part (1).
- `AlgebraicGeometry.Scheme.IdealSheafData.unitsToH1_naturality` and `h1ToPic_naturality` —
  the two squares of the naturality ladder that involve the connecting maps. This is part (2).

Proved rather than assumed are the two squares of the ladder that do not involve the
connecting maps, `AlgebraicGeometry.Scheme.IdealSheafData.unitsMap_subschemeι_naturality` and
`pic_map_subschemeι_naturality`, and the consequence that the chapter actually consumes,
`AlgebraicGeometry.Scheme.IdealSheafData.injective_pic_map_subschemeι_of_subsingleton`: if
`H¹(W, I)` vanishes, a line bundle on `W` trivial on `W₀` is trivial. Also proved is
`AlgebraicGeometry.Scheme.IdealSheafData.injective_h1ToPic_of_surjective_unitsMap`: if every
unit on `W₀` extends to `W`, then a deformation class is determined by the line bundle it
glues.

## Implementation notes

* The two connecting maps `AlgebraicGeometry.Scheme.IdealSheafData.unitsToH1` and `h1ToPic`,
  the three exactness statements and the two naturality squares involving them are `sorry`
  **by design**: they are the open obligation attached to `prop:cube-picard-square-zero`.
  Following the convention of `WeilConjectures.AlgebraicGeometry.ChowLemma`, the maps are
  definitions and their properties separate statements, so that a consumer uses them directly
  rather than destructing an existential.
* The six are **coupled**: a sorried definition has no defining property, so the five
  statements about `unitsToH1` and `h1ToPic` cannot be proved before those two definitions are
  replaced by honest ones, and whoever does that has to discharge all six at once.
* What is missing for an honest construction is, in order: the truncated exponential sequence
  `1 ⟶ I ⟶ 𝒪_W^× ⟶ i_* 𝒪_{W₀}^× ⟶ 1` as a short exact sequence of abelian sheaves on `W`
  (the one substantial point being that `𝒪_W^× ⟶ i_* 𝒪_{W₀}^×` is locally surjective, because
  a section of `𝒪_W` lifting a unit is a unit when the ideal is nil); the long exact sequence
  of `WeilConjectures.AlgebraicGeometry.Cohomology.LongExactSequence` generalised from
  `ShortComplex W.Modules` to a short exact sequence of abelian sheaves (its proofs use the
  module structure nowhere); and a natural isomorphism `Pic W ≃* Multiplicative (H¹(W, 𝒪_W^×))`
  — the sheaf of units and its cohomology are already available, in
  `WeilConjectures.AlgebraicGeometry.Cohomology.Units`. With those three, `unitsToH1` and
  `h1ToPic` become ordinary definitions and the five statements ordinary consequences of the
  long exact sequence.
* The two left-hand terms are spelled as groups of units of rings of global sections,
  `Γ(W, 𝒪)ˣ` and `Γ(W₀, 𝒪)ˣ`, and the map between them as
  `AlgebraicGeometry.Scheme.Hom.unitsMap`. That is the same group as `H⁰` of the sheaf of
  units `AlgebraicGeometry.Scheme.unitsSheaf`, by
  `AlgebraicGeometry.Scheme.unitsH.mulEquiv₀`, and it is the form a consumer can use without
  going through the additive shell of the sheaf.
* The sequence is written multiplicatively throughout, as the blueprint does: the two ends are
  groups of units and `Pic` is a multiplicative group, so the middle term appears as
  `Multiplicative (H¹(W, I))`. Exactness is `MonoidHom.range _ = MonoidHom.ker _`.
* Naturality is stated for a morphism `g : W' ⟶ W` with `I.comap g ≤ I'` — `g` pulls `I` *into*
  `I'`, which is weaker than the blueprint's *onto* and therefore gives a stronger statement —
  together with the comparison morphism `φ : g^* I ⟶ I'` of `𝒪_{W'}`-modules. The hypothesis
  `hφ` says that `φ` is compatible with the two inclusions into the structure sheaves; it is
  the precise form of "the right vertical map pulls `I` back onto `I'`", and it determines `φ`
  uniquely, since `I' ⟶ 𝒪_{W'}` is a monomorphism. Such a `φ` is constructed from `hg` by
  `AlgebraicGeometry.Scheme.IdealSheafData.comapModulesMap`, and `comapModulesMap_toModulesι`
  is the hypothesis `hφ` for it.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {W W' : Scheme.{u}}

/-! ### The five-term sequence of a square-zero thickening -/

variable (I : W.IdealSheafData)

/-- The connecting homomorphism `Γ(W₀, 𝒪^×) ⟶ H¹(W, I)` of the five-term sequence of a
square-zero thickening: the boundary map of the truncated exponential sequence
`1 ⟶ I ⟶ 𝒪_W^× ⟶ i_* 𝒪_{W₀}^× ⟶ 1`.

This is `sorry` by design; see the implementation notes of this file. -/
noncomputable def unitsToH1 (hI : I ^ 2 = 0) :
    Γ(I.subscheme, ⊤)ˣ →* Multiplicative (I.toModules.H 1) :=
  sorry

/-- The map `H¹(W, I) ⟶ Pic W` of the five-term sequence of a square-zero thickening: a
cohomology class of the ideal is the class of the line bundle it glues.

This is `sorry` by design; see the implementation notes of this file. -/
noncomputable def h1ToPic (hI : I ^ 2 = 0) :
    Multiplicative (I.toModules.H 1) →* W.Pic :=
  sorry

/-- **Exactness at `Γ(W₀, 𝒪^×)`** of the five-term sequence of a square-zero thickening: a unit
on `W₀` extends to `W` exactly when its image in `H¹(W, I)` vanishes. -/
theorem range_unitsMap_subschemeι_eq_ker (hI : I ^ 2 = 0) :
    (Hom.unitsMap I.subschemeι).range = (I.unitsToH1 hI).ker :=
  sorry

/-- **Exactness at `H¹(W, I)`** of the five-term sequence of a square-zero thickening. -/
theorem range_unitsToH1_eq_ker (hI : I ^ 2 = 0) :
    (I.unitsToH1 hI).range = (I.h1ToPic hI).ker :=
  sorry

/-- **Exactness at `Pic W`** of the five-term sequence of a square-zero thickening: a line bundle
on `W` is trivial on the closed subscheme `W₀` exactly when it comes from a class in
`H¹(W, I)`. -/
theorem range_h1ToPic_eq_ker (hI : I ^ 2 = 0) :
    (I.h1ToPic hI).range = (Pic.map I.subschemeι).ker :=
  sorry

/-- **A line bundle on a square-zero thickening with vanishing `H¹` of the ideal is determined
by its restriction.** This is the consequence of the five-term exact sequence that the theorem
of the cube consumes. -/
theorem injective_pic_map_subschemeι_of_subsingleton (hI : I ^ 2 = 0)
    [Subsingleton (I.toModules.H 1)] : Function.Injective (Pic.map I.subschemeι) := by
  have : Subsingleton (Multiplicative (I.toModules.H 1)) :=
    inferInstanceAs (Subsingleton (I.toModules.H 1))
  rw [← MonoidHom.ker_eq_bot_iff, ← range_h1ToPic_eq_ker I hI, Subgroup.eq_bot_iff_forall]
  rintro x ⟨y, rfl⟩
  rw [Subsingleton.elim y 1, map_one]

/-- **If every unit on the closed subscheme extends to the thickening, a deformation class is
determined by the line bundle it glues**: the map `H¹(W, I) ⟶ Pic W` of the five-term
sequence of a square-zero thickening is injective as soon as
`Γ(W, 𝒪)ˣ ⟶ Γ(W₀, 𝒪)ˣ` is surjective. -/
lemma injective_h1ToPic_of_surjective_unitsMap (hI : I ^ 2 = 0)
    (hsurj : Function.Surjective (Hom.unitsMap I.subschemeι)) :
    Function.Injective (I.h1ToPic hI) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← range_unitsToH1_eq_ker I hI, Subgroup.eq_bot_iff_forall]
  rintro x ⟨y, rfl⟩
  exact (range_unitsMap_subschemeι_eq_ker I hI).le (MonoidHom.mem_range.mpr (hsurj y))

/-! ### Naturality in the thickening -/

variable (I' : W'.IdealSheafData) (g : W' ⟶ W)

/-- The first square of the naturality ladder: restriction of global units to the closed
subscheme commutes with pullback along `g`.

```
  Γ(W, 𝒪)ˣ ──unitsMap I.subschemeι──▶ Γ(W₀, 𝒪)ˣ
     │                                     │
     │ unitsMap g                          │ unitsMap (subschemeMapOfComapLe …)
     ▼                                     ▼
  Γ(W', 𝒪)ˣ ─unitsMap I'.subschemeι─▶ Γ(W₀', 𝒪)ˣ
```
-/
lemma unitsMap_subschemeι_naturality (hg : I.comap g ≤ I') :
    (Hom.unitsMap (subschemeMapOfComapLe I I' g hg)).comp (Hom.unitsMap I.subschemeι) =
      (Hom.unitsMap I'.subschemeι).comp (Hom.unitsMap g) := by
  rw [← Hom.unitsMap_comp, ← Hom.unitsMap_comp, subschemeMapOfComapLe_subschemeι]

/-- The last square of the naturality ladder: restriction of line bundles to the closed
subscheme commutes with pullback along `g`.

```
  Pic W ──Pic.map I.subschemeι──▶ Pic W₀
    │                               │
    │ Pic.map g                     │ Pic.map (subschemeMapOfComapLe …)
    ▼                               ▼
  Pic W' ─Pic.map I'.subschemeι─▶ Pic W₀'
```
-/
lemma pic_map_subschemeι_naturality (hg : I.comap g ≤ I') :
    (Pic.map (subschemeMapOfComapLe I I' g hg)).comp (Pic.map I.subschemeι) =
      (Pic.map I'.subschemeι).comp (Pic.map g) := by
  rw [← Pic.map_comp, ← Pic.map_comp, subschemeMapOfComapLe_subschemeι]

variable (φ : (Modules.pullback g).obj I.toModules ⟶ I'.toModules)

/-- **The map `H^k(W, I) ⟶ H^k(W', I')` induced by `g` and a comparison morphism
`φ : g^* I ⟶ I'`**: the pullback map on cohomology along `g`, followed by `φ`. -/
noncomputable def hMap (k : ℕ) : I.toModules.H k →+ I'.toModules.H k :=
  (Modules.H.mapAddHom φ k).comp (Modules.H.pullbackAddHom g I.toModules k)

@[simp]
lemma hMap_apply (k : ℕ) (x : I.toModules.H k) :
    hMap I I' g φ k x = Modules.H.map φ k (Modules.H.pullbackAddHom g I.toModules k x) :=
  rfl

/-- **The map `H^k(W, I) ⟶ H^k(W', I')` taken at the canonical comparison morphism**
`AlgebraicGeometry.Scheme.IdealSheafData.comapModulesMap`. In degree one this is the map the
two naturality squares hold for without any further hypothesis; see
`unitsToH1_naturality_comapModulesMap` and `h1ToPic_naturality_comapModulesMap`. -/
noncomputable def hMapOfComapLe (hg : I.comap g ≤ I') (k : ℕ) :
    I.toModules.H k →+ I'.toModules.H k :=
  hMap I I' g (comapModulesMap I I' g hg) k

@[simp]
lemma hMapOfComapLe_apply (hg : I.comap g ≤ I') (k : ℕ) (x : I.toModules.H k) :
    hMapOfComapLe I I' g hg k x =
      Modules.H.map (comapModulesMap I I' g hg) k
        (Modules.H.pullbackAddHom g I.toModules k x) :=
  rfl

/-- The vertical map `H¹(W, I) ⟶ H¹(W', I')` of the naturality ladder: the degree-one case of
`AlgebraicGeometry.Scheme.IdealSheafData.hMap`, written multiplicatively. -/
noncomputable def h1Map :
    Multiplicative (I.toModules.H 1) →* Multiplicative (I'.toModules.H 1) :=
  AddMonoidHom.toMultiplicative (hMap I I' g φ 1)

@[simp]
lemma toAdd_h1Map (x : Multiplicative (I.toModules.H 1)) :
    Multiplicative.toAdd (h1Map I I' g φ x) = hMap I I' g φ 1 (Multiplicative.toAdd x) :=
  rfl

/-- The vertical map `H¹(W, I) ⟶ H¹(W', I')` of the naturality ladder, taken at the canonical
comparison morphism `AlgebraicGeometry.Scheme.IdealSheafData.comapModulesMap`. This is the map
the two naturality squares hold for without any further hypothesis; see
`unitsToH1_naturality_comapModulesMap` and `h1ToPic_naturality_comapModulesMap`. -/
noncomputable def h1MapOfComapLe (hg : I.comap g ≤ I') :
    Multiplicative (I.toModules.H 1) →* Multiplicative (I'.toModules.H 1) :=
  h1Map I I' g (comapModulesMap I I' g hg)

@[simp]
lemma toAdd_h1MapOfComapLe (hg : I.comap g ≤ I')
    (x : Multiplicative (I.toModules.H 1)) :
    Multiplicative.toAdd (h1MapOfComapLe I I' g hg x) =
      hMapOfComapLe I I' g hg 1 (Multiplicative.toAdd x) :=
  rfl

variable (hI : I ^ 2 = 0) (hI' : I' ^ 2 = 0) (hg : I.comap g ≤ I')
  (hφ : (Modules.pullback g).map I.toModulesι ≫ (Modules.pullbackUnitIso g).hom =
    φ ≫ I'.toModulesι)

include hφ in
/-- The square of the naturality ladder around the connecting homomorphism.

```
  Γ(W₀, 𝒪)ˣ ────δ────▶ H¹(W, I)
      │                    │
      │ unitsMap           │ h1Map
      ▼                    ▼
  Γ(W₀', 𝒪)ˣ ───δ'───▶ H¹(W', I')
```
-/
theorem unitsToH1_naturality :
    (I'.unitsToH1 hI').comp (Hom.unitsMap (subschemeMapOfComapLe I I' g hg)) =
      (h1Map I I' g φ).comp (I.unitsToH1 hI) :=
  sorry

include hφ in
/-- The square of the naturality ladder around the map `H¹(W, I) ⟶ Pic W`.

```
  H¹(W, I) ──h1ToPic──▶ Pic W
      │                    │
      │ h1Map              │ Pic.map g
      ▼                    ▼
  H¹(W', I') ─h1ToPic'─▶ Pic W'
```
-/
theorem h1ToPic_naturality :
    (Pic.map g).comp (I.h1ToPic hI) = (I'.h1ToPic hI').comp (h1Map I I' g φ) :=
  sorry

/-- The square of the naturality ladder around the connecting homomorphism, for the canonical
comparison morphism `g^* I ⟶ I'`. -/
theorem unitsToH1_naturality_comapModulesMap :
    (I'.unitsToH1 hI').comp (Hom.unitsMap (subschemeMapOfComapLe I I' g hg)) =
      (h1MapOfComapLe I I' g hg).comp (I.unitsToH1 hI) :=
  unitsToH1_naturality I I' g (comapModulesMap I I' g hg) hI hI' hg
    (comapModulesMap_toModulesι I I' g hg).symm

/-- The square of the naturality ladder around the map `H¹(W, I) ⟶ Pic W`, for the canonical
comparison morphism `g^* I ⟶ I'`. -/
theorem h1ToPic_naturality_comapModulesMap :
    (Pic.map g).comp (I.h1ToPic hI) = (I'.h1ToPic hI').comp (h1MapOfComapLe I I' g hg) :=
  h1ToPic_naturality I I' g (comapModulesMap I I' g hg) hI hI'
    (comapModulesMap_toModulesι I I' g hg).symm

end AlgebraicGeometry.Scheme.IdealSheafData
