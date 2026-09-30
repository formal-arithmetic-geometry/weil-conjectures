/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.ProEtale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek

/-!
# Coefficients and the geometric operation package of the trace formula

The Lefschetz-Verdier trace formula is developed in the blueprint over an *axiomatised*
package of the six operations: the sketch fixes the data of the functors together with
their adjunctions, composition isomorphisms, base change, the projection formula and the
identification `Rf_* = Rf_!` for proper `f`, and quotes their geometric realisation from
the six operations chapter.

This file formalises that specification. The four functors themselves are **not** redefined:
the fields of `AlgebraicGeometry.ProEtale.GeometricOperations` are exactly the comparison
data which this project has not yet built, stated for the pro-étale functors that it has.

## Main definitions

- `AlgebraicGeometry.ProEtale.GeometricCoefficients`: the coefficient stage, carrying
  `Dᵇctf(X, A)`.
- `AlgebraicGeometry.ProEtale.DerivedBraiding`: a braiding on `D(X, A)` for every scheme `X`.
- `AlgebraicGeometry.ProEtale.GeometricOperations`: the geometric operation package.
- `AlgebraicGeometry.ProEtale.GeometricOperations.verdierDual`: the Verdier dual
  `D_X K = RHom(K, ω_X)` for the package's dualizing complex `ω_X`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.upperShriekId`,
  `AlgebraicGeometry.ProEtale.GeometricOperations.upperShriekIdIso`,
  `AlgebraicGeometry.ProEtale.GeometricOperations.upperShriekComp`: the identity and
  composition isomorphisms `(𝟙 X)^! ≃ 𝟭` and `(f ≫ g)^! ≃ f^! g^!`, conjugate to the fields
  `lowerShriekId` and `lowerShriekComp`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.upperStarUnit`,
  `AlgebraicGeometry.ProEtale.GeometricOperations.upperStarTensor`: the unit and tensor
  isomorphisms of the monoidal structure `upperStarMonoidal` of `Lf^*`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.dualizingCongr`: transport of `ω` along an
  equality of structure morphisms.

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.ctf_lowerStar`: `Dᵇctf` is stable under
  `Rf_*` for proper `f`.

## Implementation notes

The blueprint's `Λ`-valued pro-étale six operations are rendered by the functors this
project has:

* `Lf^*` is `(AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor`,
* `Rf_*` is `(AlgebraicGeometry.ProEtale.lowerStar A f).rightDerivedFunctor`,
* `Rf_!` is `AlgebraicGeometry.ProEtale.rightDerivedLowerShriek A f`,
* `f^!` is `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A f`,
* `⊗ᴸ` and `RHom` are the monoidal structure and internal hom of
  `DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)`, which is monoidal closed, so
  `A_X` is `𝟙_ _` and `RHom(K, L)` is `(ihom K).obj L`;
* the two adjunctions are `derivedUpperStarLowerStarAdjunction` and
  `rightDerivedUpperShriekAdjunction`.

The coefficients are an arbitrary Grothendieck abelian monoidal closed category `A` rather
than the blueprint's finite ring `𝒪_E/ϖⁿ`; the intended instantiation is
`A = ModuleCat (𝒪_E/ϖⁿ)`. Constructibility on the pro-étale site is not available, so the
subcategory `Dᵇctf(X, A) ⊆ D(X, A)` of bounded constructible objects of finite Tor
amplitude is carried as data by `GeometricCoefficients`.

This project installs a monoidal structure on `D(X, A)` but not yet its braiding. The
braidings of all the `D(X, A)` are therefore supplied at once by the temporary class
`DerivedBraiding`, whose instances are global, rather than by a separate instance argument
for each scheme, and the package requires the monoidal structure `upperStarMonoidal` of
every `Lf^*` to be braided for them (`upperStarMonoidal_braiding`). So all braidings in the
trace formula are the same choice, compatible with pullback. The choice is not pinned to the
Koszul-sign braiding induced from `A`, and the trace statements are only correct for that
braiding; once it is constructed, `DerivedBraiding` should be removed and
`upperStarMonoidal_braiding` becomes a theorem.

Two limitations of the package as stated.

* The comparison data are *not* pinned to the canonical maps: `properComparison` and
  `openPurity` to the natural transformations `Rf_! ⟶ Rf_*` and `f^! ⟶ Lf^*`,
  `upperStarMonoidal` to the oplax monoidal structure of the left adjoint `Lf^*` of the lax
  monoidal `Rf_*`, and `kunnethVerdier` to the map `p_X^* M ⊗ᴸ p_Y^* D_Y N ⟶
  RHom(p_Y^* N, p_X^! M)` built from the projection formula, base change, tensor-hom and the
  `!`-adjunction. This project constructs none of these at the level of derived categories.
* The coherence imposed is only at identities: the unit axioms of `lowerShriekId`, and the
  identifications of `properComparison`, `dualizingBase`, `dualizingComp` and the unit of
  `upperStarMonoidal` at `f = 𝟙`. The compatibility of `properComparison` and `dualizingComp`
  with composition (`lowerShriekComp` and the composition of `Rf_*`), and between
  `baseChange` and `lowerShriekComp`, is not imposed.

Since `Correspondence.globalOperator` and `GeometricOperations.integral` are composites of
these isomorphisms, the second limitation matters. Rescaling `properComparison f` by a unit
of `A` at a non-identity `f` rescales `globalOperator` and `integral` without changing the
stalk traces. So the trace theorems of `Pairing.lean`, `ProperPushforward.lean` and
`Main.lean` need the composition coherences as extra axioms before they can be proved
from the package. All of this belongs to the six operations chapter rather than to this
block.

The dualizing complex `ω_X = a_X^! A` *is* constructible when `a_X` admits a
compactification, but it is needed for morphisms whose compactification is not in scope, so
it is carried as a field and tied to its construction by `dualizingIso`; `dualizingBase`
normalises `ω_s` to `A_s`, which is what makes `End (A_s)` the coefficient ring in which
integrals and local terms take their values.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Coefficients and geometric categories: a choice, for every scheme `X`, of the
subcategory `Dᵇctf(X, A) ⊆ D(X, A)` of bounded constructible objects of finite Tor
amplitude, triangulated and stable under `Lf^*` and `Rf_!`
(blueprint: `sk-d-setup`). -/
structure GeometricCoefficients where
  /-- `Dᵇctf(X, A)`, the bounded constructible objects of finite Tor amplitude. -/
  ctf (X : Scheme.{u}) : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
  /-- `Dᵇctf(X, A)` is a triangulated subcategory of `D(X, A)`. -/
  isTriangulated_ctf (X : Scheme.{u}) : (ctf X).IsTriangulated
  /-- `Dᵇctf(X, A)` is closed under isomorphisms. -/
  isClosedUnderIsomorphisms_ctf (X : Scheme.{u}) : (ctf X).IsClosedUnderIsomorphisms
  /-- `Dᵇctf` is stable under `Lf^*`. -/
  ctf_upperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) (hK : ctf Y K) :
    ctf X (((upperStar A f).leftDerivedFunctor).obj K)
  /-- `Dᵇctf` is stable under `Rf_!`. -/
  ctf_lowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : ctf X K) :
    ctf Y ((rightDerivedLowerShriek A f).obj K)

instance (G : GeometricCoefficients A) (X : Scheme.{u}) : (G.ctf X).IsTriangulated :=
  G.isTriangulated_ctf X

instance (G : GeometricCoefficients A) (X : Scheme.{u}) : (G.ctf X).IsClosedUnderIsomorphisms :=
  G.isClosedUnderIsomorphisms_ctf X

/-- A braiding on the derived category `D(X, A)` of the pro-étale site of every scheme `X`.
This project does not yet construct the braiding induced by that of `A`; the class makes the
braidings of all the `D(X, A)` one choice, supplied by a global instance.

This class is a temporary stand-in. It should be removed once the braiding on `D(X, A)`
induced from the symmetric structure of `A` (with the Koszul signs on complexes) is
constructed, and the global instance below may then conflict with that canonical instance.
The braiding is not constrained: the trace statements of this block are only correct for the
Koszul-sign braiding, since for another braiding the categorical trace changes (for example
`dim k[1]` is `-1` only for the Koszul signs). -/
class DerivedBraiding where
  /-- the braiding on `D(X, A)`. -/
  braidedCategory (X : Scheme.{u}) :
    BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))

instance [DerivedBraiding A] (X : Scheme.{u}) :
    BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  DerivedBraiding.braidedCategory X

variable [DerivedBraiding A]

/-- The geometric operation package over a base `s`: the comparison data of the six
operations that the blueprint fixes, namely the dualizing complex `ω_X = a_X^! A` with its
composition `f^! ω_Y ≃ ω_X`, the identification `Rf_* = Rf_!` for proper `f`, composition
of exceptional direct images, `!`-base change, the projection formula, open-immersion
purity, the closed-immersion unit `1 ≃ Ri^! Ri_*`, the monoidal structure of the
pullback `Lf^*`, braided for `DerivedBraiding`, biduality
`K ≃ D_X D_X K` on `Dᵇctf`, and the Künneth-Verdier isomorphism. The identity isomorphism
`R(𝟙 X)_! ≃ 𝟭` is tied to `lowerShriekComp` by unit axioms, and `properComparison`,
`dualizingBase`, `dualizingComp` and the unit of `Lf^*` are tied to the identity
isomorphisms at `f = 𝟙`.

The functors and the two adjunctions are *not* fields: they are the pro-étale functors of
`WeilConjectures.SixFunctors.ProEtale`, listed in the module docstring
(blueprint: `sk-d-six`). -/
structure GeometricOperations (s : Scheme.{u}) extends GeometricCoefficients A where
  /-- the dualizing complex `ω_X = a_X^! A` of a geometric scheme `a : X ⟶ s`. -/
  dualizing {X : Scheme.{u}} (a : X ⟶ s) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)
  /-- `ω_X` is `a_X^! A` whenever `a_X` admits a compactification. -/
  dualizingIso {X : Scheme.{u}} (a : X ⟶ s) [HasCompactification a] :
    dualizing a ≅ (rightDerivedUpperShriek A a).obj (𝟙_ _)
  /-- the normalisation `ω_s ≃ A_s` of the dualizing complex of the base. -/
  dualizingBase :
    dualizing (𝟙 s) ≅ 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))
  /-- dualizing composition: `f^! ω_Y ≃ ω_X`. -/
  dualizingComp {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Y ⟶ s) [HasCompactification f] :
    (rightDerivedUpperShriek A f).obj (dualizing a) ≅ dualizing (f ≫ a)
  /-- `Rf_* = Rf_!` for proper `f`. -/
  properComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [IsProper f] :
    rightDerivedLowerShriek A f ≅ (lowerStar A f).rightDerivedFunctor
  /-- composition of the exceptional direct images: `Rf_! ⋙ Rg_! ≃ R(f ≫ g)_!`. -/
  lowerShriekComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f]
      [HasCompactification g] [HasCompactification (f ≫ g)] :
    rightDerivedLowerShriek A f ⋙ rightDerivedLowerShriek A g ≅
      rightDerivedLowerShriek A (f ≫ g)
  /-- the identity isomorphism of the exceptional direct image: `R(𝟙 X)_! ≃ 𝟭`. -/
  lowerShriekId (X : Scheme.{u}) :
    rightDerivedLowerShriek A (𝟙 X) ≅ 𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
  /-- left unit axiom: `lowerShriekComp (𝟙 X) f` is `lowerShriekId X` whiskered by `Rf_!`,
  that is, the square

  ```
    R(𝟙 X)_! ⋙ Rf_! ──lowerShriekComp (𝟙 X) f──▶ R(𝟙 X ≫ f)_!
          │                                           │
    lowerShriekId X ◫ Rf_!           rightDerivedLowerShriekCongr (id_comp f)
          ▼                                           ▼
       𝟭 ⋙ Rf_!  ──────────── leftUnitor ──────────▶ Rf_!
  ```

  commutes. -/
  lowerShriekComp_id_left {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
      [HasCompactification (𝟙 X ≫ f)] :
    lowerShriekComp (𝟙 X) f = Functor.isoWhiskerRight (lowerShriekId X) _ ≪≫
      Functor.leftUnitor _ ≪≫ rightDerivedLowerShriekCongr A (Category.id_comp f).symm
  /-- right unit axiom: `lowerShriekComp f (𝟙 Y)` is `lowerShriekId Y` whiskered by
  `Rf_!`, that is, the square

  ```
    Rf_! ⋙ R(𝟙 Y)_! ──lowerShriekComp f (𝟙 Y)──▶ R(f ≫ 𝟙 Y)_!
          │                                           │
    Rf_! ◫ lowerShriekId Y           rightDerivedLowerShriekCongr (comp_id f)
          ▼                                           ▼
       Rf_! ⋙ 𝟭  ──────────── rightUnitor ─────────▶ Rf_!
  ```

  commutes. -/
  lowerShriekComp_id_right {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
      [HasCompactification (f ≫ 𝟙 Y)] :
    lowerShriekComp f (𝟙 Y) = Functor.isoWhiskerLeft _ (lowerShriekId Y) ≪≫
      Functor.rightUnitor _ ≪≫ rightDerivedLowerShriekCongr A (Category.comp_id f).symm
  /-- for `f = 𝟙 X`, `properComparison` is the composite
  `R(𝟙 X)_! ≃ 𝟭 ≃ R(𝟙 X)_*` of `lowerShriekId X` and the identity isomorphism of `R(𝟙 X)_*`,
  the conjugate of `leftDerivedUpperStarId`. -/
  properComparison_id (X : Scheme.{u}) :
    properComparison (𝟙 X) = lowerShriekId X ≪≫
      conjugateIsoEquiv Adjunction.id (derivedUpperStarLowerStarAdjunction A (𝟙 X))
        (leftDerivedUpperStarId A X)
  /-- the normalisation `ω_s ≃ A_s` is `ω_s ≃ (𝟙 s)^! A_s ≃ A_s`, the second map being the
  identity isomorphism of `(𝟙 s)^!`, the conjugate of `lowerShriekId s`. -/
  dualizingBase_eq :
    dualizingBase = dualizingIso (𝟙 s) ≪≫
      (conjugateIsoEquiv Adjunction.id (rightDerivedUpperShriekAdjunction A (𝟙 s))
        (lowerShriekId s)).symm.app (𝟙_ _)
  /-- for `f = 𝟙 X`, `dualizingComp` is `(𝟙 X)^! ω_X ≃ ω_X`, the identity isomorphism of
  `(𝟙 X)^!` (the conjugate of `lowerShriekId X`), transported along `𝟙 X ≫ a = a`. -/
  dualizingComp_id {X : Scheme.{u}} (a : X ⟶ s) :
    dualizingComp (𝟙 X) a =
      (conjugateIsoEquiv Adjunction.id (rightDerivedUpperShriekAdjunction A (𝟙 X))
        (lowerShriekId X)).symm.app (dualizing a) ≪≫
        eqToIso (congrArg dualizing (Category.id_comp a).symm)
  /-- `!`-base change along a Cartesian square: `Lg^* Rf_! ≃ Rf'_! Lg'^*`, for

  ```
     X' ──g'──→ X
     │          │
   f'│          │f
     ↓          ↓
     Y' ──g───→ Y
  ```
  -/
  baseChange {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (sq : IsPullback g' f' f g) [HasCompactification f] [HasCompactification f'] :
    rightDerivedLowerShriek A f ⋙ (upperStar A g).leftDerivedFunctor ≅
      (upperStar A g').leftDerivedFunctor ⋙ rightDerivedLowerShriek A f'
  /-- the projection formula `Rf_! K ⊗ᴸ L ≃ Rf_! (K ⊗ᴸ Lf^* L)`, as an isomorphism of
  bifunctors `D(X, A) × D(Y, A) ⥤ D(Y, A)`. -/
  projectionFormula {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (rightDerivedLowerShriek A f).prod
          (𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))) ⋙
        MonoidalCategory.tensor (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) ≅
      (𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))).prod
          ((upperStar A f).leftDerivedFunctor) ⋙
        MonoidalCategory.tensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) ⋙
          rightDerivedLowerShriek A f
  /-- open-immersion purity: `j^! ≃ Lj^*` for an open immersion `j`. -/
  openPurity {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [HasCompactification j] :
    rightDerivedUpperShriek A j ≅ (upperStar A j).leftDerivedFunctor
  /-- the closed-immersion unit: `1 ≃ Ri^! Ri_*` for a closed immersion `i`. -/
  closedUnit {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i] :
    𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) ≅
      (lowerStar A i).rightDerivedFunctor ⋙ rightDerivedUpperShriek A i
  /-- `Lf^*` is monoidal: the unit `A_X ≃ Lf^* A_Y` and the tensor comparison
  `Lf^* M ⊗ᴸ Lf^* N ≃ Lf^* (M ⊗ᴸ N)`, with their naturality, associativity and unitality. -/
  upperStarMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((upperStar A f).leftDerivedFunctor).CoreMonoidal
  /-- for `f = 𝟙 X`, the pullback `L(𝟙 X)^* A_X ≃ A_X` of the constant sheaf is the
  identity isomorphism `L(𝟙 X)^* ≃ 𝟭`. -/
  upperStarUnit_id (X : Scheme.{u}) :
    (upperStarMonoidal (𝟙 X)).εIso.inv = (leftDerivedUpperStarId A X).hom.app (𝟙_ _)
  /-- the monoidal structure of `Lf^*` is braided: its tensor map `μ` commutes with the
  braidings `β` of `D(Y, A)` and `D(X, A)`, that is, the square

  ```
    Lf^* M ⊗ Lf^* N ──μ──▶ Lf^*(M ⊗ N)
          │                    │
        β │                    │ Lf^* β
          ▼                    ▼
    Lf^* N ⊗ Lf^* M ──μ──▶ Lf^*(N ⊗ M)
  ```

  commutes. This is the axiom of `Functor.Braided`, stated by hand because
  `upperStarMonoidal` is a `Functor.CoreMonoidal` rather than a `Functor.Monoidal`
  instance. -/
  upperStarMonoidal_braiding {X Y : Scheme.{u}} (f : X ⟶ Y)
      (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((upperStarMonoidal f).μIso M N).hom ≫ ((upperStar A f).leftDerivedFunctor).map (β_ M N).hom =
      (β_ _ _).hom ≫ ((upperStarMonoidal f).μIso N M).hom
  /-- the evaluation-adjoint map `K ⟶ D_X D_X K`. -/
  bidualityMap {X : Scheme.{u}} (a : X ⟶ s)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    K ⟶ (ihom ((ihom K).obj (dualizing a))).obj (dualizing a)
  /-- biduality on `Dᵇctf`: the evaluation-adjoint map `K ⟶ D_X D_X K` is invertible. -/
  isIso_bidualityMap {X : Scheme.{u}} (a : X ⟶ s)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : ctf X K) :
    IsIso (bidualityMap a K)
  /-- the Künneth-Verdier isomorphism `κ_{M,N} : M ⊠ D_Y N ≃ RHom(p_Y^* N, p_X^! M)` for
  `M ∈ Dᵇctf(X)` and `N ∈ Dᵇctf(Y)`, where `X` and `Y` are separated of finite type over a
  field `s = Spec k` (blueprint `sk-thm-sf-kunneth-verdier`). It is stated for every
  Cartesian square over `s`, so that both orientations are available on `pullback aY aX`. -/
  kunnethVerdier {Z X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s} {pX : Z ⟶ X} {pY : Z ⟶ Y}
      [s.IsSpecOfField]
      [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
      [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
      (sq : IsPullback pX pY aX aY) [HasCompactification pX]
      (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hM : ctf X M)
      (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) (hN : ctf Y N) :
    ((upperStar A pX).leftDerivedFunctor).obj M ⊗
        ((upperStar A pY).leftDerivedFunctor).obj ((ihom N).obj (dualizing aY)) ≅
      (ihom (((upperStar A pY).leftDerivedFunctor).obj N)).obj
        ((rightDerivedUpperShriek A pX).obj M)

variable {A}

/-- The Verdier dual `D_X K = RHom(K, ω_X)` taken with respect to the dualizing complex of
a geometric operation package (part of blueprint `sk-d-six`). -/
noncomputable def GeometricOperations.verdierDual {s : Scheme.{u}}
    (G : GeometricOperations A s) {X : Scheme.{u}} (a : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (ihom K).obj (G.dualizing a)

namespace GeometricOperations

variable {s : Scheme.{u}} (G : GeometricOperations A s)

/-- Transport of the dualizing complex along an equality of structure morphisms:
`ω_a ≅ ω_b` for `a = b`. -/
noncomputable def dualizingCongr {X : Scheme.{u}} {a b : X ⟶ s} (h : a = b) :
    G.dualizing a ≅ G.dualizing b :=
  eqToIso (congrArg G.dualizing h)

@[simp]
lemma dualizingCongr_rfl {X : Scheme.{u}} {a : X ⟶ s} :
    G.dualizingCongr (rfl : a = a) = Iso.refl _ :=
  rfl

/-- `Dᵇctf` is stable under `Rf_*` for proper `f`: it is stable under `Rf_!`, which is
`Rf_*` by `properComparison`. -/
lemma ctf_lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K) :
    G.ctf Y (((lowerStar A f).rightDerivedFunctor).obj K) :=
  (G.ctf Y).prop_of_iso ((G.properComparison f).app K) (G.ctf_lowerShriek f K hK)

/-- The pullback of the constant sheaf, `Lf^* A_Y ≃ A_X`: the inverse of the unit of the
monoidal structure `GeometricOperations.upperStarMonoidal` of `Lf^*`. -/
noncomputable def upperStarUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((upperStar A f).leftDerivedFunctor).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (G.upperStarMonoidal f).εIso.symm

/-- For `f = 𝟙 X`, `upperStarUnit` is the identity isomorphism `L(𝟙 X)^* ≃ 𝟭`. -/
@[simp]
lemma upperStarUnit_hom_id (X : Scheme.{u}) :
    (G.upperStarUnit (𝟙 X)).hom = (leftDerivedUpperStarId A X).hom.app (𝟙_ _) :=
  G.upperStarUnit_id X

/-- The tensor comparison `Lf^* (M ⊗ᴸ N) ≃ Lf^* M ⊗ᴸ Lf^* N` of the pullback: the inverse of
the tensor map of the monoidal structure `GeometricOperations.upperStarMonoidal` of
`Lf^*`. -/
noncomputable def upperStarTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((upperStar A f).leftDerivedFunctor).obj (M ⊗ N) ≅
      ((upperStar A f).leftDerivedFunctor).obj M ⊗ ((upperStar A f).leftDerivedFunctor).obj N :=
  ((G.upperStarMonoidal f).μIso M N).symm

/-- The identity isomorphism `(𝟙 X)^! ≃ 𝟭` of the exceptional inverse image: the conjugate
of the field `lowerShriekId : R(𝟙 X)_! ≃ 𝟭` along the adjunctions `R(𝟙 X)_! ⊣ (𝟙 X)^!` and
`𝟭 ⊣ 𝟭`. -/
noncomputable def upperShriekId (X : Scheme.{u}) :
    rightDerivedUpperShriek A (𝟙 X) ≅ 𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  (conjugateIsoEquiv Adjunction.id (rightDerivedUpperShriekAdjunction A (𝟙 X))
    (G.lowerShriekId X)).symm

/-- Under the conjugation bijection between the adjunctions `R(𝟙 X)_! ⊣ (𝟙 X)^!` and
`𝟭 ⊣ 𝟭`, the identity isomorphism of the exceptional direct image corresponds to the inverse
of the identity isomorphism of the exceptional inverse image:

```
  R(𝟙 X)_! ⊣ (𝟙 X)^!        lowerShriekId : R(𝟙 X)_! ≅ 𝟭
       ↕ conjugate                   ↦
       𝟭 ⊣ 𝟭               upperShriekId.symm : 𝟭 ≅ (𝟙 X)^!
``` -/
@[simp]
lemma conjugateIsoEquiv_lowerShriekId (X : Scheme.{u}) :
    conjugateIsoEquiv Adjunction.id (rightDerivedUpperShriekAdjunction A (𝟙 X))
        (G.lowerShriekId X) = (G.upperShriekId X).symm := by
  simp [upperShriekId]

/-- The identity isomorphism `𝟭 ≃ (𝟙 X)^!` of the exceptional inverse image: the inverse of
`GeometricOperations.upperShriekId`. -/
noncomputable def upperShriekIdIso (X : Scheme.{u}) :
    𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) ≅
      rightDerivedUpperShriek A (𝟙 X) :=
  (G.upperShriekId X).symm

/-- The composition isomorphism `(f ≫ g)^! ≃ g^! ⋙ f^!` of exceptional inverse images:
the conjugate of `GeometricOperations.lowerShriekComp` along the adjunctions
`R(f ≫ g)_! ⊣ (f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ g^! ⋙ f^!`. -/
noncomputable def upperShriekComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    rightDerivedUpperShriek A (f ≫ g) ≅
      rightDerivedUpperShriek A g ⋙ rightDerivedUpperShriek A f :=
  conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (f ≫ g))
    ((rightDerivedUpperShriekAdjunction A f).comp (rightDerivedUpperShriekAdjunction A g))
    (G.lowerShriekComp f g)

/-- Under the conjugation bijection between the adjunctions `R(f ≫ g)_! ⊣ (f ≫ g)^!` and
`Rf_! ⋙ Rg_! ⊣ g^! ⋙ f^!`, the composition isomorphism of the exceptional direct images
corresponds to the composition isomorphism of the exceptional inverse images:

```
  R(f ≫ g)_! ⊣ (f ≫ g)^!       lowerShriekComp f g : Rf_! ⋙ Rg_! ≅ R(f ≫ g)_!
          ↕ conjugate                          ↦
  Rf_! ⋙ Rg_! ⊣ g^! ⋙ f^!      upperShriekComp f g : (f ≫ g)^! ≅ g^! ⋙ f^!
``` -/
@[simp]
lemma conjugateIsoEquiv_lowerShriekComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (f ≫ g))
        ((rightDerivedUpperShriekAdjunction A f).comp (rightDerivedUpperShriekAdjunction A g))
        (G.lowerShriekComp f g) = G.upperShriekComp f g :=
  rfl

end GeometricOperations

/-- Transport of the derived exceptional direct image along an equality of morphisms. This
is `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekCongr`, under the name used by the
trace formula files. -/
noncomputable abbrev lowerShriekCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [HasCompactification f] [HasCompactification g] :
    rightDerivedLowerShriek A f ≅ rightDerivedLowerShriek A g :=
  rightDerivedLowerShriekCongr A h

end AlgebraicGeometry.ProEtale
