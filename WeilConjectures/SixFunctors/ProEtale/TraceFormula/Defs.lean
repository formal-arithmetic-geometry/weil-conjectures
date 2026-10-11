/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.ProEtale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude
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
data which this project has not yet built, stated for the pro-étale functors that it has, on
the geometric categories of the blueprint (`sk-d-setup`, `sk-d-six`): the bounded constructible
complexes of finite Tor amplitude `Dᵇctf(X, A)` on schemes separated of finite type over the
base.

## Main definitions

- `AlgebraicGeometry.ProEtale.IsGeometric`: a scheme `X` with `a : X ⟶ s` is *geometric* over
  `s` if `a` is separated and of finite type.
- `AlgebraicGeometry.ProEtale.Ctf`: the full subcategory `Dᵇctf(X, A)` of `D(X, A)`, the
  bounded constructible objects of finite Tor amplitude
  (`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`).
- `AlgebraicGeometry.ProEtale.GeometricCoefficients`: the coefficient stage: the stability of
  `Dᵇctf` under the operations, on geometric schemes.
- `AlgebraicGeometry.ProEtale.GeometricCoefficients.upperStarCtf`, `lowerShriekCtf`,
  `upperShriekCtf`, `lowerStarCtf`: the operations as functors between the categories
  `Dᵇctf`, and `AlgebraicGeometry.ProEtale.GeometricCoefficients.exceptionalAdjunction`: the
  adjunction `Rf_! ⊣ Rf^!` between them (blueprint `sk-prop-sf-existence` (c)).
- `AlgebraicGeometry.ProEtale.DerivedBraiding`: a braiding on `D(X, A)` for every scheme `X`.
- `AlgebraicGeometry.ProEtale.GeometricOperations`: the geometric operation package.
- `AlgebraicGeometry.ProEtale.GeometricOperations.verdierDual`: the Verdier dual
  `D_X K = RHom(K, ω_X)` for the package's dualizing complex `ω_X`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.upperShriekId`,
  `AlgebraicGeometry.ProEtale.GeometricOperations.upperShriekIdIso`,
  `AlgebraicGeometry.ProEtale.GeometricOperations.upperShriekComp`: the identity and
  composition isomorphisms `(𝟙 X)^! ≃ 𝟭` and `(f ≫ g)^! ≃ f^! g^!` on `Dᵇctf`, conjugate to the
  fields `lowerShriekId` and `lowerShriekComp`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.upperStarUnit`,
  `AlgebraicGeometry.ProEtale.GeometricOperations.upperStarTensor`: the unit and tensor
  isomorphisms of the monoidal structure `upperStarMonoidal` of `Lf^*`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.dualizingCongr`: transport of `ω` along an
  equality of structure morphisms.
- `AlgebraicGeometry.ProEtale.GeometricOperations.bidualityMap`: the evaluation-adjoint map
  `K ⟶ D_X D_X K`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.kunnethVerdierMap`,
  `AlgebraicGeometry.ProEtale.GeometricOperations.kunnethVerdier`: the canonical Künneth-Verdier
  map `M ⊠ D_Y N ⟶ RHom(p_Y^* N, p_X^! M)` and, on `Dᵇctf`, the isomorphism it is.

## Implementation notes

The blueprint's `Λ`-valued pro-étale six operations are rendered by the functors this
project has:

* `Lf^*` is `(AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor`,
* `Rf_*` is `(AlgebraicGeometry.ProEtale.lowerStar A f).rightDerivedFunctor`,
* `Rf_!` is `AlgebraicGeometry.ProEtale.rightDerivedLowerShriek A f`,
* `f^!` is the constructible exceptional inverse image
  `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A f` of blueprint `sk-def-sf-operations`
  (vi), `ν_X^* ∘ f^× ∘ Rν_{Y,*}`,
* `⊗ᴸ` and `RHom` are the monoidal structure and internal hom of
  `DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)`, which is monoidal closed, so
  `A_X` is `𝟙_ _` and `RHom(K, L)` is `(ihom K).obj L`;
* the two adjunctions are `derivedUpperStarLowerStarAdjunction` and the exceptional adjunction
  `GeometricCoefficients.exceptionalAdjunction` on `Dᵇctf`.

The pro-étale `Rf_!` is not a left adjoint on the whole derived category (blueprint
`sk-rem-sf-fullcd-scope`), so the exceptional adjunction is only available on `Dᵇctf`, where it
is a theorem (`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekAdjunction`): every object
of `Dᵇctf` is bounded below of étale origin.

`Dᵇctf(X, A)` is not data: it is the property
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor` of bounded constructible
complexes of étale origin of finite Tor amplitude, which is the blueprint's `Dᵇctf(X, A)` at the
finite coefficient stages `A = 𝒪_E/ϖⁿ` (blueprint `sk-d-setup`, `def-weil-pbc-proetale-modules`).
The coefficients are an arbitrary Grothendieck abelian monoidal closed concrete category `A`;
the intended instantiation is `A = ModuleCat (𝒪_E/ϖⁿ)`. They are assumed to have étale
exceptional inverse images preserving bounded below objects
(`AlgebraicGeometry.Etale.HasBoundedBelowUpperShrieks`), out of which the constructible `f^!` is
built; this holds for torsion coefficients, in particular for `ModuleCat (𝒪_E/ϖⁿ)`.

The fields of the package are the comparison isomorphisms of the six operations restricted to
`Dᵇctf` on geometric schemes, that is, natural isomorphisms between functors out of the
categories `Dᵇctf`. This is what makes the package inhabitable by the six operations over the
bases of the blueprint, a field or a regular scheme of dimension at most one (biduality on
`Dᵇctf`, `isIso_bidualityMap`, fails over more general bases): for `A = 𝒪_E/ϖⁿ` with `ℓ`
invertible on the base, every object of `Dᵇctf` is of étale origin, and the
fields are the étale statements of the six functors chapter (finiteness, proper and `!`-base
change, the projection formula, `Rf_! = Rf_*` for proper `f`, biduality and Künneth-Verdier),
transported along the comparison `ν^*` (blueprint `sk-prop-sf-comparison`). On the whole
unbounded pro-étale derived category several of them fail: `Rp_*` does not commute with
coproducts for the structure morphism of an elliptic curve (blueprint
`sk-rem-sf-fullcd-scope`), so neither the projection formula nor `!`-base change holds there
for all objects. The one exception is the monoidal structure `upperStarMonoidal` of `Lf^*`,
which is stated on the whole derived category: the derived pullback along a morphism of ringed
topoi with constant coefficients commutes with derived tensor products of arbitrary complexes,
and the stronger statement is what the Künneth-Verdier map needs.

This project installs a monoidal structure on `D(X, A)` but not yet its braiding. The
braidings of all the `D(X, A)` are therefore supplied at once by the temporary class
`DerivedBraiding`, whose instances are global, rather than by a separate instance argument
for each scheme, and the package requires the monoidal structure `upperStarMonoidal` of
every `Lf^*` to be braided for them (`upperStarMonoidal_braiding`). So all braidings in the
trace formula are the same choice, compatible with pullback. The trace statements are only
correct for the Koszul-sign braiding induced from `A`, so `DerivedBraiding` pins the sign of
the braiding of `A_X[1]` with itself to `-1`; once the braiding is constructed,
`DerivedBraiding` should be removed and `upperStarMonoidal_braiding` becomes a theorem.

The comparison isomorphisms are tied to each other by coherence axioms: the unit axioms of
`lowerShriekId`; the identifications of `properComparison`, `dualizingBase`, `dualizingComp`
and the unit of `upperStarMonoidal` at `f = 𝟙`; the compatibility of `properComparison` with
composition (`properComparison_comp`, against `lowerShriekComp` and the composition of
`Rf_*`) and of `dualizingComp` with composition (`dualizingComp_comp`); and the
compatibility of `baseChange` with vertical pasting of Cartesian squares
(`baseChange_paste_vert`, against `lowerShriekComp`). Without them, rescaling
`properComparison f` by a unit of `A` at a non-identity `f` would rescale
`Correspondence.globalOperator` and `GeometricOperations.integral` without changing the
stalk traces.

The Künneth-Verdier comparison is not a free isomorphism either: it is the canonical map
`GeometricOperations.kunnethVerdierMap`, built from the projection formula, `!`-base change,
the monoidal structure of the pullback, tensor-hom and the `!`-adjunction, and the package
only asserts that it is invertible (`isIso_kunnethVerdierMap`).

Biduality is not a free isomorphism either: `GeometricOperations.bidualityMap` is the
tensor-hom adjoint of evaluation, and the package only asserts that it is invertible
(`isIso_bidualityMap`).

There is no open-purity field. Its only use in the trace formula was the restriction of a
Borel-Moore section to a clopen piece in the local terms, and the local terms are instead
built from the canonical idempotent `AlgebraicGeometry.ProEtale.clopenIdempotent` of the
clopen piece, which uses no package data (`GeometricOperations.localTerm`).

The remaining comparison data are still *not* pinned to canonical maps: `properComparison`
to the natural transformation `Rf_! ⟶ Rf_*`, `projectionFormula` to the inverse of the
projection map `AlgebraicGeometry.ProEtale.projectionMap`, and `upperStarMonoidal` to the
tensor comparison `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso`. The last two maps
now exist; pinning these fields to them is left to a follow-up.

The dualizing complex `ω_X = a_X^! A` is carried as a field, tied to its construction by
`dualizingIso` whenever `a_X` admits a compactification; `dualizingBase` normalises `ω_s` to
`A_s`, which is what makes `End (A_s)` the coefficient ring in which integrals and local terms
take their values.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

/-- A scheme `X` with a morphism `a : X ⟶ s` is *geometric* over `s` if `a` is separated and of
finite type (blueprint `sk-d-setup`). -/
class IsGeometric {X s : Scheme.{u}} (a : X ⟶ s) : Prop where
  isSeparated : IsSeparated a := by infer_instance
  locallyOfFiniteType : LocallyOfFiniteType a := by infer_instance
  quasiCompact : QuasiCompact a := by infer_instance

attribute [instance] IsGeometric.isSeparated IsGeometric.locallyOfFiniteType
  IsGeometric.quasiCompact

instance {X s : Scheme.{u}} (a : X ⟶ s) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a] : IsGeometric a where

/-- Being geometric is a property of the structure morphism, transported along equalities. -/
lemma IsGeometric.of_eq {X s : Scheme.{u}} {a b : X ⟶ s} (h : a = b) [IsGeometric a] :
    IsGeometric b :=
  h ▸ ‹_›

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- The category `Dᵇctf(X, A)` of bounded constructible objects of finite Tor amplitude of
`D(X_proét, A)` (blueprint `sk-d-setup`), as a full subcategory. -/
abbrev Ctf (X : Scheme.{u}) : Type _ :=
  (DerivedCategory.constructibleFiniteTor A X).FullSubcategory

section CtfFunctors

variable {A} {X Y : Scheme.{u}}

/-- The pullback `Lf^* : Dᵇctf(Y) ⥤ Dᵇctf(X)`, given that it preserves `Dᵇctf`. -/
noncomputable abbrev ctfUpperStar (f : X ⟶ Y)
    (h : ∀ K, DerivedCategory.constructibleFiniteTor A Y K →
      DerivedCategory.constructibleFiniteTor A X (((upperStar A f).leftDerivedFunctor).obj K)) :
    Ctf A Y ⥤ Ctf A X :=
  ObjectProperty.lift _ ((DerivedCategory.constructibleFiniteTor A Y).ι ⋙
    (upperStar A f).leftDerivedFunctor) fun K ↦ h _ K.property

/-- The exceptional direct image `Rf_! : Dᵇctf(X) ⥤ Dᵇctf(Y)`, given that it preserves
`Dᵇctf`. -/
noncomputable abbrev ctfLowerShriek (f : X ⟶ Y) [HasCompactification f]
    (h : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
      DerivedCategory.constructibleFiniteTor A Y ((rightDerivedLowerShriek A f).obj K)) :
    Ctf A X ⥤ Ctf A Y :=
  ObjectProperty.lift _ ((DerivedCategory.constructibleFiniteTor A X).ι ⋙
    rightDerivedLowerShriek A f) fun K ↦ h _ K.property

/-- The exceptional inverse image `Rf^! : Dᵇctf(Y) ⥤ Dᵇctf(X)`, given that it preserves
`Dᵇctf`. -/
noncomputable abbrev ctfUpperShriek (f : X ⟶ Y) [HasCompactification f]
    (h : ∀ L, DerivedCategory.constructibleFiniteTor A Y L →
      DerivedCategory.constructibleFiniteTor A X ((rightDerivedUpperShriek A f).obj L)) :
    Ctf A Y ⥤ Ctf A X :=
  ObjectProperty.lift _ ((DerivedCategory.constructibleFiniteTor A Y).ι ⋙
    rightDerivedUpperShriek A f) fun L ↦ h _ L.property

/-- The direct image `Rf_* : Dᵇctf(X) ⥤ Dᵇctf(Y)`, given that it preserves `Dᵇctf`. -/
noncomputable abbrev ctfLowerStar (f : X ⟶ Y)
    (h : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
      DerivedCategory.constructibleFiniteTor A Y (((lowerStar A f).rightDerivedFunctor).obj K)) :
    Ctf A X ⥤ Ctf A Y :=
  ObjectProperty.lift _ ((DerivedCategory.constructibleFiniteTor A X).ι ⋙
    (lowerStar A f).rightDerivedFunctor) fun K ↦ h _ K.property

/-- Blueprint `sk-prop-sf-existence` (c): the exceptional adjunction `Rf_! ⊣ Rf^!` between the
categories `Dᵇctf`, whenever both functors preserve `Dᵇctf`. It is
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekAdjunction`: every object of `Dᵇctf` is
bounded below of étale origin. -/
noncomputable def ctfExceptionalAdjunction (f : X ⟶ Y) [HasCompactification f]
    (h₁ : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
      DerivedCategory.constructibleFiniteTor A Y ((rightDerivedLowerShriek A f).obj K))
    (h₂ : ∀ L, DerivedCategory.constructibleFiniteTor A Y L →
      DerivedCategory.constructibleFiniteTor A X ((rightDerivedUpperShriek A f).obj L)) :
    ctfLowerShriek f h₁ ⊣ ctfUpperShriek f h₂ :=
  rightDerivedUpperShriekAdjunction f _ _ (fun _ hK ↦ hK.plusEtaleOrigin)
    (fun _ hL ↦ hL.plus) h₁ h₂

/-- Transport of the exceptional direct image on `Dᵇctf` along an equality of morphisms. -/
noncomputable def ctfLowerShriekCongr {f g : X ⟶ Y} (e : f = g) [HasCompactification f]
    [HasCompactification g]
    (h₁ : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
      DerivedCategory.constructibleFiniteTor A Y ((rightDerivedLowerShriek A f).obj K))
    (h₂ : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
      DerivedCategory.constructibleFiniteTor A Y ((rightDerivedLowerShriek A g).obj K)) :
    ctfLowerShriek f h₁ ≅ ctfLowerShriek g h₂ :=
  eqToIso <| by
    subst e
    rfl

/-- A natural transformation between functors into `Dᵇctf(X)`, given by one between their
composites with the inclusion into `D(X, A)`. -/
noncomputable def ctfHomMk {C : Type*} [Category C] {F G : C ⥤ Ctf A X}
    (e : F ⋙ (DerivedCategory.constructibleFiniteTor A X).ι ⟶
      G ⋙ (DerivedCategory.constructibleFiniteTor A X).ι) : F ⟶ G :=
  ((DerivedCategory.constructibleFiniteTor A X).fullyFaithfulι.whiskeringRight C).preimage e

omit [Etale.HasBoundedBelowUpperShrieks A] in
@[simp]
lemma ctfHomMk_app_hom {C : Type*} [Category C] {F G : C ⥤ Ctf A X}
    (e : F ⋙ (DerivedCategory.constructibleFiniteTor A X).ι ⟶
      G ⋙ (DerivedCategory.constructibleFiniteTor A X).ι) (c : C) :
    ((ctfHomMk e).app c).hom = e.app c := by
  simp [ctfHomMk]

instance isIso_ctfHomMk {C : Type*} [Category C] {F G : C ⥤ Ctf A X}
    (e : F ⋙ (DerivedCategory.constructibleFiniteTor A X).ι ⟶
      G ⋙ (DerivedCategory.constructibleFiniteTor A X).ι) [IsIso e] : IsIso (ctfHomMk e) := by
  have : IsIso (((Functor.whiskeringRight C _ _).obj
      (DerivedCategory.constructibleFiniteTor A X).ι).map (ctfHomMk e)) := by
    rw [ctfHomMk, Functor.FullyFaithful.map_preimage]
    infer_instance
  exact ((DerivedCategory.constructibleFiniteTor A X).fullyFaithfulι.whiskeringRight
    C).isIso_of_isIso_map _

end CtfFunctors

/-- A morphism `f : X ⟶ Y` is a *morphism of geometric schemes* over `s` if there is a structure
morphism `a_Y : Y ⟶ s` for which `Y` and `X`, via `f ≫ a_Y`, are geometric over `s`
(blueprint `sk-d-setup`). It is a proposition, so that data indexed by it does not depend on
the structure morphisms. -/
def IsGeometricHom (s : Scheme.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ aY : Y ⟶ s, IsGeometric aY ∧ IsGeometric (f ≫ aY)

lemma IsGeometricHom.mk {s X Y : Scheme.{u}} {f : X ⟶ Y} {aX : X ⟶ s} {aY : Y ⟶ s}
    [IsGeometric aX] [IsGeometric aY] (hf : f ≫ aY = aX) : IsGeometricHom s f :=
  ⟨aY, inferInstance, IsGeometric.of_eq hf.symm⟩

/-- The identity of a geometric scheme is a morphism of geometric schemes. -/
lemma IsGeometricHom.id {s X : Scheme.{u}} (aX : X ⟶ s) [IsGeometric aX] :
    IsGeometricHom s (𝟙 X) :=
  .mk (Category.id_comp aX)

/-- The structure morphism of a geometric scheme is a morphism of geometric schemes. -/
lemma IsGeometricHom.of_isGeometric {s X : Scheme.{u}} (aX : X ⟶ s) [IsGeometric aX] :
    IsGeometricHom s aX :=
  .mk (aY := 𝟙 s) (Category.comp_id aX)

namespace IsGeometricHom

variable {s X Y Z : Scheme.{u}}

/-- A morphism of geometric schemes is separated. -/
lemma isSeparated {f : X ⟶ Y} (hf : IsGeometricHom s f) : IsSeparated f := by
  obtain ⟨a, _, _⟩ := hf
  exact IsSeparated.of_comp (f := f) (g := a)

/-- A morphism of geometric schemes is locally of finite type. -/
lemma locallyOfFiniteType {f : X ⟶ Y} (hf : IsGeometricHom s f) : LocallyOfFiniteType f := by
  obtain ⟨a, _, _⟩ := hf
  exact locallyOfFiniteType_of_comp f a

/-- A morphism of geometric schemes is quasi-compact. -/
lemma quasiCompact {f : X ⟶ Y} (hf : IsGeometricHom s f) : QuasiCompact f := by
  obtain ⟨a, _, _⟩ := hf
  exact QuasiCompact.of_comp f a

/-- The source of a morphism of geometric schemes is geometric. -/
lemma id_source {f : X ⟶ Y} (hf : IsGeometricHom s f) : IsGeometricHom s (𝟙 X) := by
  obtain ⟨a, _, _⟩ := hf
  exact .id (f ≫ a)

/-- Morphisms of geometric schemes are stable under composition. -/
lemma comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsGeometricHom s f) (hg : IsGeometricHom s g) :
    IsGeometricHom s (f ≫ g) := by
  have := hf.isSeparated
  have := hf.locallyOfFiniteType
  have := hf.quasiCompact
  obtain ⟨c, _, _⟩ := hg
  exact ⟨c, inferInstance, by rw [Category.assoc]; infer_instance⟩

end IsGeometricHom

/-- Coefficients and geometric categories (blueprint: `sk-d-setup`): the stability of the
categories `Dᵇctf(X, A)` of bounded constructible objects of finite Tor amplitude
(`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`) on geometric schemes over
`s` under the operations: they contain `A_X`, are stable under `⊗ᴸ`, `Lf^*`, `Rf_!`, `Rf^!`
and, for `f` proper, `Rf_*`. These are the stability theorems of the six functors chapter
(blueprint `sk-thm-sf-ctf-stability`, `sk-prop-sf-rf-shriek-preservation`), which hold at the
finite coefficient stages `A = 𝒪_E/ϖⁿ` over a field in which `ℓ` is invertible. A scheme `X` is
geometric when `𝟙 X` is a morphism of geometric schemes. -/
structure GeometricCoefficients (s : Scheme.{u}) : Prop where
  /-- `A_X` lies in `Dᵇctf(X)`. -/
  ctf_unit {X : Scheme.{u}} (hX : IsGeometricHom s (𝟙 X)) :
    DerivedCategory.constructibleFiniteTor A X (𝟙_ _)
  /-- `Dᵇctf(X)` is stable under `⊗ᴸ`. -/
  ctf_tensor {X : Scheme.{u}} (hX : IsGeometricHom s (𝟙 X))
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K)
    (hL : DerivedCategory.constructibleFiniteTor A X L) :
    DerivedCategory.constructibleFiniteTor A X (K ⊗ L)
  /-- `Dᵇctf` is stable under `Lf^*`. -/
  ctf_upperStar {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsGeometricHom s f)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hK : DerivedCategory.constructibleFiniteTor A Y K) :
    DerivedCategory.constructibleFiniteTor A X (((upperStar A f).leftDerivedFunctor).obj K)
  /-- `Dᵇctf` is stable under `Rf_!`. -/
  ctf_lowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f] {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) :
    DerivedCategory.constructibleFiniteTor A Y ((rightDerivedLowerShriek A f).obj K)
  /-- `Dᵇctf` is stable under the constructible `Rf^!`. -/
  ctf_upperShriek {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f] {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : DerivedCategory.constructibleFiniteTor A Y L) :
    DerivedCategory.constructibleFiniteTor A X ((rightDerivedUpperShriek A f).obj L)
  /-- `Dᵇctf` is stable under `Rf_*` for proper `f`. -/
  ctf_lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsGeometricHom s f) [IsProper f]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) :
    DerivedCategory.constructibleFiniteTor A Y (((lowerStar A f).rightDerivedFunctor).obj K)

namespace GeometricCoefficients

variable {A} {s : Scheme.{u}} (G : GeometricCoefficients A s)

/-- `Dᵇctf(X, A)`, the bounded constructible objects of finite Tor amplitude of `D(X, A)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`). It does not depend on
`G`; the argument is there for the dot notation `G.ctf`. -/
@[nolint unusedArguments]
abbrev ctf (_G : GeometricCoefficients A s) (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  DerivedCategory.constructibleFiniteTor A X

variable {X Y : Scheme.{u}}

/-- The pullback `Lf^* : Dᵇctf(Y) ⥤ Dᵇctf(X)` along a morphism of geometric schemes. -/
noncomputable abbrev upperStarCtf (f : X ⟶ Y) (hf : IsGeometricHom s f) : Ctf A Y ⥤ Ctf A X :=
  ctfUpperStar f fun _ hK ↦ G.ctf_upperStar f hf hK

/-- The exceptional direct image `Rf_! : Dᵇctf(X) ⥤ Dᵇctf(Y)` along a morphism of geometric
schemes. -/
noncomputable abbrev lowerShriekCtf (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f] : Ctf A X ⥤ Ctf A Y :=
  ctfLowerShriek f fun _ hK ↦ G.ctf_lowerShriek f hf hK

/-- The exceptional inverse image `Rf^! : Dᵇctf(Y) ⥤ Dᵇctf(X)` along a morphism of geometric
schemes. -/
noncomputable abbrev upperShriekCtf (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f] : Ctf A Y ⥤ Ctf A X :=
  ctfUpperShriek f fun _ hL ↦ G.ctf_upperShriek f hf hL

/-- The direct image `Rf_* : Dᵇctf(X) ⥤ Dᵇctf(Y)` along a proper morphism of geometric
schemes. -/
noncomputable abbrev lowerStarCtf (f : X ⟶ Y) (hf : IsGeometricHom s f) [IsProper f] :
    Ctf A X ⥤ Ctf A Y :=
  ctfLowerStar f fun _ hK ↦ G.ctf_lowerStar f hf hK

/-- Blueprint `sk-prop-sf-existence` (c): the exceptional adjunction `Rf_! ⊣ Rf^!` between the
categories `Dᵇctf` of geometric schemes. -/
noncomputable abbrev exceptionalAdjunction (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f] : G.lowerShriekCtf f hf ⊣ G.upperShriekCtf f hf :=
  ctfExceptionalAdjunction f _ _

/-- The counit `Rf_! Rf^! L ⟶ L` of the exceptional adjunction at `L ∈ Dᵇctf(Y)`, as a
morphism of `D(Y, A)`. -/
noncomputable def exceptionalCounit (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f] (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (hL : G.ctf Y L) :
    (rightDerivedLowerShriek A f).obj ((rightDerivedUpperShriek A f).obj L) ⟶ L :=
  ((G.exceptionalAdjunction f hf).counit.app ⟨L, hL⟩).hom

/-- The exceptional adjunction `Hom(Rf_! K, L) ≃ Hom(K, Rf^! L)` for `K ∈ Dᵇctf(X)` and
`L ∈ Dᵇctf(Y)`, as a bijection of `Hom`-sets of `D(X, A)` and `D(Y, A)`. -/
noncomputable def exceptionalHomEquiv (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hL : G.ctf Y L) :
    ((rightDerivedLowerShriek A f).obj K ⟶ L) ≃ (K ⟶ (rightDerivedUpperShriek A f).obj L) :=
  (G.ctf Y).fullyFaithfulι.homEquiv.symm.trans
    (((G.exceptionalAdjunction f hf).homEquiv ⟨K, hK⟩ ⟨L, hL⟩).trans
      (G.ctf X).fullyFaithfulι.homEquiv)

/-- The exceptional adjunction `Hom(Rf_! K, L) ≃ Hom(K, Rf^! L)` is natural in `L`. -/
lemma exceptionalHomEquiv_naturality_right (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K)
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hL : G.ctf Y L)
    (hL' : G.ctf Y L') (φ : (rightDerivedLowerShriek A f).obj K ⟶ L) (g : L ⟶ L') :
    G.exceptionalHomEquiv f hf hK hL' (φ ≫ g) =
      G.exceptionalHomEquiv f hf hK hL φ ≫ (rightDerivedUpperShriek A f).map g :=
  congrArg (·.hom) ((G.exceptionalAdjunction f hf).homEquiv_naturality_right
    (X := ⟨K, hK⟩) (Y := ⟨L, hL⟩) (Y' := ⟨L', hL'⟩) (ObjectProperty.homMk φ)
    (ObjectProperty.homMk g))

/-- The exceptional adjunction `Hom(Rf_! K, L) ≃ Hom(K, Rf^! L)` is natural in `K`. -/
lemma exceptionalHomEquiv_naturality_left (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f]
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K)
    (hK' : G.ctf X K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hL : G.ctf Y L)
    (g : K ⟶ K') (φ : (rightDerivedLowerShriek A f).obj K' ⟶ L) :
    G.exceptionalHomEquiv f hf hK hL ((rightDerivedLowerShriek A f).map g ≫ φ) =
      g ≫ G.exceptionalHomEquiv f hf hK' hL φ :=
  congrArg (·.hom) ((G.exceptionalAdjunction f hf).homEquiv_naturality_left
    (X' := ⟨K, hK⟩) (X := ⟨K', hK'⟩) (Y := ⟨L, hL⟩) (ObjectProperty.homMk g)
    (ObjectProperty.homMk φ))

/-- The exceptional adjunction sends the counit `Rf_! Rf^! L ⟶ L` to the identity. -/
@[simp]
lemma exceptionalHomEquiv_exceptionalCounit (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f]
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hL : G.ctf Y L) :
    G.exceptionalHomEquiv f hf (G.ctf_upperShriek f hf hL) hL
        (G.exceptionalCounit f hf L hL) = 𝟙 _ := by
  have h : (G.exceptionalAdjunction f hf).homEquiv _ ⟨L, hL⟩
      ((G.exceptionalAdjunction f hf).counit.app ⟨L, hL⟩) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id, Equiv.apply_symm_apply]
  exact congrArg (·.hom) h

end GeometricCoefficients

/-- A braiding on the derived category `D(X, A)` of the pro-étale site of every scheme `X`.
This project does not yet construct the braiding induced by that of `A`; the class makes the
braidings of all the `D(X, A)` one choice, supplied by a global instance.

This class is a temporary stand-in. It should be removed once the braiding on `D(X, A)`
induced from the symmetric structure of `A` (with the Koszul signs on complexes) is
constructed, and the global instance below may then conflict with that canonical instance.
The trace statements of this block are only correct for the Koszul-sign braiding: for the
unsigned braiding `tr(𝟙 ∣ A_X[1]) = +1` instead of `-1`. The field
`braiding_unit_shift_one` pins that sign: the braiding of `A_X[1]` with itself is `-1`. -/
class DerivedBraiding where
  /-- the braiding on `D(X, A)`. -/
  braidedCategory (X : Scheme.{u}) :
    BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
  /-- the Koszul sign: the braiding of `A_X[1]` with itself is `-1`. -/
  braiding_unit_shift_one (X : Scheme.{u}) :
    letI := braidedCategory X
    (β_ ((𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))⟦(1 : ℤ)⟧)
      ((𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)))⟦(1 : ℤ)⟧)).hom = -𝟙 _

instance [DerivedBraiding A] (X : Scheme.{u}) :
    BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  DerivedBraiding.braidedCategory X

variable [DerivedBraiding A]

/-- The Künneth-Verdier map `pX^* M ⊗ᴸ pY^* RHom(N, ω) ⟶ RHom(pY^* N, pX^! M)` for
morphisms `pX : Z ⟶ X`, `pY : Z ⟶ Y`, assembled from a monoidal structure `μ` of `LpY^*`,
a projection formula `pf` for `pX` on `Dᵇctf` and an *exceptional trace*
`t : RpX_! pY^* ω ⟶ A_X`: the tensor-hom adjoint of

```
  pY^* N ⊗ᴸ (pX^* M ⊗ᴸ pY^* RHom(N, ω)) ≃ pX^* M ⊗ᴸ pY^* (N ⊗ᴸ RHom(N, ω))
      ──ev──▶ pX^* M ⊗ᴸ pY^* ω ──▶ pX^! M,
```

whose last map is the exceptional adjoint of
`RpX_! (pX^* M ⊗ᴸ pY^* ω) ≃ RpX_! pY^* ω ⊗ᴸ M ──t──▶ A_X ⊗ᴸ M ≃ M`, for the exceptional
adjunction at the objects `pX^* M ⊗ᴸ pY^* ω` and `M` of `Dᵇctf`.
`GeometricOperations.kunnethVerdierMap` instantiates it with the package data. -/
noncomputable def kunnethVerdierMapOf {X Y Z : Scheme.{u}} {pX : Z ⟶ X} {pY : Z ⟶ Y}
    [HasCompactification pX]
    (h₁ : ∀ K, DerivedCategory.constructibleFiniteTor A Z K →
      DerivedCategory.constructibleFiniteTor A X ((rightDerivedLowerShriek A pX).obj K))
    (h₂ : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
      DerivedCategory.constructibleFiniteTor A Z (((upperStar A pX).leftDerivedFunctor).obj K))
    {ω : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (μ : ((upperStar A pY).leftDerivedFunctor).CoreMonoidal)
    (pf : ((ctfLowerShriek pX h₁ ⋙ (DerivedCategory.constructibleFiniteTor A X).ι).prod
          (DerivedCategory.constructibleFiniteTor A X).ι) ⋙
        MonoidalCategory.tensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) ≅
      ((DerivedCategory.constructibleFiniteTor A Z).ι.prod
          (ctfUpperStar pX h₂ ⋙ (DerivedCategory.constructibleFiniteTor A Z).ι)) ⋙
        MonoidalCategory.tensor (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) ⋙
          rightDerivedLowerShriek A pX)
    (t : (rightDerivedLowerShriek A pX).obj (((upperStar A pY).leftDerivedFunctor).obj ω) ⟶
      𝟙_ _)
    (hω : DerivedCategory.constructibleFiniteTor A Z (((upperStar A pY).leftDerivedFunctor).obj ω))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (hM : DerivedCategory.constructibleFiniteTor A X M)
    (hMω : DerivedCategory.constructibleFiniteTor A Z
      (((upperStar A pX).leftDerivedFunctor).obj M ⊗
        ((upperStar A pY).leftDerivedFunctor).obj ω))
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((upperStar A pX).leftDerivedFunctor).obj M ⊗
        ((upperStar A pY).leftDerivedFunctor).obj ((ihom N).obj ω) ⟶
      (ihom (((upperStar A pY).leftDerivedFunctor).obj N)).obj
        ((rightDerivedUpperShriek A pX).obj M) :=
  MonoidalClosed.curry <|
    (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫
      (_ ◁ ((μ.μIso N ((ihom N).obj ω)).hom ≫
        ((upperStar A pY).leftDerivedFunctor).map ((ihom.ev N).app ω))) ≫
      rightDerivedUpperShriekHomEquiv pX hMω.plusEtaleOrigin hM.plus
        ((rightDerivedLowerShriek A pX).map (β_ _ _).hom ≫
          pf.inv.app (⟨_, hω⟩, ⟨M, hM⟩) ≫ (t ▷ M) ≫ (λ_ M).hom)

/-- The geometric operation package over a base `s` (blueprint: `sk-d-six`): the comparison data
of the six operations that the blueprint fixes, on the categories `Dᵇctf` of geometric schemes
over `s`, namely the dualizing complex `ω_X = a_X^! A` with its composition `f^! ω_Y ≃ ω_X`,
the identification `Rf_* = Rf_!` for proper `f`, composition of exceptional direct images,
`!`-base change, the projection formula, the monoidal structure of the pullback `Lf^*`, braided
for `DerivedBraiding`, and the invertibility of two canonical maps: the biduality map
`K ⟶ D_X D_X K` on `Dᵇctf`, and the Künneth-Verdier map `kunnethVerdierMapOf`. The
identity isomorphism `R(𝟙 X)_! ≃ 𝟭` is tied to `lowerShriekComp` by unit axioms, and
`lowerShriekComp` is associative;
`properComparison`, `dualizingBase`, `dualizingComp` and the unit of `Lf^*` are tied to the
identity isomorphisms at `f = 𝟙`; `properComparison` and `dualizingComp`
are compatible with composition, and `baseChange` with vertical pasting.

The functors and the two adjunctions are *not* fields: they are the pro-étale functors of
`WeilConjectures.SixFunctors.ProEtale`, listed in the module docstring, and the exceptional
adjunction on `Dᵇctf` is a theorem (`GeometricCoefficients.exceptionalAdjunction`). -/
structure GeometricOperations (s : Scheme.{u}) extends GeometricCoefficients A s where
  /-- the dualizing complex `ω_X = a_X^! A` of a scheme `a : X ⟶ s`. -/
  dualizing {X : Scheme.{u}} (a : X ⟶ s) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)
  /-- `ω_X` is `a_X^! A` whenever `a_X` admits a compactification. -/
  dualizingIso {X : Scheme.{u}} (a : X ⟶ s) [HasCompactification a] :
    dualizing a ≅ (rightDerivedUpperShriek A a).obj (𝟙_ _)
  /-- `ω_X` lies in `Dᵇctf(X)` for a geometric `X`. -/
  ctf_dualizing {X : Scheme.{u}} (a : X ⟶ s) [IsGeometric a] :
    DerivedCategory.constructibleFiniteTor A X (dualizing a)
  /-- the normalisation `ω_s ≃ A_s` of the dualizing complex of the base. -/
  dualizingBase :
    dualizing (𝟙 s) ≅ 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))
  /-- dualizing composition: `f^! ω_Y ≃ ω_X`. -/
  dualizingComp {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Y ⟶ s) [IsGeometric a]
      [IsGeometric (f ≫ a)] [HasCompactification f] :
    (rightDerivedUpperShriek A f).obj (dualizing a) ≅ dualizing (f ≫ a)
  /-- `Rf_* = Rf_!` for proper `f`, on `Dᵇctf`. -/
  properComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsGeometricHom s f)
      [HasCompactification f] [IsProper f] :
    toGeometricCoefficients.lowerShriekCtf f hf ≅ toGeometricCoefficients.lowerStarCtf f hf
  /-- composition of the exceptional direct images: `Rf_! ⋙ Rg_! ≃ R(f ≫ g)_!` on `Dᵇctf`. -/
  lowerShriekComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsGeometricHom s f)
      (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g)) [HasCompactification f]
      [HasCompactification g] [HasCompactification (f ≫ g)] :
    toGeometricCoefficients.lowerShriekCtf f hf ⋙ toGeometricCoefficients.lowerShriekCtf g hg ≅
      toGeometricCoefficients.lowerShriekCtf (f ≫ g) hfg
  /-- the identity isomorphism of the exceptional direct image: `R(𝟙 X)_! ≃ 𝟭` on `Dᵇctf`. -/
  lowerShriekId (X : Scheme.{u}) (hX : IsGeometricHom s (𝟙 X)) :
    toGeometricCoefficients.lowerShriekCtf (𝟙 X) hX ≅ 𝟭 (Ctf A X)
  /-- left unit axiom: `lowerShriekComp (𝟙 X) f` is `lowerShriekId` whiskered by `Rf_!`,
  that is, the square

  ```
    R(𝟙 X)_! ⋙ Rf_! ──lowerShriekComp (𝟙 X) f──▶ R(𝟙 X ≫ f)_!
          │                                           │
    lowerShriekId ◫ Rf_!                 ctfLowerShriekCongr (id_comp f)
          ▼                                           ▼
       𝟭 ⋙ Rf_!  ──────────── leftUnitor ──────────▶ Rf_!
  ```

  commutes. -/
  lowerShriekComp_id_left {X Y : Scheme.{u}} (f : X ⟶ Y) (hX : IsGeometricHom s (𝟙 X))
      (hf : IsGeometricHom s f) (hf' : IsGeometricHom s (𝟙 X ≫ f)) [HasCompactification f]
      [HasCompactification (𝟙 X ≫ f)] :
    lowerShriekComp (𝟙 X) f hX hf hf' =
      Functor.isoWhiskerRight (lowerShriekId X hX) _ ≪≫ Functor.leftUnitor _ ≪≫
        ctfLowerShriekCongr (Category.id_comp f).symm _ _
  /-- right unit axiom: `lowerShriekComp f (𝟙 Y)` is `lowerShriekId` whiskered by `Rf_!`,
  that is, the square

  ```
    Rf_! ⋙ R(𝟙 Y)_! ──lowerShriekComp f (𝟙 Y)──▶ R(f ≫ 𝟙 Y)_!
          │                                           │
    Rf_! ◫ lowerShriekId                 ctfLowerShriekCongr (comp_id f)
          ▼                                           ▼
       Rf_! ⋙ 𝟭  ──────────── rightUnitor ─────────▶ Rf_!
  ```

  commutes. -/
  lowerShriekComp_id_right {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsGeometricHom s (𝟙 Y))
      (hf : IsGeometricHom s f) (hf' : IsGeometricHom s (f ≫ 𝟙 Y)) [HasCompactification f]
      [HasCompactification (f ≫ 𝟙 Y)] :
    lowerShriekComp f (𝟙 Y) hf hY hf' =
      Functor.isoWhiskerLeft _ (lowerShriekId Y hY) ≪≫ Functor.rightUnitor _ ≪≫
        ctfLowerShriekCongr (Category.comp_id f).symm _ _
  /-- associativity of the composition isomorphisms of the exceptional direct images: for
  `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ W`, the two isomorphisms
  `Rh_! Rg_! Rf_! ≃ R((f ≫ g) ≫ h)_!` built from `lowerShriekComp` agree at every object of
  `Dᵇctf(X)`, that is, the square

  ```
    Rh_! Rg_! Rf_! ──Rh_! (lowerShriekComp f g)──▶ Rh_! R(f ≫ g)_!
          │                                              │
    lowerShriekComp g h                     lowerShriekComp (f ≫ g) h
          ▼                                              ▼
    R(g ≫ h)_! Rf_! ──lowerShriekComp f (g ≫ h)──▶ R(f ≫ g ≫ h)_! = R((f ≫ g) ≫ h)_!
  ```

  commutes (blueprint `def-trf-global-operator`, item 3: the composition law is an
  isomorphism of functors with the associativity compatibility). -/
  lowerShriekComp_assoc {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (hf : IsGeometricHom s f) (hg : IsGeometricHom s g) (hh : IsGeometricHom s h)
      (hfg : IsGeometricHom s (f ≫ g)) (hgh : IsGeometricHom s (g ≫ h))
      (hfgh : IsGeometricHom s (f ≫ g ≫ h)) (hfgh' : IsGeometricHom s ((f ≫ g) ≫ h))
      [HasCompactification f] [HasCompactification g] [HasCompactification h]
      [HasCompactification (f ≫ g)] [HasCompactification (g ≫ h)]
      [HasCompactification (f ≫ g ≫ h)] [HasCompactification ((f ≫ g) ≫ h)] (K : Ctf A X) :
    (rightDerivedLowerShriek A h).map ((lowerShriekComp f g hf hg hfg).hom.app K).hom ≫
        ((lowerShriekComp (f ≫ g) h hfg hh hfgh').hom.app K).hom =
      ((lowerShriekComp g h hg hh hgh).hom.app
          ((toGeometricCoefficients.lowerShriekCtf f hf).obj K)).hom ≫
        ((lowerShriekComp f (g ≫ h) hf hgh hfgh).hom.app K).hom ≫
        ((ctfLowerShriekCongr (Category.assoc f g h).symm
          (fun _ hK ↦ toGeometricCoefficients.ctf_lowerShriek _ hfgh hK)
          (fun _ hK ↦ toGeometricCoefficients.ctf_lowerShriek _ hfgh' hK)).hom.app K).hom
  /-- for `f = 𝟙 X`, `properComparison` is the composite
  `R(𝟙 X)_! ≃ 𝟭 ≃ R(𝟙 X)_*` of `lowerShriekId` and the identity isomorphism of `R(𝟙 X)_*`,
  the conjugate of `leftDerivedUpperStarId`, at every object of `Dᵇctf(X)`. -/
  properComparison_id (X : Scheme.{u}) (hX : IsGeometricHom s (𝟙 X)) (K : Ctf A X) :
    ((properComparison (𝟙 X) hX).hom.app K).hom = ((lowerShriekId X hX).hom.app K).hom ≫
      (conjugateIsoEquiv Adjunction.id (derivedUpperStarLowerStarAdjunction A (𝟙 X))
        (leftDerivedUpperStarId A X)).hom.app K.obj
  /-- the normalisation `ω_s ≃ A_s` is `ω_s ≃ (𝟙 s)^! A_s ≃ A_s`, the second map being the
  identity isomorphism of `(𝟙 s)^!` on `Dᵇctf`, the conjugate of `lowerShriekId`. -/
  dualizingBase_eq :
    dualizingBase = dualizingIso (𝟙 s) ≪≫
      (DerivedCategory.constructibleFiniteTor A s).ι.mapIso
        (X := (toGeometricCoefficients.upperShriekCtf (𝟙 s) (.id (𝟙 s))).obj
          ⟨𝟙_ _, toGeometricCoefficients.ctf_unit (.id (𝟙 s))⟩)
        (Y := ⟨𝟙_ _, toGeometricCoefficients.ctf_unit (.id (𝟙 s))⟩)
        ((conjugateIsoEquiv Adjunction.id
          (toGeometricCoefficients.exceptionalAdjunction (𝟙 s) (.id (𝟙 s)))
          (lowerShriekId s (.id (𝟙 s)))).symm.app
            ⟨𝟙_ _, toGeometricCoefficients.ctf_unit (.id (𝟙 s))⟩)
  /-- for `f = 𝟙 X`, `dualizingComp` is `(𝟙 X)^! ω_X ≃ ω_X`, the identity isomorphism of
  `(𝟙 X)^!` on `Dᵇctf` (the conjugate of `lowerShriekId`), transported along `𝟙 X ≫ a = a`. -/
  dualizingComp_id {X : Scheme.{u}} (a : X ⟶ s) [IsGeometric a] :
    dualizingComp (𝟙 X) a =
      (DerivedCategory.constructibleFiniteTor A X).ι.mapIso
        (X := (toGeometricCoefficients.upperShriekCtf (𝟙 X) (.id a)).obj
          ⟨dualizing a, ctf_dualizing a⟩) (Y := ⟨dualizing a, ctf_dualizing a⟩)
        ((conjugateIsoEquiv Adjunction.id
          (toGeometricCoefficients.exceptionalAdjunction (𝟙 X) (.id a))
          (lowerShriekId X (.id a))).symm.app ⟨dualizing a, ctf_dualizing a⟩) ≪≫
        eqToIso (congrArg dualizing (Category.id_comp a).symm)
  /-- `properComparison` is compatible with composition: for proper `f` and `g`,
  `properComparison (f ≫ g)` is, at every object of `Dᵇctf(X)`, the composite

  ```
    R(f ≫ g)_! ≃ Rf_! ⋙ Rg_! ≃ Rf_* ⋙ Rg_! ≃ Rf_* ⋙ Rg_* ≃ R(f ≫ g)_*
  ```

  of `lowerShriekComp f g`, `properComparison f`, `properComparison g` and the composition
  isomorphism of `R(-)_*`, the conjugate of `leftDerivedUpperStarComp`. -/
  properComparison_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsGeometricHom s f)
      (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g)) [HasCompactification f]
      [HasCompactification g] [HasCompactification (f ≫ g)] [IsProper f] [IsProper g]
      (K : Ctf A X) :
    ((properComparison (f ≫ g) hfg).hom.app K).hom =
      ((lowerShriekComp f g hf hg hfg).inv.app K).hom ≫
        (rightDerivedLowerShriek A g).map ((properComparison f hf).hom.app K).hom ≫
        ((properComparison g hg).hom.app ((toGeometricCoefficients.lowerStarCtf f hf).obj K)).hom ≫
        (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction A (f ≫ g))
          ((derivedUpperStarLowerStarAdjunction A g).comp
            (derivedUpperStarLowerStarAdjunction A f))
          (leftDerivedUpperStarComp A f g).symm).inv.app K.obj
  /-- `dualizingComp` is compatible with composition: `dualizingComp (f ≫ g) a` is the
  composite

  ```
    (f ≫ g)^! ω_a ≃ f^! g^! ω_a ≃ f^! ω_{g ≫ a} ≃ ω_{f ≫ g ≫ a}
  ```

  of the composition isomorphism of `(-)^!` on `Dᵇctf` (the conjugate of `lowerShriekComp f g`),
  `dualizingComp g a` and `dualizingComp f (g ≫ a)`, transported along associativity. -/
  dualizingComp_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : Z ⟶ s)
      [IsGeometric a] [IsGeometric (g ≫ a)] [IsGeometric (f ≫ g ≫ a)]
      [IsGeometric ((f ≫ g) ≫ a)] [HasCompactification f] [HasCompactification g]
      [HasCompactification (f ≫ g)] :
    dualizingComp (f ≫ g) a =
      (DerivedCategory.constructibleFiniteTor A X).ι.mapIso
          (X := (toGeometricCoefficients.upperShriekCtf (f ≫ g) (.mk (aY := a) rfl)).obj
            ⟨dualizing a, ctf_dualizing a⟩)
          (Y := (toGeometricCoefficients.upperShriekCtf f (.mk (aY := g ≫ a) rfl)).obj
            ((toGeometricCoefficients.upperShriekCtf g (.mk (aY := a) rfl)).obj
              ⟨dualizing a, ctf_dualizing a⟩))
          ((conjugateIsoEquiv
            (toGeometricCoefficients.exceptionalAdjunction (f ≫ g) (.mk (aY := a) rfl))
            ((toGeometricCoefficients.exceptionalAdjunction f (.mk (aY := g ≫ a) rfl)).comp
              (toGeometricCoefficients.exceptionalAdjunction g (.mk (aY := a) rfl)))
            (lowerShriekComp f g (.mk (aY := g ≫ a) rfl) (.mk (aY := a) rfl)
              (.mk (aY := a) rfl))).app ⟨dualizing a, ctf_dualizing a⟩) ≪≫
        (rightDerivedUpperShriek A f).mapIso (dualizingComp g a) ≪≫ dualizingComp f (g ≫ a) ≪≫
        eqToIso (congrArg dualizing (Category.assoc f g a).symm)
  /-- `properComparison` is compatible with the shifts: the identification `Rf_! ≃ Rf_*` at
  `K⟦n⟧` is, through the commutation of `Rf_!` and `Rf_*` with the shift, the shift of the
  identification at `K`. The two functors are triangulated and the identification is one of
  triangulated functors. -/
  properComparison_commShift {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsGeometricHom s f)
      [HasCompactification f] [IsProper f] (K : Ctf A X) (n : ℤ) :
    ((properComparison f hf).hom.app
          ⟨K.obj⟦n⟧, ProEtale.DerivedCategory.constructibleFiniteTor.shift K.property n⟩).hom ≫
        (((lowerStar A f).rightDerivedFunctor).commShiftIso n).hom.app K.obj =
      ((rightDerivedLowerShriek A f).commShiftIso n).hom.app K.obj ≫
        ((properComparison f hf).hom.app K).hom⟦n⟧'
  /-- `lowerShriekComp` is compatible with the shifts: the composition `Rg_! Rf_! ≃ R(f ≫ g)_!`
  at `K⟦n⟧` is, through the commutation of the functors with the shift, the shift of the
  composition at `K`. The functors are triangulated and the composition is an isomorphism of
  triangulated functors. -/
  lowerShriekComp_commShift {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (hf : IsGeometricHom s f) (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g))
      [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
      (K : Ctf A X) (n : ℤ) :
    ((lowerShriekComp f g hf hg hfg).hom.app
          ⟨K.obj⟦n⟧, ProEtale.DerivedCategory.constructibleFiniteTor.shift K.property n⟩).hom ≫
        ((rightDerivedLowerShriek A (f ≫ g)).commShiftIso n).hom.app K.obj =
      (rightDerivedLowerShriek A g).map
          (((rightDerivedLowerShriek A f).commShiftIso n).hom.app K.obj) ≫
        ((rightDerivedLowerShriek A g).commShiftIso n).hom.app
          ((rightDerivedLowerShriek A f).obj K.obj) ≫
        ((lowerShriekComp f g hf hg hfg).hom.app K).hom⟦n⟧'
  /-- `!`-base change along a Cartesian square of geometric schemes: `Lg^* Rf_! ≃ Rf'_! Lg'^*`
  on `Dᵇctf`, for

  ```
     X' ──g'──→ X
     │          │
   f'│          │f
     ↓          ↓
     Y' ──g───→ Y
  ```
  -/
  baseChange {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (sq : IsPullback g' f' f g) (hf : IsGeometricHom s f) (hg : IsGeometricHom s g)
      (hf' : IsGeometricHom s f') (hg' : IsGeometricHom s g') [HasCompactification f]
      [HasCompactification f'] :
    toGeometricCoefficients.lowerShriekCtf f hf ⋙ toGeometricCoefficients.upperStarCtf g hg ≅
      toGeometricCoefficients.upperStarCtf g' hg' ⋙ toGeometricCoefficients.lowerShriekCtf f' hf'
  /-- `!`-base change is compatible with vertical pasting of Cartesian squares: for

  ```
     X' ──g_X──→ X
     │           │
   f'│           │f
     ↓           ↓
     Y' ──g_Y──→ Y
     │           │
   h'│           │h
     ↓           ↓
     Z' ──g_Z──→ Z
  ```

  the base change of the outer square is the composite of the two base changes, read through
  `lowerShriekComp f h` and `lowerShriekComp f' h'`. -/
  baseChange_paste_vert {X' X Y' Y Z' Z : Scheme.{u}} {gX : X' ⟶ X} {f' : X' ⟶ Y'}
      {f : X ⟶ Y} {gY : Y' ⟶ Y} {h' : Y' ⟶ Z'} {h : Y ⟶ Z} {gZ : Z' ⟶ Z}
      (sq₁ : IsPullback gX f' f gY) (sq₂ : IsPullback gY h' h gZ) (hf : IsGeometricHom s f)
      (hh : IsGeometricHom s h) (hf' : IsGeometricHom s f') (hh' : IsGeometricHom s h')
      (hgX : IsGeometricHom s gX) (hgY : IsGeometricHom s gY) (hgZ : IsGeometricHom s gZ)
      (hfh : IsGeometricHom s (f ≫ h)) (hfh' : IsGeometricHom s (f' ≫ h'))
      [HasCompactification f] [HasCompactification f'] [HasCompactification h]
      [HasCompactification h'] [HasCompactification (f ≫ h)] [HasCompactification (f' ≫ h')] :
    baseChange (sq₁.paste_vert sq₂) hfh hgZ hfh' hgX =
      Functor.isoWhiskerRight (lowerShriekComp f h hf hh hfh).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (baseChange sq₂ hh hgZ hh' hgY) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (baseChange sq₁ hf hgY hf' hgX) _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (lowerShriekComp f' h' hf' hh' hfh')
  /-- the projection formula `Rf_! K ⊗ᴸ L ≃ Rf_! (K ⊗ᴸ Lf^* L)`, as an isomorphism of
  bifunctors `Dᵇctf(X, A) × Dᵇctf(Y, A) ⥤ D(Y, A)`. -/
  projectionFormula {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsGeometricHom s f)
      [HasCompactification f] :
    ((toGeometricCoefficients.lowerShriekCtf f hf ⋙
          (DerivedCategory.constructibleFiniteTor A Y).ι).prod
        (DerivedCategory.constructibleFiniteTor A Y).ι) ⋙
        MonoidalCategory.tensor (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) ≅
      ((DerivedCategory.constructibleFiniteTor A X).ι.prod
          (toGeometricCoefficients.upperStarCtf f hf ⋙
            (DerivedCategory.constructibleFiniteTor A X).ι)) ⋙
        MonoidalCategory.tensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) ⋙
          rightDerivedLowerShriek A f
  /-- `Lf^*` is monoidal: the unit `A_X ≃ Lf^* A_Y` and the tensor comparison
  `Lf^* M ⊗ᴸ Lf^* N ≃ Lf^* (M ⊗ᴸ N)`, with their naturality, associativity and unitality. This
  holds on the whole derived category (see the module docstring). -/
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
  /-- biduality on `Dᵇctf`: the evaluation-adjoint map `K ⟶ D_X D_X K`, the tensor-hom
  adjoint of `RHom(K, ω_X) ⊗ᴸ K ≃ K ⊗ᴸ RHom(K, ω_X) ──ev──▶ ω_X`, is invertible. -/
  isIso_bidualityMap {X : Scheme.{u}} (a : X ⟶ s) [IsGeometric a]
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
      (hK : DerivedCategory.constructibleFiniteTor A X K) :
    IsIso (MonoidalClosed.curry
      ((β_ ((ihom K).obj (dualizing a)) K).hom ≫ (ihom.ev K).app (dualizing a)))
  /-- Künneth-Verdier: for `X` and `Y` separated of finite type over a field `s = Spec k`,
  `M ∈ Dᵇctf(X)` and `N ∈ Dᵇctf(Y)`, the canonical map
  `κ_{M,N} : M ⊠ D_Y N ⟶ RHom(p_Y^* N, p_X^! M)` is invertible
  (blueprint `sk-thm-sf-kunneth-verdier`). The map is `kunnethVerdierMapOf` for the monoidal
  structure of `Lp_Y^*`, the projection formula for `p_X` and the exceptional trace

  ```
    Rp_{X!} p_Y^* ω_Y ≃ a_X^* Ra_{Y!} ω_Y ≃ a_X^* Ra_{Y!} a_Y^! A ──ε──▶ a_X^* A ≃ A_X
  ```

  built from `!`-base change, `dualizingIso`, the counit of `Ra_{Y!} ⊣ a_Y^!` and the unit of
  `Lf^*`. It is stated for every Cartesian square over `s`, so that both orientations are
  available on `pullback aY aX`. -/
  isIso_kunnethVerdierMap {Z X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s} {pX : Z ⟶ X}
      {pY : Z ⟶ Y} [s.IsSpecOfField] [IsGeometric aX] [IsGeometric aY] [IsGeometric (pX ≫ aX)]
      [HasCompactification aX] [HasCompactification aY]
      (sq : IsPullback pX pY aX aY) [HasCompactification pX]
      (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
      (hM : DerivedCategory.constructibleFiniteTor A X M)
      (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
      (hN : DerivedCategory.constructibleFiniteTor A Y N) :
    haveI : IsGeometric (pY ≫ aY) := IsGeometric.of_eq sq.w
    IsIso (kunnethVerdierMapOf A
      (fun _ hK ↦ toGeometricCoefficients.ctf_lowerShriek pX (.mk (aY := aX) rfl) hK)
      (fun _ hK ↦ toGeometricCoefficients.ctf_upperStar pX (.mk (aY := aX) rfl) hK)
      (upperStarMonoidal pY) (projectionFormula pX (.mk (aY := aX) rfl))
      (((baseChange sq.flip (.of_isGeometric aY) (.of_isGeometric aX) (.mk (aY := aX) rfl)
          (.mk (aY := aY) rfl)).inv.app ⟨dualizing aY, ctf_dualizing aY⟩).hom ≫
        ((upperStar A aX).leftDerivedFunctor).map
          ((rightDerivedLowerShriek A aY).map (dualizingIso aY).hom ≫
            toGeometricCoefficients.exceptionalCounit aY (.of_isGeometric aY) (𝟙_ _)
              (toGeometricCoefficients.ctf_unit (.id (𝟙 s)))) ≫
        (upperStarMonoidal aX).εIso.inv)
      (toGeometricCoefficients.ctf_upperStar pY (.mk (aY := aY) rfl) (ctf_dualizing aY)) M hM
      (toGeometricCoefficients.ctf_tensor (.id (pX ≫ aX))
        (toGeometricCoefficients.ctf_upperStar pX (.mk (aY := aX) rfl) hM)
        (toGeometricCoefficients.ctf_upperStar pY (.mk (aY := aY) rfl) (ctf_dualizing aY)))
      N)

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

/-- The evaluation-adjoint map `K ⟶ D_X D_X K`: the tensor-hom adjoint of
`D_X K ⊗ᴸ K ≃ K ⊗ᴸ D_X K ──ev──▶ ω_X`. -/
noncomputable def bidualityMap {X : Scheme.{u}} (a : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    K ⟶ G.verdierDual a (G.verdierDual a K) :=
  MonoidalClosed.curry ((β_ (G.verdierDual a K) K).hom ≫ (ihom.ev K).app (G.dualizing a))

/-- Transport of the dualizing complex along an equality of structure morphisms:
`ω_a ≅ ω_b` for `a = b`. -/
noncomputable def dualizingCongr {X : Scheme.{u}} {a b : X ⟶ s} (h : a = b) :
    G.dualizing a ≅ G.dualizing b :=
  eqToIso (congrArg G.dualizing h)

@[simp]
lemma dualizingCongr_rfl {X : Scheme.{u}} {a : X ⟶ s} :
    G.dualizingCongr (rfl : a = a) = Iso.refl _ :=
  rfl

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

/-- The inverse form of the field `properComparison_id`. -/
lemma properComparison_id_inv_app_hom (X : Scheme.{u}) (hX : IsGeometricHom s (𝟙 X))
    (K : Ctf A X) :
    ((G.properComparison (𝟙 X) hX).inv.app K).hom =
      (conjugateIsoEquiv Adjunction.id (derivedUpperStarLowerStarAdjunction A (𝟙 X))
          (leftDerivedUpperStarId A X)).inv.app K.obj ≫
        ((G.lowerShriekId X hX).inv.app K).hom := by
  rw [← cancel_epi ((G.properComparison (𝟙 X) hX).hom.app K).hom,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app, G.properComparison_id,
    Category.assoc, Iso.hom_inv_id_app_assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.hom_inv_id_app]

/-- The tensor comparison `Lf^* (M ⊗ᴸ N) ≃ Lf^* M ⊗ᴸ Lf^* N` of the pullback: the inverse of
the tensor map of the monoidal structure `GeometricOperations.upperStarMonoidal` of
`Lf^*`. -/
noncomputable def upperStarTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((upperStar A f).leftDerivedFunctor).obj (M ⊗ N) ≅
      ((upperStar A f).leftDerivedFunctor).obj M ⊗ ((upperStar A f).leftDerivedFunctor).obj N :=
  ((G.upperStarMonoidal f).μIso M N).symm

/-- The identity isomorphism `(𝟙 X)^! ≃ 𝟭` of the exceptional inverse image on `Dᵇctf`: the
conjugate of the field `lowerShriekId : R(𝟙 X)_! ≃ 𝟭` along the adjunctions
`R(𝟙 X)_! ⊣ (𝟙 X)^!` and `𝟭 ⊣ 𝟭`. -/
noncomputable def upperShriekId (X : Scheme.{u}) (hX : IsGeometricHom s (𝟙 X)) :
    G.upperShriekCtf (𝟙 X) hX ≅ 𝟭 (Ctf A X) :=
  (conjugateIsoEquiv Adjunction.id (G.exceptionalAdjunction (𝟙 X) hX) (G.lowerShriekId X hX)).symm

/-- Under the conjugation bijection between the adjunctions `R(𝟙 X)_! ⊣ (𝟙 X)^!` and
`𝟭 ⊣ 𝟭`, the identity isomorphism of the exceptional direct image corresponds to the inverse
of the identity isomorphism of the exceptional inverse image:

```
  R(𝟙 X)_! ⊣ (𝟙 X)^!        lowerShriekId : R(𝟙 X)_! ≅ 𝟭
       ↕ conjugate                   ↦
       𝟭 ⊣ 𝟭               upperShriekId.symm : 𝟭 ≅ (𝟙 X)^!
``` -/
@[simp]
lemma conjugateIsoEquiv_lowerShriekId (X : Scheme.{u}) (hX : IsGeometricHom s (𝟙 X)) :
    conjugateIsoEquiv Adjunction.id (G.exceptionalAdjunction (𝟙 X) hX) (G.lowerShriekId X hX) =
      (G.upperShriekId X hX).symm := by
  simp [upperShriekId]

/-- The identity isomorphism `K ≃ (𝟙 X)^! K` of the exceptional inverse image at an object of
`Dᵇctf(X)`, as an isomorphism of `D(X, A)`. -/
noncomputable def upperShriekIdIso (X : Scheme.{u}) (hX : IsGeometricHom s (𝟙 X))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : G.ctf X K) :
    K ≅ (rightDerivedUpperShriek A (𝟙 X)).obj K :=
  (DerivedCategory.constructibleFiniteTor A X).ι.mapIso (X := ⟨K, hK⟩)
    (Y := (G.upperShriekCtf (𝟙 X) hX).obj ⟨K, hK⟩) ((G.upperShriekId X hX).symm.app ⟨K, hK⟩)

/-- The composition isomorphism `(f ≫ g)^! ≃ g^! ⋙ f^!` of exceptional inverse images on
`Dᵇctf`: the conjugate of `GeometricOperations.lowerShriekComp` along the adjunctions
`R(f ≫ g)_! ⊣ (f ≫ g)^!` and `Rf_! ⋙ Rg_! ⊣ g^! ⋙ f^!`. -/
noncomputable def upperShriekComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsGeometricHom s f) (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g))
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    G.upperShriekCtf (f ≫ g) hfg ≅ G.upperShriekCtf g hg ⋙ G.upperShriekCtf f hf :=
  conjugateIsoEquiv (G.exceptionalAdjunction (f ≫ g) hfg)
    ((G.exceptionalAdjunction f hf).comp (G.exceptionalAdjunction g hg))
    (G.lowerShriekComp f g hf hg hfg)

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
    (hf : IsGeometricHom s f) (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g))
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    conjugateIsoEquiv (G.exceptionalAdjunction (f ≫ g) hfg)
        ((G.exceptionalAdjunction f hf).comp (G.exceptionalAdjunction g hg))
        (G.lowerShriekComp f g hf hg hfg) = G.upperShriekComp f g hf hg hfg :=
  rfl

/-- The composition isomorphism `f^! g^! L ≃ (f ≫ g)^! L` of exceptional inverse images at an
object `L` of `Dᵇctf(Z)`, as an isomorphism of `D(X, A)`. -/
noncomputable def upperShriekCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsGeometricHom s f) (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g))
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) (hL : G.ctf Z L) :
    (rightDerivedUpperShriek A f).obj ((rightDerivedUpperShriek A g).obj L) ≅
      (rightDerivedUpperShriek A (f ≫ g)).obj L :=
  (DerivedCategory.constructibleFiniteTor A X).ι.mapIso
    (X := (G.upperShriekCtf g hg ⋙ G.upperShriekCtf f hf).obj ⟨L, hL⟩)
    (Y := (G.upperShriekCtf (f ≫ g) hfg).obj ⟨L, hL⟩)
    ((G.upperShriekComp f g hf hg hfg).symm.app ⟨L, hL⟩)

/-- `GeometricOperations.upperShriekCompIso` is natural in `L`. -/
@[reassoc]
lemma upperShriekCompIso_hom_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsGeometricHom s f) (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g))
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)} (hL : G.ctf Z L)
    (hL' : G.ctf Z L') (φ : L ⟶ L') :
    (rightDerivedUpperShriek A f).map ((rightDerivedUpperShriek A g).map φ) ≫
        (G.upperShriekCompIso f g hf hg hfg L' hL').hom =
      (G.upperShriekCompIso f g hf hg hfg L hL).hom ≫
        (rightDerivedUpperShriek A (f ≫ g)).map φ :=
  congrArg (·.hom) ((G.upperShriekComp f g hf hg hfg).inv.naturality
    (X := ⟨L, hL⟩) (Y := ⟨L', hL'⟩) (ObjectProperty.homMk φ))

/-- The exceptional trace `Rp_{X!} p_Y^* ω_Y ⟶ A_X` of a Cartesian square `Z = X ×_s Y`: the
composite

```
  Rp_{X!} p_Y^* ω_Y ≃ a_X^* Ra_{Y!} ω_Y ≃ a_X^* Ra_{Y!} a_Y^! A ──ε──▶ a_X^* A ≃ A_X
```

of `!`-base change, `dualizingIso`, the counit of `Ra_{Y!} ⊣ a_Y^!` and `upperStarUnit`. -/
noncomputable def exceptionalTrace {Z X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
    {pX : Z ⟶ X} {pY : Z ⟶ Y} [IsGeometric aX] [IsGeometric aY] [IsGeometric (pX ≫ aX)]
    [HasCompactification aY] (sq : IsPullback pX pY aX aY) [HasCompactification pX] :
    (rightDerivedLowerShriek A pX).obj (((upperStar A pY).leftDerivedFunctor).obj
        (G.dualizing aY)) ⟶ 𝟙_ _ :=
  haveI : IsGeometric (pY ≫ aY) := IsGeometric.of_eq sq.w
  ((G.baseChange sq.flip (.of_isGeometric aY) (.of_isGeometric aX) (.mk (aY := aX) rfl)
      (.mk (aY := aY) rfl)).inv.app ⟨G.dualizing aY, G.ctf_dualizing aY⟩).hom ≫
    ((upperStar A aX).leftDerivedFunctor).map
      ((rightDerivedLowerShriek A aY).map (G.dualizingIso aY).hom ≫
        G.exceptionalCounit aY (.of_isGeometric aY) (𝟙_ _) (G.ctf_unit (.id (𝟙 s)))) ≫
    (G.upperStarUnit aX).hom

/-- The Künneth-Verdier map `κ_{M,N} : p_X^* M ⊗ᴸ p_Y^* D_Y N ⟶ RHom(p_Y^* N, p_X^! M)` of a
Cartesian square `Z = X ×_s Y` and `M ∈ Dᵇctf(X)`: `kunnethVerdierMapOf` for the monoidal
structure of `Lp_Y^*`, the projection formula for `p_X` and
`GeometricOperations.exceptionalTrace` (part of blueprint `sk-thm-sf-kunneth-verdier`). -/
noncomputable def kunnethVerdierMap {Z X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
    {pX : Z ⟶ X} {pY : Z ⟶ Y} [IsGeometric aX] [IsGeometric aY] [IsGeometric (pX ≫ aX)]
    [HasCompactification aY] (sq : IsPullback pX pY aX aY) [HasCompactification pX]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hM : G.ctf X M)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((upperStar A pX).leftDerivedFunctor).obj M ⊗
        ((upperStar A pY).leftDerivedFunctor).obj (G.verdierDual aY N) ⟶
      (ihom (((upperStar A pY).leftDerivedFunctor).obj N)).obj
        ((rightDerivedUpperShriek A pX).obj M) :=
  haveI : IsGeometric (pY ≫ aY) := IsGeometric.of_eq sq.w
  kunnethVerdierMapOf A (fun _ hK ↦ G.ctf_lowerShriek pX (.mk (aY := aX) rfl) hK)
    (fun _ hK ↦ G.ctf_upperStar pX (.mk (aY := aX) rfl) hK) (G.upperStarMonoidal pY)
    (G.projectionFormula pX (.mk (aY := aX) rfl)) (G.exceptionalTrace sq)
    (G.ctf_upperStar pY (.mk (aY := aY) rfl) (G.ctf_dualizing aY)) M hM
    (G.ctf_tensor (.id (pX ≫ aX)) (G.ctf_upperStar pX (.mk (aY := aX) rfl) hM)
      (G.ctf_upperStar pY (.mk (aY := aY) rfl) (G.ctf_dualizing aY))) N

/-- The Künneth-Verdier isomorphism `κ_{M,N} : M ⊠ D_Y N ≃ RHom(p_Y^* N, p_X^! M)` for
`M ∈ Dᵇctf(X)` and `N ∈ Dᵇctf(Y)`, where `X` and `Y` are separated of finite type over a
field `s = Spec k`: the map `GeometricOperations.kunnethVerdierMap`, invertible by the field
`isIso_kunnethVerdierMap` (blueprint: `sk-thm-sf-kunneth-verdier`). -/
noncomputable def kunnethVerdier {Z X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
    {pX : Z ⟶ X} {pY : Z ⟶ Y} [s.IsSpecOfField] [IsGeometric aX] [IsGeometric aY]
    [IsGeometric (pX ≫ aX)] [HasCompactification aX]
    [HasCompactification aY] (sq : IsPullback pX pY aX aY) [HasCompactification pX]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hM : G.ctf X M)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) (hN : G.ctf Y N) :
    ((upperStar A pX).leftDerivedFunctor).obj M ⊗
        ((upperStar A pY).leftDerivedFunctor).obj (G.verdierDual aY N) ≅
      (ihom (((upperStar A pY).leftDerivedFunctor).obj N)).obj
        ((rightDerivedUpperShriek A pX).obj M) :=
  haveI : IsIso (G.kunnethVerdierMap sq M hM N) := G.isIso_kunnethVerdierMap sq M hM N hN
  asIso (G.kunnethVerdierMap sq M hM N)

end GeometricOperations

end AlgebraicGeometry.ProEtale
