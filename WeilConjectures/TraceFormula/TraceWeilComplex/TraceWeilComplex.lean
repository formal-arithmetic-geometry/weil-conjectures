/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceOperations.GeometricOperationPackage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCanonicalPullbackComposition
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.RelativeFrobeniusGeometricFiber
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-! # Frobenius correspondences, Weil complexes and Weil data

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-correspondences/sk-d-weil/_section.md (blueprint: sk-d-weil).

Everything is stated over the geometric operation package of `sk-d-six`
(`AlgebraicGeometry.ProEtale.TraceOperations.GeometricOperations`) over a base scheme `s`, with
coefficients `Λ`; the node's arbitrary finite commutative `ℓ`-primary ring `A` is the
specialization `Λ = C(-,A)` (`finiteGeometricOperationPackage`), exactly as for the global
operator `traceGlobalOperator` of `sk-d-operator`. `D(X,A)` is `TraceOperations.D Λ X`, and
`D^b_ctf(X,A)` is `ConstantModelConstructibleFiniteTor` (as in `GeometricOperations.biduality`).
* `WeilComplex`: `(Φ₁, K, φ)` with `Φ₁ : X → X` over `s` and `φ : Φ₁^*K → K` arbitrary;
* `frobeniusPower`, `iterate`: `Φ_m = Φ₁^m` and `φ_m`, by pullback composition
  (`condensedCanonicalPullbackComposition`, lem-weil-pbc-proetale-derived-pullback-composition),
  with `φ₀` the identification `id^*K ≃ K` of the package (`starIdentity`);
* `frobeniusPullbackCompact`, `globalOperator`: `T_{c_m}(φ_m) = RΓ_c(X, φ_m) ∘ (Φ_m)^*`, the
  pullback map built from the unit of `Φ_m^* ⊣ RΦ_{m*}`, the inverse proper identification and
  the composition isomorphism for `a_X Φ_m = a_X` of the package (as in `traceGlobalOperator`,
  for the graph correspondence `c_m = (id_X, Φ_m)`);
* `stalkEndomorphism`: `F_{x,m} = (φ_m)_{x̄}` at a point `x̄ : s → X` over `s` fixed by `Φ_m`;
* `modelFrobenius`, `FrobeniusCorrespondence`, `WeilDatum`: the model case
  `X = X₀ ×_{F_q} k`, `Φ_X` the base change of the `q`-power Frobenius of `X₀`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.TraceWeilComplex

section General

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {s : Scheme.{u}}

variable (Λ) in
/-- A *Weil complex* on an `s`-scheme `X`: an endomorphism `Φ₁ : X → X` over `s` (so it fixes
the scalar field), a complex `K ∈ D(X,A)`, and a Frobenius coefficient morphism
`φ : Φ₁^*K → K`, an arbitrary map without an invertibility requirement.
Source: "A *Weil complex* on `X` consists of an endomorphism `Φ₁ : X → X` over `s` ..., a
complex `K ∈ D(X,A)`, and a *Frobenius coefficient morphism* `φ : Φ₁^*K → K`, an arbitrary map
without an invertibility requirement" (blueprint: sk-d-weil). -/
structure WeilComplex (X : Over s) where
  /-- The Frobenius endomorphism `Φ₁ : X → X` over `s`. -/
  frobenius : X ⟶ X
  /-- The complex `K ∈ D(X,A)`. -/
  complex : TraceOperations.D Λ X.left
  /-- The Frobenius coefficient morphism `φ : Φ₁^*K → K`. -/
  coefficient : (TraceOperations.star Λ frobenius.left).obj complex ⟶ complex

/-- The power `Φ_m = Φ₁^m` of an endomorphism over `s`, with `Φ₀ = id_X` and
`Φ_{m+1} = Φ₁ ∘ Φ_m`.
Source: "Put `Φ_m = Φ₁^m`" (blueprint: sk-d-weil). -/
def frobeniusPower {X : Over s} (Φ : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | m + 1 => frobeniusPower Φ m ≫ Φ

variable (Λ) in
/-- The pullback composition isomorphism `(f ≫ g)^* ≅ f^* ∘ g^*` of
lem-weil-pbc-proetale-derived-pullback-composition (`condensedCanonicalPullbackComposition`),
isolated in one abbreviation.
Source: "by composing the pulled-back copies of `φ` using pullback composition"
(blueprint: sk-d-weil). -/
abbrev pullbackComposition {X Y Z : Over s} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TraceOperations.star Λ (f ≫ g).left ≅
      TraceOperations.star Λ g.left ⋙ TraceOperations.star Λ f.left :=
  CondensedRing.condensedCanonicalPullbackComposition Λ f.left g.left

/-- The iterate `φ_m : Φ_m^*K → K` of the Frobenius coefficient morphism: `φ₀` is the
identification `id^*K ≃ K`, and `φ_{m+1}` is
`(Φ_m Φ₁)^*K ≅ Φ_m^*Φ₁^*K → Φ_m^*K → K` (pullback composition, `Φ_m^*φ`, then `φ_m`), so that
`φ_m = φ ∘ Φ₁^*φ ∘ ⋯ ∘ (Φ₁^{m-1})^*φ`.
Source: "define the iterate `φ_m : Φ_m^*K → K` by composing the pulled-back copies of `φ` using
pullback composition (`φ₀` is the identification `id^*K ≃ K`)" (blueprint: sk-d-weil). -/
def WeilComplex.iterate {X : Over s} (W : WeilComplex Λ X) :
    ∀ m : ℕ, (TraceOperations.star Λ (frobeniusPower W.frobenius m).left).obj W.complex ⟶
      W.complex
  | 0 => (TraceOperations.starIdentity Λ X.left).hom.app W.complex
  | m + 1 =>
      (pullbackComposition Λ (frobeniusPower W.frobenius m) W.frobenius).hom.app W.complex ≫
        (TraceOperations.star Λ (frobeniusPower W.frobenius m).left).map W.coefficient ≫
        W.iterate m

/-- The pullback map `(Φ)^* : RΓ_c(X,K) → RΓ_c(X, Φ^*K)` of a proper endomorphism `Φ` of `X`
over `s`: `Ra_{X!}` of the unit of `Φ^* ⊣ RΦ_*`, then `Ra_{X!}` of the inverse proper
identification `RΦ_! ≅ RΦ_*`, then the composition isomorphism
`Ra_{X!}RΦ_! ≅ R(a_XΦ)_! = Ra_{X!}` of the package of sk-d-six.
Source: "`(Φ_X^m)^* : RΓ_c(X,K) → RΓ_c(X,(Φ_X^m)^*K)` is the pullback map induced by the unit
of `(Φ_X^m)^* ⊣ R(Φ_X^m)_*`" (blueprint: sk-d-weil); the arrows are the first three arrows of
`T_c(u)` of sk-d-operator for `c₂ = Φ`. -/
def frobeniusPullbackCompact (O : TraceOperations.Given Λ s)
    (P : TraceOperations.GeometricOperations O) {X : Over s} [HasCompactification X.hom]
    (Φ : X ⟶ X) [IsProper Φ.left] (K : TraceOperations.D Λ X.left) :
    (TraceOperations.Comparisons.compactlySupported O X).obj K ⟶
      (TraceOperations.Comparisons.compactlySupported O X).obj
        ((TraceOperations.star Λ Φ.left).obj K) := by
  have e : Φ ≫ TraceOperations.structureMap X = TraceOperations.structureMap X :=
    Over.OverMorphism.ext Φ.w
  haveI : HasCompactification (Φ ≫ TraceOperations.structureMap X).left :=
    HasCompactification.of_eq (f := (TraceOperations.structureMap X).left)
      (congrArg Over.Hom.left e).symm
  let sX := TraceOperations.Comparisons.compactlySupported O X
  let η := (CondensedRing.derivedUpperStarLowerStarAdjunction Λ Φ.left).unit.app K
  let r : O.shriek (Φ ≫ TraceOperations.structureMap X) ≅
      O.shriek (TraceOperations.structureMap X) := eqToIso (by simp only [e])
  let μ := P.comparisons.composition Φ (TraceOperations.structureMap X) ≪≫ r
  exact sX.map (η ≫ (P.comparisons.proper Φ).inv.app ((TraceOperations.star Λ Φ.left).obj K)) ≫
    μ.hom.app ((TraceOperations.star Λ Φ.left).obj K)

/-- The global operator `F_{c,m} = T_{c_m}(φ_m) = RΓ_c(X, φ_m) ∘ (Φ_m)^*` of a Weil complex
whose power `Φ_m` is proper and whose complex lies in the given operation domain `dom X`
(`hW`), for the graph correspondence `c_m = (id_X, Φ_m)` with coefficient map `φ_m`. The
comparisons are evaluated at `Φ_m^*K` and `RΦ_{m!}Φ_m^*K`, which lie in the given operation
domains by `Given.star_mem` and `Given.shriek_mem`.
Source: "Its operator on cohomology with compact support ... is the endomorphism
`T_{c_m}(ψ_m) = RΓ_c(X,ψ_m) ∘ (Φ_X^m)^*`" and "The graph correspondence is
`c_m = (id_X, Φ_m)`, with coefficient map `φ_m`. Write `F_{c,m} = T_{c_m}(φ_m)` for the global
operator" (blueprint: sk-d-weil); sk-d-six, opening ("uses the given operations wherever the
displayed composites are defined"). -/
def WeilComplex.globalOperatorOf (O : TraceOperations.Given Λ s)
    (P : TraceOperations.GeometricOperations O) {X : Over s} [HasCompactification X.hom]
    (W : WeilComplex Λ X) (m : ℕ) [IsProper (frobeniusPower W.frobenius m).left]
    (hW : O.dom X W.complex) :
    (TraceOperations.Comparisons.compactlySupported O X).obj W.complex ⟶
      (TraceOperations.Comparisons.compactlySupported O X).obj W.complex :=
  frobeniusPullbackCompact O P (frobeniusPower W.frobenius m) W.complex
      ⟨O.star_mem _ hW, O.shriek_mem _ (O.star_mem _ hW)⟩ ≫
    (TraceOperations.Comparisons.compactlySupported O X).map (W.iterate m)

open Classical in
/-- The global operator `F_{c,m} = T_{c_m}(φ_m) = RΓ_c(X, φ_m) ∘ (Φ_m)^*` of a Weil complex
whose power `Φ_m` is proper, for the graph correspondence `c_m = (id_X, Φ_m)` with coefficient
map `φ_m`.
Source: "Its operator on cohomology with compact support ... is the endomorphism
`T_{c_m}(ψ_m) = RΓ_c(X,ψ_m) ∘ (Φ_X^m)^*`" and "The graph correspondence is
`c_m = (id_X, Φ_m)`, with coefficient map `φ_m`. Write `F_{c,m} = T_{c_m}(φ_m)` for the global
operator" (blueprint: sk-d-weil). -/
def WeilComplex.globalOperator (O : TraceOperations.Given Λ s)
    (P : TraceOperations.GeometricOperations O) {X : Over s} [HasCompactification X.hom]
    (W : WeilComplex Λ X) (m : ℕ) [IsProper (frobeniusPower W.frobenius m).left] :
    (TraceOperations.Comparisons.compactlySupported O X).obj W.complex ⟶
      (TraceOperations.Comparisons.compactlySupported O X).obj W.complex :=
  frobeniusPullbackCompact O P (frobeniusPower W.frobenius m) W.complex ≫
    (TraceOperations.Comparisons.compactlySupported O X).map (W.iterate m)

/-- On the given operation domain the global operator is the displayed composite.
Source: sk-d-weil, global operator (blueprint: sk-d-weil).
Proof: unfold the case split and take its positive branch. -/
theorem WeilComplex.globalOperator_eq (O : TraceOperations.Given Λ s)
    (P : TraceOperations.GeometricOperations O) {X : Over s} [HasCompactification X.hom]
    (W : WeilComplex Λ X) (m : ℕ) [IsProper (frobeniusPower W.frobenius m).left]
    (hW : O.dom X W.complex) :
    W.globalOperator O P m = W.globalOperatorOf O P m hW := by
  unfold WeilComplex.globalOperator
  exact dif_pos hW

/-- Pullbacks along equal morphisms over `s` are identified.
Source: "`x̄^*K ≃ x̄^*Φ_m^*K`" for a point fixed by `Φ_m` (blueprint: sk-d-weil). -/
def starCongr {X Y : Over s} {f g : X ⟶ Y} (h : f = g) :
    TraceOperations.star Λ f.left ≅ TraceOperations.star Λ g.left := by
  subst h
  exact Iso.refl _

/-- The stalk endomorphism `F_{x,m} = (φ_m)_{x̄} : x̄^*K ≃ x̄^*Φ_m^*K → x̄^*K` at a point
`x̄ : s → X` over `s` fixed by `Φ_m` (`x̄ ≫ Φ_m = x̄`): the identification along
`Φ_m x̄ = x̄` and pullback composition, followed by `x̄^*φ_m`.
Source: "For a point `x̄ : s → X` over `s` fixed by `Φ_m` ..., the stalk endomorphism is
`F_{x,m} = (φ_m)_{x̄} : x̄^*K ≃ x̄^*Φ_m^*K → x̄^*K`" (blueprint: sk-d-weil). -/
def WeilComplex.stalkEndomorphism {X : Over s} (W : WeilComplex Λ X) (m : ℕ)
    (x : TraceOperations.base s ⟶ X) (hx : x ≫ frobeniusPower W.frobenius m = x) :
    (TraceOperations.star Λ x.left).obj W.complex ⟶
      (TraceOperations.star Λ x.left).obj W.complex :=
  (starCongr (Λ := Λ) hx.symm).hom.app W.complex ≫
    (pullbackComposition Λ x (frobeniusPower W.frobenius m)).hom.app W.complex ≫
    (TraceOperations.star Λ x.left).map (W.iterate m)

end General

section Model

variable (D : FiniteFieldDatum.{u})

/-- The model Frobenius `Φ_X : X → X` of `X = X₀ ×_{F_q} k`, as a morphism over `s = Spec k`:
the base change along `Spec k → Spec F_q` of the `q`-power absolute scheme Frobenius of `X₀`
(which is a morphism over `F_q`, `model_frobenius_over`).
Source: "Denote by `Φ_X : X → X` the base change of the `q`-power scheme Frobenius of `X₀`"
(blueprint: sk-d-weil); def-weil-absolute-frobenius-scheme, def-pc-base-change. -/
def modelFrobenius (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    D.geometricFiber X₀ ⟶ D.geometricFiber X₀ :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
    (Over.homMk (X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a)
      (D.model_frobenius_over X₀.hom))

/-- The underlying morphism of the model Frobenius is the relative Frobenius of the geometric
fibre (def-weil-relative-frobenius-geometric-fiber).
Source: "the base change of the `q`-power scheme Frobenius of `X₀`" (blueprint: sk-d-weil).
Proof: both are the `left` component of the image of the same `Over.homMk` under
`Over.pullback` (`rfl`). -/
theorem modelFrobenius_left (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (modelFrobenius D X₀).left = FiniteFieldDatum.relativeFrobenius D X₀ := by
  rfl

/-- The model Frobenius is a finite `k`-morphism and a universal homeomorphism.
Source: "It is a finite `k`-morphism and a universal homeomorphism" (blueprint: sk-d-weil).
Proof: the absolute `q`-power Frobenius of `X₀` is integral and a universal homeomorphism
(identity on spaces, `p`-power on sections; Stacks 0CC8); for `X₀` of finite type over `F_q` it
is finite (integral and of finite type, Stacks 01WJ). Both properties are stable under the base
change `Spec k → Spec F_q` (Stacks 01WL, 0CEX). -/
theorem modelFrobenius_finite_universalHomeomorphism (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsFinite (modelFrobenius D X₀).left ∧
      IsUniversalHomeomorphism (modelFrobenius D X₀).left := by
  have hF : (X₀.left.iterateFrobenius D.prime
      (D.model_characteristic X₀.hom) D.a).IsFrobenius (Nat.card D.k₀) := by
    rw [D.card_base, D.cardinality_eq]
    exact X₀.left.isFrobenius_iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a
  have hp := IsPullback.of_hasPullback X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  have hΦ := D.relativeFrobenius_projections X₀
  rw [modelFrobenius_left]
  exact ⟨hF.isFinite_of_isPullback hp hΦ.2 hΦ.1,
    hF.isUniversalHomeomorphism_of_isPullback hp hΦ.2 hΦ.1⟩

/-- Every power `Φ_X^m` of the model Frobenius is proper (a composite of finite morphisms).
Source: "It is a finite `k`-morphism" (blueprint: sk-d-weil); def-weil-proper-morphism.
Proof: induction on `m`: `Φ_X^0 = id` is proper; `Φ_X^{m+1} = Φ_X^m ≫ Φ_X` is a composite of
proper morphisms, `Φ_X` being finite (`modelFrobenius_finite_universalHomeomorphism`), hence
proper. -/
theorem modelFrobeniusPower_isProper (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) :
    IsProper (frobeniusPower (modelFrobenius D X₀) m).left := by
  have := (modelFrobenius_finite_universalHomeomorphism D X₀).1
  induction m with
  | zero =>
      change IsProper (𝟙 (D.geometricFiber X₀).left)
      infer_instance
  | succ m hm =>
      have := hm
      change IsProper ((frobeniusPower (modelFrobenius D X₀) m).left ≫
        (modelFrobenius D X₀).left)
      infer_instance

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

variable (Λ) in
/-- A *Frobenius correspondence* on `K ∈ D^b_ctf(X,A)`, `X = X₀ ×_{F_q} k`: a morphism
`ψ : Φ_X^*K → K`, not necessarily invertible.
Source: "A *Frobenius correspondence* on `K` is a morphism, not necessarily invertible,
`ψ : Φ_X^*K → K`, `K ∈ D^b_ctf(X,A)`" (blueprint: sk-d-weil). -/
abbrev FrobeniusCorrespondence (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (K : ConstantModelConstructibleFiniteTor Λ (D.geometricFiber X₀).left) :=
  (TraceOperations.star Λ (modelFrobenius D X₀).left).obj K.obj ⟶ K.obj

/-- The Weil complex with the model Frobenius attached to a Frobenius correspondence; its
iterates `iterate m` are the iterates `ψ_m = ψ ∘ Φ_X^*ψ ∘ ⋯ ∘ (Φ_X^{m-1})^*ψ`.
Source: "for the model Frobenius and `K ∈ D^b_ctf(X,A)`, `φ` is a Frobenius correspondence and
`φ_m` is its `m`-th iterate as above" (blueprint: sk-d-weil). -/
def FrobeniusCorrespondence.toWeilComplex {X₀ : Over (Spec (CommRingCat.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    {K : ConstantModelConstructibleFiniteTor Λ (D.geometricFiber X₀).left}
    (ψ : FrobeniusCorrespondence D Λ X₀ K) : WeilComplex Λ (D.geometricFiber X₀) where
  frobenius := modelFrobenius D X₀
  complex := K.obj
  coefficient := ψ

/-- The operator `T_{c_m}(ψ_m) = RΓ_c(X,ψ_m) ∘ (Φ_X^m)^*` of a Frobenius correspondence on
cohomology with compact support: the global operator of its Weil complex, defined since every
`Φ_X^m` is proper (`modelFrobeniusPower_isProper`).
Source: "Since its first leg is the identity, `ψ_m` is a cohomological correspondence on `(X,K)`
for `c_m`. Its operator on cohomology with compact support ... is the endomorphism
`T_{c_m}(ψ_m) = RΓ_c(X,ψ_m) ∘ (Φ_X^m)^*`" (blueprint: sk-d-weil). -/
def FrobeniusCorrespondence.operator (O : TraceOperations.Given Λ (Spec (.of D.k)))
    (P : TraceOperations.GeometricOperations O) {X₀ : Over (Spec (CommRingCat.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [HasCompactification (D.geometricFiber X₀).hom]
    {K : ConstantModelConstructibleFiniteTor Λ (D.geometricFiber X₀).left}
    (ψ : FrobeniusCorrespondence D Λ X₀ K) (m : ℕ) :
    (TraceOperations.Comparisons.compactlySupported O (D.geometricFiber X₀)).obj K.obj ⟶
      (TraceOperations.Comparisons.compactlySupported O (D.geometricFiber X₀)).obj K.obj :=
  haveI : IsProper (frobeniusPower (FrobeniusCorrespondence.toWeilComplex D ψ).frobenius m).left :=
    modelFrobeniusPower_isProper D X₀ m
  (FrobeniusCorrespondence.toWeilComplex D ψ).globalOperator O P m

/-- The operator of a Frobenius correspondence is the displayed composite of sk-d-weil: its
complex `K ∈ D^b_ctf` lies in the given operation domain (`Given.ctf_mem`).
Source: sk-d-weil, operator (blueprint: sk-d-weil); sk-d-six, opening.
Proof: `WeilComplex.globalOperator_eq` at the membership `Given.ctf_mem`. -/
theorem FrobeniusCorrespondence.operator_eq (O : TraceOperations.Given Λ (Spec (.of D.k)))
    (P : TraceOperations.GeometricOperations O) {X₀ : Over (Spec (CommRingCat.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [HasCompactification (D.geometricFiber X₀).hom]
    {K : ConstantModelConstructibleFiniteTor Λ (D.geometricFiber X₀).left}
    (ψ : FrobeniusCorrespondence D Λ X₀ K) (m : ℕ) :
    haveI : IsProper
        (frobeniusPower (FrobeniusCorrespondence.toWeilComplex D ψ).frobenius m).left :=
      modelFrobeniusPower_isProper D X₀ m
    FrobeniusCorrespondence.operator D O P ψ m =
      (FrobeniusCorrespondence.toWeilComplex D ψ).globalOperatorOf O P m
        (O.ctf_mem _ K) := by
  have : IsProper
      (frobeniusPower (FrobeniusCorrespondence.toWeilComplex D ψ).frobenius m).left :=
    modelFrobeniusPower_isProper D X₀ m
  exact WeilComplex.globalOperator_eq _ _ _ _ _

variable (Λ) in
/-- A *Weil datum*: a Weil complex with a separated finite-type model `X₀/F_q`, the model
Frobenius `Φ₁ = Φ_X`, `K ∈ D^b_ctf(X,A)` and `φ` an isomorphism `Φ₁^*K ≃ K`.
Source: "A *Weil datum* is a Weil complex with `X₀/F_q` separated of finite type, the model
Frobenius, `K ∈ D_ctf(X,A)` and `φ` an isomorphism `Φ₁^*K ≃ K`" (blueprint: sk-d-weil). -/
structure WeilDatum where
  /-- The model `X₀` over `F_q`. -/
  model : Over (Spec (CommRingCat.of D.k₀))
  [locallyOfFiniteType : LocallyOfFiniteType model.hom]
  [quasiCompact : QuasiCompact model.hom]
  [isSeparated : IsSeparated model.hom]
  /-- The complex `K ∈ D^b_ctf(X,A)` on `X = X₀ ×_{F_q} k`. -/
  complex : ConstantModelConstructibleFiniteTor Λ (D.geometricFiber model).left
  /-- The Frobenius coefficient isomorphism `φ : Φ_X^*K ≃ K`. -/
  coefficient : (TraceOperations.star Λ (modelFrobenius D model).left).obj complex.obj ≅
    complex.obj

attribute [instance] WeilDatum.locallyOfFiniteType WeilDatum.quasiCompact WeilDatum.isSeparated

/-- The underlying Weil complex of a Weil datum: `(Φ_X, K, φ)`.
Source: "A *Weil datum* is a Weil complex with ..." (blueprint: sk-d-weil). -/
def WeilDatum.toWeilComplex (W : WeilDatum D Λ) : WeilComplex Λ (D.geometricFiber W.model) where
  frobenius := modelFrobenius D W.model
  complex := W.complex.obj
  coefficient := W.coefficient.hom

end Model

end WeilConjectures.TraceWeilComplex
