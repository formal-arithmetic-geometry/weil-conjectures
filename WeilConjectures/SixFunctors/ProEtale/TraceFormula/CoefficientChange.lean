/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main

/-!
# Finite-level coefficient change in the trace formula

Let `R ⟶ S` be a homomorphism of finite commutative rings whose exponent is invertible on the
base. Derived scalar extension `Ψ = - ⊗ᴸ_R S` of pro-étale sheaves preserves `Dᵇctf`, commutes
with `Rf_!` and with `Lf^*`, and carries a Weil complex `(K, φ)` with coefficients in `R` to a
Weil complex `(Ψ K, Ψ φ)` with coefficients in `S`. Compact cohomology and the geometric stalks
commute with `Ψ` compatibly with the global and the local Frobenius operators, and `Ψ` carries
categorical traces over `R` to categorical traces over `S`, so the finite-coefficient trace
formula over `R` maps to the one over `S` (blueprint `sk-p-trace-coeff`,
`thm-trf-finite-coefficient-map`).

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex.extendScalars`: the scalar extension `(Ψ K, Ψ φ)` of
  a Weil complex.
- `AlgebraicGeometry.ProEtale.GeometricOperations.ExtendScalarsCompatible`: two geometric
  operation packages over `R` and over `S` whose comparison data correspond under `Ψ`.

## Main results

- `AlgebraicGeometry.ProEtale.WeilComplex.stalkFrobenius_extendScalars`: the stalk Frobenius of
  the scalar extension is the scalar extension of the stalk Frobenius.
- `AlgebraicGeometry.ProEtale.WeilComplex.globalOperator_graph_extendScalars`: the global
  Frobenius operator on `RΓ_c` of the scalar extension is the scalar extension of the global
  Frobenius operator.
- `AlgebraicGeometry.ProEtale.WeilComplex.extendScalars_compactCohomology_stalk`: blueprint
  `sk-p-trace-coeff`.
- `AlgebraicGeometry.ProEtale.WeilComplex.trace_stalkFrobenius_extendScalars`: the trace
  identity `ρ(tr_R(F_{x,m} ∣ K_x̄)) = tr_S(F_{x,m} ∣ (Ψ K)_x̄)`.

## Implementation notes

The geometric operation packages are axiomatised (`AlgebraicGeometry.ProEtale.GeometricOperations`)
and their comparison data `properComparison` and `lowerShriekComp` are not pinned to canonical
maps; the blueprint takes them to be natural in the coefficient ring
(`def-trf-coefficient-conventions`). For two arbitrary packages over `R` and over `S` this
naturality is a property, `GeometricOperations.ExtendScalarsCompatible`, relating them through
the canonical comparison maps of `Ψ` with `Rf_!` and `Rf_*`, which are constructed and shown to be
isomorphisms in `WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars.LowerShriek`.

The braidings of the derived categories are the temporary choice `DerivedBraiding`, so the
compatibility of `Ψ` with them can only be a hypothesis: the trace identities are stated for a
braided monoidal structure on `Ψ` over the base, as the package does for `Lf^*`
(`GeometricOperations.upperStarMonoidal_braiding`). The induced map on coefficient rings
`End (𝟙_ D(s, R)) ⟶ End (𝟙_ D(s, S))` is `t ↦ ε ≫ Ψ t ≫ η`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [Finite R] [Finite S]

section Constructible

/-- Over a field in which the exponent of `R` is invertible, derived scalar extension preserves
`Dᵇctf` on every geometric scheme. -/
lemma constructibleFiniteTor_leftDerivedSheafExtendScalars_of_isGeometricHom {k : Type u}
    [Field k] [HasInvertibleExponent R (Spec (.of k))] {X : Scheme.{u}}
    (hX : IsGeometricHom (Spec (.of k)) (𝟙 X))
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) X
      ((L(sheafExtendScalars (algebraMap R S) X)).obj K) := by
  obtain ⟨a, _, _⟩ := hX
  have : HasInvertibleExponent R X := .of_hom (𝟙 X ≫ a)
  exact constructibleFiniteTor_leftDerivedSheafExtendScalars (𝟙 X ≫ a) hK

end Constructible

namespace WeilComplex

variable {R S} {s X : Scheme.{u}} {aX : X ⟶ s}

variable (S) in
/-- The scalar extension `(Ψ K, Ψ φ)` of a Weil complex `(K, φ)` with coefficients in `R`: the
same Frobenius `Φ₁`, the complex `Ψ K = K ⊗ᴸ_R S` and the coefficient morphism
`Φ₁^* Ψ K ≅ Ψ Φ₁^* K ──Ψ φ──▶ Ψ K` (blueprint `def-trf-coefficient-conventions`,
`thm-trf-finite-coefficient-map`). -/
noncomputable def extendScalars (W : WeilComplex (A := ModuleCat.{u + 1} R) aX) :
    WeilComplex (A := ModuleCat.{u + 1} S) aX where
  frobenius := W.frobenius
  frobenius_comp := W.frobenius_comp
  obj := (L(sheafExtendScalars (algebraMap R S) X)).obj W.obj
  coeff := (leftDerivedUpperStarExtendScalarsIso R S W.frobenius).hom.app W.obj ≫
    (L(sheafExtendScalars (algebraMap R S) X)).map W.coeff

variable (W : WeilComplex (A := ModuleCat.{u + 1} R) aX)

@[simp]
lemma extendScalars_frobeniusIterate (m : ℕ) :
    (W.extendScalars S).frobeniusIterate m = W.frobeniusIterate m :=
  rfl

instance isProper_extendScalars_frobeniusIterate (m : ℕ) [IsProper (W.frobeniusIterate m)] :
    IsProper ((W.extendScalars S).frobeniusIterate m) :=
  ‹IsProper (W.frobeniusIterate m)›

/-- The iterated coefficient morphisms of the scalar extension are the scalar extensions of the
iterated coefficient morphisms: `(Ψ φ)_m = Ψ (φ_m)` through `Φ_m^* Ψ K ≅ Ψ Φ_m^* K`. -/
lemma coeffIterate_extendScalars (m : ℕ) :
    (W.extendScalars S).coeffIterate m =
      (leftDerivedUpperStarExtendScalarsIso R S (W.frobeniusIterate m)).hom.app W.obj ≫
        (L(sheafExtendScalars (algebraMap R S) X)).map (W.coeffIterate m) :=
  sorry

/-- **The stalk Frobenius commutes with coefficient change**: through
`Lx^* Ψ K ≅ Ψ Lx^* K`, the stalk Frobenius `F_{x,m}` of the scalar extension `Ψ K` is the scalar
extension of the stalk Frobenius of `K`. -/
lemma stalkFrobenius_extendScalars (m : ℕ) (x : s ⟶ X) (hx : x ≫ W.frobeniusIterate m = x) :
    (W.extendScalars S).stalkFrobenius m x hx =
      (leftDerivedUpperStarExtendScalarsIso R S x).hom.app W.obj ≫
        (L(sheafExtendScalars (algebraMap R S) s)).map (W.stalkFrobenius m x hx) ≫
          (leftDerivedUpperStarExtendScalarsIso R S x).inv.app W.obj :=
  sorry

end WeilComplex

namespace GeometricOperations

variable {R S} [DerivedBraiding (ModuleCat.{u + 1} R)] [DerivedBraiding (ModuleCat.{u + 1} S)]
  {s : Scheme.{u}}

/-- Two geometric operation packages over `R` and over `S` are *compatible with scalar extension*
if their comparison data correspond under derived scalar extension `Ψ = - ⊗ᴸ_R S`, through the
canonical comparison maps `Ψ (Rf_! K) ⟶ Rf_! (Ψ K)` and `Ψ (Rf_* K) ⟶ Rf_* (Ψ K)`: the
composition isomorphisms `Rg_! Rf_! ≃ R(f ≫ g)_!` and the identifications `Rf_! ≃ Rf_*` for
proper `f` are natural in the coefficient ring (blueprint `def-trf-coefficient-conventions`).
The argument `hΨ` is the stability of `Dᵇctf` under `Ψ`. -/
structure ExtendScalarsCompatible (G_R : GeometricOperations (ModuleCat.{u + 1} R) s)
    (G_S : GeometricOperations (ModuleCat.{u + 1} S) s)
    (hΨ : ∀ {X : Scheme.{u}} (_ : IsGeometricHom s (𝟙 X))
      {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K →
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) X
          ((L(sheafExtendScalars (algebraMap R S) X)).obj K)) : Prop where
  /-- the composition isomorphisms of `R(-)_!` correspond under `Ψ`. -/
  lowerShriekComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsGeometricHom s f)
      (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g)) [HasCompactification f]
      [HasCompactification g] [HasCompactification (f ≫ g)]
      {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
      (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K) :
    (L(sheafExtendScalars (algebraMap R S) Z)).map
        ((G_R.lowerShriekComp f g hf hg hfg).hom.app ⟨K, hK⟩).hom ≫
      (rightDerivedLowerShriekExtendScalarsMap R S (f ≫ g)).app K =
    (rightDerivedLowerShriekExtendScalarsMap R S g).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} S) g).map
        ((rightDerivedLowerShriekExtendScalarsMap R S f).app K) ≫
      ((G_S.lowerShriekComp f g hf hg hfg).hom.app ⟨_, hΨ hf.id_source hK⟩).hom
  /-- the identifications `Rf_! ≃ Rf_*` for proper `f` correspond under `Ψ`. -/
  properComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsGeometricHom s f)
      [HasCompactification f] [IsProper f]
      {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
      (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K) :
    (L(sheafExtendScalars (algebraMap R S) Y)).map
        ((G_R.properComparison f hf).hom.app ⟨K, hK⟩).hom ≫
      (rightDerivedLowerStarExtendScalarsMap R S f).app K =
    (rightDerivedLowerShriekExtendScalarsMap R S f).app K ≫
      ((G_S.properComparison f hf).hom.app ⟨_, hΨ hf.id_source hK⟩).hom

variable {G_R : GeometricOperations (ModuleCat.{u + 1} R) s}
  {G_S : GeometricOperations (ModuleCat.{u + 1} S) s}
  {hΨ : ∀ {X : Scheme.{u}} (_ : IsGeometricHom s (𝟙 X))
      {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K →
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) X
          ((L(sheafExtendScalars (algebraMap R S) X)).obj K)}
  (hG : ExtendScalarsCompatible G_R G_S hΨ)

include hG in
/-- The proper pullback `RΓ_c(X, K) ⟶ RΓ_c(X', Lh^* K)` along a proper `h` commutes with
derived scalar extension, through the comparison maps `Ψ RΓ_c ⟶ RΓ_c Ψ` and `Lh^* Ψ ≅ Ψ Lh^*`. -/
theorem properPullback_extendScalars {X X' : Scheme.{u}} {aX : X ⟶ s} {aX' : X' ⟶ s}
    [IsGeometric aX] [IsGeometric aX'] [HasCompactification aX] [HasCompactification aX']
    (h : X' ⟶ X) [IsProper h] (hh : h ≫ aX = aX')
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K) :
    (L(sheafExtendScalars (algebraMap R S) s)).map (G_R.properPullback h hh hK) ≫
        (rightDerivedLowerShriekExtendScalarsMap R S aX').app
          ((L((h)^*[ModuleCat.{u + 1} R])).obj K) =
      (rightDerivedLowerShriekExtendScalarsMap R S aX).app K ≫
        G_S.properPullback h hh (hΨ (.id aX) hK) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} S) aX').map
            ((leftDerivedUpperStarExtendScalarsIso R S h).hom.app K) :=
  sorry

include hG in
/-- The global operator of the graph correspondence of a proper endomorphism `g` with
coefficient map `v : Lg^* K ⟶ K` commutes with derived scalar extension: through
`Ψ RΓ_c(X, K) ⟶ RΓ_c(X, Ψ K)`, the global operator of `Ψ v` is the scalar extension of the
global operator of `v`. -/
theorem globalOperator_ofGraph_extendScalars {X : Scheme.{u}} {aX : X ⟶ s} [IsGeometric aX]
    [HasCompactification aX]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K) (g : X ⟶ X)
    (hg : g ≫ aX = aX) [IsProper g] (v : (L((g)^*[ModuleCat.{u + 1} R])).obj K ⟶ K) :
    (L(sheafExtendScalars (algebraMap R S) s)).map
        (Correspondence.globalOperator G_R (Correspondence.ofGraph G_R aX K hK g hg v) hK) ≫
      (rightDerivedLowerShriekExtendScalarsMap R S aX).app K =
    (rightDerivedLowerShriekExtendScalarsMap R S aX).app K ≫
      Correspondence.globalOperator G_S
        (Correspondence.ofGraph G_S aX _ (hΨ (.id aX) hK) g hg
          ((leftDerivedUpperStarExtendScalarsIso R S g).hom.app K ≫
            (L(sheafExtendScalars (algebraMap R S) X)).map v)) (hΨ (.id aX) hK) := by
  rw [Correspondence.globalOperator_ofGraph, Correspondence.globalOperator_ofGraph,
    Functor.map_comp, Category.assoc]
  have nat := (rightDerivedLowerShriekExtendScalarsMap R S aX).naturality v
  simp only [Functor.comp_map] at nat
  rw [nat, ← Category.assoc, properPullback_extendScalars hG g hg hK, Category.assoc,
    Category.assoc, Functor.map_comp]

end GeometricOperations

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace WeilComplex

open GeometricOperations

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] [Finite R] [Finite S]
  [DerivedBraiding (ModuleCat.{u + 1} R)] [DerivedBraiding (ModuleCat.{u + 1} S)]
  {s X : Scheme.{u}} {aX : X ⟶ s}
  {G_R : GeometricOperations (ModuleCat.{u + 1} R) s}
  {G_S : GeometricOperations (ModuleCat.{u + 1} S) s}
  {hΨ : ∀ {X : Scheme.{u}} (_ : IsGeometricHom s (𝟙 X))
      {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))},
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X K →
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} S) X
          ((L(sheafExtendScalars (algebraMap R S) X)).obj K)}

/-- **The global Frobenius operator commutes with coefficient change**: through the comparison
`Ψ RΓ_c(X, K) ⟶ RΓ_c(X, Ψ K)`, the global operator `F_{c,m}` of the scalar extension of a Weil
complex is the scalar extension of the global operator `F_{c,m}`. -/
theorem globalOperator_graph_extendScalars (hG : ExtendScalarsCompatible G_R G_S hΨ)
    [IsGeometric aX] [HasCompactification aX] (W : WeilComplex (A := ModuleCat.{u + 1} R) aX)
    (hW : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} R) X W.obj) (m : ℕ)
    [IsProper (W.frobeniusIterate m)] :
    (L(sheafExtendScalars (algebraMap R S) s)).map
        (Correspondence.globalOperator G_R (W.graph G_R hW m) hW) ≫
      (rightDerivedLowerShriekExtendScalarsMap R S aX).app W.obj =
    (rightDerivedLowerShriekExtendScalarsMap R S aX).app W.obj ≫
      Correspondence.globalOperator G_S ((W.extendScalars S).graph G_S (hΨ (.id aX) hW) m)
        (hΨ (.id aX) hW) := by
  dsimp only [graph]
  rw [coeffIterate_extendScalars]
  exact globalOperator_ofGraph_extendScalars hG hW _ _ _

end WeilComplex

end AlgebraicGeometry.ProEtale
