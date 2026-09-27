/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing

/-!
# Proper pushforward of correspondences and the proper trace comparison

A *proper pushforward diagram* pushes an endocorrespondence `(C, c, u)` on `(X, K)` along a
proper `f : X ⟶ Y` and a compatible `g : C ⟶ D`, where `b = (b₁, b₂) : D ⟶ Y × Y` is
correspondence shaped: the pushed correspondence has support `D`, legs `b`, coefficient
complex `K' = Rf_* K` and coefficient map `[f, g]_! u : b₂^* K' ⟶ b₁^! K'`. The two leg
relations `bᵢ ∘ g = f ∘ cᵢ` induce a map `h : Fix(c) ⟶ Fix(b)` on fixed schemes, along
which trace classes are compatible; specialising to `Y = s` recovers the equality between
the categorical trace of the global operator on compactly supported cohomology and the
integral of the trace class.

## Main definitions

- `AlgebraicGeometry.ProEtale.ProperPushforwardDiagram`: a proper pushforward diagram.
- `AlgebraicGeometry.ProEtale.ProperPushforwardDiagram.fixMap`: the induced map
  `h : Fix(c) ⟶ Fix(b)` on fixed schemes.
- `AlgebraicGeometry.ProEtale.ProperPushforwardDiagram.pushforwardCorrespondence`: the
  pushed correspondence `(D, b, [f, g]_! u)` (blueprint `sk-d-proper-pushforward`).

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMoorePushforward_traceClass`: the
  induced map on fixed schemes carries the trace class to the pushed trace class.
- `AlgebraicGeometry.ProEtale.GeometricOperations.trace_globalOperator_eq_integral_traceClass`:
  the trace of the global operator is the integral of the trace class.

## Implementation notes

Two departures from the sketch. The structure carries the support `D` of the target
together with its structure morphism and the statements that the legs `b₁`, `b₂` lie over
`s`, since that is what makes `b` a correspondence in the sense of blueprint `sk-d-corr`,
and it carries `f ≫ a_Y = a_X`, which the sketch leaves implicit in writing `Rf_*` between
geometric categories over `s`. The induced map `h : Fix(c) ⟶ Fix(b)` is *not* a field: the
fixed schemes are equalisers and the two leg relations force `g` to carry `Fix(c)` into
`Fix(b)`, so `h` is `ProperPushforwardDiagram.fixMap`, defined by the universal property,
and its two characterising identities are `fixMap_ι` and `fixMap_str`.

The coefficient map of `pushforwardCorrespondence` is a composite of comparison maps that
the package only postulates, so it is `opaque` for the reason explained in
`WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence`.

Properness of `h`, which the blueprint deduces from properness of `f` and `g` by factoring
`h` through `C ×_D Fix(b)`, is taken as an instance hypothesis, as is the compactification
needed for the Borel-Moore pushforward.
-/

@[expose] public section

universe u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X : Scheme.{u}} {aX : X ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}

/-- A *proper pushforward diagram* on an endocorrespondence `(C, c, u)` on `(X, K)`: a
geometric scheme `a_Y : Y ⟶ s`, a proper morphism `f : X ⟶ Y` over `s`, a
correspondence-shaped target `b = (b₁, b₂) : D ⟶ Y × Y` over `s`, and a morphism
`g : C ⟶ D` of supports with `bᵢ ∘ g = f ∘ cᵢ`:

```
        c₁         c₂
    X ←──── C ────→ X
    │       │       │
   f│      g│       │f
    ↓       ↓       ↓
    Y ←──── D ────→ Y
        b₁         b₂
```

No Cartesian condition on either leg square is imposed, and nothing is assumed proper over
`s` (blueprint: `sk-d-proper-pushforward`). -/
structure ProperPushforwardDiagram (c : Correspondence aX aX K K) where
  /-- the target geometric scheme `Y`. -/
  tgt : Scheme.{u}
  /-- the structure morphism `a_Y : Y ⟶ s`. -/
  tgtStr : tgt ⟶ s
  /-- the proper morphism `f : X ⟶ Y` along which the correspondence is pushed. -/
  f : X ⟶ tgt
  /-- `f` is proper. -/
  [isProper_f : IsProper f]
  /-- `f` is a morphism over `s`. -/
  f_comp : f ≫ tgtStr = aX
  /-- the support `D` of the target correspondence. -/
  supp : Scheme.{u}
  /-- the structure morphism `a_D : D ⟶ s`. -/
  str : supp ⟶ s
  /-- the exceptional leg `b₁ : D ⟶ Y`. -/
  fst : supp ⟶ tgt
  /-- the ordinary-pullback leg `b₂ : D ⟶ Y`. -/
  snd : supp ⟶ tgt
  /-- `b₁` is a morphism over `s`. -/
  fst_comp : fst ≫ tgtStr = str
  /-- `b₂` is a morphism over `s`. -/
  snd_comp : snd ≫ tgtStr = str
  /-- `b₁` admits a compactification, so that `b₁^!` is available. -/
  [hasCompactification_fst : HasCompactification fst]
  /-- the morphism `g : C ⟶ D` of supports. -/
  g : c.supp ⟶ supp
  /-- the relation `b₁ ∘ g = f ∘ c₁`. -/
  g_fst : g ≫ fst = c.fst ≫ f
  /-- the relation `b₂ ∘ g = f ∘ c₂`. -/
  g_snd : g ≫ snd = c.snd ≫ f

attribute [instance] ProperPushforwardDiagram.isProper_f
  ProperPushforwardDiagram.hasCompactification_fst

namespace ProperPushforwardDiagram

variable {c : Correspondence aX aX K K} (P : ProperPushforwardDiagram c)

@[simp]
lemma g_comp_str : P.g ≫ P.str = c.str := by
  rw [← P.fst_comp, ← Category.assoc, P.g_fst, Category.assoc, P.f_comp, c.fst_comp]

/-- The map `h : Fix(c) ⟶ Fix(b)` induced on fixed schemes: the two leg relations force
`g` to carry `Fix(c)` into `Fix(b)`, and the fixed schemes are equalisers
(part of blueprint `sk-d-proper-pushforward`). -/
noncomputable def fixMap : c.fix ⟶ equalizer P.fst P.snd :=
  equalizer.lift (c.fixι ≫ P.g) <| by
    have h : c.fixι ≫ c.fst = c.fixι ≫ c.snd := equalizer.condition _ _
    rw [Category.assoc, Category.assoc, P.g_fst, P.g_snd, ← Category.assoc, ← Category.assoc,
      h]

@[simp]
lemma fixMap_ι : P.fixMap ≫ equalizer.ι P.fst P.snd = c.fixι ≫ P.g :=
  equalizer.lift_ι _ _

@[simp]
lemma fixMap_str : P.fixMap ≫ equalizer.ι P.fst P.snd ≫ P.str = c.fixStr := by
  rw [← Category.assoc, fixMap_ι, Category.assoc, P.g_comp_str, Correspondence.fixStr]

/-- The coefficient map `[f, g]_! u = δ ∘ Rg_* u ∘ γ : b₂^* K' ⟶ b₁^! K'` of the pushed
correspondence, where `K' = Rf_* K`,

`γ : b₂^* Rf_* K ⟶ Rg_* g^* b₂^* Rf_* K ≃ Rg_* c₂^* f^* Rf_* K ⟶ Rg_* c₂^* K`

is the unit of `g^* ⊣ Rg_*` followed by the leg relation and the counit of `f^* ⊣ Rf_*`,
and `δ : Rg_* c₁^! K ⟶ b₁^! K'` is the exceptional adjoint of

`Rb_{1!} Rg_* c₁^! K ≃ Rf_! Rc_{1!} c₁^! K ⟶ Rf_! K ≃ K'`,

properness identifying `Rg_* = Rg_!` and `Rf_* = Rf_!`. -/
noncomputable opaque pushforwardCoeff :
    ((upperStar A P.snd).leftDerivedFunctor).obj
        (((lowerStar A P.f).rightDerivedFunctor).obj K) ⟶
      (rightDerivedUpperShriek A P.fst).obj
        (((lowerStar A P.f).rightDerivedFunctor).obj K) := 0

/-- The correspondence `(D, b, [f, g]_! u)` obtained by pushing an endocorrespondence
`(C, c, u)` forward along a proper pushforward diagram: an endocorrespondence on `(Y, K')`
for `K' = Rf_* K` (part of blueprint `sk-d-proper-pushforward`). -/
noncomputable def pushforwardCorrespondence :
    Correspondence P.tgtStr P.tgtStr
      (((lowerStar A P.f).rightDerivedFunctor).obj K)
      (((lowerStar A P.f).rightDerivedFunctor).obj K) where
  supp := P.supp
  str := P.str
  fst := P.fst
  snd := P.snd
  fst_comp := P.fst_comp
  snd_comp := P.snd_comp
  coeff := P.pushforwardCoeff

@[simp]
lemma fixMap_comp_pushforwardCorrespondence_fixStr :
    P.fixMap ≫ P.pushforwardCorrespondence.fixStr = c.fixStr :=
  P.fixMap_str

/-- The dualizing complexes of the two fixed schemes agree: the induced map `h` composed
with the structure morphism of `Fix(b)` is the structure morphism of `Fix(c)`. -/
lemma dualizing_fixStr (G : GeometricOperations A s) :
    G.dualizing c.fixStr =
      G.dualizing (P.fixMap ≫ P.pushforwardCorrespondence.fixStr) :=
  congrArg G.dualizing P.fixMap_comp_pushforwardCorrespondence_fixStr.symm

end ProperPushforwardDiagram

namespace GeometricOperations

/-- Proper pushforward compatibility: for an endocorrespondence `(C, c, u)` on `(X, K)` and
a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` with `f : X ⟶ Y` and `g : C ⟶ D`
proper, the induced map `h : Fix(c) ⟶ Fix(b)` on fixed schemes carries the trace class of
`u` to the trace class of the pushed coefficient map,

`h_* Tr_c(u) = Tr_b([f, g]_! u)` in `Hom(A_{Fix b}, ω_{Fix b})`.

No properness over `s` of `X`, `Y`, `C` or `D` is required, and neither leg square is
assumed Cartesian (blueprint: `sk-p-proper`). -/
theorem borelMoorePushforward_traceClass (G : GeometricOperations A s)
    {c : Correspondence aX aX K K} (P : ProperPushforwardDiagram c) [IsProper P.g]
    [HasCompactification P.fixMap] [IsProper P.fixMap] :
    G.borelMoorePushforward P.fixMap P.pushforwardCorrespondence.fixStr
        (G.traceClass c ≫ eqToHom (P.dualizing_fixStr G)) =
      G.traceClass P.pushforwardCorrespondence :=
  sorry

/-- Proper global trace comparison: for `X` proper over `s`, `K` in `Dᵇctf(X, A)` and an
endocorrespondence `(C, c, u)` on `(X, K)` whose ordinary leg `c₂` is proper, the
categorical trace of the global operator `T_c(u)` on compactly supported cohomology
`RΓ_c(X, K)` is the integral of the trace class over the fixed scheme,

`tr_A(T_c(u) ∣ RΓ_c(X, K)) = ∫_{Fix(c)} Tr_c(u)`.

This is the proper pushforward compatibility applied to the diagram with `Y = s`, `f = a_X`
and `g = a_C = a_X ∘ c₂`, followed by the point normalisation of blueprint `sk-p-pairing`
(blueprint: `sk-c-proper-global`). -/
theorem trace_globalOperator_eq_integral_traceClass
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))]
    (G : GeometricOperations A s) [HasCompactification aX] [IsProper aX]
    (hK : G.ctf X K) (c : Correspondence aX aX K K) [IsProper c.snd]
    [HasCompactification c.snd] [HasRightDual ((rightDerivedLowerShriek A aX).obj K)]
    [HasCompactification c.fixStr] [IsProper c.fixStr] :
    MonoidalCategory.trace (Correspondence.globalOperator G c) =
      G.integral c.fixStr (G.traceClass c) :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
