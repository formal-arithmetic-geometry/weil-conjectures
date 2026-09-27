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

- `AlgebraicGeometry.ProEtale.ProperPushforwardDiagram` (blueprint
  `sk-d-proper-pushforward`)
- `AlgebraicGeometry.ProEtale.ProperPushforwardDiagram.pushforwardCorrespondence`: the
  pushed correspondence `(D, b, [f, g]_! u)`

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.borelMoorePushforward_traceClass`
  (blueprint `sk-p-proper`)
- `AlgebraicGeometry.ProEtale.GeometricOperations.trace_globalOperator_eq_integral_traceClass`
  (blueprint `sk-c-proper-global`)
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X : Scheme.{u}} {aX : X ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}

/-- Blueprint `sk-d-proper-pushforward`: Proper pushforward of a correspondence and its trace.

A *proper pushforward diagram* on an endocorrespondence `(C, c, u)` on `(X, K)` consists of
a geometric scheme `a_Y : Y ⟶ s`, a proper morphism `f : X ⟶ Y` over `s`, a
correspondence-shaped target `b = (b₁, b₂) : D ⟶ Y × Y` over `s`, and a morphism
`g : C ⟶ D` of supports with `bᵢ ∘ g = f ∘ cᵢ` for `i = 1, 2`. No Cartesian condition on
either leg square is imposed, and nothing is assumed proper over `s`.

Out of this data the blueprint builds `K' = Rf_* K` and the pushed coefficient map
`[f, g]_! u : b₂^* K' ⟶ b₁^! K'`; that construction is
`ProperPushforwardDiagram.pushforwardCorrespondence`.

Two departures from the sketch. First, the structure carries the support `D` of the target
together with its structure morphism and the statements that the legs `b₁`, `b₂` lie over
`s`, since that is what makes `b` a correspondence in the sense of blueprint `sk-d-corr`,
and it carries `f ≫ a_Y = a_X`, which the sketch leaves implicit in writing `Rf_*` between
geometric categories over `s`. Second, the induced map `h : Fix(c) ⟶ Fix(b)` on fixed
schemes is carried as a field `fixMap`, pinned down by `fixMap_ι`: the fixed schemes are
equalisers, so `h` is the unique map with `h ≫ ι_{Fix b} = ι_{Fix c} ≫ g`, and it exists
because the two leg relations force `g` to carry `Fix(c)` into `Fix(b)`. The further field
`fixMap_str`, saying that `h` lies over the base, is a consequence of the others; it is
recorded because it is what makes the trace-class compatibility typecheck. -/
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
  /-- the induced map `h : Fix(c) ⟶ Fix(b)` on fixed schemes. -/
  fixMap : c.fix ⟶ equalizer fst snd
  /-- `h` is induced by `g`; this determines `h`, since `ι_{Fix b}` is a monomorphism. -/
  fixMap_ι : fixMap ≫ equalizer.ι fst snd = c.fixι ≫ g
  /-- `h` is a morphism over `s`; a consequence of the remaining fields. -/
  fixMap_str : fixMap ≫ equalizer.ι fst snd ≫ str = c.fixStr

attribute [instance] ProperPushforwardDiagram.isProper_f
  ProperPushforwardDiagram.hasCompactification_fst

/-- The correspondence `(D, b, [f, g]_! u)` obtained by pushing an endocorrespondence
`(C, c, u)` forward along a proper pushforward diagram. It is an endocorrespondence on
`(Y, K')` for `K' = Rf_* K`, with legs `b₁`, `b₂` and coefficient map

`[f, g]_! u = δ ∘ Rg_* u ∘ γ : b₂^* K' ⟶ b₁^! K'`,

where `γ : b₂^* Rf_* K ⟶ Rg_* g^* b₂^* Rf_* K ≃ Rg_* c₂^* f^* Rf_* K ⟶ Rg_* c₂^* K` is the
unit of `g^* ⊣ Rg_*` followed by the leg relation and the counit of `f^* ⊣ Rf_*`, and
`δ : Rg_* c₁^! K ⟶ b₁^! K'` is the exceptional adjoint of
`Rb_{1!} Rg_* c₁^! K ≃ Rf_! Rc_{1!} c₁^! K ⟶ Rf_! K ≃ K'`, properness identifying
`Rg_* = Rg_!` and `Rf_* = Rf_!`. The composite uses comparison maps that the package
`AlgebraicGeometry.ProEtale.GeometricOperations` only postulates, so the coefficient field
is stated with its precise type and left with a `sorry` body. -/
noncomputable def ProperPushforwardDiagram.pushforwardCorrespondence
    {c : Correspondence aX aX K K} (P : ProperPushforwardDiagram c) :
    Correspondence P.tgtStr P.tgtStr
      (((lowerStar A P.f).rightDerivedFunctor).obj K)
      (((lowerStar A P.f).rightDerivedFunctor).obj K) where
  supp := P.supp
  str := P.str
  fst := P.fst
  snd := P.snd
  fst_comp := P.fst_comp
  snd_comp := P.snd_comp
  coeff := sorry

namespace GeometricOperations

/-- Blueprint `sk-p-proper`: Proper pushforward compatibility.

For an endocorrespondence `(C, c, u)` on `(X, K)` and a proper pushforward diagram
`(f, g) : (C, c) ⟶ (D, b)` with `f : X ⟶ Y` and `g : C ⟶ D` proper, the induced map
`h : Fix(c) ⟶ Fix(b)` on fixed schemes carries the trace class of `u` to the trace class of
the pushed coefficient map:

`h_* Tr_c(u) = Tr_b([f, g]_! u)` in `Hom(A_{Fix b}, ω_{Fix b})`,

where `h_*` is the Borel-Moore pushforward of blueprint `sk-d-integral`. No properness over
`s` of `X`, `Y`, `C` or `D` is required, and neither leg square is assumed Cartesian.

Properness of `h`, which the blueprint deduces from properness of `f` and `g` by factoring
`h` through `C ×_D Fix(b)`, is taken as an instance hypothesis, as is the compactification
needed for the Borel-Moore pushforward. The left-hand side is transported along
`fixMap_str`, which identifies `h ≫ a_{Fix b}` with `a_{Fix c}`. -/
theorem borelMoorePushforward_traceClass (G : GeometricOperations A s)
    {c : Correspondence aX aX K K} (P : ProperPushforwardDiagram c) [IsProper P.g]
    [HasCompactification P.fixMap] [IsProper P.fixMap] :
    G.borelMoorePushforward P.fixMap P.pushforwardCorrespondence.fixStr
        (G.traceClass c ≫ eqToHom (by rw [← P.fixMap_str]; rfl)) =
      G.traceClass P.pushforwardCorrespondence :=
  sorry

/-- Blueprint `sk-c-proper-global`: Proper global trace comparison.

Let `X` be proper over `s`, let `K` lie in `Dᵇctf(X, A)` and let `(C, c, u)` be an
endocorrespondence on `(X, K)` whose ordinary leg `c₂` is proper. Then the categorical
trace of the global operator `T_c(u)` on compactly supported cohomology `RΓ_c(X, K)` is the
integral of the trace class over the fixed scheme:

`tr_A(T_c(u) ∣ RΓ_c(X, K)) = ∫_{Fix(c)} Tr_c(u)`.

This is the proper pushforward compatibility applied to the diagram with `Y = s`, `f = a_X`
and `g = a_C = a_X ∘ c₂`, followed by the point normalisation of blueprint `sk-p-pairing`.

Perfectness of `RΓ_c(X, K)`, which the blueprint gets from `K ∈ Dᵇctf(X, A)` and properness
of `X`, is rendered as `HasRightDual` on that object, and `tr_A` is
`CategoryTheory.MonoidalCategory.trace`, taken in `D(s, A)`; this project installs a
monoidal structure on a derived category but not yet a braiding, so the symmetry of
`D(s, A)` is an instance hypothesis. Properness of `Fix(c)` over `s`, which follows from
properness of `X` and of `c₂` together with separatedness, is an instance hypothesis too,
since it is what makes the integral defined. -/
theorem trace_globalOperator_eq_integral_traceClass
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))]
    (G : GeometricOperations A s) [HasCompactification aX] [IsProper aX]
    (_hK : G.ctf X K) (c : Correspondence aX aX K K) [IsProper c.snd]
    [HasCompactification c.snd] [HasRightDual ((rightDerivedLowerShriek A aX).obj K)]
    [HasCompactification c.fixStr] [IsProper c.fixStr] :
    MonoidalCategory.trace (Correspondence.globalOperator G c) =
      G.integral c.fixStr (G.traceClass c) :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
