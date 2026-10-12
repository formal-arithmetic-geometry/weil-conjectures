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
- `AlgebraicGeometry.ProEtale.ProperPushforwardDiagram.pushforwardCoeff`: the pushed
  coefficient map `[f, g]_! u = δ ∘ Rg_* u ∘ γ`, with `γ = pushforwardCoeffUnit` and
  `δ = pushforwardCoeffCounit`.
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
fixed schemes are equalizers and the two leg relations force `g` to carry `Fix(c)` into
`Fix(b)`, so `h` is `ProperPushforwardDiagram.fixMap`, defined by the universal property,
and its two characterising identities are `fixMap_ι` and `fixMap_str`.

The coefficient map `pushforwardCoeff` of `pushforwardCorrespondence` is the composite
`δ ∘ Rg_* u ∘ γ` of `pushforwardCoeffUnit` (`γ`) and `pushforwardCoeffCounit` (`δ`), built
from the adjunctions of `Lg^* ⊣ Rg_*`, `Lf^* ⊣ Rf_*`, `Rc_{1!} ⊣ c₁^!` and
`Rb_{1!} ⊣ b₁^!` with the package fields `properComparison` (for `f` and `g`) and
`lowerShriekComp`, so it needs `g` proper and `g ≫ b₁` compactifiable; both are fields
of `ProperPushforwardDiagram`. The trace class of the pushed correspondence needs `Rf_* K`
in `Dᵇctf`, which is `GeometricCoefficients.ctf_lowerStar`.

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
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  {s X : Scheme.{u}} {aX : X ⟶ s}
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

The morphism `g` is proper, as the blueprint requires, and `g ≫ b₁` admits a
compactification. No Cartesian condition on either leg square is imposed, and nothing is
assumed proper over `s` (blueprint: `sk-d-proper-pushforward`). -/
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
  /-- `g` is proper. -/
  [isProper_g : IsProper g]
  /-- `g ≫ b₁` admits a compactification, so that `Rg_! ⋙ Rb_{1!} ≃ R(g ≫ b₁)_!` is
  available. TODO: this follows from `g` proper and `b₁` compactifiable once the project
  proves that compactifiable morphisms are closed under composition, and should then be
  removed. -/
  [hasCompactification_g_comp_fst : HasCompactification (g ≫ fst)]
  /-- the relation `b₁ ∘ g = f ∘ c₁`. -/
  g_fst : g ≫ fst = c.fst ≫ f
  /-- the relation `b₂ ∘ g = f ∘ c₂`. -/
  g_snd : g ≫ snd = c.snd ≫ f

attribute [instance] ProperPushforwardDiagram.isProper_f
  ProperPushforwardDiagram.hasCompactification_fst
  ProperPushforwardDiagram.isProper_g
  ProperPushforwardDiagram.hasCompactification_g_comp_fst

namespace ProperPushforwardDiagram

variable {c : Correspondence aX aX K K} (P : ProperPushforwardDiagram c)

@[simp]
lemma g_comp_str : P.g ≫ P.str = c.str := by
  rw [← P.fst_comp, ← Category.assoc, P.g_fst, Category.assoc, P.f_comp, c.fst_comp]

/-- The map `h : Fix(c) ⟶ Fix(b)` induced on fixed schemes: the two leg relations force
`g` to carry `Fix(c)` into `Fix(b)`, and the fixed schemes are equalizers
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

/-- The inclusion `Fix(b) ⟶ D` of the fixed scheme of the target is a closed immersion when
`Y` is separated over `s`: it is the base change of the diagonal of `a_Y` along
`b = (b₁, b₂) : D ⟶ Y ×_s Y`. -/
instance isClosedImmersion_equalizer_ι [IsSeparated P.tgtStr] :
    IsClosedImmersion (equalizer.ι P.fst P.snd) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_equalizer_ι_diagonal P.fst P.snd (P.fst_comp.trans P.snd_comp.symm)).flip
    (inferInstanceAs (IsClosedImmersion (pullback.diagonal P.tgtStr)))

/-- The first factor `κ = (i_c, h) : Fix(c) ⟶ C ×_D Fix(b)` of the factorisation
`h = π ∘ κ` of the induced map on fixed schemes, where `π : C ×_D Fix(b) ⟶ Fix(b)` is the base
change of `g` (part of blueprint `lem-trf-fixed-map-proper`). -/
noncomputable def fixMapFactor : c.fix ⟶ pullback P.g (equalizer.ι P.fst P.snd) :=
  pullback.lift c.fixι P.fixMap P.fixMap_ι.symm

@[reassoc (attr := simp)]
lemma fixMapFactor_snd :
    P.fixMapFactor ≫ pullback.snd P.g (equalizer.ι P.fst P.snd) = P.fixMap :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma fixMapFactor_fst :
    P.fixMapFactor ≫ pullback.fst P.g (equalizer.ι P.fst P.snd) = c.fixι :=
  pullback.lift_fst _ _ _

/-- `κ : Fix(c) ⟶ C ×_D Fix(b)` is a closed immersion: its composite with the separated
projection to `C` is the closed immersion `i_c : Fix(c) ⟶ C`. -/
instance isClosedImmersion_fixMapFactor [IsSeparated aX] [IsSeparated P.tgtStr] :
    IsClosedImmersion P.fixMapFactor := by
  have : IsClosedImmersion (P.fixMapFactor ≫ pullback.fst P.g (equalizer.ι P.fst P.snd)) := by
    rw [fixMapFactor_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst P.g (equalizer.ι P.fst P.snd))

/-- The induced map `h : Fix(c) ⟶ Fix(b)` is proper: `i_b ∘ h = g ∘ i_c` is proper and the
closed immersion `i_b` is separated. -/
instance isProper_fixMap [IsSeparated aX] [IsSeparated P.tgtStr] : IsProper P.fixMap := by
  have : IsProper (P.fixMap ≫ equalizer.ι P.fst P.snd) := by
    rw [fixMap_ι]
    infer_instance
  exact IsProper.of_comp _ (equalizer.ι P.fst P.snd)

/-- Blueprint `lem-trf-fixed-map-proper`: for `X` and `Y` separated over `s`,

1. the induced map `h : Fix(c) ⟶ Fix(b)` factors as `h = π ∘ κ` with `π` the base change of
   `g` along `i_b : Fix(b) ⟶ D` and `κ` a closed immersion;
2. `h` and `q = f × f : X ×_s X ⟶ Y ×_s Y` are proper. -/
theorem fixMap_factorization_and_isProper [IsSeparated aX] [IsSeparated P.tgtStr] :
    P.fixMapFactor ≫ pullback.snd P.g (equalizer.ι P.fst P.snd) = P.fixMap ∧
      IsClosedImmersion P.fixMapFactor ∧ IsProper P.fixMap ∧
      IsProper (pullback.map aX aX P.tgtStr P.tgtStr P.f P.f (𝟙 s)
        ((Category.comp_id _).trans P.f_comp.symm) ((Category.comp_id _).trans P.f_comp.symm)) :=
  ⟨P.fixMapFactor_snd, inferInstance, inferInstance,
    MorphismProperty.pullbackMap (P := @IsProper) (inferInstanceAs (IsProper P.f))
      (inferInstanceAs (IsProper P.f))
      P.f_comp.symm P.f_comp.symm⟩

/-- The support map `b = (b₁, b₂) : D ⟶ Y ×_s Y` of the target. -/
noncomputable def toProd : P.supp ⟶ pullback P.tgtStr P.tgtStr :=
  pullback.lift P.fst P.snd (P.fst_comp.trans P.snd_comp.symm)

section

variable [DerivedBraiding A]

/-- The first half `γ : b₂^* Rf_* K ⟶ Rg_* c₂^* K` of the pushed coefficient map: the
composite

`b₂^* Rf_* K ⟶ Rg_* g^* b₂^* Rf_* K ≃ Rg_* c₂^* f^* Rf_* K ⟶ Rg_* c₂^* K`

of the unit of `g^* ⊣ Rg_*`, the leg relation and the counit of `f^* ⊣ Rf_*`
(blueprint `def-trf-coefficient-pushforward` (1), subsection `sk-d-proper-pushforward`). -/
noncomputable def pushforwardCoeffUnit :
    ((upperStar A P.snd).leftDerivedFunctor).obj
        (((lowerStar A P.f).rightDerivedFunctor).obj K) ⟶
      ((lowerStar A P.g).rightDerivedFunctor).obj
        (((upperStar A c.snd).leftDerivedFunctor).obj K) :=
  (derivedUpperStarLowerStarAdjunction A P.g).unit.app _ ≫
    ((lowerStar A P.g).rightDerivedFunctor).map
      (((leftDerivedUpperStarComp A P.g P.snd).symm ≪≫ leftDerivedUpperStarCongr A P.g_snd ≪≫
          leftDerivedUpperStarComp A c.snd P.f).hom.app _ ≫
        ((upperStar A c.snd).leftDerivedFunctor).map
          ((derivedUpperStarLowerStarAdjunction A P.f).counit.app K))

variable [IsGeometric aX] [IsGeometric P.tgtStr] [IsGeometric c.str] [IsGeometric P.str]

/-- The second half `δ : Rg_* c₁^! K ⟶ b₁^! Rf_* K` of the pushed coefficient map, for
`K ∈ Dᵇctf(X)` on geometric schemes: the exceptional adjoint of

`Rb_{1!} Rg_* c₁^! K ≃ Rf_! Rc_{1!} c₁^! K ⟶ Rf_! K ≃ Rf_* K`,

properness identifying `Rg_* = Rg_!` and `Rf_* = Rf_!`
(blueprint `def-trf-coefficient-pushforward` (2), subsection `sk-d-proper-pushforward`). -/
noncomputable def pushforwardCoeffCounit (G : GeometricOperations A s) (hK : G.ctf X K) :
    ((lowerStar A P.g).rightDerivedFunctor).obj ((rightDerivedUpperShriek A c.fst).obj K) ⟶
      (rightDerivedUpperShriek A P.fst).obj
        (((lowerStar A P.f).rightDerivedFunctor).obj K) :=
  have : HasCompactification (c.fst ≫ P.f) := .of_eq P.g_fst
  have hg : IsGeometricHom s P.g := .mk P.g_comp_str
  have hfst : IsGeometricHom s P.fst := .mk P.fst_comp
  have hcfst : IsGeometricHom s c.fst := .mk c.fst_comp
  have hf : IsGeometricHom s P.f := .mk P.f_comp
  have hc : G.ctf c.supp ((rightDerivedUpperShriek A c.fst).obj K) :=
    G.ctf_upperShriek c.fst hcfst hK
  G.exceptionalHomEquiv P.fst hfst (G.ctf_lowerStar P.g hg hc) (G.ctf_lowerStar P.f hf hK)
    ((rightDerivedLowerShriek A P.fst).map ((G.properComparison P.g hg).inv.app ⟨_, hc⟩).hom ≫
      ((G.lowerShriekComp P.g P.fst hg hfst (hg.comp hfst) ≪≫
          ctfLowerShriekCongr P.g_fst _ _ ≪≫
          (G.lowerShriekComp c.fst P.f hcfst hf (hcfst.comp hf)).symm).hom.app ⟨_, hc⟩).hom ≫
      (rightDerivedLowerShriek A P.f).map (G.exceptionalCounit c.fst hcfst K hK) ≫
      ((G.properComparison P.f hf).hom.app ⟨K, hK⟩).hom)

/-- The coefficient map `[f, g]_! u = δ ∘ Rg_* u ∘ γ : b₂^* K' ⟶ b₁^! K'` of the pushed
correspondence, where `K' = Rf_* K`, `γ` is `pushforwardCoeffUnit` and `δ` is
`pushforwardCoeffCounit` (blueprint `def-trf-coefficient-pushforward` (3), subsection
`sk-d-proper-pushforward`). -/
noncomputable def pushforwardCoeff (G : GeometricOperations A s) (hK : G.ctf X K) :
    ((upperStar A P.snd).leftDerivedFunctor).obj
        (((lowerStar A P.f).rightDerivedFunctor).obj K) ⟶
      (rightDerivedUpperShriek A P.fst).obj
        (((lowerStar A P.f).rightDerivedFunctor).obj K) :=
  P.pushforwardCoeffUnit ≫ ((lowerStar A P.g).rightDerivedFunctor).map c.coeff ≫
    P.pushforwardCoeffCounit G hK

/-- The correspondence `(D, b, [f, g]_! u)` obtained by pushing an endocorrespondence
`(C, c, u)` with `K ∈ Dᵇctf(X)` forward along a proper pushforward diagram of geometric
schemes: an endocorrespondence on `(Y, K')` for `K' = Rf_* K`
(part of blueprint `sk-d-proper-pushforward`). -/
noncomputable def pushforwardCorrespondence (G : GeometricOperations A s) (hK : G.ctf X K) :
    Correspondence P.tgtStr P.tgtStr
      (((lowerStar A P.f).rightDerivedFunctor).obj K)
      (((lowerStar A P.f).rightDerivedFunctor).obj K) where
  supp := P.supp
  str := P.str
  fst := P.fst
  snd := P.snd
  fst_comp := P.fst_comp
  snd_comp := P.snd_comp
  coeff := P.pushforwardCoeff G hK

/-- The support map of the pushed correspondence is `P.toProd`, which does not depend on the
package. -/
@[simp]
lemma pushforwardCorrespondence_toProd (G : GeometricOperations A s) (hK : G.ctf X K) :
    (P.pushforwardCorrespondence G hK).toProd = P.toProd :=
  rfl

/-- The support map of the pushed correspondence is `P.toProd`, so it admits a
compactification when `P.toProd` does. -/
instance hasCompactification_pushforwardCorrespondence_toProd (G : GeometricOperations A s)
    (hK : G.ctf X K) [HasCompactification P.toProd] :
    HasCompactification (P.pushforwardCorrespondence G hK).toProd :=
  inferInstanceAs (HasCompactification P.toProd)

/-- The structure morphism of the pushed correspondence is that of `D`, which is geometric. -/
instance isGeometric_pushforwardCorrespondence_str (G : GeometricOperations A s)
    (hK : G.ctf X K) : IsGeometric (P.pushforwardCorrespondence G hK).str :=
  inferInstanceAs (IsGeometric P.str)

@[simp]
lemma fixMap_comp_pushforwardCorrespondence_fixStr {G : GeometricOperations A s}
    {hK : G.ctf X K} : P.fixMap ≫ (P.pushforwardCorrespondence G hK).fixStr = c.fixStr :=
  P.fixMap_str

/-- The dualizing complexes of the two fixed schemes agree: the induced map `h` composed
with the structure morphism of `Fix(b)` is the structure morphism of `Fix(c)`. -/
lemma dualizing_fixStr {G : GeometricOperations A s} {hK : G.ctf X K} :
    G.dualizing c.fixStr =
      G.dualizing (P.fixMap ≫ (P.pushforwardCorrespondence G hK).fixStr) :=
  congrArg G.dualizing P.fixMap_comp_pushforwardCorrespondence_fixStr.symm

end

end ProperPushforwardDiagram

namespace GeometricOperations

variable [DerivedBraiding A]

/-- Proper pushforward compatibility: for an endocorrespondence `(C, c, u)` on `(X, K)` and
a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` with `f : X ⟶ Y` and `g : C ⟶ D`
proper, the induced map `h : Fix(c) ⟶ Fix(b)` on fixed schemes carries the trace class of
`u` to the trace class of the pushed coefficient map,

`h_* Tr_c(u) = Tr_b([f, g]_! u)` in `Hom(A_{Fix b}, ω_{Fix b})`.

No properness over `s` of `X`, `Y`, `C` or `D` is required, and neither leg square is
assumed Cartesian (blueprint: `sk-p-proper`). -/
theorem borelMoorePushforward_traceClass (G : GeometricOperations A s)
    [s.IsSpecOfField] [HasCompactification aX] [QuasiCompact aX]
    (hK : G.ctf X K) {c : Correspondence aX aX K K} [IsGeometric c.str]
    [HasCompactification c.toProd]
    (P : ProperPushforwardDiagram c) [HasCompactification P.tgtStr] [QuasiCompact P.tgtStr]
    [IsGeometric P.str] [HasCompactification P.toProd]
    [HasCompactification P.fixMap] [IsProper P.fixMap] :
    haveI : IsGeometric (P.fixMap ≫ (P.pushforwardCorrespondence G hK).fixStr) :=
      IsGeometric.of_eq P.fixMap_comp_pushforwardCorrespondence_fixStr.symm
    G.borelMoorePushforward P.fixMap (P.pushforwardCorrespondence G hK).fixStr
        (G.traceClass c hK ≫ eqToHom P.dualizing_fixStr) =
      G.traceClass (P.pushforwardCorrespondence G hK)
        (G.ctf_lowerStar P.f (.mk P.f_comp) hK) :=
  sorry

/-- Proper global trace comparison: for `X` geometric and proper over `s`, `K` in
`Dᵇctf(X, A)` and an endocorrespondence `(C, c, u)` on `(X, K)` with geometric support whose
ordinary leg `c₂` is proper, the categorical trace of the global operator `T_c(u)` on
compactly supported cohomology `RΓ_c(X, K)` is the integral of the trace class over the fixed
scheme,

`tr_A(T_c(u) ∣ RΓ_c(X, K)) = ∫_{Fix(c)} Tr_c(u)`.

This is the proper pushforward compatibility applied to the diagram with `Y = s`, `f = a_X`
and `g = a_C = a_X ∘ c₂`, followed by the point normalisation of blueprint `sk-p-pairing`
(blueprint: `sk-c-proper-global`). -/
theorem trace_globalOperator_eq_integral_traceClass (G : GeometricOperations A s)
    [HasCompactification aX] [IsProper aX]
    [s.IsSpecOfField] (hK : G.ctf X K) (c : Correspondence aX aX K K) [IsGeometric c.str]
    [IsProper c.snd] [HasCompactification c.str] [HasCompactification c.toProd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj K)]
    [HasCompactification c.fixStr] [IsProper c.fixStr] :
    MonoidalCategory.trace (Correspondence.globalOperator G c hK) =
      G.integral c.fixStr (G.traceClass c hK) :=
  sorry

/-- Blueprint `thm-trf-lefschetz-verdier`, the Lefschetz-Verdier trace comparison: for `X`
proper over `s`, an endocorrespondence `(C, c, u)` on `(X, K)` with proper ordinary leg `c₂` and
whose fixed scheme is proper over `s` and a finite disjoint union of clopen pieces
`j_β : β ⟶ Fix(c)`, the trace of the global operator on `RΓ_c(X, K)` is the sum of the local
terms, `tr_A(T_c(u) ∣ RΓ_c(X, K)) = ∑_β LT_β(u)`. It combines the proper global trace
comparison `trace_globalOperator_eq_integral_traceClass` (blueprint `sk-c-proper-global`) with
the decomposition into local terms `integral_eq_sum_localTerm` (blueprint `sk-p-local`). -/
theorem trace_globalOperator_eq_sum_localTerm (G : GeometricOperations A s)
    [HasCompactification aX] [IsProper aX]
    [s.IsSpecOfField] (hK : G.ctf X K) (c : Correspondence aX aX K K) [IsGeometric c.str]
    [IsProper c.snd] [HasCompactification c.str] [HasCompactification c.toProd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj K)]
    [HasCompactification c.fixStr] [IsProper c.fixStr] {ι : Type u} [Fintype ι]
    {B : ι → Scheme.{u}} (j : ∀ i, B i ⟶ c.fix) [∀ i, IsOpenImmersion (j i)]
    (hclosed : ∀ i, IsClosed (Set.range (j i).base))
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).base) (Set.range (j i').base))
    (hcover : ⋃ i, Set.range (j i).base = Set.univ) :
    MonoidalCategory.trace (Correspondence.globalOperator G c hK) =
      ∑ i, G.localTerm c.fixStr (j i) (hclosed i) (G.traceClass c hK) := by
  rw [G.trace_globalOperator_eq_integral_traceClass hK c,
    G.integral_eq_sum_localTerm c.fixStr j hclosed hdisj hcover]

end GeometricOperations

end AlgebraicGeometry.ProEtale
