/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DualBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Package
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Dual base change

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sk-d-proper-pushforward/sk-thm-sf-compatibility/thm-sf-dual-base-change.md`,
node `thm-sf-dual-base-change` (blueprint: thm-sf-dual-base-change).

The statement is on the finite-coefficient, unbounded derived categories supplied by
`def-sf-datum`.  The exchange is the canonical `Ex_!` of `def-exchange-projection`; the
dual map is its conjugate mate under the composite A1 adjunctions.  The coherence fields
below record naturality and horizontal and vertical pasting of that same canonical family,
and the final field records the A4 proper-coincidence form.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w uC vC uD vD uE vE
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The canonical direct-image compositor `R(g₁)_* ⋙ R(g₂)_* ≅ R(g₁ ≫ g₂)_*`.
(blueprint: `thm-sf-dual-base-change`, step 4). -/
noncomputable def dualBaseChangeDirectImageCompositor
    {Λ : Type (u + 1)} [CommRing Λ]
    {T S U : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ U) :
    R((g₁)_*[ModuleCat.{u + 1} Λ]) ⋙ R((g₂)_*[ModuleCat.{u + 1} Λ]) ≅
      R((g₁ ≫ g₂)_*[ModuleCat.{u + 1} Λ]) :=
  rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) g₁ g₂

/-- The canonical unbounded `R_!` compositor.  It is assembled from the unbounded
compactification composition isomorphism of `LowerShriekComposition.lean:276` and the canonical
compactification comparison maps; no `Nonempty` choice is made. -/
noncomputable def dualBaseChangeLowerShriekCompositor
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] ≅
      R(f ≫ g)_![ModuleCat.{u + 1} Λ] :=
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  Functor.isoWhiskerRight (rightDerivedLowerShriekIso Λ e.restrict).symm _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso Λ d e ≪≫
    rightDerivedLowerShriekIso Λ (d.comp e)

/-- The exceptional compositor obtained by conjugating the unbounded `R_!` compositor.
(blueprint: `thm-sf-dual-base-change`, step 4). -/
noncomputable def dualBaseChangeExceptionalCompositor
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    R(f ≫ g)^![Λ] ≅ R(g)^![Λ] ⋙ R(f)^![Λ] :=
  conjugateIsoEquiv (rightDerivedUpperShriekAdjunction Λ (f ≫ g))
    ((rightDerivedUpperShriekAdjunction Λ f).comp
      (rightDerivedUpperShriekAdjunction Λ g))
    (dualBaseChangeLowerShriekCompositor (Λ := Λ) f g)

/-- Two composable Cartesian squares and their Cartesian pasted square.  The second square is
geometric data: all three pullback witnesses are fields, while the mate and compositor isomorphisms
used below are definitions from the canonical derived six-functor constructions.
(blueprint: `thm-sf-dual-base-change`, step 4). -/
structure DualBaseChangePastingData where
  X : Scheme.{u}
  X₁ : Scheme.{u}
  X₂ : Scheme.{u}
  Y : Scheme.{u}
  Y₁ : Scheme.{u}
  Y₂ : Scheme.{u}
  f : X ⟶ Y
  f₁ : X₁ ⟶ Y₁
  f₂ : X₂ ⟶ Y₂
  g₁ : Y₁ ⟶ Y
  g₂ : Y₂ ⟶ Y₁
  g₁' : X₁ ⟶ X
  g₂' : X₂ ⟶ X₁
  sq₁ : IsPullback g₁' f₁ f g₁
  sq₂ : IsPullback g₂' f₂ f₁ g₂
  sq₁₂ : IsPullback (g₂' ≫ g₁') f₂ f (g₂ ≫ g₁)
  hcf : HasCompactification f
  hcf₁ : HasCompactification f₁
  hcf₂ : HasCompactification f₂
  hqf : QuasiCompact f
  hqf₁ : QuasiCompact f₁
  hqf₂ : QuasiCompact f₂
  E₀ : Scheme.{u}
  E₁ : Scheme.{u}
  E₂ : Scheme.{u}
  V₀ : Scheme.{u}
  V₁ : Scheme.{u}
  V₂ : Scheme.{u}
  e₁ : E₀ ⟶ E₁
  e₂ : E₁ ⟶ E₂
  a₁ : V₁ ⟶ E₁
  a₂ : V₂ ⟶ E₂
  a₁' : V₀ ⟶ E₀
  v₁ : V₀ ⟶ V₁
  v₂ : V₁ ⟶ V₂
  vsq₁ : IsPullback a₁' v₁ e₁ a₁
  vsq₂ : IsPullback a₁ v₂ e₂ a₂
  vsq₁₂ : IsPullback a₁' (v₁ ≫ v₂) (e₁ ≫ e₂) a₂
  hce₁ : HasCompactification e₁
  hce₂ : HasCompactification e₂
  hce₁₂ : HasCompactification (e₁ ≫ e₂)
  hqe₁ : QuasiCompact e₁
  hqe₂ : QuasiCompact e₂
  hqe₁₂ : QuasiCompact (e₁ ≫ e₂)
  hcv₁ : HasCompactification v₁
  hcv₂ : HasCompactification v₂
  hcv₁₂ : HasCompactification (v₁ ≫ v₂)
  hqv₁ : QuasiCompact v₁
  hqv₂ : QuasiCompact v₂
  hqv₁₂ : QuasiCompact (v₁ ≫ v₂)

/-- The horizontal mate-pasting equation for a `DualBaseChangePastingData` chain.  The two
`R(g)_*` compositors and the conjugated unbounded `R(f)_!` compositor are pinned by their named
canonical definitions (blueprint: `thm-sf-dual-base-change`, step 4). -/
noncomputable def dualBaseChangeHorizontalPasting
    (p : DualBaseChangePastingData) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : Prop :=
  letI := p.hcf
  letI := p.hcf₁
  letI := p.hcf₂
  letI := p.hqf
  letI := p.hqf₁
  letI := p.hqf₂
  let β₁ := rightDerivedUpperShriekLowerStarBaseChangeIso Λ p.sq₁
  let β₂ := rightDerivedUpperShriekLowerStarBaseChangeIso Λ p.sq₂
  let β₁₂ := rightDerivedUpperShriekLowerStarBaseChangeIso Λ p.sq₁₂
  let dY := (dualBaseChangeDirectImageCompositor (Λ := Λ) p.g₂ p.g₁).symm
  let dX := dualBaseChangeDirectImageCompositor (Λ := Λ) p.g₂' p.g₁'
  β₁₂ =
    Functor.isoWhiskerRight dY R(p.f)^![Λ] ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft R((p.g₂)_*[ModuleCat.{u + 1} Λ]) β₁ ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight β₂ R((p.g₁')_*[ModuleCat.{u + 1} Λ]) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R(p.f₂)^![Λ] dX

/-- The vertical mate-pasting equation.  It is the inverse-oriented equation for the same
canonical pasted-square comparison; its orientation and compositor placement differ from the
horizontal equation (blueprint: `thm-sf-dual-base-change`, step 4). -/
noncomputable def dualBaseChangeVerticalPasting
    (p : DualBaseChangePastingData) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : Prop :=
  letI := p.hce₁
  letI := p.hce₂
  letI := p.hce₁₂
  letI := p.hqe₁
  letI := p.hqe₂
  letI := p.hqe₁₂
  letI := p.hcv₁
  letI := p.hcv₂
  letI := p.hcv₁₂
  letI := p.hqv₁
  letI := p.hqv₂
  letI := p.hqv₁₂
  let β₁ := rightDerivedUpperShriekLowerStarBaseChangeIso Λ p.vsq₁
  let β₂ := rightDerivedUpperShriekLowerStarBaseChangeIso Λ p.vsq₂
  let β₁₂ := rightDerivedUpperShriekLowerStarBaseChangeIso Λ p.vsq₁₂
  let eF := dualBaseChangeExceptionalCompositor (Λ := Λ) p.e₁ p.e₂
  let eF' := dualBaseChangeExceptionalCompositor (Λ := Λ) p.v₁ p.v₂
  β₁₂ ≪≫ Functor.isoWhiskerRight eF' R((p.a₁')_*[ModuleCat.{u + 1} Λ]) =
    Functor.isoWhiskerLeft R((p.a₂)_*[ModuleCat.{u + 1} Λ]) eF ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight β₂ R(p.e₁)^![Λ] ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R(p.v₂)^![Λ] β₁

/-- Naturality in the square is stated for every actual pair of composable Cartesian squares;
the canonical mate of the pasted square is required to satisfy the horizontal and vertical mate
pasting equations with the canonical direct-image and exceptional compositors
(blueprint: `thm-sf-dual-base-change`, step 4). -/
def dualBaseChangeNaturality
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} [HasCompactification f] [HasCompactification f']
    [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (β : R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ R(f)^![Λ] ≅
      R(f')^![Λ] ⋙ R((g')_*[ModuleCat.{u + 1} Λ])) : Prop :=
  β = rightDerivedUpperShriekLowerStarBaseChangeIso Λ sq ∧
  ∀ (p : DualBaseChangePastingData),
    dualBaseChangeHorizontalPasting p Λ ∧ dualBaseChangeVerticalPasting p Λ

/-- Compatibility with horizontal and vertical pasting of actual Cartesian squares
(blueprint: `thm-sf-dual-base-change`, step 4). -/
def dualBaseChangePasting
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] : Prop :=
  ∃ (p : DualBaseChangePastingData),
    dualBaseChangeHorizontalPasting p Λ ∧ dualBaseChangeVerticalPasting p Λ

/-- Dual base change in the finite-coefficient unbounded datum.

Source place: node `thm-sf-dual-base-change` in
`literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-proper-pushforward/
sk-thm-sf-compatibility/thm-sf-dual-base-change.md`
(blueprint: thm-sf-dual-base-change).

The first witness is the canonical compact-support exchange
`Ex_! : Lg^* Rf_! ≅ Rf'_! Lg'^*`; the second is the inverse conjugate of that
exchange, hence `Rf^! Rg_* ≅ Rg'_* Rf'^!`.  The two coherence predicates are retained
for the same witness and the proper clause is expressed using the A4 identifications
`Ru_! ≅ Ru_*`.  The five proof steps are: (1) the canonical
`rightDerivedLowerShriekBaseChangeMap` exchange and its A2 invertibility; (2) the
composite A1 adjunctions; (3) the inverse conjugate mate; (4) mate-calculus naturality,
horizontal and vertical pasting on actual Cartesian squares with the canonical direct-image and
conjugated unbounded exceptional compositors and square comparisons; and (5) the A4 proper
substitution.
-/
theorem dualBaseChange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ Spec (.of k))
    [HasCompactification f] [QuasiCompact f] [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    [HasCompactification (f ≫ aY)]
    (S : SixOperationsPackage Λ k f aY)
    {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    [IsSeparated f] [LocallyOfFiniteType f]
    [IsSeparated f'] [LocallyOfFiniteType f']
    [IsSeparated g] [LocallyOfFiniteType g]
    [IsSeparated g'] [LocallyOfFiniteType g']
    [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g) :
    ∃ τ : R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ≅
        L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ],
      ∃ β : R((g)_*[ModuleCat.{u + 1} Λ]) ⋙ R(f)^![Λ] ≅
          R(f')^![Λ] ⋙ R((g')_*[ModuleCat.{u + 1} Λ]),
        τ.hom = rightDerivedLowerShriekBaseChangeMap Λ sq ∧
        β = rightDerivedUpperShriekLowerStarBaseChangeIso Λ sq ∧
        dualBaseChangeNaturality
          sq β ∧
        dualBaseChangePasting (Λ := Λ) ∧
        (IsProper g → IsProper g') ∧
        (∀ [IsProper g] [IsProper g'],
          ∃ β! : R(g)_![ModuleCat.{u + 1} Λ] ⋙ R(f)^![Λ] ≅
              R(f')^![Λ] ⋙ R(g')_![ModuleCat.{u + 1} Λ],
            β! = rightDerivedUpperShriekLowerShriekBaseChangeIso Λ sq) := by
  sorry

end AlgebraicGeometry.Etale
