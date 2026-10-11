/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF maintainer L
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Challenge: the five upstream declarations under the proper base change theorem

Decision of the human (2026-10-12 04:20 +08, `GOAL.md`): the targets of the run are the five
declarations of the source repository (branch `slopmaster2` at `7d675a263`) on which the earlier
target `thm-weil-pbc-bounded-below` rests. They are its five `sorry`s. This file holds their
statements verbatim, with `sorry` proofs (`stages/2-statements.md` §4):

1. `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`,
   `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`, line 133;
2. `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper`,
   `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine`, line 145;
3. `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed`,
   `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`, line 88;
4. `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`,
   `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`, line 120;
5. `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity`,
   `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty`, line 321.

(The line is that of the `theorem` keyword.) Target 5 is **not locked** until the upstream side
answers (proposal (c′), `GOAL.md`).

When the five are proved, the earlier target (`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`
and `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring` in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`) follows by the library's own
sorry-free assembly.

## Imports

This file imports only modules that define what the statements use, and none of the four modules
of the targets (each of them declares a target, so importing it would clash with the statement
here):

- `Mathlib.FieldTheory.IsAlgClosed.Basic`, `Mathlib.FieldTheory.IsSepClosed`: `IsAlgClosed`,
  `IsSepClosed`;
- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`;
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `AlgebraicGeometry.ProjectiveLine`,
  `AlgebraicGeometry.ProjectiveSpace.map`;
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`: the instance
  `ModuleCat.isGrothendieckAbelian_of_commRing` (priority high) through which the library's
  statements find `IsGrothendieckAbelian (ModuleCat Λ)`; without it the elaborated types differ
  from the library's (see the earlier version of this file, commit 2e1c48405);
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`: `R+(-)`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`: geometric points as points of the
  small étale site (`pointSmallEtale`);
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`;
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf`:
  `AlgebraicGeometry.Scheme.IsTorsionSheaf` and
  `AlgebraicGeometry.Etale.DerivedCategory.Plus.torsionHomology`;
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`: `Etale.baseChangeSourceFunctor`,
  `Etale.baseChangeTargetFunctor`, `Etale.baseChangeHomologyMap`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`: `Etale.cohomologyMap`.

## The two definitions restated

Targets 2 and 5 use `AlgebraicGeometry.Etale.HasTorsionBaseChange` and
`AlgebraicGeometry.Etale.HasInjectiveAcyclicity`, which the library defines in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` (lines 135 and 187 at
`7d675a263`), the module of target 5. That module cannot be imported here, so the two definitions
are restated below verbatim, under the same names. `tools/target_types.sh check` compares only the
theorems; the two definitions are compared with the library's by Lean comparator and by the target
review.

The theorems are written with their full names (no `namespace`), so that
`tools/target_types.sh` reads the names it looks up off the `theorem` lines.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

open AlgebraicGeometry Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Definitions

variable {X Y : Scheme.{u}}

/-- **The base change property** `PBC(f)` for torsion coefficients, verbatim from
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` (line 135 at
`7d675a263`): for every cartesian square with `f` on the right and every `K ∈ D⁺(X_ét, Λ)`
whose cohomology sheaves are all torsion, the derived base change map is an isomorphism.
(blueprint: def-weil-pbc-property) -/
def AlgebraicGeometry.Etale.HasTorsionBaseChange (f : X ⟶ Y) : Prop :=
  ∀ ⦃Y' X' : Scheme.{u}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄ (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
    Etale.DerivedCategory.Plus.torsionHomology Λ X K →
      IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)

/-- **Injective acyclicity** `IA(f)`, verbatim from
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` (line 187 at
`7d675a263`): for every cartesian square with `f` on the right and every injective torsion sheaf
`I` of `Λ`-modules on `X_ét`, `Rᵠf'_*(g'^{-1} I) = 0` for `q > 0`.
(blueprint: def-weil-pbc-injective-acyclicity-property) -/
def AlgebraicGeometry.Etale.HasInjectiveAcyclicity (f : X ⟶ Y) : Prop :=
  ∀ ⦃Y' X' : Scheme.{u}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄ (_sq : IsPullback g' f' f g)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)), IsTorsionSheaf I → Injective I →
      ∀ q : ℤ, 0 < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
            (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
          (R+((f')_*[ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
                ((g')^*[ModuleCat.{u + 1} Λ].obj I))))

end Definitions

/-- **Target 1. The exchange morphism of `ℙ¹` on a geometric stalk.** For a cartesian square
with `ℙ¹_S ⟶ S` on the right, a torsion sheaf `F` of `Λ`-modules on `ℙ¹_S`, and compatible
geometric points `σ`, `τ`, `ι` whose fields are algebraic over the residue fields, the stalk at
`τ` of the degree-`q` exchange morphism `g⁻¹ Rᵠp_* F ⟶ Rᵠf'_* g'⁻¹ F` is, up to *some* additive
isomorphisms of its source and target, the pullback map `Hᵠ(ℙ¹_k, F|) ⟶ Hᵠ(ℙ¹_{k'}, F|)`.
Verbatim from `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`
(line 133 at `7d675a263`).
(blueprint: `lemma-weil-pbc-p1-exchange-geometric-stalk`) -/
theorem AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k))
    (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (φ : S.residueField s ⟶ .of k),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (φ : T.residueField t ⟶ .of k'),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ T.fromSpecResidueField t = τ)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionSheaf F] (q : ℕ) :
    ∃ (e₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (e₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ ι)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, e₂ ((((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ ι)
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q (e₁ x) :=
  sorry

/-- **Target 2. Reduction of proper base change to the projective line**: if the projection
`ℙ¹_S ⟶ S` satisfies `AlgebraicGeometry.Etale.HasTorsionBaseChange` for every scheme `S`, then
so does every proper morphism of schemes. Verbatim from
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` (line 145 at `7d675a263`).
(blueprint: `prop-weil-pbc-reduction-to-projective-line`; Stacks 0A4F) -/
theorem AlgebraicGeometry.Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.HasTorsionBaseChange Λ f :=
  sorry

/-- **Target 3. Invariance of the cohomology of a proper curve under extension of algebraically
closed fields.** For algebraically closed `k ⊆ k'`, a proper curve `C` over `k`, a torsion étale
sheaf `F` of `Λ`-modules on `C` and a cartesian square over `Spec k' ⟶ Spec k`, the pullback map
`Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` on the cohomology of the underlying abelian sheaves is bijective.
Verbatim from `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` (line 88 at `7d675a263`).
(blueprint: `prop-weil-pbc-algebraically-closed-extension`; Stacks 0A5E) -/
theorem AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed {k k' : Type u}
    [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

/-- **Target 4. Passage between separably closed fields.** If the cohomology of proper curves is
invariant under extensions of algebraically closed fields (the hypothesis `H`, which is target 3),
then for separably closed `k ⊆ k'`, a proper curve `C` over `k`, a torsion étale sheaf `F` of
`Λ`-modules on `C` and a cartesian square over `Spec k' ⟶ Spec k`, the pullback map
`Hᵠ(C, F) ⟶ Hᵠ(C', ι'^* F)` is bijective. Verbatim from
`WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` (line 120 at `7d675a263`).
(blueprint: `lemma-weil-pbc-curve-separably-closed-passage`) -/
theorem AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed
    (H : ∀ {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
      {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
      (_ : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [Scheme.IsTorsionSheaf F] (q : ℕ),
      Function.Bijective (Etale.cohomologyMap ι'
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q))
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) :=
  sorry

/-- **Target 5 — NOT LOCKED until the upstream side answers** (decision of the human,
2026-10-12 04:20 +08: the human takes it to the upstream side with proposal (c′), which re-proves
`AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveLine` without it so that it leaves the
earlier target's closure). **Injective acyclicity implies the base change property**, over an
arbitrary coefficient ring: a proper morphism with injective acyclicity satisfies the base change
property for torsion coefficients. Verbatim from
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` (line 321 at
`7d675a263`).
(blueprint: `lemma-weil-pbc-property-iff-acyclicity`; Stacks 0A4B) -/
theorem AlgebraicGeometry.Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    (hf : Etale.HasInjectiveAcyclicity Λ f) : Etale.HasTorsionBaseChange Λ f :=
  sorry
