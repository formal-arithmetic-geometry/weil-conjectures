# AlgebraicGeometry.Etale.CompactificationUpperShriek retirement

## Reason

The assigned coproduct theorem is used only by the legacy
`AlgebraicGeometry.Etale.CompactificationUpperShriek` namespace. No other source opens or
references that namespace or its compactification-specific constructions. The active
`AlgebraicGeometry.Etale.rightDerivedUpperShriek` lives in `Derived.UpperShriek`; for general
coefficients it takes an explicit left-adjoint instance. Its finite-module-coefficient
instance is already proved via `Derived.LowerShriekLeftAdjoint`.

Retire the unused auxiliary route and withdraw its only remaining obligation, under
brief step 8d. This is pruning, not a proof or a claimed counterexample to the historical
arbitrary-Grothendieck-coefficient assertion. Its cited finite-amplitude argument does
not establish that generality: the available geometric theorem treats torsion module
coefficients. No replacement weaker theorem is introduced.

The adapted legacy module is unclaimed (claim checked in `coord/claims`). Its two original
public imports remain, so the two direct importing modules need no source change. There
are no forced adaptations and no target statement or active definition changes.
The removed definitions cannot be made aliases of the active API with their original
types: their unconditional adjoint-existence hypothesis is precisely the unused stronger
assertion being withdrawn. No consumer needs a compatibility declaration.

The unit `sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps` arrays.
The existing finite-coefficient ambient-adjoint theorem, attached to
`thm-amb-etale-exceptional-adjoint`, still uses the same compactification, preservation
of coproducts, and Brown representability. This delivery leaves that theorem and its
imports in place. No unit route is bypassed.

## Old

The complete original legacy module (including implicit binders, instances and notation):

```lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.Grothendieck
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import Sheaf.AlgebraicGeometry.ProperEtaleDerivedLowerStarCoproducts

/-!

# Derived Upper Shriek

The exceptional inverse image `Rf^!` along a morphism `f : X ⟶ Y` admitting a compactification
is *constructed* here out of the two halves of the derived lower shriek
`Rf_! = Di_! ⋙ Rg_*` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:

`Rf^! := Rg^! ⋙ Di^*`,

where `Rg^!` is a chosen right adjoint of the derived pushforward `Rg_*` along the *proper*
morphism `g`, and `Di^*` is the levelwise pullback along the open immersion `i`, which is right
adjoint to `Di_!` by `Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. The
adjunction `Rf_! ⊣ Rf^!` is then the composite of these two adjunctions. The only input taken
for granted is that `Rg_*` is a left adjoint for proper `g`; it is *not* assumed that `Rf_!`
is a left adjoint for a general `f`, that is a theorem here.

`Rf^!` is only defined on the unbounded derived categories: it does not preserve bounded
below objects in general, so it does not restrict to `D⁺`.

# Main Results

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isProper` : for `g` proper,
  `Rg_*` is a left adjoint on `D(Z_ét)`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactification` : `Rf^!` with respect to
  a compactification `c`, with scoped notation `Rf^!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekOfCompactificationAdjunction` : the
  adjunction `Rf_!(c)[A] ⊣ Rf^!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek` : `Rf^! : D(Y_ét) ⥤ D(X_ét)` for the
  chosen compactification, with scoped notation `R(f)^![A]`.

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction` : the adjunction `Rf_! ⊣ Rf^!`
  on the unbounded derived categories.

- `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` : `Rf_!` is a left adjoint
  on `D(X_ét)`, a consequence of the previous item.

## Implementation notes

* `isLeftAdjoint_rightDerivedLowerStar_of_isProper` applies Brown representability to the
  coproduct-preservation theorem
  `proper_rightDerivedLowerStar_preservesCoproducts_for_grothendieck`.
* `Rg^!` for proper `g` is `Functor.rightAdjoint`, i.e. an arbitrary choice of right adjoint
  extracted from the instance, not a construction. Only the adjunction
  `Adjunction.ofIsLeftAdjoint` should be used about it. The composite `Rf^!` is a construction
  out of it and `Di^*`.
* The derived adjunction `Di_! ⊣ Di^*` goes through the total left derived functor of `i_!`,
  which is why the K-flat hypotheses on the coefficient category `A` of
  `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek` are needed for the
  adjunctions of this file, though not for the definition of `Rf^!` itself.
* There is no underived `f^!`, but the notation still carries the `R` of `R(f)_![A]` and
  `R((g)_*[A])`, to mark that it lives on derived categories rather than on sheaves.

## TODO

* The composition `R(f ≫ g)^! ≅ R(g)^! ⋙ R(f)^!`, from the corresponding compatibility
  of `Rf_!`.
* For `f` étale, `Rf^! = f^*`; for `f` proper, `Rf^!` is right adjoint to `Rf_*`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale.CompactificationUpperShriek

section Proper

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g]

/-- For a proper morphism `g : Z ⟶ Y`, the derived pushforward `Rg_* : D(Z_ét) ⥤ D(Y_ét)` is a
left adjoint; its right adjoint is the exceptional inverse image `Rg^!` along `g`. -/
instance isLeftAdjoint_rightDerivedLowerStar_of_isProper :
    ((g)_*[A]).rightDerivedFunctor.IsLeftAdjoint := by
  let : Limits.HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf Z.smallEtaleTopology A) := IsGrothendieckAbelian.hasColimits _
  let : Limits.HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf Y.smallEtaleTopology A) := IsGrothendieckAbelian.hasColimits _
  let : Limits.HasCoproducts.{u + 1}
      (DerivedCategory (Sheaf Z.smallEtaleTopology A)) := derived_hasCoproducts
  let : Limits.HasCoproducts.{u + 1}
      (DerivedCategory (Sheaf Y.smallEtaleTopology A)) := derived_hasCoproducts
  let adj := mapDerivedUpperStarLowerStarAdjunction A g
  let : ((g)_*[A]).rightDerivedFunctor.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  let : ((g)_*[A]).rightDerivedFunctor.IsTriangulated := adj.isTriangulated_rightAdjoint
  let : ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
      ((g)_*[A]).rightDerivedFunctor := fun J ↦
    proper_rightDerivedLowerStar_preservesCoproducts_for_grothendieck A g J
  exact DerivedCategory.isLeftAdjoint_of_preservesCoproducts ((g)_*[A]).rightDerivedFunctor

end Proper

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The exceptional inverse image `Rf^! : D(Y_ét) ⥤ D(X_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of étale sheaves: a chosen
right adjoint `Rg^!` of the derived pushforward `Rg_*` along the proper `g`, followed by the
levelwise pullback `Di^*` along the open immersion `i`. -/
noncomputable def rightDerivedUpperShriekOfCompactification :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  ((c.g)_*[A]).rightDerivedFunctor.rightAdjoint ⋙ D((c.i)^*[A])

@[inherit_doc rightDerivedUpperShriekOfCompactification]
scoped notation "Rf^!("c")[" A "]" =>
  rightDerivedUpperShriekOfCompactification A c

end OfCompactification

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

section Unbounded

/-- The exceptional inverse image `Rf^! : D(Y_ét) ⥤ D(X_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: the
functor `rightDerivedUpperShriekOfCompactification` attached to the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def rightDerivedUpperShriek :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  Rf^!(HasCompactification.compactification f)[A]

@[inherit_doc rightDerivedUpperShriek]
scoped notation "R(" f ")^![" A "]" =>
  rightDerivedUpperShriek A f

lemma rightDerivedUpperShriek_eq : R(f)^![A] =
    Rf^!(HasCompactification.compactification f)[A] := rfl

end Unbounded

section Adjunction

/- The K-flat resolution package on the coefficient category `A`, needed for the derived
adjunction `Di_! ⊣ Di^*` along the open immersion of a compactification, see
`Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The adjunction `Rf_! ⊣ Rf^!` attached to a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
the composite of the derived adjunction `Di_! ⊣ Di^*` along the open immersion `i` and of the
adjunction `Rg_* ⊣ Rg^!` along the proper `g`. -/
noncomputable def rightDerivedUpperShriekOfCompactificationAdjunction {f : X ⟶ Y}
    (c : Compactification f) : Rf_!(c)[A] ⊣ Rf^!(c)[A] :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).comp
    (Adjunction.ofIsLeftAdjoint _)

/-- The adjunction `Rf_! ⊣ Rf^!` on the unbounded derived categories of étale sheaves. -/
noncomputable def rightDerivedUpperShriekAdjunction : R(f)_![A] ⊣ R(f)^![A] :=
  rightDerivedUpperShriekOfCompactificationAdjunction A (HasCompactification.compactification f)

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` is a left adjoint, its right adjoint
being `R(f)^![A]`. -/
instance isLeftAdjoint_rightDerivedLowerShriek : (R(f)_![A]).IsLeftAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isLeftAdjoint

instance : (R(f)^![A]).IsRightAdjoint :=
  (rightDerivedUpperShriekAdjunction A f).isRightAdjoint

end Adjunction

end Etale.CompactificationUpperShriek

end AlgebraicGeometry
```

The complete original auxiliary module, withdrawn in `deleted.txt`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-! Proper étale derived direct image and coproducts.

Source: SGA 4, Exp. XVIII, Theorem 3.1.4; Stacks Project, Tag 0F5Y.
(blueprint: lem-etale-proper-derived-lower-star-coproducts)
-/

@[expose] public section

set_option autoImplicit false

universe u' u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- For a proper morphism, the total right derived direct image preserves all coproducts.

Source: SGA 4, Exp. XVIII, Theorem 3.1.4; Stacks Project, Tag 0F5Y.
(blueprint: lem-etale-proper-derived-lower-star-coproducts-for-grothendieck)

Proof in words: direct image along a proper morphism has finite cohomological amplitude on each
quasi-compact étale open, and its higher direct images commute with filtered colimits. Therefore
its total right derived functor commutes with arbitrary coproducts. Restriction to quasi-compact
opens detects isomorphisms, so the local comparisons assemble to the global coproduct comparison.
The derived categories of sheaves of objects of a Grothendieck abelian category have the required
coproducts, and this preservation statement is the input to Brown representability.
-/
theorem proper_rightDerivedLowerStar_preservesCoproducts_for_grothendieck
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g] :
    ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((g)_*[A]).rightDerivedFunctor := by
  sorry

end AlgebraicGeometry.Etale
```

## New

The legacy module remains importable with its original two public imports. Its unused
namespace and its definitions, lemmas, instances and scoped notation are withdrawn.

```lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!
# Legacy compactification upper-shriek imports

The unused `AlgebraicGeometry.Etale.CompactificationUpperShriek` API has been retired.
The active exceptional inverse image and its adjunction are provided by
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`: existence is an explicit hypothesis
for general coefficients and is proved for finite module coefficients in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.

The two public imports are retained for compatibility with importers of this module.
No unconditional proper-pushforward adjoint or arbitrary-coefficient coproduct assertion
is exported here.
-/
```

`lean/Sheaf/AlgebraicGeometry/ProperEtaleDerivedLowerStarCoproducts.lean` is withdrawn
via `deleted.txt`. Its node remains as a historical statement, with `lean: null` and
its proof fields documenting retirement. This does not assert that statement was proved.

## Users

Audit commands:

```text
python3 tools/downstream.py WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek --uses isLeftAdjoint_rightDerivedLowerStar_of_isProper rightDerivedUpperShriekOfCompactification rightDerivedUpperShriek rightDerivedUpperShriek_eq rightDerivedUpperShriekOfCompactificationAdjunction rightDerivedUpperShriekAdjunction isLeftAdjoint_rightDerivedLowerShriek
python3 tools/downstream.py WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek --direct --uses AlgebraicGeometry.Etale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper AlgebraicGeometry.Etale.CompactificationUpperShriek.rightDerivedUpperShriekOfCompactification
```

The direct importers are `WeilConjectures` and `Derived.UpperShriek`. All external
whole-word hits refer to the active API, not the retired namespace. A scratch Lean probe
imports all 46 candidate modules with `import all`, traverses all loaded declaration
types and available bodies, and finds zero external constants referencing the retired
namespace (677,022 declarations inspected). The unchanged original `Derived.UpperShriek`
also compiles against the replacement legacy module. The table includes every transitive
importer reported by the tool as well as every name hit and both changed modules.
No remaining target definition uses a retired constant; no target requires statement
review as a consequence of a definition change in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperEtaleDerivedLowerStarCoproducts | H1 | H1 item: withdraw the unused auxiliary theorem; zero remaining holes. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| Sheaf.Paper.FiniteConstantCokernel | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.Paper.ProEtaleStratifiedCounit | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.Paper.ProEtaleStratifiedEssentialImage | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| TargetsCheck | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures | unclaimed | Unchanged direct importer; retained module path and public imports remain valid. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Trace | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.EtaleCohomology.TateTwist.Basic | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.TateTwist.KummerClass | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.EtaleCohomology.TateTwist.Normalized | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Convolution | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Unit | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.UnitVanishing | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.Composition | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.BidualitySupport | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek | unclaimed | Unclaimed module adapted: retire the unused namespace; retain both original public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDual | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDualProper | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DirectImage | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DoubleDual | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Duality | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GeometricBiduality | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PointBiduality | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SingleDelta | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | XRdbb7091a3d1839f4 | Unchanged direct importer; original source compiles against retired API; active adjunction route unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Duality | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition | unclaimed | Unchanged; short-name hit belongs to active Etale/ProEtale API; compiled-expression audit finds no retired dependency. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.Statement | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged transitive importer; no removed-name source hit; active exported definitions unchanged. |

## Status

landed 20261017T003421-L-3315038 2026-10-17 (merge of deliver/H1/Sheaf.AlgebraicGeometry.ProperEtaleDerivedLowerStarCoproducts)
