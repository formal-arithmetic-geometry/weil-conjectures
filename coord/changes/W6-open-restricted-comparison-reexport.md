# AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_comparison_transport

## Reason

Restore the quarantined item as a functioning historical public import path for
its already proved adopted source declaration. The archived proof imports the
withdrawn Sheaf OpenRestrictedRepresentativeData module, which now declares
nothing. The canonical theorem is already proved in WeilConjectures and uses
the same representative-data/comparison-square argument. A compiled mixed-import check of the archived implementation, with only its
withdrawn dependency redirected, fails with:

```text
error: AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_comparison_transport
has already been declared
```

Thus retaining a second local declaration collides when a consumer also imports
the upstream transport theorem or its parent OpenComparisonIntoPullbackTransport.

This repairs the missing proof dependency and avoids the duplicate public
implementation. No upstream file is edited and the quarantine archive is kept.

## Old

The quarantined module, including its complete original signature and proof:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
import Sheaf.AlgebraicGeometry.OpenRestrictedComparisonCore
import Sheaf.AlgebraicGeometry.OpenRestrictedRepresentativeData

/-! # Comparison on the literal restriction of a complex

Source: Stacks Project, Tag 0DJ8, locality of equation-bc; Tag 0DJ9.
(blueprint: lem-pc-open-restricted-comparison-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

set_option linter.unusedVariables false in
/-- Open transport for the literal termwise restriction of a K-flat complex.
Unlike transport to an arbitrary representative, this only compares a complex
with its actual restriction, and constructs its derived identification.

Proof: put j = U.ι, p = pullback.fst g′ j, q = pullback.snd g′ j. Since p and j
are open immersions, their tensor pullbacks are the exact restriction functors:
compare their adjunctions to direct image by uniqueness of left adjoints. The
universal derived counits identify these exact restrictions with derived pullback.
The additive restriction-stalk natural isomorphism on complexes consequently
descends to the derived categories and cohomology, giving η independently of P.
Let Q be the displayed literal restriction. It is K-flat by open restriction,
so the specified pullback counit for q at Q is invertible. The exact restriction
identification followed by derived pullback of eP gives eQ.
At z the open-immersion stalk maps for j and p are ring isomorphisms. The
pullback condition and stalkMap_comp identify the base rings and their actions.
The restriction-stalk extension isomorphism identifies the stalk complexes of
P and Q. Apply the universal derived base-ring extension, cohomology, final
scalar extension and forgetting scalars to obtain l. The comparison_eq and
localized_eq model equations identify the comparison arrows with the universal
counit and its extension/restriction transpose. Their naturality, together with
tensorStalkIso, gives the comparison square on these literal restrictions.
The universal-counit characterization of derived composition identifies its
right-hand transport with β. This proves the displayed equation. No change of
representative is required here. Empty opens have no z; top opens, zero complexes
and zero rings satisfy the same construction. No base-flatness is assumed.
Source: Stacks Project, Tag 0DJ8 (locality of equation-bc), Tag 0DJ9 (source-open
induction), and Tag 06YB (K-flatness can be checked on stalks).
(blueprint: lem-pc-open-restricted-comparison-transport). -/
theorem exists_open_restricted_comparison_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (U : X.Opens)
    (sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g)
    (z : (pullback g' U.ι : Scheme.{u})) (i : ℤ) :
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
      AddCommGrpCat.{u}
    let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
      AddCommGrpCat.{u}
    let H := comparisonStalkCohomology X' (pullback.fst g' U.ι z) i ⋙ F
    let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
    ∃ η : H ≅ derivedPullback (pullback.fst g' U.ι) ⋙ HU,
      ∀ (K : schemeDerivedCategory X)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (hP : P.IsAcyclicTensorKFlat)
        (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
        (eP : DerivedCategory.Q.obj P ≅ K),
      let Q : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
        ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
      ∃ (hQ : Q.IsAcyclicTensorKFlat) (hcQ : IsIso ((counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
        (eQ : DerivedCategory.Q.obj Q ≅ (derivedPullback U.ι).obj K),
      let a := F.map (comparisonIntoPullback f f' g g' sq
        (pullback.fst g' U.ι z) P hcP i)
      let b := FU.map (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sqU z Q hcQ i)
      let β := openRestrictedCompositionMap g' U K
      ∃ l : (Arrow.mk a).left ≅ (Arrow.mk b).left,
        a ≫ H.map ((derivedPullback g').map eP.hom) ≫
            η.hom.app ((derivedPullback g').obj K) =
          l.hom ≫ b ≫ HU.map ((derivedPullback (pullback.snd g' U.ι)).map eQ.hom ≫ β) := by
  refine Exists.imp ?_
    (exists_open_restricted_comparison_square.{u, w} f f' g g' sq U sqU z i)
  intro η hη K P hP hcP eP
  obtain ⟨hQ, hcQ, eQ, _⟩ :=
    exists_open_restricted_representative_data U (pullback.snd g' U.ι) K P hP eP
  have hs := hη K P hP hcP eP hcQ eQ
  exact ⟨hQ, hcQ, eQ, hs⟩

end AlgebraicGeometry.SingleComplexBaseChange
```

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonTransport

/-! # Comparison on the literal restriction of a complex

Source: Stacks Project, Tag 0DJ8, locality of equation-bc; Tag 0DJ9.
(blueprint: lem-pc-open-restricted-comparison-transport).

Re-export the adopted source proof at the historical module path. Its K-flat
predicate `IsKFlatTensor` has the same defining acyclic-test-complex formula as
`IsAcyclicTensorKFlat`, retained through the public naturality import. The
comparison maps, representative data and derived-composition transport agree.
-/

@[expose] public section
```

The adopted declaration's signature is identical to the archived signature
except that it spells the K-flat predicate IsKFlatTensor instead of
IsAcyclicTensorKFlat. Their defining bodies are identical: every acyclic complex
F has acyclic total tensor F tensor P, using the same monoidal category. A
kernel-checked predicate-equality probe uses rfl. A second probe repeats the
full original signature and applies the adopted theorem with every original
argument unchanged. It also imports the adopted parent, exercising consumers
which load both historical and canonical module paths.

The public naturality import retains the original predicate spelling and all
three original public imports remain. The original private Core and withdrawn
RepresentativeData imports are replaced by the adopted transport proof's
private dependencies. No hypothesis, universe, map or conclusion changes; in
particular there is no new base-flatness assumption. Empty opens (no z), top
opens, zero complexes and zero rings still use exactly the same statement.
No target meaning or unit step changes. The node's Lean attachment points to
the unique upstream provider; its mathematical statement and dependencies stay.

## Users

Source searches find no live importer of the historical item and one archived
importer. The read-only downstream script reports unknown module because the
item is quarantined. The DAG parent lem-pc-open-comparison-into-pullback-transport
continues to cite this node; it is not withdrawn or bypassed. The canonical
parent has a live upstream implementation with the same theorem applications.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport | W6 | Restore the historical path as a public re-export. |
| Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport | unclaimed | Archived importer; all theorem names and arguments retained, no edit. |
| WeilConjectures.AlgebraicGeometry.OpenComparisonIntoPullbackTransport | unclaimed | Unchanged canonical parent; mixed-import probe checks compatibility. |

Other quarantined modules remain archived and are not asserted repaired.

## Status

landed 20261021T162130-L-292211 2026-10-21 (merge of deliver/W6/Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport)
