## What changed

Repair H10 (reviewer X-9f564, returned head 9f5647fb4): the module now constructs
`perfectOverlapStageStatement`, `perfectOverlapCoherenceStatement`, and
`perfectOverlapCoreStatement` as transparent propositions. Each body is the complete
formerly inline result verbatim, including its dependent lets, hypotheses, quantifiers
and equations. The corresponding theorem retains every original outer binder and
states that exact proposition. No mathematical statement or Challenge declaration
changes; this is a definitionally equal representation of the three existing nodes.

Native sampling identified the serialization/elaboration hotspot as
`Lean.Meta.FunInfo.collectDeps_visit` (50.93% of sampled cycles, with another 9.53%
in its free-variable lookup). Its uncached traversal repeats expressions expanded
from the dependent lets. A stage-only profile spent 24.5 seconds in `.olean`
serialization. Merely changing the hom projection proof or caching category and
additivity instances did not fix the fresh 60-second artifact timeout.

The core proof now unfolds the core proposition and obtains the stage and coherence
theorems at their original outer arguments. It unfolds those propositions in local
hypotheses, applies them to the same supplied objects and comparisons, and packages
the same witnesses and induced-transition equation. This retains the stage/coherence
route while keeping constant-application parameter metadata small. The coherence
proof still takes homs and normalizes categorical composition. All work stays in
this module; no file or proof is split and no timeout is raised.

The two older E2/F6 interface corrections described next remain part of this delivery.
Their geometric statements are unchanged by H10. The new performance change record
is `coord/changes/perfect-overlap-statement-cache.md`, with the exact received inline
statements, the complete proposition definitions, and all 425 downstream users plus
this module. The three existing nodes record each proposition alongside its theorem
in `lean.declarations`; these are representations of the same propositions, not new
mathematical notions or new nodes.

Repaired return E2 with a coordinated interface correction in
`Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore`.
The stage theorem now retains the prescribed limit-transition equality rather than
`∃ e, True`. It also supplies functorial transports `κU`, `κV`, `siteU`, `siteV`
and equations pinning `θU`, `θV` to the supplied `φU`, `φV`. Thus the remaining
geometric obligation records what Tag 09RF actually needs: descent of the specified
transition through E, with its limit equation, not arbitrary overlap existence.

The coherence theorem receives the diagram, transition, local identifications and
the induced-transition equality as hypotheses. Its complete proof takes homs of
that equality and normalizes categorical composition. The core packaging proof now
passes this equality explicitly. The final core has the same binders and definitionally identical result, now named
by the exact transparent proposition definition; no Challenge declaration changes. Only this module names the two
changed intermediate declarations, so no external source adaptation is forced.

Updated all three existing node copies, their actual Lean signatures, their proof
routes and dependencies. The two changed statements have coordinated
`statement_change` records including every DAG citer. The change record is
`coord/changes/perfect-overlap-prescribed-transition.md`; its Users table includes
all 425 transitive importers plus the own module returned by downstream.py.

Repaired F6 by removing the counterexample/realization route from the coherence
node's proof. Its actual proof is elementary and uses no realization theorem.
Consequently `lem-pc-two-open-comparison-realization` is not a proof dependency of
the repaired theorem. The mathematical reason for the interface correction remains
in the statement-change record and below, not as a purported proof.

### H10 repair: fresh artifacts and unchanged original importer

The final-source verification is performed in `scratchpad/h10-final-clean`, whose
`.lbuild` did not exist before the check. `lcompile.py --all` compiles the delivered
core and the original, byte-for-byte unchanged direct importer in import order.
The setup for the importer explicitly resolves the core from that new `.lbuild`.
The final source passed without errors or warnings: core artifact generation took
29.6 seconds, and the unchanged importer compiled against those artifacts in
32.5 seconds. Both use the unchanged 60-second limit. All `.olean`, `.olean.server`,
`.olean.private`, `.ir`, `.ir.sig` and `.ilean` companions exist as real files for
both modules. The delivered core is byte-for-byte the compiled core; the importer
matches the frozen original source hash recorded below.

```text
== Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore (compiled)
[29.6 s]
== Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram (compiled)
[32.5 s]
[exit code 0: compiled]
```

Command: `python3 /home/ubuntu/weil-launcher/lcompile.py --all` followed by the
sandbox path `scratchpad/h10-final-clean` (full group/item sandbox prefix).
Compiler output is also retained there as `compile.log`.

Independent original-signature examples recover all three received theorem types
by unfolding only the corresponding proposition definition. The final check against
the fresh artifacts passed in 47.4 seconds without errors or warnings. It printed
axioms: all three proposition definitions and coherence use only `propext`,
`Classical.choice`, and `Quot.sound`; stage and core additionally use `sorryAx`
from the existing stage obligation. Its output is retained in
`scratchpad/h10-final-clean/statements-and-axioms.log`.

The following frozen baseline graph and importer source remain the review materials
requested by the earlier H10 return. The second-reading text at the end predates this
performance repair; its unsuccessful artifact checks are historical, not the current
gate result. This author has not written or altered the independent second reading.

The earlier H10 packet supplement was only a scratch file and was not included
in the report extracted into the review packet. This repair embeds the relevant
baseline graph and every unchanged direct-importer source in this delivered report,
so the regenerated review packet contains them even if the reviewer's clone lacks
these modules. No Lean replacement is requested by this packet repair.

The frozen baseline is `eb1a3c591f62b793fc64d0a99de3c1e9df181c62`. Its complete import graph contains
11351 modules. Scanning every graph entry for imports of the delivered core
produces exactly the direct-importer list below, with no omitted importer.
The full frozen graph is available on this machine at
`/home/ubuntu/weil-sandbox/H1/Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore/scratchpad/h10-repair/baseline-import-graph.json`
(SHA-256 `ac955261210ef0da8b377159ebf0dc7d771163ababf59ae1e2fd7a26b8671bc1`). The complete direct-importer slice is embedded here:

```json
{
  "baseline_commit": "eb1a3c591f62b793fc64d0a99de3c1e9df181c62",
  "direct_importers": [
    "Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram"
  ],
  "entries": {
    "Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore": {
      "imports": [
        "Sheaf.AlgebraicGeometry.PerfectComplex",
        "WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent",
        "Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation",
        "Sheaf.AlgebraicGeometry.DerivedPullbackComposition",
        "Sheaf.AlgebraicGeometry.PerfectDescendMorphisms",
        "Sheaf.AlgebraicGeometry.DerivedPullbackPerfect",
        "Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses",
        "Sheaf.AlgebraicGeometry.TwoOpenComparisonDiagram"
      ],
      "source_sha256": "b12814763eac4f187e9a7fd09bc50261dcfab1094ce6988e5293352954bd5e14"
    },
    "Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram": {
      "imports": [
        "Sheaf.AlgebraicGeometry.PerfectComplex",
        "Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore",
        "WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent",
        "Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation",
        "Sheaf.AlgebraicGeometry.DerivedPullbackComposition",
        "Sheaf.AlgebraicGeometry.PerfectDescendMorphisms",
        "Sheaf.AlgebraicGeometry.DerivedPullbackPerfect",
        "Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses",
        "Sheaf.AlgebraicGeometry.TwoOpenComparisonDiagram"
      ],
      "source_sha256": "b8d59f3753f6e901bb1aaac8a56eed67bc4a5c9fae8d6045c924d0f68ab2115a"
    }
  }
}
```

Before PASS, restore the unchanged importer below under the indicated module path
in a fresh review directory. Compile the actual delivered core into that directory's
`.lbuild` with `lcompile.py --all`, then compile the unchanged importer separately
with `lcompile.py`. This prevents a check against shared, old-core artifacts from
being mistaken for a direct-importer check against the delivery. The source hash
must match the frozen graph hash above; do not adapt the importer before recording
its original compilation result. The importer source is review material only and
is not a changed or adapted delivered module.

### Unchanged baseline source: lean/Sheaf/AlgebraicGeometry/PerfectOverlapTransitionComparisonDiagram.lean

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.PerfectDescendMorphisms
import Sheaf.AlgebraicGeometry.DerivedPullbackPerfect
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

public import Sheaf.AlgebraicGeometry.TwoOpenComparisonDiagram

/-! # Finite-stage descent of a prescribed overlap transition

Source: Stacks Project, Tags 09RE and 09RF.
(blueprint: lem-pc-perfect-overlap-transition-comparison-diagram).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

set_option synthInstance.maxHeartbeats 400000 in
-- Elaborating simultaneous exact restriction comparisons needs this instance budget.
set_option maxHeartbeats 1600000 in
-- The dependent comparison diagram requires this elaboration budget.
set_option linter.unusedVariables false in
/-- Descend the prescribed overlap transition with coherent comparison data.
This only concerns the two local objects and one overlap equation: it has no
quantification over a global stage object or its realizations.
Source: Stacks Project, Tags 09RE, 09RF, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-transition-comparison-diagram).

Proof: Work on the directed tail above j. The quasi-separated finitely presented
stage Yj has compact intersection W of its compact opens. The open immersion
W into Yj is quasi-compact, hence W is finitely presented over Spec Rj.
Restrict A and B to W; they remain perfect. Compose the restrictions of φU
and φV inverse to obtain the prescribed isomorphism between their limit
pullbacks. Use the canonical derived composition and open-restriction
comparisons to identify the cartesian base changes of W with the inverse-image
intersections. Apply perfect_descend_morphisms, including its invertibility
clause, to descend that isomorphism to a stage k on the tail. Transport it to
the exact overlap restrictions of A' and B' to obtain e.
Construct HU,HV,HW as derived pullback on the three open subschemes followed
by the derived inverse open equivalences. The canonical restriction/pullback
comparisons give βU,βV,βW and γU,γV. On K-flat representatives their coherence
is tensor associativity and the unit/counit identities for open equivalences;
the derived universal property preserves these identities. These actual
functors and canonical comparisons supply d, rather than an arbitrary diagram.
Composition comparisons identify HU A' and HV B' with the original limit
pullbacks on localized sites; compose with φU,φV to get θU,θV. The descended
pullback equation for e is exactly the displayed equation after these
canonical identifications. This argument constructs no global stage object F.
Empty or coincident opens use the same comparisons and inverse equations. -/
theorem perfect_overlap_transition_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))
      let f := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U' := f ⁻¹ᵁ U
      let V' := f ⁻¹ᵁ V
      let instY : Category (schemeDerivedCategory Yk) := inferInstance
      let instU : Category (schemeDerivedCategory U'.toScheme) := inferInstance
      let instV : Category (schemeDerivedCategory V'.toScheme) := inferInstance
      let instW : Category (schemeDerivedCategory (U' ⊓ V').toScheme) := inferInstance
      let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
      let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
      let SU : schemeDerivedCategory U'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
      let SV : schemeDerivedCategory V'.toScheme ⥤
          schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
      let TU : schemeDerivedCategory Yk ⥤ schemeDerivedCategory U'.toScheme :=
        (schemeOpenRestriction Yk U').mapDerivedCategory
      let TV : schemeDerivedCategory Yk ⥤ schemeDerivedCategory V'.toScheme :=
        (schemeOpenRestriction Yk V').mapDerivedCategory
      let TW : schemeDerivedCategory Yk ⥤ schemeDerivedCategory (U' ⊓ V').toScheme :=
        (schemeOpenRestriction Yk (U' ⊓ V')).mapDerivedCategory
      let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))
      let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Yk
        (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
      ∃ (d : SchemeTwoOpenComparisonDiagram X Yk g U' V' P Q)
        (e : SU.obj A' ≅ SV.obj B')
        (θU : d.toDiagram.HU.obj A' ≅ RU.obj E)
        (θV : d.toDiagram.HV.obj B' ≅ RV.obj E),
        d.toDiagram.γU.inv.app A' ≫ SP.map θU.hom ≫ τU.hom.app E =
          d.toDiagram.HW.map e.hom ≫ d.toDiagram.γV.inv.app B' ≫
            SQ.map θV.hom ≫ τV.hom.app E := by
  exact perfect_overlap_transition_comparison_core R c hc i Z t j hij
    (by intro U V; exact ⟨j, le_rfl⟩)

end AlgebraicGeometry
```


## Proved and sorry left
The corrected `perfect_overlap_transition_comparison_core_coherence` is proved
without sorry, using only equality congruence and categorical projection equations.
This is a proof of the corrected conditional statement, not of the false original
statement; do not count it as geometric descent progress or a decomposition.
Original-statement holes proved: 0 of 2. No new holes or new modules were added.
The three exact proposition definitions are fully constructed and contain no sorry.
No new theorem with a hole is introduced, and no hole moves into a definition.
One existing geometric obligation remains, with its corrected stronger statement:
`perfect_overlap_transition_comparison_core_stage`, node
`lem-pc-perfect-overlap-transition-comparison-core-stage`.
Its proof is exactly `:= by sorry`, with the descent and transport proof in words
in its docstring and node. This repair consolidates the actual prescribed-transition
construction in that existing stage obligation; it does not claim the previous
stage/coherence reduction was valid. No split-off theorem is introduced.

`perfect_overlap_transition_comparison_core` retains its statement and compiles
from the corrected stage obligation and the proved conditional coherence theorem.
It still reaches sorryAx through the stage obligation and is not an axiom-free proof.

## No longer needed
H10 removes no imports, nodes, modules or geometric proof dependencies. The core still
uses stage followed by coherence; naming their exact propositions adds no lower item.
No pruning or mathematical proof progress is claimed for this compilation repair.

No imports removed and no modules globally pruned. The remaining stage construction
needs perfect morphism descent, pullback-perfectness, composition, and open
restriction comparisons; their proof-dependency imports stay.
The coherence node no longer needs its old dependencies
`def-pc-two-open-comparison-diagram`,
`lem-pc-derived-pullback-open-restriction-universes`, and
`lem-pc-ringed-spaces-derived-pullback-composition` as proof dependencies: the diagram
is a statement dependency and the latter two are still needed by the stage route.
The rejected counterexample route through
`lem-pc-two-open-comparison-realization` is not used in the revised proof and does
not enter the import closure by this delivery. These local dependency removals are
not claimed as pruning whole modules from the targets' reach.

## Where the brief, the DAG or earlier work was wrong
H10: the earlier standalone checks and the baseline graph/importer material did not
meet the fresh artifact gate. Native profiling located the actual repeated dependency
traversal, and the named proposition representations fix it with the full statements
preserved. The unchanged direct importer is tested against final fresh artifacts;
checking it against the old shared core would not establish this repair.

E2: the old coherence theorem was false for arbitrary e₀. The constant one-stage
field system with Z=P¹, A=B=O and E=O, taking e₀ to be the transition of O(1),
refutes it: compatible local identifications would give O(1) ≅ O. Merely marking it
disputed left the invalid core proof in place. The new hypothesis excludes this
transition unless it actually induces the specified transition through E.
The source [Stacks Tag 09RF](https://stacks.math.columbia.edu/tag/09RF) explicitly
chooses c pulling back to the identifications through E in its two-open induction;
[Tag 09RE](https://stacks.math.columbia.edu/tag/09RE) gives the Hom continuity used
to descend it and its inverse. The old `True` conclusion lost this information.
The corrected stage also records how its local identifications arise from φU,φV.

F6: the returned coherence node used a realization-based counterexample in its
`proof` while omitting that lemma from `uses`/`proof_deps`. The revised proof removes
that route entirely, so its empty proof-dependency list now matches the actual Lean
argument. No metadata falsely describes the counterexample as the proof.

Checked the empty overlap and constant one-stage cases. In the empty overlap all
transition equations are between the unique maps of zero objects. In a constant
system the prescribed transition is the one induced by the supplied comparisons,
and the O(1) transition with E=O does not satisfy the coherence hypothesis.
The unit's realized statement/step lists are empty; no unit or chapter route changes.
No forced adaptations, new nodes, arbitrary data choices, or axioms are introduced.

## Earlier second reading (a previous round; superseded)

1. Compared the whole delivered module with the repository using `diff -u`.
   The signature of `perfect_overlap_transition_comparison_core` is byte for byte
   unchanged. The stage and coherence signatures do change, exactly as declared
   in `coord/changes/perfect-overlap-prescribed-transition.md`; checked both Old
   and New blocks verbatim against the respective Lean signatures. No definition
   or target changes. A search of all Lean sources finds no external named caller
   of either changed intermediate theorem; the sole caller is the adapted core
   packaging proof. Checked the change-record Users table and both complete DAG
   citer lists. Verdict: a declared interface repair, not an unchanged-statement
   proof of the old coherence theorem.

2. Compiled the delivered module through `lcompile.py`: clean, exit 0 (39.2 s).
   Read the complete coherence proof: `congrArg Iso.hom hinduced` followed by
   the listed projection equations and associativity proves precisely the stated
   conditional hom equation. Read the core proof: it obtains the same `k`, `d`,
   `e`, and local identifications from stage, then supplies its equality to
   coherence. A fresh scratch copy with `#print axioms` compiled (41.2 s):
   coherence uses only `propext`, `Classical.choice`, `Quot.sound`; stage and core
   additionally use `sorryAx`. Exactly one `sorry` remains, the named stage
   theorem recorded above. No forbidden declaration, hidden hole, definition,
   or arbitrary witness chosen into data is introduced. An additional scratch
   `--all` check containing fresh copies of core and its unchanged direct importer
   timed out twice at 60 s while emitting the core artifacts, before reaching the
   importer; this does not establish a fresh importer compilation. Ordinary core
   compilation, the fresh axiom scratch check, and the required deliver3 dry-run
   compile/preflight all passed. The maintainer's global artifact build remains
   the definitive check of this delivery, including that emission-time limit.
   Verdict: the conditional
   proof is sound; geometric descent is still open and is not counted as proved.

3. No new or split-off statement is introduced. Read the strengthened existing
   stage obligation and its docstring against Stacks Tags 09RE and 09RF, especially
   09RF's two-open induction where the descended isomorphism pulls back to the
   prescribed identifications through E. Perfectness of the two overlap objects
   permits Hom descent; compactness and quasi-separatedness give the compact
   overlap. Descending an inverse and its two identities yields an isomorphism.
   The two equations for theta retain the supplied phi comparisons via the stated
   natural transports, and the final equation retains the prescribed transition.
   In a constant one-stage system the actual transition satisfies this equation;
   an unrelated O(1) transition with E=O is not required to satisfy it. Empty
   overlap, one empty open, and zero local objects cause no excluded cases.
   Repeated searches with different wording: LeanFinder's query about spreading
   isomorphisms of restricted perfect complexes over directed ring colimits found
   only unrelated homological-complex tools; Loogle `CategoryTheory.Iso.hom`
   found the standard projection and extensionality tools already sufficient for
   coherence. The initial `Iso.congr_hom` query found no such identifier.
   Searched `lean/Sheaf`, `lean/WeilConjectures`, and upstream Picard sources for
   overlap transitions, prescribed transitions, and perfect descent/continuity.
   The downstream transition wrappers ultimately call this core; they cannot
   close its stage obligation without a cycle. Verdict: no few-minute closure or
   duplicate existing statement found; the stage remains a documented obligation.

4. Checked the top-down route: prescribed finite-stage descent supplies stage,
   and elementary projection supplies coherence. Public imports supply signature
   notions (perfect objects, base-change maps, finite presentation, the comparison
   diagram); all four geometric proof-dependency imports are plain `import`.
   They remain the plan for the open stage theorem. No proof-only public import
   was added. `No longer needed` lists all three old coherence proof dependencies;
   they are still needed as statement data or by the stage route, so no module
   pruning is claimed. Read `dag/units/sk-thm-picard-semicon.json`: its realized
   statement list is empty and its step list is `[[]]`; none is bypassed or edited.
   Verdict: route retained, no new split or claimed geometric progress.

5. Opened all three delivered node records. Their `lean.statement` fields equal
   the actual Lean signatures verbatim, and each `proof_deps` is exactly the union
   of step `uses`. Coherence's elementary projection proof correctly has no proof
   dependency. Stage cites morphism descent, pullback perfectness, the diagram,
   restriction comparisons, composition comparisons, and restriction maps; read
   the corresponding imported declarations. Core cites stage and coherence in
   the order actually used. `proof_origin` explicitly records the interface repair;
   no realization/counterexample is presented as a proof. The only statement
   changes are coordinated in their records with all citers. No new nodes require
   creation fields. Verdict: Lean and metadata agree, including the remaining hole.

Second reading changed no delivered Lean code or node: the repair and elementary
proof are correct as written. Added this independent review and fresh scratch
checks. Original-statement holes proved remain 0 of 2, new holes 0, split off 0;
this delivery repairs the invalid interface and makes no proof-progress claim.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module to the repository with diff and independently
   extracted its declarations. The final core signature is byte for byte unchanged.
   Stage and coherence change only as declared by the change record; its Old/New
   blocks match the respective signatures verbatim. No definition or target changes.
   Searching all library Lean sources finds no named external caller of those two
   intermediate declarations. Verdict: coordinated interface repair, not a proof
   of the false old statement.

2. Fresh single-file compilation passed (33.7 seconds). A separate scratch copy
   with print-axioms commands passed (35.0 seconds): coherence uses only propext,
   Classical.choice and Quot.sound; stage and core additionally use sorryAx.
   Read both proof bodies: coherence projects Iso.hom and normalizes composition;
   core passes the same stage witnesses and its induced-transition equation. Exactly
   one named sorry remains, in stage; no forbidden declaration or data definition
   is introduced. Fresh artifact generation with the unchanged direct importer
   timed out at 60 seconds in the core before reaching that importer. A scratch
   experiment disabling optional let-to-have cleanup also timed out and is excluded
   from delivery. Verdict: local proof checks pass; no successful fresh artifact or
   direct-importer check is claimed. The outstanding H10 reader gate is retained.

3. No new split-off statement or node is introduced. Read the existing stronger
   stage obligation and its complete docstring argument against
   [Stacks 09RE](https://stacks.math.columbia.edu/tag/09RE) and
   [Stacks 09RF](https://stacks.math.columbia.edu/tag/09RF): Hom continuity descends
   the prescribed transition and inverse, and a common later stage satisfies both
   inverse identities. The transports retain the supplied local identifications.
   Empty overlap, zero objects and a constant one-stage system impose no excluded
   case; an arbitrary incompatible transition is no longer asserted. Repeated
   msearch queries for Iso.hom (Loogle) and isomorphism descent for perfect complexes
   over filtered ring colimits (LeanFinder), plus differently worded rg searches
   through both library roots, found no shorter geometric closure. Related local
   model and transition wrappers are downstream of this core. Verdict: the
   geometric obligation remains open; corrected coherence is elementary.

4. Public imports supply the final signature's perfectness, base-change, finite
   presentation and diagram notions. The four geometric proof-plan imports remain
   plain imports and are used by the open stage's recorded route. No imports or
   modules are pruned. No longer needed accounts for all old coherence dependencies.
   Read the unit's realized field (empty statement list and one empty step list);
   it is untouched. Independently scanned the frozen full import graph: the sole
   direct importer is PerfectOverlapTransitionComparisonDiagram. Its repository
   source SHA-256 matches the embedded baseline source hash in this report. Verdict:
   route retained and H10 packet materials present, with compilation gate unresolved.

5. All three node lean.statement fields match the delivered signatures verbatim;
   proof_deps equals the union of each proof's uses. Stage describes the remaining
   geometric construction, coherence has the actual elementary proof and no
   geometric proof dependencies, and core uses stage then coherence. Read the
   relevant imported morphism-descent, perfect-pullback, composition, restriction
   and diagram declarations. The statement-change records identify the citers.
   Verdict: Lean and DAG agree; no new-node creation fields are needed.

This reading changes only the report, adding current checks and explicitly retaining
the unresolved fresh artifact/direct-importer gate. No Lean or node edit was justified.
Original-statement holes proved: 0 of 2; holes added: 0; split off: 0; pruned: none.


## Second reading by H1

1. Compared the complete delivered module with the read-only repository using diff.
   The existing signatures are not byte-for-byte unchanged: the stage and coherence
   interface repairs and all three named result propositions are explicitly declared
   in the two change records. Verified that every repository theorem signature is
   included verbatim in those records. The core result is definitionally unchanged;
   the formerly false arbitrary-transition coherence claim is not counted as proved.
   Public imports are unchanged and no external named caller of stage or coherence
   occurs in either library root. Verdict: declared interface repair, no accidental
   weakening or target edit.

2. Independently read coherence's hom projection and the complete core packaging
   proof. The same stage witnesses and induced-transition equality are passed to
   coherence. Ordinary compilation passed in 28.6 seconds. Exactly one sorry remains,
   in perfect_overlap_transition_comparison_core_stage; no forbidden declaration,
   hole in a definition, or arbitrary witness chosen into data occurs. All three
   new proposition definitions are explicit expressions of Prop.

3. No new split-off theorem or node is introduced. The strengthened existing stage
   retains the prescribed transition and its transports, as required by Stacks
   09RF's two-open induction; read 09RE and 09RF independently. On a constant
   one-stage system use the transition induced through E, not an arbitrary
   incompatible transition. Empty opens, empty overlap and zero objects introduce
   no exceptional case. Repeated LeanFinder search for isomorphism descent of
   perfect complexes over filtered ring colimits found only general category and
   derived-category tools; Loogle confirmed the hom projection tool. Local searches
   for overlap/transition and descent found no independent shorter geometric proof.
   Read perfect_descend_morphisms and the exact comparison structure: assembling
   their geometric comparisons is substantial and remains honestly open.

4. The route remains stage descent followed by elementary hom projection. All
   four geometric proof-plan imports are plain imports and remain relevant to the
   open stage construction; public imports supply statement notions. No import
   or whole module is pruned. No longer needed accounts for all three old coherence
   proof dependencies (now statement data or stage dependencies). The unit
   sk-thm-picard-semicon has no realized statement nodes and one empty realized
   step list; no unit route is bypassed. Verdict: route and pruning report agree.

5. Parsed all three delivered nodes and checked their lean.statement fields
   verbatim against the delivered theorem headers. Each proof_deps equals the
   union of its proof steps' uses. Coherence's empty list matches its elementary
   proof; core uses stage and coherence, and stage records its open geometric
   construction. The proposition definitions are listed with their existing
   theorem nodes. Verdict: Lean and DAG agree; no new-node metadata is needed.

Second reading changed only this report. No Lean or node repair was justified.
Original-statement holes proved: 0 of 2; holes added: 0; split off: 0; pruned: none.
This is an interface and performance repair, not a geometric proof-progress claim.

Fresh independent artifact gate passed in scratchpad/second-reader-current, with
no pre-existing .lbuild: delivered core compiled in 29.2 seconds; the original
statement examples and print-axioms check in 44.6 seconds; the byte-for-byte
repository direct importer in 32.3 seconds. All three original inline proposition
examples compile by unfolding their named definitions. The core copy matches the
delivered source and the importer is an unchanged copy of the read-only repository
source. Coherence and all proposition definitions use only propext, Classical.choice
and Quot.sound. Stage and core additionally use sorryAx from the named stage hole.
This supersedes the historical unsuccessful artifact checks above. Verdict: current
fresh artifacts, unchanged importer, original propositions and axioms all pass.
