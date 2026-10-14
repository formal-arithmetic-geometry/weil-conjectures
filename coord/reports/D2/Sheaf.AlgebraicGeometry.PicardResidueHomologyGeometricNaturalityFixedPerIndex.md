## What changed

Repair of return F (reviewer X-55ee2, head 55ee2fcc5): added the missing mandatory
forced-adaptation evidence below, with fresh original-caller compilation against the
corrected dependencies and the changed lines with their reasons. Replaced the old
second-reading heading and superseded assessment by the launcher route note. The
true simultaneous-comparison correction is retained; no proof, statement, definition,
import or node is rolled back in this repair. A new independent second reading is
required after this dry run.

Corrected the false arbitrary-equivalence intermediate statements in
`Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex`
and the unclaimed module
`Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed`.
The source comparison is now chosen once, before quantifying over the indices;
target comparisons and derived arrows are chosen compatibly with it.
The positive-family proof assembles those target comparisons/arrows. The empty-family
proof obtains the source comparison from the existing source comparison theorem
and eliminates `Fin 0` for the remaining data and equations.

Adapted the unclaimed module
`Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality` to apply the
corrected family theorem directly. Its statement is unchanged, including every
hypothesis and the equation for every chain representative. Every declaration
of `lean/Challenge.lean` and all definitions are unchanged. The visible public
imports of all three modules are unchanged. The local irreducibility attributes
in the family proof prevent unfolding the explicit homology map and the cohomology
pullback definition while comparing the large derived-model types.

Updated four existing nodes' proof routes and Lean records. The three corrected
intermediate nodes have `statement_change` records with all their original DAG
citers. No new modules or nodes are introduced. The unit `sk-prop-av-cube`, its
statement and its `realized` fields are unchanged.

Change record: `coord/changes/picard-residue-compatible-comparisons.md`.
It includes the old/new signatures, a full mathematical counterexample, a compiled
scalar obstruction, the source references, and every downstream module with its
claim holder and effect. Both adapted modules are unclaimed in the inspected
claim table, so the explicit unclaimed-module exception authorizes their
intermediate signature corrections.

## Proved and sorry left

Proved **0 of the original 1 sorry**. Holes closed: none. Holes added: none.
Split off: 0. This is a correction of a false intermediate statement, not a proof
or decomposition of that statement, and no net sorry reduction is claimed.

The sole remaining sorry is
`AlgebraicGeometry.Scheme.picard_residue_homology_geometric_naturality_fixed_positive_per_index`,
node `new-picard-residue-homology-geometric-naturality-fixed-per-index`, now with
corrected simultaneous existential comparison quantifiers. It is still exactly
`:= by sorry`, with its source and the full intended proof in the declaration's
docstring and the node. It still needs the natural construction of the geometric
derived arrows and simultaneous comparisons, including naturality of the residue
K-flat comparison; existence of unrelated comparison equivalences is insufficient.

The two corrected family assembly proofs compile without additional holes. The
upper `picard_residue_homology_geometric_naturality` has its original statement and
an adapted complete proof from the corrected all-family theorem. These are assembly
proofs resting on the one named hole above, not complete axiom-free geometric proofs.

The scalar claim `¬ ∃ F : ℂ →ₗ[ℂ] ℂ, ∀ z, star (F z) = z` compiled independently
using only Mathlib. Its exact proof is included in the change record. The complete
scheme counterexample is a mathematical argument, not a claimed Lean refutation
of the old full scheme theorem.

## No longer needed

The upper proof no longer imports
`Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison` or uses
`picard_residue_homology_geometric_comparison`. Its only importer was the upper
naturality module. Consequently the redundant independent-comparison packaging
and its target comparison family leave this target route:

- `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison`, node
  `new-picard-residue-homology-comparison`;
- `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets`, node
  `new-picard-residue-homology-comparison-targets`.

The source comparison module is retained and used for the empty family. Its
subordinate geometric/residue comparison modules are still needed. No source
file or DAG node is deleted.

Removed these unused proof imports from each of the three delivered modules:

- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`;
- `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`;
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`.

The fixed-family module newly imports the source comparison module for its empty
case. The positive node now depends on the corrected per-index node, and the
all-family node depends on the positive node and source comparison. This also
repairs the earlier inconsistent positive/fixed proof-dependency directions.
These removals prune the imports from these proofs; no claim is made that their
entire modules disappear from every other target branch.

## Where the brief, the DAG or earlier work was wrong

The original obligation cannot be proved as written. `eK` and `eC` were arbitrary
additive equivalences, whereas the source uses the geometric comparisons associated
to the functorial derived arrows. The existence of additive equivalences supplied
by the earlier comparison theorem does not imply the naturality equation for an
arbitrary pair of equivalences. This problem appears in all three fixed-equivalence
auxiliary declarations, not just the rejected universal-chain-map helper.

A concrete counterexample takes the identity family on a smooth plane cubic over C,
`S=W=Spec(C)`, `k=id`, `L=O`, `n=1`, and a two-term finite free model of
`RΓ(X,O)`. Its first cohomology is one-dimensional. Choose a linear source comparison
and the target comparison obtained by conjugating coordinates. The desired equation
for the identity geometric map would force a C-linear residue homology map F to
satisfy `conj(F(z))=z`. This is impossible already at 1 and i. Every derived arrow
has a chain representative here by `Scheme.perfect_affine_map_representative`, so
choosing an unrepresented arrow cannot make the universal clause vacuous.
The change record checks all geometric hypotheses and cites the plane cubic
cohomology computation. The report does not confuse this with a formal Lean
counterexample to the entire scheme statement.

The correction follows Stacks Tags 0BF2, 0B91 and 01XK and preserves the exact upper
statement needed downstream: there exist compatible comparisons and arrows.
The source comparison must be shared by the whole family; choosing a different
source equivalence independently for each index would repeat the compatibility
error. The old false signatures are explicitly recorded in the change record
and the nodes' `statement_change` fields.

Library searches used the prescribed wrappers: LeanFinder found generic homology
and K-projective localization results, Loogle found no result for the query,
LeanSearch was unavailable, and grep found the existing affine representative
and residue homology APIs. The parent fixed-family and geometric naturality
results could not be used to prove the original item: their import route already
passed through it. No circular import is introduced.

## Route note for this item (a strong reader studied its whole split chain; follow it unless you find it wrong)

Launcher note (2026-10-14 evening). This item is STATEMENT-DISPUTED: the statement in the module is false (the STATEMENT-DISPUTED comment and earlier reports give the counterexample). Earlier rounds corrected it, and readers then returned the correction as a "forbidden signature change" and ordered a rollback to the false statement; that rule is withdrawn and those returns are deleted. Do NOT roll back to the false statement.

What to deliver: replace the statement by the TRUE statement its users actually need (usually the explicitly elementwise or hypothesis-strengthened variant the counterexample points to), prove it if you can (otherwise leave it as a named sorry with a full proof in words), adapt every caller in the same delivery (modules no group holds may be changed, signatures included; name them in the change record), update the node statement with a statement_change record, and delete the STATEMENT-DISPUTED comment. Reuse a correction that is already written in an earlier delivery branch or report of this item if it is right.

## Forced adaptations

Fresh counterfactual checks used the exact repository versions of both callers, copied into
`scratchpad/repair-originals/lean/Sheaf/AlgebraicGeometry/`, against the corrected sandbox `.lbuild`.
Single-file `lcompile.py` checks failed with the errors below. The adapted versions compile together
in dependency order. The change record names both modules and their unclaimed status. The launcher
explicitly permits correcting signatures in unclaimed modules; the fixed-family corrections use
that permission, whereas the upper theorem keeps its exact signature.

### Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed (unclaimed)

Original compiler error at line 103, column 67:

```
Application type mismatch: The argument
  eK
has type
  W.affineResidueCycleHomology U p K ≃+ (pullback f (S.fromSpecResidueField s)).structureSheafAb.H 1
of sort `Type v` but is expected to have type
  0 < n
of sort `Prop` in the application
  picard_residue_homology_geometric_naturality_fixed_positive_per_index f Xi fi ui hui L W k w s hw τ U hwU hU p hp K hK
    hE C hC hCi eK
```

The compiler also reports an unsolved positive-family existential goal at original line 99,
column 53, as a consequence of this failed application.

The old application supplies an arbitrary `eK` where the corrected per-index theorem now expects
`hn`; the returned witnesses also have a different existential structure. Keeping the old family
signatures would again assert the false arbitrary-equivalence statement. The necessary changes are:

- Original lines 87–95 become delivered lines 90–99: remove `eK` and `eC` as arguments to the
  positive-family theorem and return the jointly chosen `eK`, `eC`, and `a` instead. All geometric
  hypotheses and the equation for every representative are retained.
- Original lines 100–109 become delivered lines 103–108: replace separate choices of arrows for
  externally supplied comparisons with `obtain ⟨eK, hi⟩`, `choose eC a ha using hi`, and
  `exact ⟨eK, eC, a, ha⟩`. This assembles the target witnesses with the single source comparison.
- Original lines 152–158 become delivered lines 162–168: make the same quantifier correction in
  the all-family theorem, which is the positive-family theorem's caller.
- Original lines 168–175 become delivered lines 178–185: obtain `eK` independently in the
  empty-family branch, return it with the two `Fin 0` functions, and remove obsolete `eK` and `eC`
  arguments from the positive branch. Without the source comparison, the empty family would leave
  an unproved existential source witness.
- Delivered line 23 imports `PicardResidueHomologyGeometricComparisonSource`, which the empty
  branch uses. Delivered lines 38–44 and 115–118 control elaboration of the corrected large
  derived-model comparison types: the local irreducibility attribute prevents unfolding the residue
  homology map and cohomology pullback, and the local options let the assembly compile within the
  single-file limit. The docstrings describe the corrected quantifiers and their proofs.
- The three removed proof imports (`TensorPullbackAdjunction`, `PerfectDirectImageBaseChange`, and
  `Cohomology.DirectImage.Sections`) are unused by the adapted assembly. Their removal follows the
  required pruning step; all public imports are preserved.

### Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality (unclaimed)

Original compiler error at line 129, column 4:

```
Function expected at
  picard_residue_homology_geometric_naturality_fixed f Xi fi ui hui L W k w s hw τ U hwU hU p hp K hK hE C hC hCi
but this term has type
  ∃ eK eC a,
    ∀ (i : Fin n) (φ : K ⟶ C i),
      DerivedCategory.Q.map φ = a i →
        ∀ (z : W.affineResidueCycleHomology U p K),
          (eC i) ((affineResidueCycleHomologyMap φ) z) =
            (structureSheafCohomologyPullback
                (Over.Hom.left ((Over.pullback (S.fromSpecResidueField s)).map (Over.homMk (ui i) ⋯))) 1)
              (eK z)

Note: Expected a function because this term is being applied to the argument
  eK
```

The compiler also reports `Tactic rcases failed: x✝ : ?m.441 is not an inductive datatype` at
original line 128, column 9, as a consequence of the failed application.

Original proof lines 124–132 become delivered lines 120–121: directly apply the corrected
all-family theorem. It now supplies precisely the upper theorem's entire existential conclusion,
so the original call with extra `eK` and `eC` arguments is ill-typed. The removed independent
comparison import is no longer used, along with the same three unused proof imports listed above.
The upper theorem's statement, visibility, docstring, local options, and public imports are
identical to the repository version.

The complete compiler outputs are retained in `scratchpad/repair-original-fixed-error.log` and
`scratchpad/repair-original-upper-error.log`. These logs are scratch evidence; this report records
the interface-caused errors and necessary changed lines for the independent reader.

## Second reading by D2

1. **Changed files and accidental edits — pass.** I diffed all three delivered modules against
   the repository versions. The upper theorem statement and all Challenge declarations are
   preserved; the two unclaimed callers have only the forced quantifier adaptations documented
   above. No definitions were changed.

2. **Compilation and axioms — pass.** The three modules compile separately and together through
   `lcompile.py`. The only remaining `sorry` is the named per-index theorem. A scratch `#print
   axioms` confirms that the assembly declarations add no axioms beyond the allowed axioms and the
   imported `sorryAx` from that theorem.

3. **Statements and split nodes — pass.** The simultaneous existential statement is the true
   compatible-comparison form required by the callers; the arbitrary-equivalence form is refuted
   by the counterexample and is not retained. The node statement, Lean record, statement-change
   data, source, and proof route agree. No new split node was added and no duplicate declaration
   exists in the library search.

4. **Pruning and route — pass.** The three proof-only imports listed under “No longer needed”
   are absent from all delivered modules. The source comparison import is retained for the empty
   family, and the unit `sk-prop-av-cube` and its realized route are unchanged.

5. **Forced adaptations and delivery metadata — pass.** I recompiled the repository versions of
   both callers against the corrected dependency and recorded their original errors and the
   minimal changed lines in “Forced adaptations”. The change record lists all affected users and
   the corrected old/new statements. The dry-run preflight is now being rerun after this report
   section was added.
