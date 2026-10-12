## What changed

Proved `AlgebraicGeometry.Etale.exists_finiteEtaleTrace_degree` with its signature unchanged.
The proof constructs a finite locally free structure, chooses the fibre degree at a point
of the connected base, and proves it constant using the existing locally constant degree
theorem. It computes the dimension of every geometric fibre using the proved source-library
base-change API, applies the existing geometric-fibre splitting theorem, reindexes the
coproduct by `Fin d`, and constructs a point equivalence to establish finiteness and
cardinality. The remaining trace computation is isolated in one new module,
`Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegreeTrace`.

The original target module has no remaining `sorry`. Its proof uses the existing admitted
`finiteLocallyFree_fiberDimension_isLocallyConstant` and the new fixed-degree trace lemma.
The source-library geometric splitting and the fibre-degree comparison lemmas are proved.
This is a reduction, not an assertion that all transitive dependencies are proved.

## Proved and sorry left

- Proved: `AlgebraicGeometry.Etale.exists_finiteEtaleTrace_degree`, node
  `lem-weil-pbc-finite-etale-trace-degree` (the single original sorry).
- Added sorry: `AlgebraicGeometry.Etale.finiteEtaleTrace_comp_restriction`, node
  `lem-weil-pbc-finite-etale-trace-degree-trace`, in its own new module. Its statement is
  only the fixed-degree trace part; it neither constructs a degree nor asserts anything
  about geometric fibres. Its docstring and node give the geometric count, localization,
  split-sum calculation and sheaf descent proof, including degree zero and empty base.
- Existing admitted dependency used: `AlgebraicGeometry.finiteLocallyFree_fiberDimension_isLocallyConstant`,
  node `lem-weil-pbc-finite-locally-free-degree-locally-constant` (not changed here).

Both delivery modules compile without warnings using `lcompile.py --all`.

## No longer needed

Removed direct proof imports from the parent:

- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists`: redundant, already public through
  `FiniteEtaleTrace`. Its characterization remains necessary for the trace definition.
- `Sheaf.AlgebraicGeometry.GaloisCategories`: its category definitions are unnecessary;
  `exists_overIso_sigma_of_isSepClosed` is already public from `FiberDegree`.
- `Sheaf.Paper.FiniteEtaleEtaleLocalSplit`: needed by the new trace subproblem, whose
  module imports it; it is no longer a direct dependency of the parent's proof.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: already public through
  `FiniteEtaleTrace`; localization still belongs to the new trace subproblem.

The former explicit affine-chart argument for the geometric fibre is unnecessary:
`Scheme.Hom.fiberDegree_of_isPullback` and `fiberDegree_eq_finrankΓ` already prove the
needed dimension equality. Thus `def-weil-affine-spectrum`,
`def-weil-finite-integral-morphism` and `lem-weil-pbc-fibre-product-affine-spectra` are
removed from the parent's direct proof dependencies. The latter is not used by the new
trace proof plan either. The definitions and helpers may still be reached elsewhere.
`def-galois-categories` is also removed as a direct dependency; its proved geometric
fibre theorem stays. The remaining localization, algebraic closure, coproduct and
covering nodes of the original plan are retained under the new trace node, not pruned.
The parent's node now lists the actual constant-degree, geometric fibre, coproduct and
fixed-degree trace steps.

For completeness, every dependency removed from the parent's old `proof_deps` is listed
here with its disposition:

- `def-galois-categories`: category packaging not used; the geometric-fibre theorem remains.
- `def-weil-affine-spectrum`, `def-weil-finite-integral-morphism`,
  `lem-weil-pbc-fibre-product-affine-spectra`: the affine calculation is replaced by proved API.
- `def-weil-pbc-scheme-conventions`: remains a statement dependency; no separate proof step.
- `def-pc-fibre-product`, `def-weil-algebraic-closure`,
  `def-weil-pbc-abelian-etale-sheaves`, `def-weil-pbc-etale-site`,
  `def-weil-pbc-finite-etale-trace`, `lem-weil-pbc-etale-covering-base-change`,
  `lem-weil-pbc-etale-inverse-image-restriction`,
  `lem-weil-pbc-finite-etale-etale-local-split`, `lem-weil-pbc-finite-etale-trace-exists`,
  `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-scheme-coproduct-copies`:
  retained in the new trace lemma's proof plan, rather than direct parent dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The planned affine calculation duplicates existing
proved source-library API. The unit `sk-thm-p1` and its realized nodes are unchanged;
this is a simplification below the unit level. The pre-existing use of the proved
`lem-galois-geometric-fibre` from the finite-etale unit is retained.

Checked edge cases: the source theorem allows an empty coproduct, and the explicit
reindexing and point equivalence work with `d = 0`. The parent uses `ConnectedSpace X`
only to choose a point and make the degree constant. The new trace lemma omits
connectedness because the local computation applies to every base of prescribed degree;
on the empty base the empty covering forces all section groups to be zero.

Read the target module, the finite locally free degree statement and definition, the
trace definition and full existence-characterization signature, the geometric splitting
and base-change source proofs, and the local splitting theorem. Sources 03SH and 04HN
were checked on the Stacks website because literature files are absent on this machine.
LeanFinder and Loogle found degree/local-constancy ingredients; the trace search found no
matching theorem. LeanSearch returned HTTP 500 and is recorded as unavailable.

## New nodes

`lem-weil-pbc-finite-etale-trace-degree-trace` states just trace after restriction for
an already prescribed finite locally free degree. Its Lean module is
`lean/Sheaf/AlgebraicGeometry/FiniteEtaleTraceDegreeTrace.lean`. Its proof is the last
four stages of the original argument with an independent geometric cardinality
calculation, so it does not depend on the parent and creates no cycle. The statement
has no nonempty or connected-base hypothesis. No change records are needed: all existing
signatures and public imports are unchanged.

## Second reading by J2

1. Signature preservation: compared the parent with the repository using `diff -u`.
   The only changes are four plain proof imports removed, one plain proof import added,
   and the proof replacing `sorry`. The entire existing declaration header and docstring
   are unchanged byte for byte; all three public imports are unchanged. There are no
   changed definitions or existing statements and no change records are required.
2. Proof and trust: independently compiled both modules in import order with `lcompile.py
   --all`, without errors or warnings. The parent has no `sorry`; the sole new `sorry`
   is the public named theorem `finiteEtaleTrace_comp_restriction`. No forbidden trust
   declarations or hollow definitions occur. A scratch copy with `#print axioms` shows
   `[propext, Classical.choice, Quot.sound, sorryAx]` for the parent and trace lemma.
   The geometric splitting, base-change fibre-degree and finrank comparison lemmas each
   show only the three permitted axioms. Thus this delivery closes the parent by a
   reduction, and does not claim to discharge its admitted dependencies.
3. Split statement: read the new trace module, its complete node and the chosen-trace
   definition and `existsUnique_finiteEtaleTrace` characterization. Read Stacks
   [03SH](https://stacks.math.columbia.edu/tag/03SH), the paragraph after Definition 03SE,
   and [04HN](https://stacks.math.columbia.edu/tag/04HN). The fixed-degree formula is
   exactly the trace clause, with finite locally free degree supplying finiteness;
   it does not assert constant-degree existence or geometric splitting. It is strictly
   part of the original argument. In its proof plan, the geometric splitting statement
   supplies finiteness, an over-isomorphism and the dimension count; 04HN supplies a
   pointed neighbourhood and clopen coproduct, so the count there applies at that point.
   Localization and split-sum are precisely properties (1) and (2) of the trace family;
   the inverse-image restriction identifies the unit, and sheaf separatedness descends
   the equality. Tested degree zero (empty sum), degree one (identity), disconnected
   bases of prescribed degree (same local calculation), and empty base (all site objects
   empty, with zero section groups). No surjectivity or invertibility is needed.
   Independently searched LeanFinder for transfer composed with the adjunction unit,
   Loogle for `"trace", CategoryTheory.Sheaf`, Mathlib grep for transfer/trace-unit,
   and both Lean library roots for trace/restriction/transfer. No chosen-trace degree
   formula was found. The nearby `exists_finiteEtaleModuleTrace_degree` only constructs
   some coefficient-linear trace from geometric cardinalities; it does not identify it
   with this chosen characterized abelian trace. Closing the remaining statement needs
   the localization and descent formalization and is not a few-minute repair.
4. Route and pruning: read `dag/units/sk-thm-p1.json` and its `realized` list. Neither
   this parent nor the new helper replaces a realized unit statement or step. The proved
   geometric-fibre theorem from the finite-etale unit is still used. The shortest existing
   base-change API is used in the parent; the reindexed coproduct is checked over Spec Ω,
   and the explicit point equivalence proves both finiteness and cardinality even for
   empty index sets. The new module's public imports provide its signature; its plain
   local-splitting import supports its documented remaining proof. No public proof-only
   import was introduced. Expanded `No longer needed` to enumerate all sixteen removed
   parent dependencies and distinguish those retained in the trace plan.
5. Nodes: the existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   Its five steps match, respectively, constant degree, dimension under base change,
   the over-isomorphism reindexing, the point equivalence, and the trace application.
   For both nodes, `proof_deps` is exactly the union of the steps' `uses`. Checked the
   new node's source, searches, creation, blueprint ancestry, chapter/unit and complete
   Lean record; its verbatim Lean signature agrees with the new theorem. There is no
   dependency back to the parent and hence no new cycle. The source/library matches
   `exists_overIso_sigma_of_isSepClosed` and `sigmaMk` are recorded by the existing
   geometric-fibre and coproduct-family nodes. Verdict: the proof and split are sound.

Second-reading changes: completed the pruning inventory and added this independent review.
No Lean proof or statement needed repair.
