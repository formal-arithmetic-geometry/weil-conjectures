## What changed

The existing theorem `AlgebraicGeometry.Scheme.dvr_galois_components_root_cotangent`
keeps its complete signature and docstring byte for byte. Its proof obtains principalness
of the actual normalization stalk maximal ideal and nonmembership of the structural root
in its square, applies a proved local-algebra criterion, and then uses `le_sup_left`.
The three added Sheaf imports are proof-only, written `import`.

The first worker's unproved `DvrGaloisComponentsRootCotangentCore` was removed from the
sandbox: its first conjunct was the entire target conclusion, so projecting that conjunct
was a restatement, not a reduction. It is replaced by two separate modules, one for each
strict part of the local argument:

- `DvrGaloisComponentsStalkPrincipal`: principalness of the maximal ideal. This needs neither
  invertibility of n nor divisibility of the component degrees by n.
- `DvrGaloisComponentsRootNotSquare`: the tame root germ lies outside the maximal-ideal square.

`Sheaf.RingTheory.PrincipalCotangentSpan` proves the remaining algebra calculation for any
commutative local ring with principal maximal ideal. It handles units separately and
requires neither a domain nor Noetherianity. Its `PrincipalIdealDomain` import is proof-only.
No existing definition, declaration signature, public import or target statement changed.
No change record or forced adaptation is needed.

## Proved and sorry left

Original hole closed, by declaration name:
`AlgebraicGeometry.Scheme.dvr_galois_components_root_cotangent`.

New theorem proved with no sorry:
`IsLocalRing.maximalIdeal_le_span_of_isPrincipal_of_not_mem_square`
(node `lem-sbc-principal-cotangent-span`).

Two holes added and left, each in its own new module with a complete sourced docstring proof:

- `AlgebraicGeometry.Scheme.dvr_galois_components_normalization_maximalIdeal_isPrincipal`
  (node `lem-sbc-dvr-galois-components-stalk-principal`).
- `AlgebraicGeometry.Scheme.dvr_galois_components_root_not_mem_square`
  (node `lem-sbc-dvr-galois-components-root-not-square`).

This is a decomposition, not an axiom-free proof of the item: one original hole is closed
and two lower holes are added, so the local hole net is -1. No claimed progress from landing.
The discarded core was never an upstream hole; it is not counted as a hole closed.
The target and both geometric statements have only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` in their printed axioms. The local-algebra theorem has only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No old proof dependency or repository module is pruned: the original node's `proof_deps`
was empty. All six existing public imports serve the target signature. The rejected
sandbox-only core and its import are removed; this is not target-closure pruning.
The previously mismatched sandbox node `lem-sbc-principal-cotangent-span` now describes
and records the proved local-algebra theorem, rather than the unrelated geometric core.

## Where the brief, the DAG or earlier work was wrong

The original proof plan cites literature but has no Lean declarations for its geometric
steps. That absence does not justify moving the whole conclusion to an unproved core.
The first worker did precisely that, then projected its first conjunct. The core also
lacked the required proof docstring, its node described a different local-algebra lemma,
and its `lean.statement` was an ellipsis rather than the verbatim Lean statement.
Copied K3 review certificates in that new node were unrelated to this delivery and removed.
The old report described the projection as a proof; this report records the actual
one-to-two decomposition and remaining geometric work.

## New nodes

`lem-sbc-dvr-galois-components-stalk-principal` records the principalness statement under
finite Galois component hypotheses, without the unnecessary tame bound. Its proof uses
[Stacks 09EV](https://stacks.math.columbia.edu/tag/09EV),
[09E8](https://stacks.math.columbia.edu/tag/09E8),
[00PD](https://stacks.math.columbia.edu/tag/00PD), and
[0307](https://stacks.math.columbia.edu/tag/0307).
Mathlib has integral-closure Dedekind and AtPrime DVR results, but not the needed actual
scheme-stalk comparison. The existing root-chart principalness theorem assumes normalization
finiteness and different chart data, so it cannot directly close this statement.

`lem-sbc-dvr-galois-components-root-not-square` records only nonmembership of the actual
root germ in the maximal-ideal square. Its sourced docstring follows
[09EB](https://stacks.math.columbia.edu/tag/09EB),
[0BRM](https://stacks.math.columbia.edu/tag/0BRM), and
[09E7](https://stacks.math.columbia.edu/tag/09E7), followed by the affine normalization
and localization identification. Existing chart-specific RootNormalizationRootNotSquare
reaches this item through DvrRootNormalizationMaximalIdeal, so importing it would cycle.

`lem-sbc-principal-cotangent-span` records the proved general local-algebra criterion.
A principal generator r gives tau = c*r for nonunit tau. The non-square hypothesis forces
c to be a unit; hence the root span is the maximal ideal. Unit tau has span top.
The matching statements and all three kinds of search are recorded in the node files.
No change record was added, since these are new declarations and the existing signature
has not changed.

## Second reading by J3

1. Compared the delivered existing module with the repository using `diff`. The only
   differences are three ordinary proof imports and the proof body. Checked the full
   signature text byte for byte. No existing data definition or statement changed.
   The other three modules are new. Verdict: pass after replacing the invalid core.
2. Compiled all four modules locally through `lcompile.py --all`: no errors or warnings.
   Searched all delivered Lean files for sorry and forbidden declaration forms. The only
   two sorries are the named geometric statements listed above, with sourced proof
   docstrings and nodes; no definitions or arbitrary data witnesses are introduced.
   A scratch copy of the target module printed axioms for all four declarations:
   only the permitted three axioms and, for the open geometric dependencies and target,
   `sorryAx`. Removed the scratch copy before delivery. Verdict: pass as a decomposition.
3. Read the new statements against their sources and searched with different terms using
   Lean Finder, Loogle, msearch grep and rg; LeanSearch was attempted and returned
   Internal Server Error. Searched the upstream/Sheaf and Mathlib sources.
   Neither geometric statement contains cotangent spanning. Principalness alone does not
   span tau (take tau = t^2 in k[[t]]); non-square alone does not imply spanning (take
   tau = x in k[[x,y]]). Principalness is independent of tameness. The second statement
   retains the tame degree hypotheses required for valuation one. Checked n=1,
   degree-one factors, r=0 (no normalization point), positive residue characteristic
   and residue characteristic zero. The general algebra proof also covers field rings
   and unit tau, and does not assume a nonzero generator. Verdict: true partial statements
   and a genuine reduction; existing declarations do not directly replace them.
4. Read the target and its plan from the top downward, then the existing root-chart
   principalness, root-not-square and DVR-comparison modules. Their stronger/different
   chart assumptions or dependency cycle prevent direct application. Retained the
   Abhyankar/root-extension route, with the final elementary generator calculation
   proved explicitly. The unit `sk-prop-input-spreading` has empty `realized.statement`
   and `realized.steps` lists; none is bypassed or changed. The old node had no
   `proof_deps`, so there are no omitted old dependencies to prune. All added imports
   in the target and the PrincipalIdealDomain helper import are proof-only. Verdict: pass.
5. Checked each node against its Lean declaration and recorded its signature verbatim.
   The existing node's proof, proof_deps and proof_origin now record the two geometric
   inputs, the proved local-algebra input, and the final supremum inclusion. Each new
   node has the required source, proof, search, creation, blueprint, chapter, unit and
   Lean fields. Verdict: pass; no copied review claim is retained for a new node.

Second reading changes: removed the restatement core; split its genuine geometric parts;
proved the local-algebra reduction; repaired docstrings, imports, nodes and hole accounting;
removed the overlong proof line and stale node convenience copy.
