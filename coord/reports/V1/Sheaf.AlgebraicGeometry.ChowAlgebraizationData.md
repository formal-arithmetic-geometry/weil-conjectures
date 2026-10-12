## What changed

The existing statement of `AlgebraicGeometry.exists_chow_algebraization_data` is unchanged.
Its proof now obtains an algebraization with proper support on Y from
`exists_chow_algebraization_core`, then applies
`chow_algebraization_pushforward_support` and combines the conclusions for the same F.
The two new modules have been repaired in the second reading: the core takes hR and
returns proper support on Y; the support lemma is the general proper-pushforward support
statement with proper support on Y as its hypothesis. No definition or existing signature
changed. All added proof-only imports are plain imports. In the core, FormalSystemsPullback
is plain-imported; its two signature dependencies are public-imported directly.

## Proved and sorry left

Hole closed in the item's module: `AlgebraicGeometry.exists_chow_algebraization_data`
(node `new-chow-algebraization-data`). Its reduction compiles, but depends on two new holes:

- `AlgebraicGeometry.exists_chow_algebraization_core`
  (node `new-chow-algebraization-core`).
- `AlgebraicGeometry.chow_algebraization_pushforward_support`
  (node `new-chow-algebraization-support`).

This is a decomposition, not a completed proof: one upper hole closed, two lower holes
added, net minus one before any changes elsewhere in the import closure. No data definition
is introduced and no arbitrary witness is chosen into a definition. F is only destructured
inside a proof of an existential proposition. Neither split lemma was closed in this review.
The geometric compactification/completion construction and the sheaf-level proper direct-image
support proof require further formalization; the existing higher-direct-image result alone
does not provide the support conclusion. The delivery tool's exhaustive axiom probes and
scratch `#print axioms` checks permit only the three standard axioms and `sorryAx`.

## No longer needed

The parent node's old direct proof dependencies are all replaced by the two new nodes:
`lem-weil-pbc-formal-systems-pullback`, `lem-weil-pbc-support-pullback-finite-type`,
`lem-weil-pbc-closed-subset-proper-over-base-union-preimage`,
`lem-weil-pbc-closed-subset-proper-over-base-properties`,
`lem-weil-pbc-pushforward-coherent-on-open`,
`lem-weil-pbc-grothendieck-existence-projective`,
`lem-weil-pbc-adic-complete-jacobson-radical`,
`lem-weil-pbc-module-support-proper-over-base`, `lem-pc-coherent-hi`,
`def-nagata-scheme-theoretic-image`, `lemma-nagata-immersion-open-in-scheme-image`,
and `pqf-lem-locnoeth-lft`. All are retained in the lower nodes' proof plans, so no
geometric step or globally unreached module is claimed pruned.

Removed direct proof imports from the item: `Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective`,
`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`,
`Sheaf.AlgebraicGeometry.PushforwardCoherentOnOpen`,
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`,
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage`,
`Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`.
Their imports move to the intermediate modules whose proof plans need them.

## Where the brief, the DAG or earlier work was wrong

The first worker omitted proper support of the degree-zero term from the core's hypotheses,
even though its proposed extension-by-zero proof needs it. It also asserted that any F with
the correct completion has proper pushforward support. That is false: let A = k[[t]],
I = (t), Z = Y = Spec(A[1/t,x]), q = id, G = 0, and F = O_Y. Every completion quotient
of F is zero, so the comparison holds, while Supp(F) = Y is not proper over A. Take L
the unit ideal, whose support complement is all of this nonempty Y; q is an isomorphism
there. The original support lemma even lacked the projective embedding hypothesis.
These unlanded new statements have been replaced, not delivered as false assumptions.

The first report called the reduction proved without identifying its negative hole net,
retained unused direct imports, and gave incomplete natural-language proofs and unsupported
search reports. This report and the new nodes correct those faults. The local checkout lacks
the Stacks TeX payload; the second reader checked the cited primary source online at
https://stacks.math.columbia.edu/tag/088E, and the support tools at Tags 0CYQ and 02O5.

## New nodes

`new-chow-algebraization-core` records the compactification, supported extension,
projective algebraization, boundary exclusion and restriction step, ending with proper
support on Y. Its source, full docstring proof, actual searches, precise Lean signature,
chapter/unit and proof dependencies are recorded.

`new-chow-algebraization-support` records proper pushforward of a coherent module with
proper support over the base. It no longer draws information away from V(I) from a
completion isomorphism. Its support-image/subset argument is independent of algebraization.
No change record is needed: only proofs and plain proof imports of the existing module
changed; the revised declarations and nodes are new, unlanded declarations.

## Second reading by V1

1. Compared the parent Lean file with the repository by diff and checked its theorem
signature byte for byte. Only the proof and plain proof imports change. No existing
statement, definition, visibility, or target changes; no other existing module is adapted.
Verdict: pass after repairing the unlanded intermediate statements.
2. Compiled all three delivered modules in dependency order using lcompile.py. Each
remaining sorry is the entire proof of one public named theorem, with a node and a
source/proof docstring. No forbidden declaration mechanism or holed definition occurs.
Checked axioms with scratch #print axioms and the delivery tool's probes.
Verdict: valid reduction with two explicitly open lemmas, not a complete proof.
3. Rejected the original support assertion by the counterexample above and restored hR
in the core. The replacements are strict parts of the geometric argument: supported
algebraization on Y, followed by proper pushforward support. For I = 0 the core is
ordinary pullback; for zero G one may use zero F; the support lemma covers empty
support and q = id. Repeated LeanFinder, Loogle and grep searches with new queries; LeanSearch returned
an Internal Server Error, which is recorded without an absence verdict,
and searched both Lean roots. No exact existing result supplies either whole step.
Verdict: pass after repair; actual searches are recorded, with no fabricated absence claim.
4. Retained the compactification/projective-existence/support-image route of 088E.
Read dag/units/sk-thm-p1.json and its realized fields: this node is a lower tool, not
a listed realizer of a unit step; no unit route is replaced. Removed the seven unused
direct proof imports from the parent and retained the relevant plans/imports below.
Verdict: pass; no globally pruned module is claimed.
5. Updated the parent's proof/proof_deps/proof_origin to the actual two-lemma reduction.
Updated both new nodes' statements and verbatim Lean signatures, complete proof plans,
source locations, dependency unions, required creation/blueprint metadata and actual
three-kind searches. Removed the parent node from the new nodes' stmt_deps so that
this split does not introduce a dependency cycle. Verdict: pass after repair.

Second-reading changes: repaired both intermediate statements and docstring proofs,
pruned unused direct proof imports, corrected the dependency records and searches,
and replaced the report with accurate decomposition accounting and review evidence.
