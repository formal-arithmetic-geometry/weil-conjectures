## What changed

Proved `PrimeSpectrum.exists_closed_component_restriction` in
`lean/Sheaf/RingTheory/ClosedComponentSpectrumRestriction.lean`, with its signature and all
public imports unchanged. The proof uses the existing, concrete
`WContractification.Restriction T` for `T = ConnectedComponents.mk '' E`. Component saturation
identifies its spectrum range with `E`; the spectrum embedding gives a homeomorphism whose
underlying function is definitionally the required comap. The existing ind-Zariski instance
and `Algebra.IndZariski.bijectiveOnStalks_algebraMap` give the required induced local-ring maps.
Updated the item's node proof and direct proof dependencies to match this assembly.

The source-library declarations already implement the clopen filtered-colimit construction,
so no new construction or intermediate theorem is necessary. Checked the cited sources:
[Stacks 097C](https://stacks.math.columbia.edu/tag/097C),
[096T](https://stacks.math.columbia.edu/tag/096T), and
[04PL](https://stacks.math.columbia.edu/tag/04PL).
The proper-base-change unit's realized statement and steps are untouched.

## Proved and sorry left

Closed the sole original hole: `PrimeSpectrum.exists_closed_component_restriction`
(node `lem-weil-pbc-closed-component-spectrum-restriction`). No holes added or left in this
module, and no split-offs. This is a proof from already proved source-library results.
The final single-file compile passes without warnings in approximately two seconds.

The proof does not assume a nonzero ring or a nonempty set: for empty `E`, `T` is empty and
the restriction has empty spectrum; for the whole spectrum it restricts to the whole range.
The quotient-topology and homeomorphism assembly handle both cases uniformly.

## No longer needed

Removed the following redundant direct proof imports:

- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Mathlib.GroupTheory.MonoidLocalization.Away`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `WeilConjectures.RingTheory.ProEtale.IndZariski`

The retained `WeilConjectures.RingTheory.ProEtale.WContractible` import publicly provides the
spectrum and ind-Zariski APIs actually used. Colimit and localization-away facts are already
packaged in the proved restriction construction and its instances. Thus the direct edges to
`def-weil-pbc-category-colimit` and `def-weil-ring-localization-away` are removed from this
node's `proof_deps`; these notions remain used inside the source-library construction, and
this report makes no claim that their modules leave the global import closure. All four
statement dependency nodes retained in `proof_deps` are used. No Sheaf module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement change. The original plan's filteredness and localization
checks were already proved by `WContractification.Restriction.indZariski`; the node's own
`lean_audit.slopmaster2` accurately pointed to the needed closed API. There is no need to
rebuild that presentation here. The plan's explicit zero-locus detour is also unnecessary:
the spectrum embedding and the restriction range equality directly yield the homeomorphism.

## Second reading by D4

1. **Signatures unchanged.** Compared the delivered Lean module and node against the repository. The
   theorem statement is byte-for-byte unchanged; only its proof, proof-only imports, and the node's
   proof metadata are changed. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, `implemented_by`, or `sorryAx`. A scratch `#print axioms`
   reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Statements and dependencies.** The existing theorem is the exact target statement. No new
   declarations or split-off statements were added. Mathlib and source searches found no shorter
   one-line theorem for the full claim. Removed the unused quotient-zero-locus proof dependency;
   the proof directly uses the Mathlib surjective-spectrum embedding and the Restriction range
   theorem. Verdict: pass.
4. **Pruning and imports.** The four redundant imports removed by the first worker are genuinely
   unused; the retained public imports support the signature and the private `WContractible`
   import supplies the concrete construction and its proved APIs. The node's proof dependencies now
   list exactly the three non-Mathlib APIs used by the proof. Verdict: pass.
5. **DAG and unit route.** The node proof steps, `proof_deps`, and `proof_origin` agree with the
   Lean proof, and the proper-base-change unit's realized statement and route remain intact.
   No new node or change record is needed. Verdict: pass.

Changed in this second reading: pruned `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus` from
that node's proof step and `proof_deps`, and documented this review.
