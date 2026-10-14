## What changed

Proved `AlgebraicGeometry.Scheme.affine_torsor_invariant_puncture_etale` with its exact existing signature. Added the proof-only import `WeilConjectures.Mathlib.RingTheory.TotallySplit`. A proved private helper converts the basic-open etale condition to algebraic etaleness of the localization. Flat base change of finite-family fixed points and the existing finite-etale fixed-points theorem then close the proof. Updated the assigned node to this route; no other interfaces changed.

## Proved and sorry left

Closed the single hole in `AlgebraicGeometry.Scheme.affine_torsor_invariant_puncture_etale` (node `lem-sbc-affine-torsor-invariant-puncture-etale`). No sorry remains and no holes were added. The private helper `puncture_etale_iff` is proved. The fixed-points tools are existing proved source-library declarations.

## No longer needed

The proof no longer uses node `lem-weil-pbc-connected-torsor-subgroup-quotient` or module `Sheaf.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient`. It was not imported in the original module, so no existing import was removed. Second reading removed the redundant added proof-only import `Mathlib.RingTheory.Localization.BaseChange`; its declarations are already available transitively. All public imports are retained for the unchanged statement. No new modules or nodes are needed. This pruning concerns this proof's dependency only; other users can still need the subgroup-quotient module.

## Where the brief, the DAG or earlier work was wrong

The original torsor-quotient route is valid but unnecessary below this unit's route: finite-family fixed points of any finite etale algebra are already finite etale, and fixed points commute with flat base change. Consequently the group-law, geometric rotation, domain, nonzero and faithful-flatness hypotheses are unnecessary to this proof; they stay exactly as supplied. No unit-realized node is bypassed (`sk-prop-input-spreading` has no realization entry for this node). Trivial and full subgroups are covered uniformly; zero localization also causes no exception. The existing docstring records the original mathematical proof and was preserved.


## Second reading by A4

1. Compared the sole delivered Lean module against the repository with `diff` and independently compared the existing theorem signature as text: byte-for-byte identical. No definition or public import changed; no change record is needed. Verdict: pass.
2. Compiled the delivered module locally with `lcompile.py` (no errors or warnings). A scratch copy with `#print axioms` shows exactly `propext`, `Classical.choice`, and `Quot.sound` for `AlgebraicGeometry.Scheme.affine_torsor_invariant_puncture_etale`, `AlgHom.finite_and_etale_fixedPoints`, and `AlgHom.tensorFixedPointsEquiv`. No sorry, prohibited declaration, hollow definition, or arbitrary witness from an unproved existence theorem occurs. Verdict: pass.
3. No statement was split off and no hole was added. Read the upstream fixed-points construction and finite-etale theorem, and searched `lean/Sheaf` and `lean/WeilConjectures/Mathlib` independently for basic-open etaleness and fixed-points results. Existing upstream tools are used directly; no duplicate public statement was introduced. The localization equivalence helper is private and proved. Trivial and full subgroups, invertible denominators, and the zero localization are covered without division by the group order or a nonemptiness assumption. Verdict: pass.
4. Read the proof from its conclusion back through the localization equivalences and flat base change. This is the direct finite-etale fixed-points route, with no torsor construction required. The old sole proof dependency `lem-weil-pbc-connected-torsor-subgroup-quotient` and its module are listed above as no longer needed. Checked `dag/units/sk-prop-input-spreading.json`: its realized statement and step lists are empty, and no unit route is bypassed. Tested removal of the extra localization import by compiling a scratch copy successfully. Verdict: pass after removing that redundant proof import.
5. Compared the delivered node with the repository node: only `proof`, `proof_deps`, and `proof_origin` change. The three recorded proof steps follow the Lean proof, and the empty proof-dependency list correctly removes the unused subgroup-quotient node. No new nodes exist. Verdict: pass.

Second-reading change: removed only the redundant proof import `Mathlib.RingTheory.Localization.BaseChange` and corrected this report accordingly; the proof itself needed no repair. Closed one existing hole, added zero holes, left zero holes in the delivered module.
