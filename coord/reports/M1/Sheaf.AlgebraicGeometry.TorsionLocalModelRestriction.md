## What changed

Restored and repaired the complete proof from returned head f1b69da02 against the
current upstream-synced `sheaf-dag` sources. Both proof-only `import all` lines now
refer directly to `WeilConjectures.AlgebraicGeometry.FormalSystemsPullback` and
`WeilConjectures.AlgebraicGeometry.TorsionControlledFormalRestriction`.
The retired `Sheaf` wrappers publicly re-export the upstream declarations, but
`import all` of those wrappers does not expose the upstream private helpers used by
this proof. Importing the actual upstream modules fixes that visibility failure.

The proofs, existing signatures, visibility, public imports and node route are
unchanged from the previously complete delivery. Relative to the current base,
the two proofs replace the holes left by the take-out. No dependency module is
changed. Fresh verification on 2026-10-17 compiles the repaired module with `lcompile.py`
in 15.8 seconds, without errors or warnings. A refreshed scratch
copy compiles in 19.2 seconds and checks both declarations with `#print axioms`: each uses only `propext`,
`Classical.choice`, and `Quot.sound`. The current base already comments out the duplicate
`affinePointedNeighbourhoods_initial_and_final_op` in
`StrictHenselizationCompatibility`; this delivery does not reintroduce it.

## Proved and sorry left

Closed both current-base holes:

- `AlgebraicGeometry.coherent_of_iso` (private helper);
- `AlgebraicGeometry.torsionLocalModel_restriction`.

Holes closed: 2. Holes added: 0. Holes left in the item: 0. Split-offs: 0.
There is no new declaration or new unresolved dependency. The main proof constructs
`Fw = R.obj F.obj`, transports the over-site normalization maps, constructs the
normalized completion comparison, and retains the supplied annihilation exponent.

## No longer needed

Replaced the two proof-only wrapper imports:

- `Sheaf.AlgebraicGeometry.FormalSystemsPullback`;
- `Sheaf.AlgebraicGeometry.TorsionControlledFormalRestriction`.

Their existing upstream counterparts supply the same proved helper declarations.
The second reading also removed three redundant proof-only imports:

- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`;
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`;
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`.

The retained upstream helper modules already expose the coherence criterion,
quasi-coherent kernel/cokernel results, and restriction preservation instances.
These results are still used, so all eight existing `proof_deps` remain needed.
Every final import is needed by the proof or its statement. No DAG node or module
is claimed to leave the targets' import closure; the existing proof route and
`proof_deps` remain accurate, so no node edit is delivered.

## Where the brief, the DAG or earlier work was wrong

The previous delivery's statement that the unchanged wrapper imports compiled
against the synced source was insufficient: after upstream adoption, private helper
visibility belongs to the actual upstream module. The first restored compile failed
on `coherent_pullback`, `completionPullbackIso`, `powerQuotientIso` and
`powerProduct_pullback_zero`. Direct `import all` of their upstream module repairs
those failures without copying definitions or adding a sorried interface.
Revalidated the retained repair in this session against the current published
build. A scratch reconstruction of the old wrapper imports reproduces the missing
helper errors, while direct upstream imports compile and have only the three
permitted axioms. Both new import directions pass `tools/import_direction.py may`.
Fresh LeanFinder, Loogle and Mathlib grep searches confirm the existing route uses
the available restriction and adjunction APIs; no new intermediate theorem is
needed. This is a source repair, not an unchanged re-push or rebase.


## Earlier second reading (a previous round; superseded)

1. Compared the sole delivered Lean module with the read-only repository using
   `diff -u`, then checked both existing declaration signatures byte for byte.
   Verdict: unchanged signatures, visibility, docstrings, public import, and
   definitions; only the two proof bodies and proof-only imports differ. There
   are no dependency-module adaptations or statement-change records to review.
2. Independently compiled the item and a fresh scratch copy containing
   `#print axioms` for both `AlgebraicGeometry.coherent_of_iso` and
   `AlgebraicGeometry.torsionLocalModel_restriction`. Both report exactly
   `propext`, `Classical.choice`, and `Quot.sound`. Scanned the delivered source:
   no holes or forbidden declarations/options. The restricted object is the
   explicit `R.obj F.obj`, with constructed maps and completion comparison; no
   arbitrary object is selected from an unproved existence theorem. Verdict:
   both original holes are closed without new holes or axioms.
3. There are no split-off statements, new declarations, or new nodes. Inspected
   the existing constructions and edge cases: `W = U`, empty opens, zero modules,
   and zero/unit ideals need no added assumptions; the same supplied positive
   exponent is retained. Fresh Mathlib grep, Loogle, and LeanFinder searches,
   together with `rg` on the project library, found no exact replacement for the
   normalized local-model assembly. The local-generators transport uses the
   existing generator API. Verdict: no disguised restatement or new obligation.
4. Read the proof from its conclusion down through coherence transport, both
   normalization equations, and actual kernel/cokernel annihilation. It reuses
   the proved upstream pullback/quotient helpers and categorical preservation
   isomorphisms. Checked `dag/units/sk-thm-p1.json` and its `realized` fields:
   this lemma is below the fixed unit route and bypasses none of its steps.
   Import-removal checks found three redundant proof imports, removed below;
   all old `proof_deps` still occur in the mathematical argument. Verdict:
   the route is valid, and the pruning report now lists every import removed.
5. Read `lem-weil-pbc-torsion-local-model-restriction.json` and the declarations
   recorded for all eight proof dependencies. Its five proof steps describe
   the implemented construction, gamma projection equation, b/q normalization,
   and transport of the unchanged bound. `proof_origin` cites the same source;
   the upstream sync has already updated the dependency records. Verdict:
   the existing node needs no edit, and there are no new nodes to validate.

Second-reading changes: removed the three redundant proof-only imports listed
under `## No longer needed`, and corrected that section's earlier assertion that
all imports were necessary. The proof bodies are unchanged. Refreshed the scratch
axiom check from the final source and compiled the final module and scratch copy.

## Second reading by M1

Independent second reading of the current repaired delivery, 2026-10-17:

1. Compared the only delivered module with the read-only repository using
   `diff -u` and independently compared both declaration signatures byte for
   byte. Also compared the public theorem signature with the node's verbatim
   `lean.statement`. Verdict: all match; only proof bodies and private imports
   change. Public imports, visibility, docstrings and definitions are unchanged.
   There are no adapted modules or statement-change records.
2. Compiled the delivered module using `lcompile.py` (19.8 seconds, no errors or
   warnings). Created a fresh scratch copy from that exact source and appended
   `#print axioms` for both declarations; it compiled in 19.9 seconds and each
   reports only `propext`, `Classical.choice`, `Quot.sound`. Scanned the source
   for holes and forbidden declarations/options: none. Read the constructions:
   Fw is explicitly R.obj F.obj; lw, aw, gamma and betaW are compositions of
   existing constructed comparisons. Verdict: two holes closed, zero added,
   no unproved existence theorem used to choose an arbitrary model.
3. No split-off statements, new declarations or new nodes occur. Independently
   searched with LeanFinder for coherence under isomorphism and ideal-power
   quotient restriction, Loogle for `SheafOfModules.IsFiniteType`, Mathlib grep
   for `Generators.ofEpi`, and `rg` on the two project roots for coherence and
   restriction comparisons. The generator transport uses the existing API;
   no exact packaged replacement for the whole assembly was found. Checked
   W = U, empty opens, zero modules, zero and unit ideals: every comparison
   remains defined, and the positive exponent supplied by ha is retained.
   Verdict: no new obligations or disguised restatement.
4. Read the proof from the conclusion back through the three conjuncts.
   The gamma projection equation uses naturality, powerQuotientIso_π and
   cokernel.π_desc; the b and q equations cancel the stated comparison maps;
   the bounds concern the actual kernel and cokernel and use their preservation
   isomorphisms. Read the upstream helpers rather than assuming the retired
   wrappers expose them. All three final imports are needed: one for the
   statement, two for directly used private proof helpers. The removed imports
   are all listed under `## No longer needed`; their results remain available
   transitively and are still used. Read the unit record and its source section:
   this node lies below the fixed route and bypasses no realized step.
   Verdict: pruning and unit route are correct; no further proof rewrite needed.
5. Read the item's node, all eight dependency Lean records, and the actual
   helper implementations. Its five proof steps, proof_deps and proof_origin
   describe the implemented argument, including the unchanged exponent and
   normalized projections. The signature matches the node verbatim, and there
   are no new nodes to validate. Verdict: no DAG change required.

Changes in this second reading: appended this independent review and refreshed
scratch axiom evidence. No further Lean or DAG edits were necessary; the existing
import repair and pruning pass review. Final count: 2 of 2 holes closed, 0 holes
added, 0 split off; no module is claimed pruned from the targets' import closure.
