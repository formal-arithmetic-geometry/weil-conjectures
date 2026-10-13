## What changed

Replaced the sole sorry of
`Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift` by a complete Lean proof
from two strictly lower statements in new modules:
`Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift` and
`Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink`.
Both are imported privately (ordinary proof imports). The existing theorem's
signature and public imports are unchanged.

The proof first extends arbitrary degreewise stalk components. It derives the
stalk chain equations from the supplied chain map, invokes shrinking, constructs
the resulting chain map with `CochainComplex.ofHom`, and proves the required
stalk equality with `HomologicalComplex.hom_ext` and degreewise cancellation of
the intermediate comparison isomorphisms. Neither new statement assumes the
conclusion of the original theorem: extension imposes no chain equations, and
shrinking starts with maps already defined near the point and extends no
prescribed stalk map.

Only the perfect source is needed: its finite support bounds both the number
of components and the number of differential defects, and finite presentation
of its terms applies with an arbitrary target. The two new statements therefore
need no perfectness assumption on Q; extension also needs no affine hypothesis
on U. The original hypotheses hU and hQ remain in the unchanged signature and
are explicitly cleared in the proof. The unused-variable linter is disabled
only for this declaration because its fixed interface keeps those hypotheses.

Updated the original DAG node's proof, proof_deps and proof_origin to match the
Lean combination. Added the two component nodes with their exact Lean
statements, sources, complete proofs in words, and search records. All three
modules compile using lcompile.py. No definitions, target signatures, existing
interfaces, or modules held by other workers were changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_chainMap_lift`
(node `lem-sc-perfect-open-stalk-chain-map-lift`). Its proof has no sorry.

Added exactly two holes, each in its own module with a complete proof docstring:

- `AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_degreewise_lift`
  (node `lem-sc-perfect-open-stalk-degreewise-lift`).
- `AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_degreewise_shrink`
  (node `lem-sc-perfect-open-stalk-degreewise-shrink`).

This is a decomposition: one upper hole closed, two lower holes added, not an
axiom-free proof of the entire argument. There are no holes left in the original
module, and no other holes added.

Edge cases checked against the statements and proofs: source support interval
empty (the source is zero in every degree), zero-rank retractions, an unbounded
or nonperfect target, and the top boundary n=b. The shrinking step checks every
n in the source interval, including b; outside it the source of the defect is
zero. The shrinking comparison may use any supplied natural isomorphism e:
eV is obtained by composing the canonical further-restriction comparison with
e, so the asserted compatibility does not demand that e was canonical.

## No longer needed

No original imports or dependency modules are pruned. Both original public
imports are needed by the unchanged statement. A trial redundant proof import
of `Mathlib.Algebra.Homology.Embedding.CochainComplex` was removed; ofHom is
already available through the existing imports.

The original node's direct proof dependency
`lem-weil-pbc-stalk-internal-hom-finite-presentation` is now used below both
component nodes, rather than directly by the combining proof. It remains needed
and is not pruned. Likewise `def-pc-perfect-complex` and
`def-sc-open-module-stalk-functor` remain needed in the statements and below the
new nodes. The finite-free pullback-to-stalk-scheme modules examined during
search are not dependencies of this route and were never imported; no pruning
credit is claimed for them.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement was found. The existing
finite-free degreewise lift and shrink results use pullback to Spec of the
stalk and actual free presentations, whereas this item uses module stalks on
the slice site and finite-free retracts. They cannot be applied directly without
additional transport and local trivialization arguments. The new statements
make the corresponding two steps precise in this item's interface.

The planned intersection of the supports of P and Q is unnecessary. The finite
support of P alone suffices, including for the differential defects with target
Q.X (n+1). This is a simplification below the unit level. The cube unit's route
is preserved; neither its statement nor any realized step is bypassed.

The local copies of the cited Stacks TeX files are absent. The sources were
read at https://stacks.math.columbia.edu/tag/09RE and
https://stacks.math.columbia.edu/tag/01CP instead. LeanSearch returned Internal
Server Error for both new statements; this is recorded as unavailable, and
LeanFinder, Loogle, Mathlib grep and repository searches were performed.

## New nodes

`lem-sc-perfect-open-stalk-degreewise-lift`, in
`dag/nodes/sec-abelian-varieties/lem-sc-perfect-open-stalk-degreewise-lift.json`,
states extension of a finite-support source's degreewise stalk maps on a common
affine neighbourhood. It imposes no chain equations and allows an arbitrary
complex Q. Its proof uses the existing finite-presentation internal-Hom stalk
comparison, finite intersection, and the restriction/stalk comparison.

`lem-sc-perfect-open-stalk-degreewise-shrink`, in
`dag/nodes/sec-abelian-varieties/lem-sc-perfect-open-stalk-degreewise-shrink.json`,
states shrinking of an already defined degreewise family with stalk chain
equations, together with its comparison formula after further restriction.
Its proof uses injectivity of the same internal-Hom comparison, the finite list
of source degrees, and naturality of restriction. No change record is required:
no existing statement, definition, or public interface was changed.

## Second reading by V3

1. **Unchanged interface: PASS.** Compared the original module with its repository
   version using diff, and separately compared the theorem signatures byte for
   byte. The hypotheses X, U, x, hxU, hU, P, Q, hP, hQ and t, all universes,
   existential witnesses V/hxV/hV/hVU/e/g, and the stalk-map equality are identical.
   Both public imports are unchanged. The only new imports are ordinary proof
   imports. There are no changed definitions, existing auxiliary signatures or
   forced adaptations, and no change record is necessary. The existing node
   differs only in proof, proof_deps and proof_origin.

2. **Proof and trust: PASS as a decomposition.** Independently compiled all three
   delivered modules in import order with lcompile.py; all compile without
   errors or warnings (3.5, 4.6 and 5.9 seconds respectively). Inspected every
   delivered Lean file: the original theorem has no sorry, and each new module
   has exactly its reported named theorem with `:= by sorry`. There are no
   definitions or prohibited declarations in this delivery. A temporary scratch
   copy with explicit #print axioms for all three declarations compiled and
   reported precisely propext, Classical.choice, Quot.sound and sorryAx. The
   scratch source was removed. The proof extracts existential witnesses only
   inside a theorem proof; it introduces no definition choosing arbitrary data
   from an unproved existence theorem. The combining proof uses the conjugated
   chain map's comm equation, CochainComplex.ofHom, degreewise hom_ext, and the
   two inv_hom identities in the correct composition order.

3. **Split statements: PASS.** Independently matched every Lean signature to its
   node's verbatim lean.statement, and read both full docstring proofs and Stacks
   Tags 01CP and 09RE. A finite-free retract is finitely presented; its bounded
   support leaves a finite list of morphisms and differential defects. For
   extension, internal-Hom stalk surjectivity represents each prescribed component.
   For shrinking, injectivity and the germ equality criterion kill the already
   defined defects. Arbitrary Q is permitted in both arguments. Checked the empty
   support interval (a>b), zero rank/source/target, unbounded Q, n=b and n=a-1.
   At n=b the defect must still be checked; at n=a-1 its source is zero. The
   supplied e in shrinking can be arbitrary: compose the further-restriction
   comparison with e to obtain eV, which gives precisely the stated formula.
   Neither lower theorem is the original chain-map lifting statement under a new
   name: extension has no chain equations, and shrinking starts with actual
   local component maps and does not lift arbitrary prescribed stalk maps.
   Fresh LeanFinder searches used finite-free-retract morphism extension and
   bounded differential defects, Loogle used `"germ", "exists"`, and msearch grep
   used finite-presentation/generated stalk terminology. Repository searches
   additionally found StalkLinearMapLocalLiftFinitePresentation and
   CoherentStalkMapExtends. The former is a one-degree internal-Hom lemma; the
   latter requires local Noetherianity and coherence. FiniteLocallyFreeStalkHomLift
   is also a one-degree lemma, and FiniteFreeStalkDegreewiseLift/Shrink use actual
   free terms and pullback to Spec of the stalk. None states either new theorem
   or closes its site-equivalence, comparison and finite-family transport in a
   few minutes. The existing internal-Hom result is used in the lower proof plans,
   not restated. Both remaining holes have complete proof docstrings and nodes.

4. **Route and pruning: PASS.** Checked that both original public imports are
   required by the unchanged signature and both new proof imports are used.
   No import can be pruned from this delivery. Each old direct proof dependency
   (def-pc-perfect-complex, def-sc-open-module-stalk-functor, and
   lem-weil-pbc-stalk-internal-hom-finite-presentation) remains below the new
   nodes; the report's No longer needed section records all three and claims no
   pruning. Read dag/units/sk-prop-av-cube.json: its realized statement and step
   lists are empty, so this delivery bypasses no recorded realized node and
   changes no unit record. The chain-map descent remains on the existing cube
   route. No shorter direct library or Mathlib proof was found. This closes one
   upper hole and adds two lower holes, a net of minus one before any independent
   ledger reachability calculation; it is not a complete axiom-free proof.

5. **DAG agreement: PASS.** Read all three node records. Existing statements and
   statement dependencies stay unchanged. Each new node's source, created,
   blueprint ancestry, chapter/unit, status and lean record are present, and its
   statement matches the hypotheses and every conclusion of the Lean theorem.
   For all three nodes, proof_deps is exactly the union of the proof steps' uses.
   The original proof record follows extension, the derived stalk chain equations,
   shrinking, ofHom and comparison cancellation in the actual Lean proof.
   The lower records follow the corresponding complete natural-language proofs.

Second reading changes: appended this independent review and recorded fresh
search evidence in the sandbox search log. No repair of Lean or node records
was needed; no additional hole was closed or added. Temporary axiom-probe source
was removed. Delivery remains the reported one-to-two decomposition.
