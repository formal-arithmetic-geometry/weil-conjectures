## What changed

Proved `AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι`
in `Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate` without changing
any existing signature, visibility, or definition body. Added proved private helpers for
Cech differential coordinates, forgetting scalar structure, degree transport, pulling
cochains along refined families, and identifying the external bidegree formula with the
ordinary cup product on the product scheme. Updated the existing node's proof route.
No imports changed and no other module was adapted.

The shorter route reuses the already-proved `cechCupCochain_leibniz` from
`Sheaf.Paper.CechCupProduct`, rather than repeating its signed face cancellation.
The pullback helper is a real coordinate construction using the existing canonical
adjunction unit; it chooses no new existence witness. Its differential identity is proved
termwise from naturality and composition of restrictions. The scalar-forgetting helper
is an additive equivalence between common section coordinates.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι`
(node `lem-sc-picard-external-cech-cup-differential-coordinate`).
Added zero holes. No `sorry` remains in the delivered module; nothing was split off.
The previously proved degree-map inclusion equation remains proved.
The module compiled cleanly through `lcompile.py`, with no warnings.

## No longer needed

None. The sole public import, `Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree`,
is needed by the unchanged statements. All four original proof-dependency nodes remain
used: the Cech models, pullback adjunction, bidegree coordinates, and ordinary Cech cup
product. Their modules remain needed. The explicit external alternating-face cancellation
is replaced by the existing ordinary Leibniz theorem, but this prunes no dependency node.
The unit's realized statement/step lists are empty and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG planned a second signed-face calculation, although the ordinary Cech Leibniz
identity is already proved in `Sheaf.Paper.CechCupProduct`. Pulling both cochains to the
product scheme lets that theorem apply. The original statement is unchanged and includes
arbitrary families, repeated tuple entries, degree zero, characteristic two, and zero
coefficients. The argument uses only additivity and restriction naturality, so these cases
require no extra hypotheses. Search results are recorded in `searches.jsonl`: LeanFinder
returned Hom-complex differential lemmas, Loogle located the generic tensor-total formula,
and Mathlib grep found no matching Cech pullback/Leibniz statement. The local library search
located the already-proved ordinary Leibniz theorem.

The earlier coordinate-relocation change record was read; this delivery preserves that
interface and needs no forced downstream adaptations. Explicit cast rewrite arguments avoid
unconstrained degree matching during elaboration. Local heartbeat limits accommodate the
remaining nested scalar/sheaf definitional reductions; the clean compile stays below the
single-file time limit.

## Second reading by A2

1. Interface: PASS. Read the full module and its diff against the repository. All three
   existing declaration signatures are byte-for-byte identical after restoring one extra
   space before `:=` in the coordinate theorem. The degree-map definition body, inclusion
   proof, visibility, variables and public import are unchanged. The earlier relocation
   change record is preserved; no new interface change or downstream adaptation is needed.
2. Proof: PASS. Independently compiled the module through `lcompile.py` (25 seconds, no
   warnings), then compiled a scratch copy with `#print axioms` for all three public
   declarations, the pullback-adjunction existence theorem and ordinary cup Leibniz theorem.
   All report exactly `propext`, `Classical.choice`, `Quot.sound`; there is no `sorryAx`.
   No sorry or forbidden declaration is present. Read the pure-tensor reduction, both degree
   transports, scalar-forgetting equivalence, termwise pullback naturality and bidegree
   comparison. The chosen adjunction comes from a proved theorem specifying its unit on
   every section by an explicit formula; this is not an arbitrary witness of an open
   existence statement. The private cochain definitions construct coordinates directly.
3. Split statements: PASS, vacuous. No statement or hole is split off and no new public
   theorem is introduced. The private helpers are all proved. Checked the small cases:
   p=q=0 has second sign +1; repeated vertices need no distinctness; empty index families
   leave no tuples; zero coefficients and characteristic two require no division or extra
   hypothesis. The restriction/naturality proof remains valid in each case.
4. Route and pruning: PASS. Independently searched the local library for Cech differential,
   pullback and Leibniz identities and used `msearch.py` grep with alternative search words.
   The existing ordinary `cechCupCochain_leibniz` is already reused; no shorter matching
   external theorem was found. The sole public import supplies the unchanged bidegree
   predicate in the statement and cannot become proof-only. Compared old/new proof_deps:
   all four original dependencies are genuinely used, so `No longer needed: None` is
   complete. Read `dag/units/sk-prop-av-cube.json`: realized statement and step lists are
   empty, and no recorded unit route is bypassed.
5. DAG: PASS. The only changed JSON fields are `proof` and `proof_origin`; proof_deps is
   unchanged and equals the union of the recorded step uses. The three steps match the
   total differential reduction, pullback compatibility, and ordinary Leibniz reduction
   in the Lean proof. The node statement and verbatim Lean signature remain unchanged;
   no new nodes need the stage-3 fields.

Second reading changed only the extra space before `:=` to restore exact signature bytes,
and added this independent review. No mathematical repair was required. One original hole
is closed, zero holes are added, zero remain in this module; this is a proof, not a
decomposition. No nodes or modules are pruned.
