## What changed

Proved AlgebraicGeometry.principalCechTotalRegroup_comm in the assigned module,
without changing its signature, visibility, existing docstring, or imports.
The proof follows the node's coordinate argument. A private, fully proved
principalCechRowToTerms_differential identifies the row inclusion followed by
the explicit differential with the horizontal term plus the signed vertical term.
Four private elementary helpers evaluate sums and integer scalar multiples of
module maps and commute equality transports with section differentials and
restrictions. The public proof uses total.hom_ext, the coproduct inclusion
formulas for D₁, D₂ and totalDesc, he, and the vertical chain-map equation of e.

The subset calculation treats the supported vertical row, supported horizontal
row, and off-row coordinates explicitly; erased empty subsets contribute zero.
The sign is converted from p.negOnePow to (-1 : A)^(card(J)-1) using positivity
of the nonempty subset's cardinality. Equality transports are handled by proved
local identities, with no assumption on coefficient boundedness or the cover.
The row calculation also covers r=0 and negative or unsupported row indices.

Searches used LeanFinder, Loogle, Mathlib grep, and rg over both library roots.
They located Mathlib's total-complex inclusion formulas, not an existing proof
of this specific regrouping identity. LeanSearch returned Internal Server Error;
this was recorded as unavailable. Stacks Tag 08D1 was read online and confirms
the total differential d₁ + (-1)^p d₂ used here.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.principalCechTotalRegroup_comm
(node lem-sc-principal-cech-regroup-differential).

No sorry remains in the delivered module. No holes were added or split off.
Every private helper is proved. This is a proof, not a decomposition into
new unproved statements. All original dependency declarations and interfaces
are unchanged. The proof does not use principalCechTotalRegroup_isIso or any
other unproved dependency theorem: it uses the explicit constructions and
already proved product, differential-value, and transport formulas.

Both the row calculation and the total-complex argument compiled locally
before being combined into the assigned module. The final delivery dry run
performs the full single-file compile and axiom probe.

## No longer needed

None. The sole original import, PrincipalCechTotalRegrouping, is needed for the
explicit regrouping definition and row inclusion formula. No node or module
from the original planned route was bypassed. No new proof-dependency imports
are needed. The temporary row module is retained only as a scratchpad draft;
it is not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The previous attempts were blocked because the last-green compiled library
lacked PrincipalCechTotalRegrouping. That dependency is now available; the
unchanged starting file compiled successfully on this retry. No dependency
was rebuilt or copied to bypass the shared-library rules.

The saved total-complex draft had unvalidated rewrites with incorrect
association and chain-map orientation. These were repaired and compiled.
The final proof implements the existing DAG plan unchanged, so no DAG update,
new node, interface change, forced adaptation, or change record is needed.
The unit's realized statement and proof steps are preserved.

## Second reading by C3

1. PASS: compared the sole delivered module with the repository using diff.
The existing public theorem's docstring and signature are byte-identical,
as are the module header, variables, visibility and sole public import.
Only five private proved helpers and the original theorem's proof were added.
No definitions, existing statements, or change records were changed.

2. PASS: independently compiled the entire module with lcompile.py, with no
errors or warnings (29.5 seconds). Token and line-width checks found no sorry,
axiom, unsafe, opaque, implemented_by, extern, or line over 100 characters.
An appended scratch-copy #print axioms checked the public theorem; the delivery
probe also checks every added declaration. The chosen differential is specified
pointwise by its proved existence theorem, which uniquely determines the map;
there is no arbitrary existence witness or hollow definition in this delivery.

3. PASS: no statements were split off, no new holes or public lemmas were added,
and no new nodes are required. Read every private helper: the four elementary
identities follow from linear-map evaluation and equality elimination, and the
row identity is strictly part of the target argument and is fully proved.
For r=0 there are no subset coordinates; for singleton subsets the empty
deletions contribute zero and the vertical sign is +1. For p<0 or p>=r
no source row survives. The branch equations handle these cases without any
added cover or boundedness hypothesis.

4. PASS: searched library and upstream sources for row, regrouping, totalDesc,
and differential comparison identities, and searched Mathlib via msearch grep
with totalDesc/comm/differential and equality-transport naturality terminology.
Found generic total-complex inclusion and transport tools, already used or
reduced by the short elementary helpers; no shorter existing regrouping proof.
The sole import supplies symbols in the public signature and must remain public.
All four original proof_deps are used through the explicit regrouping, columns,
explicit differential, and Mathlib total construction. No pruning is omitted.
Read dag/units/sk-thm-picard-duality.json: its realized fields are currently
empty; this delivery preserves them and the inherited comparison route.

5. PASS: read the item's node and dependency definitions against the Lean proof.
Its proof, proof_deps and proof_origin describe exactly the implemented
coproduct-inclusion/subset-coordinate argument. The row lemma accounts for
the sign conversion, erase-cardinality arithmetic and degree transports;
the public proof uses he and the chain-map equation of e. Checked the source
[Stacks Tag 08D1](https://stacks.math.columbia.edu/tag/08D1), whose total
differential is d1 + (-1)^p d2. No node edit is needed.

Second reading changed only this report, adding the independent review.
No Lean repair was necessary; one original hole is closed and zero are added.
