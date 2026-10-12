## What changed

Marked `AlgebraicGeometry.Scheme.module_sections_surjective_of_cech_h1_vanishing`
STATEMENT-DISPUTED without changing its signature or its original proof placeholder.
Added two fully proved private diagnostic lemmas in the item module:
`empty_family_cofinal` and `empty_family_cech_isZero`. The only added import is the
proof-only `Mathlib.Algebra.Category.Grp.Zero`.

## Proved and sorry left

Closed 0 of the item's 1 holes; added 0 holes. The original hole remains in
`AlgebraicGeometry.Scheme.module_sections_surjective_of_cech_h1_vanishing`
(node `lem-weil-pbc-module-ses-cech-h1-surjective`).

Both private diagnostic lemmas are proved without sorry. They verify, uniformly
in the scheme and open, that the predicate `Cov I V hV := IsEmpty I` satisfies
cofinality and that every selected family's degree-one cohomology is zero. The
empty-family complex has a subsingleton group in every degree; exactness at degree
one and zero homology follow from Mathlib. These are diagnostics, not a claimed
proof or decomposition of the false statement.

## No longer needed

None. No existing imports, nodes, or modules are pruned. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the Lean signature omits the requirement that the families
selected by `Cov` cover `U`. Its `hcofinal` conclusion asserts membership and
containment in the old cover, but not that the selected family covers `U`.
Consequently one can always select the empty family, and its Cech cohomology
vanishes for any sheaf. The checked private lemmas certify this failure of the
hypotheses. The DAG's natural-language statement correctly requires coverings;
the Lean signature does not encode that condition.

Concrete mathematical counterexample: take `X = P^1_k` for any nonzero field k
and `U = top`. The homogeneous coordinates x and y define the Koszul sequence
`0 -> O(-2) -> O(-1) direct-sum O(-1) -> O -> 0`, with maps `(-y,x)` and `(x,y)`.
On D(x) and D(y) one coordinate is invertible, so this sequence is short exact.
However `Gamma(P^1_k,O(-1)) = 0`, whereas `Gamma(P^1_k,O) = k`; hence the last
map on sections is not surjective. Choose the index universe large enough for
all opens, and `Cov := IsEmpty I`: both Lean hypotheses hold by the diagnostic
lemmas, including the quantification over all choices of SiteCechComplex.

The required repair is to ensure Cov members really cover U (for example a
separate `hcover` hypothesis, as in SiteSesCechH1Surjective), or to add coverage
to the family returned by `hcofinal`. This delivery deliberately leaves the
statement unchanged; an adaptation of its callers belongs in a reviewed repair.
Also review the independent index-universe parameter v: the usual local-lift
cover is indexed by points in universe u, while this signature permits v smaller
than u. The counterexample above already applies with v = u, so it does not
rely on that additional universe concern.

Searches: the source library's TopCat.Presheaf criterion requires a finite
covering refinement (with equality of its union to U), which this signature
cannot supply. The general SiteSesCechH1Surjective declaration explicitly has
hcover. LeanFinder found local-surjectivity and stalk lemmas, and Loogle found
only Mathlib's Cech functor definition; neither repairs the omitted hypothesis.

Compilation uses lcompile.py only. The dry-run result is recorded by the worker's
final READY line; no delivery is pushed by this worker.


## Second reading by M3

1. **Unchanged public contract: PASS.** Compared the whole module by `diff` with
   the repository version, then checked programmatically that the original theorem
   from its `theorem` keyword through the end of the file is byte-for-byte identical.
   No existing signature, definition, public import, or proof placeholder changed.
   The additions are two private diagnostic theorems, one proof-only import, and
   the disputed-statement comment. No change record is needed.
2. **Compilation and axioms: PASS for the diagnostics; original item OPEN.**
   `lcompile.py` compiled the module without errors or warnings. A scratch copy's
   `#print axioms` checks show only `propext`, `Classical.choice`, and `Quot.sound`
   for both `empty_family_cofinal` and `empty_family_cech_isZero`. The original
   `module_sections_surjective_of_cech_h1_vanishing` additionally uses `sorryAx`,
   as reported. There is exactly one original named theorem hole and no new hole,
   definition, forbidden declaration, or arbitrary witness chosen from an unproved
   existence theorem.
3. **Split statements and edge cases: PASS, none split off.** The private helpers
   are proved diagnostics, not dependencies used to disguise a proof of the item.
   The first explicitly selects `PEmpty` for every covering, including the empty
   open. In the second, a tuple `Fin 2 → I` would supply an impossible element
   `t 0`; hence degree-one cochains are a subsingleton, exact there, and have zero
   homology. This works for every permitted complex and every module sheaf.
   Independently searched `lean/` and Mathlib using `IsEmpty`, `cochains`,
   `isZero_of_subsingleton`, and section-surjectivity/refinement terms; the helper
   uses the existing Mathlib zero-object and exactness lemmas directly. No new
   unproved lemma or duplicated public API was introduced. The projective-line
   Koszul example in the report is a mathematical counterexample, not a claimed
   formal Lean refutation; its local exactness and failure of section-surjectivity
   agree with the omitted coverage condition.
4. **Route and pruning: PASS for this diagnostic delivery.** Read the original
   node's six-step local-lift/cocycle/gluing plan and the site analogue. The latter
   explicitly requires `hcover`; it cannot prove the unchanged signature here.
   A proof of the false signature cannot be supplied by a shorter sound route.
   No original proof dependency is claimed obsolete: the original theorem is
   still open and its dependency imports remain its intended repair plan.
   The added `Grp.Zero` import is proof-only and used. `## No longer needed` is
   complete (none), and `dag/units/sk-thm-p1.json`'s `realized` route is unchanged.
5. **DAG agreement: PASS as an unchanged open plan, not a completed proof.**
   The existing node retains its statement, proof steps, `proof_deps`, and
   `proof_origin`; no replacement proof or split node is claimed. Its natural
   language correctly says coverings, whereas the unchanged Lean signature does
   not. The dispute and the required coverage/universe review are reported above
   for a subsequent coordinated statement repair. No DAG files are delivered.

Second-reading changes: clarified the Lean comment from “vacuous” to “automatic”
(the cohomology hypothesis is actually proved for the empty family), and added
this independent review with explicit axiom results. No mathematical proof was
rewritten. Verified accounting: 0 of 1 original holes closed, 0 holes added,
0 statements split off, no imports or modules pruned.
