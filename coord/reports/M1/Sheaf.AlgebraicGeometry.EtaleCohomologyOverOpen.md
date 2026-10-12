## What changed

Marked `AlgebraicGeometry.etaleCohomologyOverOpen` as STATEMENT-DISPUTED at its
existing declaration. Its signature and its existing `sorry` are unchanged.
Added the proved private lemma
`etaleCohomologyOverOpen_degreeZero_obstruction`, which transports a proposed
cohomology equivalence through Mathlib's two `Sheaf.H.equiv₀` equivalences and
shows that it would force nontrivial global sections to be subsingleton.
No definitions, targets, imports, or DAG routes changed.

This is a disputed-statement delivery, not a proof or a decomposition of the
assigned theorem. No false intermediate assertion has been introduced to make
its proof compile.

## Proved and sorry left

Holes closed: none (0 of 1).
Holes added: none (0 split off).
The existing hole remains in `AlgebraicGeometry.etaleCohomologyOverOpen`
(node `lem-weil-pbc-etale-cohomology-over-open`).
The new private degree-zero obstruction is completely proved, with no `sorry`.
It does not count as closing the assigned hole.

## No longer needed

None. All existing imports are preserved pending repair of the statement; none
is claimed pruned. The unit `sk-prop-cd` and its route are unchanged.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: The existing Lean declaration has `Sheaf.H G q` on the left,
which means GLOBAL cohomology of X, rather than cohomology over the open object
j : U → X. This is not the natural-language statement of its DAG node.

Counterexample: q = 0, X = Spec(k) for an algebraically closed field k,
U the empty open subscheme, and G the constant integer sheaf (in the prescribed
universe, using ULift). The inclusion is an open immersion and is étale.
The Ext hypotheses can be supplied by the standard Ext instances. The left
cohomology group is Z and the right cohomology group is the zero group: sections
on a nonempty connected point are Z, whereas the empty covering forces every
abelian sheaf's sections on the empty scheme to be terminal. These groups
cannot be additively equivalent. The compiled private lemma formalizes the
obstruction from the two section-group facts via `Sheaf.H.equiv₀`.
This issue persists for a nonempty proper open: on a disjoint union of two
algebraically closed points, take U one component and the constant integer
sheaf; degree-zero groups are Z × Z and Z.

Mathlib `CategoryTheory/Sites/SheafCohomology/Basic.lean` defines `Sheaf.H`
as Ext from the constant integer sheaf, and `Sheaf.H' G q W` as the evaluation
of the cohomology presheaf at W. The existing theorem
`CategoryTheory.cohomology_over_object_localization` explicitly starts with
`Sheaf.H' F q W`. The DAG's step 3 accordingly starts with H^q(U,G), not
H^q(X,G). The site's equivalence in step 1 and restriction formula in step 2
cannot replace these different left sides. No true reduction of the current
statement exists.

A repair should start with `Sheaf.H' G q (Scheme.Etale.mk j)` on the left,
using its underlying additive group, and compare it to global cohomology of
the restricted sheaf on U. It must also restore the naturality and
quasi-coherent clauses mentioned in the DAG and docstring, but absent from
the existing Lean signature. This report is not proposing a weaker version
of the false assertion as a proof; it records the mismatch for a coordinated
statement repair under stage 3 section 3. The only direct importer found is
`Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison`; it currently mentions this
lemma in its proof docstring and leaves its theorem as `sorry`, with no Lean
application of the disputed declaration. Its affine-local argument needs
cohomology over U, exactly the DAG formulation.

Searches: LeanFinder query "cohomology over an object of a site equals
cohomology of the restricted sheaf on the localized site" found
`Sheaf.cohomologyPresheaf`, `Sheaf.cohomologyPresheafFunctor`, and `Sheaf.H`;
Loogle query "CategoryTheory.Sheaf.H.equiv₀" found the degree-zero equivalence
and its naturality lemmas. Ripgrep inspected these definitions and the
localization theorem, the existing `Scheme.Etale.overEquiv` and
`overSheafEquiv`, and every occurrence of `etaleCohomologyOverOpen` in the
library. No theorem identifies global cohomology with arbitrary open
restriction, as the counterexample rules out.

Validation: the unchanged public signature plus the proved private obstruction
compile through `lcompile.py`. The delivery dry run is the final gate.

## Second reading by M1

1. I diffed the delivered module against `sheaf-dag`; the public theorem signature and all
existing declarations are byte-for-byte unchanged. Verdict: pass.
2. I compiled the module with `lcompile.py` and appended an axiom probe. The private
obstruction compiles and uses only the permitted axioms; the sole remaining `sorry` is
the named public theorem. Verdict: pass.
3. I checked the disputed assertion against `Sheaf.H` and `Sheaf.H'` in Mathlib. `Sheaf.H`
is global cohomology, while the DAG statement requires evaluation over the open object;
the degree-zero obstruction demonstrates the mismatch. Verdict: statement disputed with
a concrete degree-zero counterexample, not a weakened proof.
4. I checked the imported declarations and the node's proof route. No import can prove the
current global-to-restricted equivalence, and no import was pruned because all are retained
for the pending repair and unit route. Verdict: pass pending statement repair.
5. I checked the unit record and report against the Lean change. The unit route is untouched;
no new node or split-off theorem was added. Verdict: pass.

Changed in this second reading: added this review record only. The existing declaration is
marked `STATEMENT-DISPUTED` with the counterexample already documented above; no target or
DAG statement was altered.
