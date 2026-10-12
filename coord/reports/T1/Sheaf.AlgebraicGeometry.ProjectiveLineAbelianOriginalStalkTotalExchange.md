## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange` by a complete
Lean assembly. ProjectiveSpace.isPullback_map supplies both local squares. The new
qcqs localization lemma supplies c₁,c₂ and their exchange compatibility. The existing
`Etale.exists_addEquiv_strictLocal_abelian_total_exchange` supplies b₁,b₂ and its
cohomology compatibility. The witnesses are c₁.trans b₁ and c₂.trans b₂; rewriting the
first equation and applying the second proves the requested equation.

The new intermediate is strictly the localization part: its input morphism is an
arbitrary qcqs morphism, and its conclusion compares two stalk exchanges. It mentions
neither Sheaf.H nor cohomologyMap and does not assert the local exchange is invertible.
The separate existing strict-local theorem performs the Ext cohomology identification.
No definition or existing statement changed. New imports are proof-only.

Both sandbox modules compiled together without warnings through lcompile.py.
Sources read online: [03Q9](https://stacks.math.columbia.edu/tag/03Q9),
[03QO](https://stacks.math.columbia.edu/tag/03QO), and the total-space restriction portion
of [095T](https://stacks.math.columbia.edu/tag/095T). The proof never invokes proper
base change, torsion, closed-fibre cohomology or curve invariance.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange`.
Its proof body contains no sorry. Added hole:
`AlgebraicGeometry.Etale.exists_addEquiv_strictHenselization_abelian_stalkExchange`.
This is a decomposition: one hole closed, one added, net zero; it is not an
axiom-free closure.

One new sorry remains:
`AlgebraicGeometry.Etale.exists_addEquiv_strictHenselization_abelian_stalkExchange`,
node `lem-weil-pbc-abelian-stalk-exchange-localization`, in
`Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization`.
Its signature, docstring and DAG node specify the full localization and coherence
argument. The existing strict-local abelian exchange theorem is already proved from
its named derived-global and Ext-comparison dependencies; their remaining proofs are
not copied or changed by this delivery.

Edge cases checked for the new lemma: q=0 is ordinary section/germ restriction;
the zero sheaf gives zero groups; separably closed field extensions can be inseparable
because etale fibres have finite separable residue extensions; arbitrary cartesian
models are transported by the unique pullback isomorphism. Only qcqs is required,
as in 03Q9. Locality and the explicit residue square are retained, so the marked
closed point and the exchange comparisons remain compatible.

## No longer needed

Removed these four direct proof imports from the item:
- `Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`;
- `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`;
- `Sheaf.Paper.InverseImageStalkGerm`;
- `Sheaf.Paper.StrictHenselizationFunctoriality`.

All four are retained by the new localization lemma's proof plan. Their nodes are
therefore not globally pruned. The original cohomology-pullback dependency is supplied
through the existing strict-local abelian exchange theorem. No node or module is
claimed to leave the targets' closure. All original public statement imports stay.
For completeness, all six old direct proof_deps leave the item's direct proof list:
`def-nagata-projective-space-base-change` remains a statement dependency and its
pullback lemma is now an explicit proof dependency;
`def-weil-pbc-cohomology-pullback` remains a statement dependency and is used through
the existing strict-local comparison;
`lem-weil-pbc-derived-exchange-termwise`, `lem-weil-pbc-inverse-image-stalk-germ`,
`lem-weil-pbc-strict-henselization-functoriality`, and
`lem-weil-pbc-unrestricted-strict-henselization-stalk` move under the new localization
node. Thus global pruning is none.

The unit sk-thm-p1 and its realized nodes are unchanged; this is below-unit factoring
of the same original-stalk/total-space argument.

## Where the brief, the DAG or earlier work was wrong

The original plan names the separate stalk formula and termwise mate but provides no
Lean interface for their compatibility after both chosen local-model transports.
The localization theorem makes that missing geometric bridge a separate item.
The existing strict-local abelian total-exchange theorem already handles the final
Ext identification, so that part need not be repeated.

The local literature checkout contains citation lists but no etale-cohomology.tex;
the exact Stacks tags were read online. LeanSearch returned Internal Server Error,
recorded as unavailable. LeanFinder, Loogle and Mathlib grep ran successfully but
returned no exact match. Searching the whole DAG found the analogous module-valued
projective-line comparison, which imports this item through the original-stalk theorem;
using it here would be circular. The new statement is the arbitrary-qcqs abelian
localization interface, not a second projective-line or module-coefficient theorem.

## New nodes

`lem-weil-pbc-abelian-stalk-exchange-localization` in sec-proper-base-change, unit
sk-thm-p1, states the qcqs localization of the abelian exchange between compatible
strict henselizations and arbitrary cartesian local models. Its module is
`Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization`.
Its four proof steps record point extension, 03Q9 total-space restriction, exact
closed-point sections, and compatibility of the termwise mates. The item node's
proof and proof_deps now match the complete Lean assembly. No change record is needed.


## Second reading by T1

1. PASS: compared the delivered item against the repository using diff and a
byte-for-byte assertion on the entire theorem signature before `:= by`.
No existing statement or definition changes; all original public imports remain.
The new imports are proof-only. The other module and its node are new.
2. PASS with the declared open dependency: both modules compile without warnings
through lcompile.py in dependency order (5.2 and 11.5 seconds). The item has no
sorry; the new public named theorem has exactly one whole-proof sorry. No forbidden
axiom, unsafe, opaque, extern, implemented_by or kernel bypass appears. A scratch
copy with #print axioms for both declarations reports only propext, Classical.choice,
Quot.sound and sorryAx. Consequently this delivery is a decomposition, not closure.
3. PASS: read both signatures and the four-step localization proof against
[03Q9](https://stacks.math.columbia.edu/tag/03Q9),
[03QO](https://stacks.math.columbia.edu/tag/03QO), and the total-space part of
[095T](https://stacks.math.columbia.edu/tag/095T). The general qcqs statement isolates
localization and its exchange coherence; the separate existing comparison handles
Ext cohomology. It does not merely rename the original projective-line conclusion.
Checked q=0 (restriction of sections), the zero sheaf, identity squares, extension of
separably closed fields including inseparable extensions, and arbitrary pullback
models. hphi and hrho ensure equality of the structural and marked residue maps;
pointed etale lift uniqueness supplies the needed coherence. The new node and
source-bearing proof docstring match. Independent searches with LeanFinder
("naturality of higher direct image stalk formula under change of pointed scheme"),
Loogle ("baseChange", "stalk"), Mathlib grep, and rg across both Lean roots found
no replacement: hits concern structure-sheaf/topological stalks or ring stalks.
The existing module-valued projective-line results depend on this item and would be
circular. Closing this compatibility theorem requires substantial formal work;
no small remaining lemma was available to close in a few minutes.
4. PASS: the assembly uses the already-proved strict-local abelian total-exchange
comparison, both ProjectiveSpace.isPullback_map squares, and the new localization
lemma. All remaining proof imports serve those proofs or the new lemma's recorded
plan; public imports supply the unchanged interfaces. Reviewed sk-thm-p1.realized:
this below-unit factoring retains the strict-local and geometric-stalk route and
does not replace any curve calculation, closed-fibre comparison or unit step.
The pruning section now lists every old proof dependency, distinguishing removal
from the direct list from global pruning (none).
5. PASS: both nodes' proof_deps equal the union of uses in their proof steps; every
referenced node exists. The item's three steps match its Lean assembly and the
new node's four steps match the unresolved localization argument. Source,
proof_origin, creation, blueprint ancestry, unit/chapter, searches and Lean records
are present. No change record is required because no existing signature or
definition changed.

Second reading changes: clarified the one-for-one decomposition accounting and
completed the old direct-dependency audit in this report. The Lean assembly and
new localization statement needed no repair.
