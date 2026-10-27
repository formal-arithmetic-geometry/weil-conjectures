## Worker report

Item: lem-weil-pbc-ordinary-finite-evaluation-transition. Group Q19, stage 1,
2026-10-22. Direct delivery with self-review; no second worker was started.

Files written: dag/nodes/sec-proper-base-change/lem-weil-pbc-ordinary-finite-evaluation-transition.json
(the existing statement, seven-step proof, complete proof dependencies, blueprint
reference and split report), citations.json (26 verbatim statement extracts), and
this report. searches.jsonl records the actual search-command results.

## New nodes

None. Zero Mathlib leaves. The two comparisons are proved in the item rather than
moved into new nodes that repeat its clauses. Scalar cancellation, local quotient
lifting and the generator computations are explicit steps. All seven steps have
fewer than 2000 characters.

Attachments: none. Searches in lean/WeilConjectures for the exact blueprint tag,
completedReductionOrdinaryComparison, completedReductionOrdinaryTransition, and
ordinary finite evaluation/quotient-transition terminology did not find an exact
project declaration of the item. The named constructions and their existence
proofs are in lean/Sheaf/Paper/CompletedPullbackReduction.lean, notably lines
638-648 and 1477-1501; these are not eligible WeilConjectures attachments under
this brief. I read their normalization and generator arguments without compiling.

WANTED: none.

No statement correction or STATEMENT-DISPUTED issue was found. The original
statement, all four statement dependencies, inherited source and blueprint origin,
and earlier Mathlib searches are retained. The original item had no proof. Its
reference to Stacks 099N gives context for derived completed pullback, but does
not itself prove the ordinary comparison's existence, generator normalization or
uniqueness. The present proof supplies those arguments explicitly. It does not
infer an ordinary comparison from a derived isomorphism.

## Searches and reuse

I searched the whole DAG for ordinary finite evaluation, quotient-unit,
profinite-coefficient-inverse-image, local tensor generators, and ordinary
restriction/pullback statements. I read the statements of the candidate
ring-restriction-square, independent inverse-image tensor comparison, scalar tower
comparison and finite ramified pullback nodes. The restriction-square result is
about a cartesian geometric square; the ramified nodes require ell-adic field
coefficients. Neither was substituted for the general Noetherian-adic assertion.
The general inverse-image tensor theorem is unnecessary: both sides here reduce
to the very same inverse image of the already-formed quotient module.

Whole-blueprint searches with tools/blueprint_refs.py for 'scalar extension',
'finite evaluation', 'ordinary finite', 'restriction pullback', and 'inverse image
tensor' found no node stating this full normalized ordinary assertion. The
ancestor query gives lemma-weil-pbc-completed-pullback-reduction. The item's
existing exact paragraph-2 origin is retained, and same_as is empty. The chapter
and unit records were read and retained. This is the ordinary scalar calculation
inside the prescribed finite-reduction route, without a change to any unit.

Mathlib searches used msearch.py exclusively. The inherited searches were kept.
The new log includes Loogle on SheafOfModules.pullback and
SheafOfModules.restrictScalars, semantic searches using both inverse-image/scalar
extension and quotient-coefficient formulations, and source searches for
pullback/restrictScalars and sheafificationCompPullback/pullbackPushforwardAdjunction.
I read the hits: SheafOfModules.pullbackPushforwardAdjunction and
sheafificationCompPullback in PullbackContinuous.lean (lines 60 and 118), and the
free-pullback context in PullbackFree.lean. They provide ordinary ingredients;
none states the two uniquely normalized comparisons for these coefficient
sheaves. The second semantic phrasing also returned ordinary module quotient
TensorProduct equivalences, not this sheaf/strict-tower assertion. A repeated
semantic query appears twice in the execution log; its identical answer was read
and is represented once in the node's search list. No search was invented and no
service failure was classified as an absence result.

## Not duplicates

No new node was created, so there are no new/existing-node pairs to distinguish.
The existing profinite coefficient inverse-image theorem and local
sheafification theorem supply exactly the nontrivial facts required.

## Review by Q19

I read the current main-20261015 blueprint proof of
lemma-weil-pbc-completed-pullback-reduction, especially paragraph 2, and compared
the item with the actual ordinary interfaces in CompletedPullbackReduction.lean.
I also read Stacks proetale.tex Tag 099N (lemma-pushforward-Noetherian-case),
including clause (5) and its proof; sites-modules.tex Tag 03EK
(section-tensor-product) and Tag 03D7
(lemma-adjoint-pullback-pushforward-modules); and sites.tex Tag 00WK
(lemma-sections-sheafification). The blueprint's derived tensor sentence is not
used to skip an ordinary normalization argument. No SGA source is used.

For step 1 I opened lem-weil-pbc-profinite-coefficient-inverse-image. Its statement
really supplies BOTH ring isomorphisms and BOTH projection/quotient equations.
The hypotheses hold: the item uses a countable tower of finite commutative rings
P_n with unital quotient maps and an arbitrary scheme map. I opened the adic
coefficient and completed pullback definitions to check that the limit and its
structural map are precisely those of this lemma. I do not assume that inverse
image generally preserves arbitrary inverse limits.

For step 2 I read the cited adic datum, completed pullback, tensor-product, and
module-sheafification statements. They give strict levelwise evaluation, the
actual inverse-image-then-scalar-extension model, and the universal extension
of a presheaf-linear map to its sheafification. Cancellation of extension along
a ring isomorphism is proved here by the two explicit multiplication/insertion
formulas. Both compositions are checked by the balancing relation. Projection
compatibility from step 1 checks the B_T' action on H_n; it is not an unproved
comparison of unrelated coefficient structures.

For step 3 the cited tensor and module-sheafification definitions justify passage
of the formulas to sheaves, and the inverse-image definition specifies the unit
and its functor on module maps. Multiplication followed by insertion gives the
normalization with pi(b), and naturality is checked on b tensor x. No claim that
all sheaf-tensor sections are globally pure tensors is made.

For step 4 I opened the entire local-sheafification statement and the constant
sheaf definition. The former actually gives local representatives. The profinite
coefficient lemma explicitly identifies the finite coefficient construction with
the constant sheaf. A representative in A/I^n lifts to A, whose reductions at ALL
levels form the required section of the specified limit. This proves local
surjectivity without demanding a global lift of every sheaf section. It uses no
flatness and no module finite generation.

For step 5 I checked that the normalization in the item only tests the quotient
unit 1 tensor m. This is weaker than specifying every z tensor m; I filled that
gap by the local lift r of step 4 and the equation
z tensor m = 1 tensor rm. The inverse-image definition supplies colimit
coprojections indexed by every arrow U to g*V; the module sheafification statement
supplies uniqueness after sheafification. These are exactly the universal
properties used to pass from the tested generators to equality of morphisms.
Base change sends the covering on V to a covering by the inverse-image site's
specified construction, and a target sheaf detects equality on that covering.
Thus no source statement about fully faithful Yoneda or mere existence of
sheafification is being used in place of a section/generator theorem.

For step 6 the adic datum supplies pi_a=q pi_b. The tensor definition and module
sheafification statement give the map induced by the explicitly checked balanced
formula. The inverse-image definition supplies its image as a map of modules;
the ring equation of step 1 checks its changed action. Restriction of scalars is
the same underlying abelian sheaf by the cited definition, which is why the
conjugation by v_b and v_a has the displayed restricted target. Naturality is
checked on z tensor h(m). This is an ordinary map, with no illicit use of a
scalar-extension exactness theorem.

For step 7 I verified the coefficient equation before simplifying the tensor.
The inner coefficient q(z) and outer coefficient q(s) both occur; the argument
never replaces them by a vague transition-compatibility claim. Tensor,
inverse-image colimit, and sheafification universal properties prove uniqueness
from all (s,z,m) generators. I opened def-cbc-completed-reduction-finite-interfaces:
it specifies these same generators and the unique transition, but I use it only
to identify the named fixed constructions after existence and uniqueness were
proved. That definition is not cited as a theorem establishing existence.

Small cases: M=0 gives zero maps; g=id gives the quotient-identity multiplication
comparison and the ordinary quotient map; a=b makes theta and the transition
identities. If I=0 and A is finite, every coefficient is the same constant sheaf
and the cancellation formulas still apply. If I=A, all P_n and completed rings
are zero and their module categories have only zero modules, with the same
formulas. Empty schemes cause no nonemptiness requirement. Nonflat modules are
allowed because only ring-isomorphism cancellation, balanced tensor maps and
sheafification are used. The positive-index restriction is retained; the Lean
natural index convention represents n by n-1, with no extra exponent-zero case.

I checked delivery-errors B-E against these files. There are no statement-only
new nodes, duplicate nodes, circular replacement clauses, unstated coefficient
changes or added module hypotheses. Every dependency in every step has a
substantive verbatim statement quotation in citations.json. The only supplied
non-elementary coefficient identification remains an explicit cited theorem;
local lifting, multiplication cancellation, normalization, and transition
formulas have their arguments in the item. There were no returned numbered
points to repair and no unfinished mathematical work.
