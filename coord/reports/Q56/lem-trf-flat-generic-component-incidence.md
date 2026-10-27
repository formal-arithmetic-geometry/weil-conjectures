# Worker report: lem-trf-flat-generic-component-incidence

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flat-generic-component-incidence.json`: existing statement, now split into four proof steps; no exact Mathlib match. Its statement, statement dependencies, inherited blueprint ancestry and earlier searches are retained.
- `citations.json`: a verbatim statement quote for each node used in each step.
- `searches.jsonl`: the search command's own records, used to append the five searches actually run this turn.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. All proof ingredients already have Mathlib-leaf nodes.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for flat/generalizing/generic-component terminology. There is no declaration stating all clauses of this item. In particular the private `generic_nonempty` in `ConnectedGenericFibreTrait.lean` only constructs a generic-fibre point over a domain, and neither chooses a generic-fibre component nor proves maximality in its closure fibre. Existing Mathlib declarations supply ingredients rather than a one-line specialization of the whole item. No Lean file was written or compiled.

## Wanted literature

None. All the sources used are available locally.

## Findings and corrections

The item was unsplit and had no previous sandbox copy or report. No released repair note exists. The statement is unchanged and is true without local finite type, Noetherianity or equidimensionality. The Stacks remark 0GSK lists equidimensionality criteria and expressly defers details: it does not itself contain a proof of this incidence assertion. Accordingly the assembly proof is honestly marked agent-written, with the precise existing Stacks ingredients cited.

The source's affine going-down route is used in its scheme form, Tag 03HV, whose proof reduces to algebraic going down. This avoids creating a duplicate of the existing `lem-weil-pbc-flat-generalizations-lift`. The direction of specialization is made explicit as membership in a singleton closure; the existing node's wording “v specializing to f(t)” means v specializes *to* f(t), rather than the reverse.

Read the chapter and unit records and the current main-20261015 locality statement, proof and unit statement. This auxiliary lemma belongs to the inherited nearby-cycle/flatification branch recorded in its blueprint ancestry; the current locality proof does not directly state it. No chapter or unit route is changed. Blueprint searches for generic components, fibre components, generalizing, sober, flat morphism and irreducible component found no blueprint statement of the full item. Existing DAG searches found all of its needed ingredients. No new node is introduced, so no new-node duplicate pair requires a distinction.

## Unfinished work

None within stage 1. The split is an argument from existing Mathlib leaves; it is not a Lean proof delivery.

## Review by Q56

I read Stacks `more-morphisms.tex`, Tag 0GSK (`remark-flat-equidimensional`), especially its second list and its warning that proofs are deferred. I read the actual lifting lemma in `morphisms.tex`, Tag 03HV (`lemma-generalizations-lift-flat`), and algebraic Tag 00HS (`lemma-flat-going-down`), including its proof by localization and faithful flatness. I also read `schemes.tex` Tags 01K1 (`lemma-fibre-topological`) and 01IS (`lemma-scheme-sober`), and `topology.tex` Tags 004V, 004W (`lemma-irreducible`) and the generic-point definition 004X. There are no new nodes requiring additional sources. The four steps are all under 2000 characters.

Step 1 uses exactly the statements of `def-pc-scheme-fibre`, `def-weil-irreducible-components` and `lem-sc-scheme-sober`, all opened and read. The fibre node expressly supplies the homeomorphism onto the set-theoretic fibre, the component definition expressly says components are closed, and scheme sobriety supplies a generic point of this closed irreducible C. The scheme to which sobriety is applied is X_s, not the possibly non-locally-closed image of that fibre in X. After establishing existence, the proof fixes an arbitrary generic point, preserving the item's “for every such x” quantifier.

Step 2 uses the opened statements of `def-sc-generic-point`, `lem-weil-pbc-flat-generalizations-lift` and `def-pc-scheme-fibre`. Being generic in S gives s in closure{eta}; the lifting statement requires only flatness, which the item assumes, and supplies y with image eta and x in closure{y}. I checked the direction against `Flat.generalizingMap` at Mathlib `UniversallyOpen.lean:134` and `GeneralizingMap` at `Inseparable.lean:359`. No local finite presentation is required. The fibre homeomorphism then gives a point y_eta of the actual scheme-theoretic generic fibre. This is the one nontrivial flatness input, cited as a theorem rather than inferred from the flatness definition.

Step 3 uses the opened `lem-sc-irreducible-components-cover` statement, specifically its assertion that every point belongs to an irreducible component, with no finiteness assumptions. It uses `lem-sc-scheme-sober` on that component of the scheme X_eta and `def-pc-scheme-fibre` to pass from the intrinsic closure in the fibre to the ambient singleton closure. I checked that these nodes say those facts, rather than borrowing a construction from their proofs. The closure-in-a-subspace formula gives y in the ambient closure of z; that closed set then contains closure{y}, hence x. This is ordinary closure monotonicity, written explicitly.

Step 4 is the elementary intermediate-subspace maximality argument. Its cited statements are the fibre homeomorphism and the definition of an irreducible component as a maximal irreducible subset. The closed subspace Z intersect f^{-1}(s) contains x, hence contains C. An irreducible larger subset in that intermediate subspace is still irreducible in f^{-1}(s), since the topology induced on that subset is identical. The maximality of C in the whole fibre therefore forces equality. Crucially, the proof does not claim that Z_s is irreducible: its components may be numerous, and only the specified C is a component of it. No separate node is needed for this two-inclusion argument from the definitions.

For C1 and C4 I checked every uses entry against the complete cited statement and copied those statements verbatim into `citations.json`. No proof invokes an uncited non-elementary comparison or a definition node in place of a flatness theorem. For B and D I checked that there is no new statement-only restatement of the item or one of its clauses; there are no new nodes at all. All dependencies are existing Mathlib leaves, so off-unit citations are generic tools and do not require a new tool-use declaration. The argument uses no SGA source.

I tested the hypotheses and conclusions on empty X or an empty special fibre (no C, hence vacuous), s=eta (the argument allows a component containing the chosen point), the identity morphism of an integral scheme, a disjoint union with an empty component fibre, nonreduced flat fibres (sobriety is valid for every scheme), and the reducible special fibre xy=t over a field polynomial ring (both special components may come from the same generic component). The proof also works for arbitrary non-Noetherian integral bases and infinitely many components: the component-cover and sobriety statements have no finiteness hypothesis. Nothing requires quasi-compactness or closedness of the fibre inclusion in X.

I read all hits of the five new logged searches, including the second LeanFinder phrasing. They give generalization lifting, scheme fibre topology and generic-point tools, not the combined incidence/maximality assertion. I read the relevant Mathlib sources for the promising hits. Searches already stored in the live item remain intact. No search that failed or was not run is represented as a successful search.

## Validation

The required `deliver.py Q56 lem-trf-flat-generic-component-incidence --no-push` exited successfully: `OK (not pushed)` at `0db094ed07f`, with server preflight passed. This includes the DAG and split checks. All 11 citation pairs have verbatim quotes, the statement is unchanged, and all four proof steps are below 2000 characters. The final push runs the delivery validation again.
