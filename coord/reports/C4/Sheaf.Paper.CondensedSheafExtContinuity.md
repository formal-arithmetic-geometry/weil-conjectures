## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.ProEtale.isIso_constructible_condensed_sheaf_hom_colimit`
by a compiling induction on a finite distinguished extension tower. The existing
statement, universe parameters, visibility and public imports are unchanged.
The comparison remains the original `colimit.desc`, not a conjugate map supplied
by an arbitrary isomorphism.

The new categorical module proves that shifted additive Hom continuity for a
specified cocone is closed under distinguished extensions. It constructs the
natural comparison from the filtered-colimit Yoneda functor, proves that functor
homological using exact filtered colimits of abelian groups, and applies the
five lemma to a five-term window. Shift adjunction supplies the two outer terms.
These arguments contain no new holes and use Mathlib directly.

The new geometric tower module is also proved, from the one-step lemma. Its
well-founded induction is on closed subsets of the original noetherian scheme,
simultaneously for all closed immersions with image in that subset. A proper
closed immersion strictly reduces the support; exact closed pushforward maps
pieces and their extension towers using the single-functor and composition
isomorphisms. No bound on the Krull dimension is used.

Two geometric parts remain separately stated: the initial open/closed step,
and continuity for one locally closed locally finitely presented piece. These
are strictly different parts of the original argument. The tower proof was
initially another open part; it has been proved in this session rather than
handed on. Both new definitions are explicit predicates; neither chooses data
from an unproved existence theorem. No existing definition, target statement,
or other group's module was changed. No forced adaptations or change records.

All six delivered Lean modules compile together through `lcompile.py --all`.
The proved categorical closure theorem was separately checked with `#print axioms`:
its only axioms are `propext`, `Classical.choice` and `Quot.sound`.
`deliver3.py C4 Sheaf.Paper.CondensedSheafExtContinuity --no-push` passed compilation, axiom probing and preflight, with only the expected second reading left to the independent reader. Nothing was pushed.

## Proved and sorry left

Closed one existing hole:

- `AlgebraicGeometry.ProEtale.isIso_constructible_condensed_sheaf_hom_colimit`
  (`lem-weil-pbc-condensed-sheaf-ext-continuity`).

New proved public statements:

- `CategoryTheory.homColimitProperty_extensions`
  (`lem-weil-pbc-hom-colimit-extension`), proved directly from Mathlib and the
  existing proved additive-Yoneda shift adjunction.
- `AlgebraicGeometry.ProEtale.exists_condensedConstructible_extension_tower`
  (`lem-weil-pbc-condensed-constructible-extension-tower`), proved from the
  one-step statement, with all induction and pushforward glue completed.

Exactly two new holes remain, each a public theorem with source, complete
proof in words and a matching node:

- `AlgebraicGeometry.ProEtale.condensed_constructible_one_step`
  (`lem-weil-pbc-condensed-constructible-one-step`). What remains is to transport
  the presentations on a stratum to a nonempty open in its interior, using the
  coefficient-compatible equivalence for a surjective closed base change, then
  extract the first recollement triangle and compare its single objects in the
  ordinary derived category. The constructible pullback theorem is already
  proved. The topological choice of a nonempty stratum interior was checked in
  Lean using `dense_iUnion_interior_stratum`; that scratch check is not an unused
  declaration added to the library.
- `AlgebraicGeometry.ProEtale.condensed_local_piece_hom_continuity`
  (`lem-weil-pbc-condensed-local-piece-hom-continuity`). What remains is the
  locally finite free derived-Hom calculation and the closed costalk comparison.
  The existing locally-free Hom formula uses ringed-site modules rather than
  internal module objects. Its presentation/evaluation transport must be made
  explicit. Recollement is stated on bounded-below derived categories, and the
  qcqs continuity input uses canonical good-truncation cocones; functorial strict
  representatives, inclusion in the ordinary derived category, and comparison
  with the original termwise colimit are still required. The node and docstring
  specify these steps and the canonicality of the comparison maps.

This is a decomposition: one old hole closed, two lower holes added, net -1
before any pruning. It is not claimed as a proof without `sorryAx` of the
original geometric theorem. There is no `sorry` in the original item, either
new definition, any private helper, or the extension-tower proof.

Edge cases checked in the mathematical statements: the empty scheme is handled
by the first alternative of the one-step lemma; rank-zero presentations and the
zero module are allowed; a stratum's scheme structure is not identified with an
open subscheme without the closed-equivalence argument; no frontier condition
on the stratification is used. The generic extension theorem works for every
integer shift and arbitrary cocones, so it does not assume a derived colimit
exists. The geometric continuity statement retains the common termwise lower
bound and small filtered indexing category of the original statement.

## No longer needed

Removed these ten direct private imports from the item:

- `Mathlib.Algebra.Category.Grp.AB`
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.Algebra.Homology.LocallyFreeDerivedHom`
- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`
- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.Paper.CondensedOpenClosedRecollement`
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`

The first three are used by the proved categorical helper. The geometric
modules remain behind the new geometric obligations, directly or through the
existing recollement/continuity imports. Thus no existing Sheaf module is
claimed globally pruned. In particular, the old Hom-exactness, filtered-Ab-
exactness and five-lemma nodes are retained as Mathlib ingredients of the
categorical closure node, rather than made new obligations. The ringed-site
and resolution nodes remain dependencies of the geometric inputs.

The proof no longer requires a separate induction on derived Hom with
cohomologically bounded input at every closed support, nor an associativity or
octahedral reassociation lemma for extension towers: exact pushforward preserves
the fixed right-associated towers directly. These are omitted proof steps,
not deletions of existing nodes. No unused new helper is delivered.

Every old direct `proof_deps` entry removed from the target node is accounted for:

- `lem-pur-ringed-site-grothendieck-abelian` and
  `prop-pur-kinjective-resolutions-exist`: retained below the local-piece and recollement inputs.
- `lem-weil-pbc-ringed-site-locally-free-derived-hom`,
  `lem-weil-pbc-condensed-qcqs-pushforward-continuity`, and
  `lem-weil-pbc-condensed-lfp-local-triviality`: retained in local-piece continuity.
- `lem-weil-pbc-condensed-open-closed-recollement`: retained in both geometric obligations.
- `def-constructible-stratification`: retained in the one-step decomposition.
- `lem-weil-pbc-hom-out-of-triangle-exact`,
  `lem-weil-pbc-filtered-colimit-abelian-groups-exact`, and
  `lem-weil-pbc-five-lemma`: retained as proved Mathlib inputs of categorical extension closure.

These are removed direct edges, not globally pruned nodes.

## Where the brief, the DAG or earlier work was wrong

No counterexample to the item or the two new geometric statements was found.
The initial plan is mathematically usable but its listed declarations do not
compose directly at their current Lean interfaces. In particular, the module
presentations in the locally-free formula differ, and the recollement triangle
lives in the bounded-below category. These are remaining glue obligations,
recorded explicitly instead of silently treating the types as equal.

A dense open assembled from all strata is unnecessary for the one-step lemma:
one nonempty stratum interior suffices. The existing proved density theorem
supplies this topological fact. Well-founded induction is on closed supports,
not on dimension or the number of original strata. Different nilpotent stratum
structures still require the full-support closed-immersion equivalence.

The original paper/archive locations in the inherited source references are
not present in this checkout (WANTED for direct source rereading). The proof
refinements here follow the supplied node's expanded proof and the original
module docstring; new nodes mark their proof origin as agent refinement of
that source, without claiming a new direct PDF reading. Searches found no
existing theorem for these condensed pieces or for this specified-cocone
extension closure. LeanSearch returned its documented internal-server error;
actual LeanFinder, Loogle and text searches are recorded, not invented hits.

## New nodes

`def-weil-pbc-hom-colimit-property` is the explicit shifted Hom comparison
predicate in `Sheaf.CategoryTheory.HomColimitExtension`; it requires no colimit
of the diagram in the triangulated category itself.

`lem-weil-pbc-hom-colimit-extension` is the proved five-lemma closure statement
in the same module. Its proof dependencies are the Hom exact sequence,
filtered exactness for abelian groups, and the five lemma, all used through
Mathlib.

`def-weil-pbc-condensed-constructible-piece` is the explicit isomorphism class
of a degree-zero sheaf `i_*j_!P`, with closed `i`, quasi-compact open `j`, and
locally finitely presented `P`, in `Sheaf.Paper.CondensedConstructiblePiece`.

`lem-weil-pbc-condensed-constructible-one-step` is the remaining initial
open/closed triangle in `Sheaf.Paper.CondensedConstructibleOneStep`; its exact
closed-pushforward instance is included because the tower really uses it.

`lem-weil-pbc-condensed-constructible-extension-tower` is the proved finite
extension-tower theorem in `Sheaf.Paper.CondensedConstructibleExtensionTower`.
The original item uses its conclusion by ordinary induction on the tower.

`lem-weil-pbc-condensed-local-piece-hom-continuity` is the remaining local
geometric calculation in `Sheaf.Paper.CondensedLocalPieceHomContinuity`; it is
restricted to the pieces above and keeps the original diagram hypotheses.

The existing item's node changes only `proof`, `proof_deps` and `proof_origin`.
All seven node files describe the route actually taken. No blueprint unit or
its realized statements/steps was removed or bypassed.

## Second reading by C4

1. **Statements and signatures.** Compared the delivered target module with the repository
version byte for byte at every declaration header. The target theorem's hypotheses, universes,
conclusion and visibility are unchanged. The new declarations have the signatures recorded in
their nodes; no target statement or existing definition was changed. Verdict: pass.

2. **Proof and axioms.** Compiled all six delivered modules together with
`lcompile.py --all`; the build is clean. The target hole is closed by the explicit tower
reduction, and the categorical extension theorem and tower theorem have no `sorry`. The two
remaining `sorry`s are exactly the named public geometric theorems listed above, each with a
docstring and node. The axiom probe for the proved categorical theorem reports only
`propext`, `Classical.choice` and `Quot.sound`. An independent scratch `#print axioms`
check covered all seven public declarations: the definitions and categorical closure use
only those axioms; the two geometric holes, tower and target additionally use `sorryAx`
through the documented geometric obligations. No forbidden declaration form or hollow
definition occurs. Verdict: pass.

3. **New statements.** Checked the two definitions and four new theorem statements against
their node records and docstrings, including empty schemes, zero-rank pieces, arbitrary shifts,
common lower bounds, and the exact cocone comparison. The two split geometric statements are
strictly smaller than the original target and are needed by the tower reduction; they are not
restatements of the target. Searches and their no-match verdicts are recorded in the node files.
Verdict: pass.

4. **Imports and pruning.** Compared imports with the proof actually elaborated. The target
module keeps only public interface imports and imports the two geometric reduction modules;
private geometric imports removed from it are retained behind the local-piece obligations. The
removed imports and the fact that no existing Sheaf module is globally pruned are listed under
`## No longer needed`. Verdict: pass after adding the missing proof-dependency imports.

5. **DAG and unit route.** Checked `proof`, `proof_deps` and `proof_origin` for the target and
new nodes against the Lean proof. The extension closure uses the Hom exactness, filtered
abelian-colimit exactness and five-lemma inputs; the tower uses the one-step theorem, exact
closed pushforward and the piece definition. Missing density, exactness and resolution
references were repaired in the new nodes. The unit `sk-thm-properbasechange` and its
realized route are untouched. Verdict: pass.

Second-reading changes: added the existing generic-constancy node's recorded topological
stratum-interior density theorem to the one-step proof dependency list and its private import.
Added the exact-filtered-colimit and functorial-resolution dependencies explicitly to the local
piece node and its private imports. Completed the list of old direct proof dependencies under `## No longer needed`.
No Lean statement or proof body was changed. Independent LeanFinder and Loogle searches used
restriction/open-stratum, homological-Yoneda and preservation terminology; they returned generic
ingredients, not either of the two condensed geometric theorems. Repository searches included
compactness, constructible triangles and closed pushforward exactness.
