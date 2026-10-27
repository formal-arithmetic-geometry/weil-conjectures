## What changed

`Sheaf.Paper.WeilCompactSupportCohomology` now proves
`WeilConjectures.zlWeilHigherShriek_representable` by composing open-extension
representability with proper higher-image representability. It proves
`WeilConjectures.zlWeilHigherShriek_compactification_independent` using the
already proved upstream common-refinement construction, proper/open interchange
along each refinement, the chosen representation isomorphisms, and full
faithfulness of `zlWeilIndEmbedding`.

The three geometric inputs are separate new statement modules:
`Sheaf.Paper.WeilIndOpenRepresentability`,
`Sheaf.Paper.WeilIndProperHigherRepresentability`, and
`Sheaf.Paper.WeilIndProperOpenHigher`. They concern respectively an arbitrary
open immersion, an arbitrary proper morphism with represented input and no open
leg, and a single proper map identifying two distinguished open copies. None is
the original compact-support representability statement under another name.
The new modules are private proof imports of the item. The item also privately
imports `WeilConjectures.Compactification.CommonRefinement` and
`Mathlib.AlgebraicGeometry.Noetherian`. Every existing declaration signature,
definition body, visibility and public import is preserved. No other group's
module is adapted. No definition or statement change record is needed.

The original node now records the actual combining arguments and explicitly
identifies the final unproved comparison. Each new node records its statement,
source, proof in words, three kinds of Mathlib search, Lean attachment and
blueprint ancestry. All four sandbox modules compiled through `lcompile.py
--all`: 42.0, 42.4, 40.0 and 45.9 seconds respectively. The subsequently edited
comparison docstring only replaces an obsolete proof-step pointer.

## Proved and sorry left

Baseline: three named holes in the item. Two original bodies now have complete
Lean combining proofs:

- `WeilConjectures.zlWeilHigherShriek_representable`.
- `WeilConjectures.zlWeilHigherShriek_compactification_independent`.

The item retains exactly one hole:

- `WeilConjectures.zlWeilHigherShriek_compactSupportComparison`, node
  `def-zl-weil-compact-support-cohomology`.

This packet adds exactly three holes, one in each new module:

- `WeilConjectures.zlIndWeilOpenShriek_representable`, node
  `lem-zl-ind-open-representability`.
- `WeilConjectures.zlIndWeilProperHigher_representable`, node
  `lem-zl-ind-proper-higher-representability`.
- `WeilConjectures.zlIndWeilProperOpenHigher`, node
  `lem-zl-ind-proper-open-higher`.

Thus the packet has four holes overall: two closed, three added, net minus one
hole closed. This is a decomposition, not a net reduction or a proof of the
geometric realization inputs. No axiom or sorry inside a definition is added.
All new statements include the empty scheme, zero object, identity map, and
(for higher images) degree-zero cases; their proofs in words cover these cases.
The proper/open statement does not assume the open square is Cartesian: the
open copy is clopen in its inverse image, and its complementary component has
zero extension-by-zero restriction.

The searches and direct source reads did not produce an existing theorem in the
required equivariant ind-category. Open representability still needs the
normalized heart-to-ind adjunction comparison. Proper representability still
needs the ordinary-heart derived realization/Ext comparison and its descent to
common stages and Weil pairs. Proper/open interchange still needs the proper
base-change comparison in that same ambient category and the derived composite
comparison. These are mathematical proof obligations, not tool failures.

## No longer needed

None. No existing import, declaration, module, DAG node or unit step is removed.
The original node had no numbered proof plan or proof dependencies to prune.
The stronger dense-refinement and finite-family assertions are not needed by
this proof: it uses the already proved upstream two-compactification result
`Compactification.exists_common_refinement`. The dense-refinement node records
the encompassing mathematical construction; no claim is made to use its stronger
Lean signature with extra hypotheses.

## Where the brief, the DAG or earlier work was wrong

The route note described a retained four-module packet and saved report; those
files were absent from this sandbox at launch. The current repository item was
present and had three holes, so it was copied and the reduction rebuilt against
current declarations. The current return file contained no numbered objections.
The mandatory initial delivery attempt waited for a delivery slot and eventually
reported `DELIVERY BUSY`; nothing was pushed by that attempt.

The original representability docstring's finite-length argument cannot justify
this construction: constructible sheaves on a positive-dimensional scheme need
not have finite length. The realization argument needs the ordinary constructible
heart, not merely the perverse-heart realization theorem. Barrett,
*The derived category of the abelian category of constructible sheaves*,
arXiv:2005.10859, Theorem 1.1 supplies the relevant positive-characteristic
ordinary-heart source on separated varieties. The proper-image lemma's proof in
words separately addresses passage to finite affine covers, common stages and
Weil pairs; that formal comparison remains unproved. The paper was downloaded
and read in the permitted sandbox scratchpad; the maintainer should register it
in `literature/LIST.md` when accepting the source addition, since the worker may
not write the shared repository or deliver arbitrary literature files.

An abstract finite-presentation shortcut in the equivariant ind-category would
be insufficient: free Frobenius orbits can have nonconstructible underlying
objects. `CommonStageWeilShriek` imports this item, so importing its heart
adjunction declarations here would create a cycle. `ZlOpenExtensionTExact` also
has absolute-separatedness hypotheses absent from this item's universally
quantified schemes; those hypotheses were not silently added. No held module
was changed to evade either issue.

## New nodes

`lem-zl-ind-open-representability` states preservation of represented objects by
open extension, independently of any proper leg. Its new module is
`lean/Sheaf/Paper/WeilIndOpenRepresentability.lean`.

`lem-zl-ind-proper-higher-representability` states preservation of represented
objects by higher proper direct image, independently of any compactification or
open leg. Its new module is
`lean/Sheaf/Paper/WeilIndProperHigherRepresentability.lean`.

`lem-zl-ind-proper-open-higher` states the proper/open interchange step for a
single proper refinement, independently of selecting a common refinement or
lifting represented objects. Its new module is
`lean/Sheaf/Paper/WeilIndProperOpenHigher.lean`.

All three inherit chapter `sec-deligne-laumon-general` and unit
`sk-l-dl-general-composition`; the unit route and realization records are kept.
There are no change records, because no existing statement or definition changes.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
