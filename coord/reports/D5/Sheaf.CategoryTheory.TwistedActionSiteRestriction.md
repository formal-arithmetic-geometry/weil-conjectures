## What changed

Replaced the original `siteRestriction` sorry with a complete Lean assembly from
three strictly smaller construction statements. The theorem's signature and its
public import are unchanged. Four new proof modules contain the three obligations
and a proved geometric-restriction theorem:

- `TwistedActionSiteCore`: construction of the labelled category, generated topology,
  coefficient sheaf, and cocontinuity of the degree-zero inclusion.
- `TwistedActionModuleRestriction`: the module fixed-pair equivalence and its
  restriction and generator normalizations, over an already specified Site.
- `TwistedActionSetRestriction`: the analogous set fixed-pair equivalence, over an
  already specified Site.
- `TwistedActionGeometricRestriction`: proved from the existing
  `continuous_cocontinuous_ringed_restriction` theorem. The proof transports its
  source coefficient ring through `coefficientRestriction`, constructs the changed
  module direct image explicitly, and composes the module adjunction with the inverse
  scalar-equivalence adjunction. Its structural-map normalization follows from the
  original theorem's heterogeneous sectionwise identity.

The item itself proves that `sigma` is an equivalence using Mathlib's actual module
pushforward equivalence and the given coefficient isomorphism. It derives the
module-addition equation by transporting additivity through the restriction
isomorphism. Finally `Adjunction.ofNatIsoLeft` converts the ordinary module
restriction adjunction to the required fixed-pair forgetful adjunction.

All changes are inside the item and new modules/nodes. No existing definition,
statement, source-library declaration, or public import changes. No shared-module
adaptation or change record is needed.

## Proved and sorry left

This is a decomposition, not a closure of the original obligation using only
standard axioms. The single original sorry in
`CategoryTheory.TwistedActionRingedSite.siteRestriction` is removed; its body now
compiles without local holes, but it depends on three new holes. Thus 1 hole is
removed and 3 are added, for a net increase of 2 in this branch.

The remaining sorries are exactly:

- `CategoryTheory.TwistedActionRingedSite.siteCore`, node
  `lem-sf-twisted-action-site-core`.
- `CategoryTheory.TwistedActionRingedSite.moduleRestriction`, node
  `lem-sf-twisted-action-module-restriction`.
- `CategoryTheory.TwistedActionRingedSite.setRestriction`, node
  `lem-sf-twisted-action-set-restriction`.

Each has its own module, source, complete proof in words, and a corresponding DAG
node. Each is a strict part of the original construction. None asserts existence
of a RestrictionPresentation or repackages the original conclusion.

Independently proved: the private `sigma_isEquivalence` helper and public
`CategoryTheory.TwistedActionRingedSite.geometricRestriction` (node
`lem-sf-twisted-action-geometric-restriction`). `#print axioms` for both reports
only `propext`, `Classical.choice`, and `Quot.sound`. The assembled upper theorem
still reports `sorryAx`, as expected from the three stated construction lemmas.

## No longer needed

No module is withdrawn and no public import is removed. The original module only
imported its statement-data module, which remains necessary. Every new proof import
is used.

The old direct dependency `lem-sf-twisted-fixed-pair-created-limits` is not used by
this proof: finite-limit preservation and the geometric adjunction come from
continuous-cocontinuous restriction. Its module remains needed by the parent
`TwistedActionRingedSite.addLimits`; it is not globally pruned. The old direct
sectionwise-set-limits and natural-bijection steps are also replaced by that
existing geometric restriction theorem. Size, site, module, fixed-pair, and
ringed-topos definitions remain needed through the data module and the new
statements. The main node now cites exactly the four new nodes whose declarations
its proof uses.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies consist of definitions and generic categorical
lemmas; none states the labelled-site construction or either normalized
restriction equivalence. Their being available does not close the construction
steps. Mathlib defines integer powers of equivalences but explicitly leaves the
addition comparisons as a TODO (`CategoryTheory/Equivalence.lean`, following
`pow_neg_one`). The site-construction obligation therefore records the required
coherence argument rather than assuming an existing powers API supplies it.

For the geometric step, the full product-of-translates construction is unnecessary:
the existing continuous-cocontinuous restriction theorem supplies both adjunctions.
The extra cocontinuity conclusion belongs to the same covering-basis calculation
already required by the core construction. The geometric theorem assumes that
property explicitly and is proved completely from it. The existing restriction
lemma is used as a general categorical tool for the same geometric step; no unit
route is replaced and no maintainer tool-use approval is edited.

Edge cases checked in the new statements: empty C; the zero coefficient ring;
identity s with a possibly nontrivial coefficient automorphism; zero modules; and
sites admitting empty covering sieves. The statements retain these cases, use no
choice of nonzero section or object, and keep the generator degree and structural
map directions of the original data. The unit record has no realized statement or
steps attached to this support node, and the unit's route is unchanged.

The ancestor tool reports no imported blueprint ancestor for the original node;
new nodes preserve that recorded null ancestor and the parent's provenance, without
inventing a different blueprint source. Searching the current blueprint for
"twisted action site" and "semidirect" found no matching imported blueprint node.

## New nodes

`lem-sf-twisted-action-site-core`: underlying labelled site, generated topology,
coefficient construction, and cocontinuity. Statement only; one sorry.

`lem-sf-twisted-action-module-restriction`: module equivalence and its two
normalizations over a specified Site. Statement only; one sorry. Additivity is
proved by the consumer, not assumed here.

`lem-sf-twisted-action-set-restriction`: set equivalence and its two normalizations
over a specified Site. Statement only; one sorry.

`lem-sf-twisted-action-geometric-restriction`: proved ringed restriction under the
explicit cocontinuity hypothesis. No sorry. The original node's proof and
proof-dependency fields are updated to the actual assembly.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
