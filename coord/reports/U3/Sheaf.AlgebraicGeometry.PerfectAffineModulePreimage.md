## What changed

Closed `AlgebraicGeometry.perfect_affine_module_preimage` without changing its signature.
Choose a complex M representing the inverse image under the affine equivalence, and use
Q(M) as the output object. The equivalence comparison identifies its associated sheaf S
with E. Transport perfectness through the over-site restriction functors, apply the
existing perfect-to-pseudo-coherent/local-Tor theorem, globalize Tor bounds, and apply
both existing affine criteria. The counit and representing isomorphism provide the
required object isomorphism; the original natural comparison is retained.

A fully proved private helper transports derived localizations along an additive
abelian-category equivalence, using Mathlib localization invariance under equivalence.
This supplies the open-subscheme localization instances required by the existing
perfectness theorem, from the over-site instances already assumed by our theorem.
It constructs an actual localization functor; no data is chosen from an unproved theorem.

Added two modules, one theorem per module:
`QuasiCompactFiniteTorDimension` proves the finite-subcover/minimum/maximum argument,
and `TorAmplitudeOpenLocal` isolates locality of vanishing in a fixed interval.
The latter is the only added sorry. All three sandbox modules compile together.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.perfect_affine_module_preimage`
(node `lem-pc-perfect-affine-module-preimage`), 1 of 1 holes in the assigned module.

Also proved the new theorem
`AlgebraicGeometry.Scheme.hasFiniteTorDimension_of_locallyFinite`
(node `lem-pc-quasi-compact-finite-tor-dimension`). This is real finite-subcover glue:
insert 0 into the finite sets of endpoints, take minimum/maximum, widen each selected
local interval, and apply fixed-interval locality. No hole remains in this module.

Added one hole:
`AlgebraicGeometry.torAmplitude_of_open_neighbourhoods`
(node `lem-pc-tor-amplitude-open-local`), whose proof is exactly `by sorry` in its own
module. Its docstring contains the complete K-flat/restriction/stalk argument from
Stacks Tag 09U9. It assumes one fixed interval on open neighbourhoods and proves
vanishing in that interval globally. It does not assert any affine equivalence,
module preimage, pseudo-coherence, or existence of global bounds.

This is a decomposition, not an unconditional proof: one original hole closed, one
strictly smaller locality hole added, net zero holes before subsequent workers prove
the imported dependencies. The existing affine criteria and perfectness theorem also
still contain their original sorries, which this delivery uses as intended.

## No longer needed

No imports or original proof-dependency nodes were removed: all four original
proof-dependency nodes are used. The statement's original public imports are retained
so every existing importer sees the same interface. The proof constructs no bounded
flat replacement or bounded projective replacement. No existing DAG node or module
is made unnecessary by this delivery.

## Where the brief, the DAG or earlier work was wrong

The planned perfectness theorem needs derived localizations of modules on open
subschemes, while the assigned signature provides only over-site localizations.
These module categories are equivalent, not definitionally the same categories.
The private helper constructs the missing instances by transporting the chosen
localizations, preserving the arbitrary morphism universe w and the existing signature.

The plan's finite-subcover paragraph did not have a named fixed-interval locality
statement. It is now isolated, with a strictly smaller conclusion than the assigned item.
The finite-subcover and endpoint arguments are proved, including the empty cover case.
The unit's realized statement/step lists are empty and its route has not been bypassed.

The repository's literature directory lacks the cited TeX files on this machine.
Read the available read-only copies of cohomology.tex and perfect.tex under
/home/ubuntu/work-bp/sheaf/literature/stacks-project, including definition-tor-amplitude,
lemma-tor-amplitude-stalk (Tag 09U9), and lemma-perfect-affine (Tag 08EB).
Searches are recorded in searches.jsonl; LeanSearch returned Internal Server Error,
while LeanFinder, Loogle and local Mathlib searches found no matching theorem.

Edge cases checked: empty schemes/zero ring (bounds [0,0] are supported by the proved
insert-0 construction), disconnected schemes with different local intervals (finite
min/max gives uniform bounds), arbitrary test module sheaves (no quasi-coherence
assumption), and independent arbitrary derived-category universes w and wA.

## New nodes

`lem-pc-quasi-compact-finite-tor-dimension` records the proved finite-subcover consequence
of local finite Tor dimension, with the same chosen open-subscheme localizations as
the existing definition. Its proof uses fixed-interval locality and elementary finite
order/compactness operations. Module: Sheaf.AlgebraicGeometry.QuasiCompactFiniteTorDimension.

`lem-pc-tor-amplitude-open-local` records the one outstanding locality step, sourced to
Stacks Tag 09U9 and its proof. Its statement fixes [a,b] before quantifying neighbourhoods
and test sheaves. Its plan names existing K-flat resolution/comparison, open restriction,
and zero-stalk detection nodes. Module: Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal.

Updated only proof, proof_deps and proof_origin of the assigned node. No existing
statement/definition was changed, no forced adaptations, and no change record is needed.

## Second reading by U3

1. Compared the delivered main module with the repository version. The theorem signature
and all existing declaration statements are byte-for-byte unchanged; only proof text,
imports, documentation, and the recorded proof route differ. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`; they compile without
errors. The assigned theorem and the finite-subcover theorem have no `sorry`, while the
single explicitly split locality theorem has exactly its named `by sorry`; no forbidden
declarations or hollow definitions were found. Verdict: pass.
3. Checked the two split-off statements against their definitions and edge cases
(empty cover, zero ring, disconnected finite covers, and arbitrary test modules). They
are strictly smaller than the assigned theorem, sourced and documented, and no duplicate
library declarations were found. Verdict: pass.
4. Checked the proof route from the top downward: the affine equivalence, perfectness
criterion, compactness globalization, and both affine criteria are all used. The
transport helper constructs localization data through an equivalence; no arbitrary
witness is selected from a bare existence theorem. No removable imports or old proof
dependencies were found. Verdict: pass.
5. Checked the DAG nodes against the declarations, proof dependencies, origins, and
new-module records. The unit route remains represented and the new locality node is the
only remaining hole. Verdict: pass.

Changed during second reading: added this review record only; no Lean declarations or
statements required repair.
