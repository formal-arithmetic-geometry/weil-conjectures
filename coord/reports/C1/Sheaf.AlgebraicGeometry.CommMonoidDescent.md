## What changed

Proved `CategoryTheory.Over.DescentDatum.exists_commMonObj_of_effective_projection`
in `Sheaf.AlgebraicGeometry.CommMonoidDescent`, keeping its full statement unchanged.
The proof checks the four pointwise laws on the fpqc pullback of each test scheme,
cancels its epimorphic projection, and builds `MonObj` and `IsCommMonObj` from the
universal points. The conclusion's multiplication and unit identities follow from
the operation factorization equations.

Added the fully proved module `Sheaf.AlgebraicGeometry.CommMonoidOperationsDescent`
with `CategoryTheory.Over.DescentDatum.exists_raw_monoid_operations_of_effective_projection`.
It descends only the multiplication and unit as morphisms, using Mathlib's fpqc
`EffectiveEpi` instance, `EffectiveEpi.desc`, cartesian uniqueness, and the transport
compatibility hypotheses. All its private helpers are proved. Added this module and
`Mathlib.AlgebraicGeometry.Sites.Fpqc` as proof-only imports to the item. Updated the
item's DAG proof and dependencies to the actual argument, and added the operation node.
The unit's effective-descent route is retained; its realized lists contain no nodes
that this delivery bypasses. No definition or existing statement was changed.

## Proved and sorry left

Proved `CategoryTheory.Over.DescentDatum.exists_commMonObj_of_effective_projection`
(node `lem-pd-comm-monoid-operations-descent`): the item's only original sorry is closed.
Also proved `CategoryTheory.Over.DescentDatum.exists_raw_monoid_operations_of_effective_projection`
(node `lem-pd-raw-monoid-operations-descent`). No sorry is left in either delivered module,
and no unproved intermediate theorem was split off. All local compilations are single-file
compilations through `lcompile.py`; both modules compile in import order without warnings.

## No longer needed

Removed the unused proof imports `Sheaf.AlgebraicGeometry.BaseChangeConventions` and
`Sheaf.AlgebraicGeometry.FpqcMorphismsDescend`. The proof does not need the node
`lem-galois-fpqc-morphisms-descend`, its canonical comparison isomorphisms, or its
`fpqc_morphisms_descend` theorem: Mathlib's effective epimorphism API gives the needed
descent directly. The removed `BaseChangeConventions` module's module-pullback,
iterated-base-change and geometric-fibre results are also unused. The definition nodes
`def-pc-base-change`, `def-pd-descent-datum` and `def-sc-group-scheme` retain their roles
as descriptions of the notions used; none is replaced or weakened. In particular,
`def-pd-descent-datum` is removed from the original node's direct `proof_deps`,
but remains a statement dependency and a proof dependency of the new raw-operation node. This is pruning
for this proof, not a claim that these modules have no other users in the targets.

## Where the brief, the DAG or earlier work was wrong

The planned appeal to full faithfulness is mathematically sound but its chosen
canonical-pullback interface requires unnecessary comparison-map bookkeeping.
Mathlib already knows that an fpqc singleton is an effective epimorphism. Descent
of the two morphisms can therefore be proved directly from the supplied transport
hypotheses. No false statement, missing hypothesis, or unit-route error was found.
The raw-operation lemma needs no commutativity assumption upstairs; commutativity
is used precisely when descending its law in the item's proof.

The blueprint source files are absent from this machine's literature directory.
WANTED: `literature/blueprint/master/blueprint/sec-picard-framework/sk-prop-jacobian-descent/lem-pd-group-scheme-descent.md`,
multiplication and unit descent step. The source place and complete proof plan were
read from the existing DAG record; the implemented proof is marked as agent-written.
LeanSearch returned Internal Server Error; this unavailable search is recorded without
a verdict. LeanFinder, Loogle, and source searches were also run. No matching descent
statement was found; the effective-epimorphism and cartesian-monoid APIs were read and used.

## New nodes

`lem-pd-raw-monoid-operations-descent`, in
`dag/nodes/sec-picard-framework/lem-pd-raw-monoid-operations-descent.json`, records the
fully proved descent of multiplication and unit morphisms, without any laws downstairs.
Its single public theorem is in `Sheaf.AlgebraicGeometry.CommMonoidOperationsDescent`.
This is strictly the operation-construction part of the original argument; the item
separately proves all four laws. The statement is valid on empty schemes as well,
since the construction uses only pullback universal properties and effective epimorphisms.
Three kinds of Mathlib search and the complete proof are recorded. No change record is needed.


## Second reading by C1

1. Compared the whole original module with the repository version. The signature of
   `exists_commMonObj_of_effective_projection`, including all binder types and both
   point identities, is byte-for-byte unchanged. Only proof helpers, its proof/docstring,
   and proof-only imports changed. No existing definition changed; no change record is
   required. The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   Verdict: pass.
2. Read both complete proofs and compiled both modules locally with `lcompile.py` in
   import order, without errors or warnings. Scratch-copy `#print axioms` checks for
   both public theorems show exactly `propext`, `Classical.choice`, and `Quot.sound`.
   Neither module has a `sorry`, hollow definition, or forbidden declaration/attribute.
   The multiplication proof identifies the two transported inputs by cartesian
   uniqueness; the unit proof uses hη and hDV; all four laws downstairs are obtained
   by cancelling the fpqc projection on arbitrary test objects. Verdict: pass.
3. There are no split-off unproved statements. The new fully proved operation theorem
   is strictly the morphism-construction part, without any laws downstairs or an
   upstairs commutativity hypothesis. Its docstring and node describe the actual proof.
   Checked identity covers, empty bases, and the empty upstairs scheme: surjectivity and
   the supplied unit give the expected restrictions, and no argument uses a point or
   nonemptiness assumption. Repeated LeanFinder and Mathlib grep searches using
   "invariant binary operation and identity" and "monoid/multiplication descent";
   inspected the source library and both project roots. No equivalent operation-descent
   theorem was found. The hits EffectiveEpi.fac and the Mathlib fpqc EffectiveEpi
   instance are precisely the APIs already used. Verdict: pass.
4. Read the original proof-dependency interface `fpqc_morphisms_descend` and the
   Mathlib fpqc instance. Direct EffectiveEpi.desc avoids canonical comparison maps;
   no shorter ready-made theorem was found. The new imports are proof-only; retained
   public imports supply the statement types and structures. Both removed modules and
   both removed direct node dependencies are accounted for above. Opened
   `dag/units/sk-prop-jacobian-descent.json`: its `realized.statement` and eight `realized.steps`
   lists are empty, and the effective-descent route is retained. No realized unit node
   is bypassed. Verdict: pass.
5. Compared both node statements and Lean signatures, and followed each proof step:
   raw-operation descent uses transport preservation, cartesian lifting and
   EffectiveEpi.desc/fac; the original node then uses its operation identities,
   local lifts, epi cancellation and universal product points. `proof_deps` is the
   union of the recorded step uses in each node. The new node carries its source,
   searches, creation record, blueprint ancestry, chapter/unit and verbatim Lean
   statement. The blueprint source itself remains unavailable as reported above;
   the existing DAG source plan and local Mathlib source were read. Verdict: pass
   against the available source plan and kernel-checked proof.

Second reading changed only this report: made the removal of
`def-pd-descent-datum` from the original node's direct proof dependencies explicit,
while noting its retained statement and raw-operation roles, and recorded the
independent review. No Lean or node repair was necessary. Holes closed: the original
`exists_commMonObj_of_effective_projection` (one of one). Holes added: none.
