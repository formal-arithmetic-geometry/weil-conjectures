## What changed

The existing theorem `AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_modN`
keeps its signature and original docstring byte for byte. Its proof converts the unit
annihilation into `(n : Λ) = 0`, constructs the explicit coefficient map
`ULift (ZMod n) →+* Λ` using `ZMod.castHom (ringChar.dvd hn) Λ` and the ULift ring
equivalence, and applies the cyclic-coefficient exchange isomorphism at the derived
restriction of K. A general coefficient-comparison theorem transfers invertibility
to the restricted Λ exchange, and a proved private reflection lemma finishes.

The proof-only auxiliary import replaces the unused private import
`Sheaf.AlgebraicGeometry.DerivedCategories`. Existing public imports are unchanged.
The new module `Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux` states the
arbitrary-ring coefficient comparison. No definition or existing statement changes;
no change record or forced adaptation is needed.

## Proved and sorry left

Hole closed in the item's source:

- `AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_modN`.

Hole added in a new module:

- `AlgebraicGeometry.isIso_restricted_derivedBaseChangeMap_iff`, node
  `lem-kun-proper-base-change-forgetful-aux`, in
  `Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux`.

The remaining statement compares exchanges for an arbitrary ring homomorphism. It
has no cyclic coefficient, annihilator, properness, or exchange-isomorphism hypothesis.
The target performs the cyclic reduction and the isomorphism reflection separately.
This is a decomposition: one source hole closed, one lower hole added, raw net zero.
The ledger determines the net in the actual targets' import closure; this report does
not claim a fully proved target or positive net progress.

The private helper `AlgebraicGeometry.isIso_of_isIso_derivedRestrictScalars_map` is
proved without holes. Scratch-copy `#print axioms` gives exactly `propext`,
`Classical.choice`, and `Quot.sound` for it. For the target and auxiliary theorem it
adds only `sorryAx`, attributable to the named auxiliary hole. Both delivered modules
compile in import order without warnings. There are no new definitions, arbitrary
witness selections, forbidden axioms, unsafe declarations, or hidden holes.

## No longer needed

Removed from the target: private import
`Sheaf.AlgebraicGeometry.DerivedCategories`. The old direct proof dependencies were
`def-weil-pbc-derived-categories` and
`lem-kun-unbounded-abelian-exchange-comparison`. They are no longer direct proof
dependencies: the former still supplies the categories appearing in the statement,
and the latter is retained through the auxiliary comparison node. The target's new
direct proof dependency is `lem-kun-proper-base-change-forgetful-aux`.

Removed from the first worker's new auxiliary module:
`WeilConjectures.SixFunctors.BaseChange.DerivedRestrictScalars` and
`Mathlib.Data.ZMod.Basic`; its general statement needs neither. The target's
auxiliary import is plain `import`, as only its proof uses that module. The
auxiliary's two public imports provide symbols in its public statement.

No existing mathematical branch or globally unreachable module is claimed pruned.
The unit route and `dag/units/sk-prop-sf-kunneth-ordinary.json` realized fields stay
unchanged.

## Where the brief, the DAG or earlier work was wrong

The first worker's remaining theorem had exactly the target's hypotheses and asked
for the same exchange to be invertible after conservative restriction to integers.
It therefore retained essentially the whole target rather than isolating the cyclic
reduction's comparison step. The second reader replaced it with a ring-map-general
comparison, and the target now constructs and actually uses `ZMod n → Λ`.

The first worker marked the target disputed at n = 0. That objection is unsupported:
`ZMod 0 = ℤ` has a canonical ring map to every Λ, and the hypothesis still assumes
invertibility of the exchange on all integer-coefficient complexes. This is enough
for the same coefficient-comparison reduction. The marker was removed, restoring
the repository docstring. For n = 1, unit annihilation forces the zero ring; identity
squares and zero complexes also give the expected invertibility test. No positivity
assumption was added.

The first auxiliary node cited the target in its statement and proof while the target
used the auxiliary: a circular dependency. The repaired auxiliary depends only on
the existing unbounded abelian-exchange comparison node. The target DAG records the
explicit coefficient map, general comparison, and proved homology reflection.

The source was verified at https://stacks.math.columbia.edu/tag/0D6J, part (3), for
the canonical unbounded direct-image comparison. The equality for the canonical
exchange mates is the additional assertion of the existing node
`lem-kun-unbounded-abelian-exchange-comparison`, not a claim attributed to 0D6J alone.
That existing node has no Lean declaration yet. The library theorem
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_restrictScalars_iff`
is bounded below; it cannot discharge the unbounded comparison. Rerun Mathlib
searches found no unbounded exchange theorem; LeanSearch was unavailable and was
recorded as unavailable. The comparison was not closed in a short proof.

## New nodes

`lem-kun-proper-base-change-forgetful-aux`: for any ring map R → S and any K, the
restricted S exchange is invertible exactly when the R exchange at restricted K is.
Its docstring proves this in words by the two canonical comparisons to the same
underlying abelian exchange and reflection of isomorphisms through exact forgetting.
The node has an exact Lean signature, source, complete proof steps, search records,
creation metadata, and the same chapter and unit as the target. No change records.

## Second reading by S2

1. Diffed the existing target module against the repository. The existing theorem's
   signature, universes, variables, docstring, visibility, and public imports are
   unchanged. Only its proof, private helper, and private proof imports differ.
   The auxiliary module is new. Verdict: pass after removing the disputed marker.

2. Compiled both modules locally through lcompile.py in import order without
   warnings. Checked scratch-copy `#print axioms` for the helper, target, and
   auxiliary: only the allowed three axioms, plus sorryAx for the latter two.
   Exactly one named theorem hole remains, with a docstring and matching node.
   No hollow data or forbidden declarations. Verdict: pass as a decomposition.

3. Rejected the first auxiliary's near-restatement and replaced it with a general
   ring-map comparison. The target now constructs the actual cyclic ring map,
   evaluates hbase at the restricted K, applies that comparison, and reflects
   isomorphisms using a proved homology argument. Checked n = 0, n = 1, the zero
   ring, zero objects, and identity squares. Searched Mathlib and both library
   roots with coefficient comparison and restriction terminology; only the bounded
   below interface exists. Verdict: repaired; one genuine comparison step open.

4. Read the proof top down, its old proof-dependency nodes, and the unit record.
   The coefficient-forgetting route remains. Removed the unused DerivedCategories
   import and the two unused imports of the auxiliary. The No longer needed
   section accounts for every old direct proof dependency absent from the new list.
   No unit realization is bypassed or edited. Verdict: pass.

5. Rebuilt the auxiliary node's self-contained statement and exact Lean signature,
   source and proof steps, three search kinds (including the recorded unavailable
   service), creation and blueprint metadata. Removed the circular dependency and
   synchronized the target proof and proof_deps. Proof_deps in each node equals the
   union of its steps' uses. Verdict: pass.

Second-reading changes: replaced the near-restatement with arbitrary-ring exchange
compatibility; constructed the cyclic ring map in the target; retained the proved
reflection argument; removed the unsupported n = 0 dispute; pruned unused imports;
repaired the circular dependency, exact signatures, search records, and missing
creation metadata; corrected hole accounting and removed linter warnings.
