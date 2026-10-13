## What changed

Replaced the first worker's equivalent restatement with a genuine two-part
reduction of `Sheaf.AlgebraicGeometry.OpenRestrictedCanonicalSquare`.
The existing theorem signature is byte for byte unchanged. Its proof now
combines the ordinary comparison square, counit compatibility, and naturality
of the specified `openDerivedStalkIso` using a proved private categorical helper.
Only the two new lemma modules are added as proof-only imports to the item.
A declaration-local unusedVariables linter option preserves the original named
K-flatness binder inside the universally quantified signature; that binder is
unused in the dependent conclusion, and introducing it in the proof does not
change that signature-level linter result.

`OpenRestrictedTensorComplexIso` constructs the tensor/restriction natural
isomorphism, its square on an open pullback, its degreewise chain isomorphism,
and its localized derived isomorphism. Every object is an explicit composite
of the library's adjunction comparisons and localization factors. There is no
new choice from a mere-existence theorem and no sorry in any definition.

`OpenRestrictedOrdinaryComparisonSquare` states the comparison before inverse
pullback counits. `OpenRestrictedCounitCompatibility` states the counit equation
before stalks and cohomology. These are strictly separate parts of the original
argument, following the existing affine-spectrum proof's separation of ordinary
comparison and counit compatibility. Their full proofs in words are in their
docstrings and nodes. They remain open.

The copied `OpenDerivedStalkIso` source is identical to the repository version;
it is present only to supply the previously missing local compiled dependency.
The delivery tool does not commit this unchanged file. Removed the equivalent
`OpenRestrictedCanonicalSquareReduced` module and its spurious split node.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_canonical_square`
(node `lem-pc-open-restricted-canonical-square`) by a real assembly proof.

Added two named holes, each with proof docstring and node:

- `AlgebraicGeometry.SingleComplexBaseChange.exists_open_restricted_ordinary_comparison_square`
  (`lem-pc-open-restricted-ordinary-comparison-square`): the ordinary-target
  comparison, without K-flatness or inverse derived pullback counits.
- `AlgebraicGeometry.SingleComplexBaseChange.openRestricted_counit_compatibility`
  (`lem-pc-open-restricted-counit-compatibility`): an equality of derived maps,
  without a base square to S, a point, cohomological degree, K-flatness, or
  counit invertibility.

This is a decomposition, not completion of the theorem: one original hole
closed and two lower holes added, hence net -1 for these delivered holes.
The pinned sorry ledger determines overall target-closure progress.
The private helper `assemble_open_counit_square` is proved, and all four new
isomorphism constructions contain no sorry. The original theorem's axioms
still include sorryAx through the two explicitly named open lemmas.

## No longer needed

No original import was removed, and no module is claimed globally pruned.
The rejected reduced module and node are removed from this delivery entirely.

The old direct proof dependencies no longer used directly by the item's proof
are `lem-pc-open-restriction-stalk-extension-iso`,
`def-pc-base-derived-tensor-cohomology-model`,
`lem-weil-pbc-module-stalk-pullback`, `lem-pc-kflat-open-restriction`, and
`lem-pc-ringed-spaces-derived-pullback-composition`.
Restriction-stalk extension, ring tensor transport, pullback stalks, and derived
composition remain in the relevant new lower nodes' plans. K-flatness is
retained in the unchanged interface but is unnecessary for the assembly.
The item's direct proof_deps now list the actual two new lemmas and the
existing definitions unfolded by its proof, with their union recorded exactly.
The unit `sk-thm-picard-semicon` has empty realized statement and step lists;
its record and chapter route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The first worker's `exists_open_restricted_canonical_square_reduced` is not
strictly smaller: it moves universal parameters into the binder list and
repeats the complete conclusion. Applying it is an equivalent restatement,
not an acceptable split. Its docstring also carried the original node tag.
It has been removed, rather than disguised for the automatic restatement test.

The first worker's original proof did not compile: `intro P hP hcP hcQ`
introduced the leading let-bound functors instead of the intended parameters,
so its P was a forgetful functor. The repaired proof begins with `dsimp only`
before introducing the actual complex and certificates.

## New nodes

`def-pc-open-restricted-tensor-complex-iso` records the four explicit tensor
restriction isomorphism constructions in `OpenRestrictedTensorComplexIso`.

`lem-pc-open-restricted-ordinary-comparison-square` records exactly the ordinary
comparison square and its ring/stalk, universal-counit, and homology proof steps.
It uses the existing generic ring-isomorphism comparison node rather than
restating that generic theorem.

`lem-pc-open-restricted-counit-compatibility` records the independent equation
of derived maps obtained from the specified composition counit equations and
the exact restriction factors.

No existing statement or definition changed; no change record is required.

## Second reading by G2

1. Compared every existing sandbox module with the repository. The only
   changed existing declaration is the original theorem's proof; its signature
   is byte for byte identical. The extra local source OpenDerivedStalkIso is
   identical. No existing definitions, visibility, or public imports changed.
   Verdict: unchanged interface.
2. Compiled all delivered modules through lcompile.py, and compiled a scratch
   copy with #print axioms for the original theorem, both new lemmas, and all
   four new constructions. The only source sorries are exactly the two new
   named lemma proofs. No axiom, unsafe, opaque, implemented_by, extern,
   skipKernelTC, or hollow definition occurs. Verdict: valid assembly with
   two disclosed lower holes; standard axioms plus sorryAx only.
3. Rejected and removed the equivalent reduced statement. The replacement
   ordinary square lacks all inverse pullback counits; the counit equation
   lacks all tensor cohomology and source comparison data. Their docstrings
   give complete proof routes. Empty opens have no point in the ordinary
   square; the counit equation still applies without a point. Top opens,
   zero complexes, zero rings, and unbounded complexes obey the same equations.
   Both statements are true without flatness over the base. Searched Mathlib
   with different queries using leanfinder, loogle, leansearch, and grep;
   leansearch was unavailable and no absence verdict is inferred. Searched
   both library roots for comparisonIntoPullback and related ordinary/counit
   transport. Existing open termwise comparisons restrict base opens and use
   different restriction functors, so do not cover arbitrary source U and
   the actual pullback scheme. The existing generic ring transport supplies
   a step of the ordinary lemma's proof, not its prescribed stalk/chain square.
   Verdict: needed, strictly smaller parts, no duplicated existing result.
4. Read the plan, dependencies, and analogous affine-spectrum assembly. The
   new proof follows the shortest applicable ordinary/counit separation and
   uses a small categorical argument for assembly. Proof-only added imports
   are plain imports. Existing public imports are needed by the signature.
   No old direct proof dependency is omitted from No longer needed, and no
   unit realization is bypassed or modified. Verdict: route retained.
5. Checked the three new records against signatures and docstrings; their
   source, complete proof steps, searches, provenance, creation, blueprint,
   chapter, unit, and lean fields are present. The existing node's proof,
   proof_deps and proof_origin now describe the actual assembly, and deps
   equal the union of uses. Verdict: DAG agrees with Lean.

Second reading changed the invalid equivalent split into an explicit ordinary
comparison/counit decomposition, repaired the intro bug, added real isomorphism
constructions, and corrected the proof accounting and DAG. Neither lower
statement was simple enough to close during this reading.
