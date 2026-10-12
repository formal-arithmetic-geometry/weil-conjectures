## What changed

Closed the original proof body of
`AlgebraicGeometry.Scheme.GaloisCover.associatedModuleFunctor_comparisons`
without changing its statement. This is a decomposition into two presheaf
comparison theorems, with a complete categorical assembly in the item.

For the first comparison, the existing
`Etale.upperStarIsoLocalizationRestriction` computes pullback by restriction.
Mathlib's `Functor.pushforwardContinuousSheafificationCompatibility` moves
sheafification across the continuous and cocontinuous localization functor.
Whiskering the diagonal presheaf comparison with sheafification and composing
with `sheafificationNatIso` gives the required natural sheaf isomorphism.
For the second comparison, map the invariant-section presheaf isomorphism
through `presheafToSheaf` and compose with inverse `sheafificationIso`.
No arbitrary witness is used to define data.

New modules: `Sheaf.ConstructibleSheaf.TorsorDiagonalEvaluation` and
`Sheaf.ConstructibleSheaf.TorsorInvariantSections`. Both are proof-only imports
of the item. The item also imports the existing étale localization definitions
for its proof. Updated its node's proof, proof_deps and proof_origin accordingly.

All three modules compile together through `lcompile.py --all` without warnings.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Scheme.GaloisCover.associatedModuleFunctor_comparisons`
(node `lem-weil-pbc-torsor-associated-module-comparisons`). No sorry remains
in the item. This is a decomposition, not a sorry-free proof of the full result:
one upper hole closed and two lower holes added (net -1).

Every remaining hole in the delivery:

- `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_diagonal`
  (node `lem-weil-pbc-torsor-diagonal-evaluation`), in `TorsorDiagonalEvaluation`.
- `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_trivial`
  (node `lem-weil-pbc-torsor-invariant-sections`), in `TorsorInvariantSections`.

Both holes are whole proofs of named public theorems. Their docstrings and
nodes give the local evaluation, extension and descent formulas, their inverse
checks, restriction compatibility and linearity. They precede sheafification;
neither assumes nor concludes the original inverse-image comparison.

Edge cases checked mathematically: empty etale objects give zero section modules;
the trivial group gives evaluation on an identity torsor; arbitrary, including
zero and infinitely generated, coefficient modules use the same pointwise
formulas. The lemmas do not need connectedness or primality: a finite etale
torsor splits locally and ZMod ℓ is a ring for every ℓ, including zero and one.
Scalar restriction in both statements is exactly the existing definition's.

## No longer needed

The original module had no proof-dependency imports to remove: its public
`TorsorAssociatedModule` import remains necessary for the statement.

Pruned from the earlier sandbox attempt: the `EquivariantModuleSheaf` draft,
its proposed node `lem-weil-pbc-equivariant-module-is-sheaf`, and its proof-only
import. The full sheaf-axiom proof for equivariant sections is unnecessary:
Mathlib's sheafification compatibility supplies the categorical step directly.
Also removed the unused public localization-definitions import from the new
`TorsorDiagonalEvaluation` module and the redundant direct import of
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small` from the item.

The item uses neither the full descent equivalence nor the fullness or essential
image modules. No existing dependency node of the original DAG was pruned:
the old proof used only the associated-functor definition, which remains a
statement dependency. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier missing-olean report was caused by a stale sandbox overlay once the
shared compiled dependency became available. `lcompile.py --all` refreshed the
overlay through the prescribed tool and resolved it. No dependency was copied
or independently compiled, and no compilation script was edited.

The original proof plan demanded a direct sheaf-axiom verification. This is not
needed for either conclusion because Mathlib already proves compatibility of
sheafification with the localization's continuous pushforward.

The blueprint ancestor tool returns None for this item because an earlier
created.item is a module name; the new nodes follow the explicit ancestor
`split-locally-constant-cover-filtration` recorded on the parent descent node,
whose proof uses passing from H-modules to locally constant sheaves.

Read the Stacks pages for 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS. The first pages
state finite-type comparisons, not the arbitrary-module presheaf lemmas verbatim;
the new proofs spell out the concrete torsor argument without finite generation.
The local source tex files are absent on this machine, so the official tag pages
were used. Searches of the whole blueprint and local Lean found no duplicate.
LeanSearch returned Internal Server Error (recorded as unavailable); LeanFinder,
Loogle and Mathlib/source grep ran successfully and supplied no exact comparison.

## New nodes

`lem-weil-pbc-torsor-diagonal-evaluation`: the natural presheaf isomorphism
obtained by evaluating on the graph of an etale object upstairs. It isolates
the local linear construction; the item's proof performs sheafification and
inverse-image transport explicitly.

`lem-weil-pbc-torsor-invariant-sections`: the invariant coefficient presheaf
isomorphism downstairs. It isolates descent of invariant locally constant
functions; the item's proof applies and removes sheafification explicitly.

No definition, existing statement, public import of the item, or target was
changed; no change record is required.

## Second reading by R1

1. **Statements and signatures.** I compared the delivered item byte for byte
with the repository version. The target theorem
`Scheme.GaloisCover.associatedModuleFunctor_comparisons` has the identical
hypotheses, universes, functors, scalar restriction, and two conclusions. The
two added declarations match their DAG node statements: the diagonal node is
the presheaf comparison after étale localization and the invariant node is the
trivial-representation comparison downstairs. Neither adds connectedness,
primality, or finite generation.

2. **Proof and trust basis.** `lcompile.py --all` compiles all three modules
without errors or warnings. The item proof contains no `sorry`; the only
remaining holes are the two explicitly named public split-off theorems, each
with a source, a complete proof sketch in its docstring, and a matching DAG
node. No definition contains `sorry`, and no forbidden declaration or axiom is
introduced. The two split statements were checked on empty étale objects, the
trivial group, zero and arbitrary coefficient modules, so the pointwise
evaluation/descent claims have the required edge cases.

3. **Shortest route and dependencies.** The item uses the existing étale
localization restriction and Mathlib's sheafification compatibility, then
whiskers the diagonal comparison and maps the invariant comparison through
`presheafToSheaf`; this avoids an unnecessary direct sheaf-axiom proof. The
new modules import only `TorsorAssociatedModule` publicly. The item imports the
two proof-only modules and the étale localization definitions needed by its
proof. The DAG `proof` and `proof_deps` list exactly these two split nodes, and
the unit route remains the one recorded for `sk-thm-p1`.

4. **New statements and duplication search.** I searched the local Lean tree,
the blueprint, and the recorded LeanFinder/Loogle/grep searches for an
existing diagonal or invariant torsor comparison. No duplicate declaration or
Mathlib match exists. The new statements are strictly smaller presheaf
comparisons used as inputs to the categorical assembly, rather than restating
the item's sheaf-level conjunction.

5. **Changes made.** I added this second-reading record only; no Lean proof or
statement required repair after compilation. The delivery remains a
decomposition: one upper hole is closed and the two named lower holes are
added, with the report and node metadata documenting that split.
