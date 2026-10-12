## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.exists_flat_single_open_locus`
with a complete Lean proof without changing its statement. The open is explicitly the
union of all opens satisfying the local single-degree condition. A proved private helper
`isZero_restrict_union` glues vanishing through the separated sheaf condition on an
arbitrary indexed cover. The proof combines negative-degree connectivity with
natural-degree vanishing, uses Mathlib's standard t-structure bounds and single-object
truncation theorem, and identifies the single object's coefficient by degree-i homology.

Added `Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology` with a complete proof of
`AlgebraicGeometry.Scheme.Modules.nonempty_homology_derivedOpenPullback_iso_restrict`.
The proof unpacks the specification of the chosen derived pullback, takes a K-flat
resolution, applies the invertible counit at that resolution, transports exactness from
ordinary open restriction, and composes the homology comparisons. It needs no boundedness,
quasi-coherence, or flatness assumption on the derived object.

Added `Sheaf.AlgebraicGeometry.FlatRestrictionUnion` for the strictly sheaf-theoretic
flatness step still to be proved. Updated the original DAG node's proof and proof dependencies
and added nodes for both new public theorems. No definition or existing statement changed.
Every delivered Lean file compiles through lcompile.py; the main file and the comparison
module contain no sorry. The empty indexed cover, empty scheme/open, rank zero,
varying ranks, and negative/nonnegative degree boundary were checked against the arguments.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.exists_flat_single_open_locus`
(node `lem-pc-derived-single-open-locus`).

The new comparison theorem
`AlgebraicGeometry.Scheme.Modules.nonempty_homology_derivedOpenPullback_iso_restrict`
(node `lem-pc-derived-open-pullback-homology`) has a complete proof from existing
declarations. The private `isZero_restrict_union` helper is also fully proved.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.isFlat_restrict_iSup_of_finiteLocallyFree`
(node `lem-pc-flat-restriction-union`), in its own new module. It asserts only the
flatness of an ordinary module restriction on the union of its finite locally free
loci; it says nothing about derived objects, connectivity, concentration, or single
complexes. This is a decomposition, with one upper hole closed and one strictly
simpler lower hole added (net zero delivered holes), not a claim of a sorry-free
result or a net-hole reduction. There are no other sorries in the delivered files.
The existing proof dependencies of the comparison may themselves still rest on sorry.

## No longer needed

Removed the redundant direct proof imports `Sheaf.AlgebraicGeometry.DerivedCategory`
and `Sheaf.AlgebraicGeometry.TensorPullback` from the item's file. They remain
transitively required through its public `DerivedPullback` import, so their modules
and definition nodes are not claimed pruned from the targets' closure. Removed an
unnecessary `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` proof import from
the new comparison after checking compilation without it.

No mathematical node or module from the original route is pruned. The original
proof dependencies on definition nodes are now represented through the statements
and the two specific supporting nodes, rather than being presented as if those
definitions alone supplied flatness and the exact-open derived comparison.
The unit's route and its realized fields are unchanged.

For completeness, the old direct proof dependencies removed from the item's node
are `def-pc-derived-category`, `def-pc-derived-pullback`,
`def-pc-flat-sheaf-modules`, and `def-pc-module-pullback`. These definition nodes
remain statement dependencies, and the supporting nodes also cite the relevant
definitions; none is claimed removed from the targets' import closure.
`def-pc-invertible-in-degree-zero` remains a direct proof dependency.

## Where the brief, the DAG or earlier work was wrong

The listed proof dependencies for the original node were definitions, not theorems
providing either the local-flatness gluing step or the comparison of the chosen
derivedPullback with exact open restriction. The stated proof plan was mathematically
sound, but these steps required actual additional Lean arguments. The exact-open
comparison and vanishing gluing are now proved; flatness locality is explicitly
isolated as the remaining subclaim.

The blueprint source file named by the original node is absent in this machine's
read-only literature tree. The supplied original node records its source paragraph
and the complete expanded proof; the supporting docstrings and nodes preserve this
provenance and mark the explicit arguments as written by an agent. LeanSearch was
unavailable with Internal Server Error; LeanFinder, Loogle and source searches were
used and recorded. No statement was found false and no statement was weakened.

## New nodes

`lem-pc-flat-restriction-union` records the ordinary-module flatness statement on
an arbitrary union of finite locally free loci, with no uniform rank requirement.
Its natural-language proof refines the cover by finite free trivializations,
checks tensor exactness there, and uses locality of exactness. The remaining sorry
is in `Sheaf.AlgebraicGeometry.FlatRestrictionUnion` only.

`lem-pc-derived-open-pullback-homology` records the proved comparison between the
homology of the chosen derived open pullback and restricted homology. Its proof
records the K-flat resolution, derived counit and homology-isomorphism composition
implemented in `Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology`.

Both nodes inherit sec-picard-framework/sk-thm-picard-perfect and trace back to the
cohomology-sheaf gluing paragraph of lem-pc-perfect-locus. No change record is needed.


## Second reading by K1

1. Compared the complete item module with its read-only repository version using
   `diff -u`. The only existing declaration is
   `AlgebraicGeometry.Scheme.Modules.exists_flat_single_open_locus`; its signature
   is byte for byte unchanged, as is its docstring. There are no delivered
   definitions or changes to target statements. The two added public statements
   have their own modules and nodes. Verdict: pass.

2. Compiled all three delivered modules in import order using `lcompile.py --all`:
   no errors or warnings. Scanned the files for forbidden declarations and holes:
   exactly one `sorry`, the named flatness theorem reported above; none occurs in
   data or a definition. Scratch copies with `#print axioms` for each public
   theorem report only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   In particular the proved comparison still inherits open upstream dependencies;
   the main theorem also uses the reported flatness hole. Verdict: valid
   decomposition, one original hole closed and one lower hole added, net zero.

3. Read `FlatRestrictionUnion.lean` against the definitions of
   `IsFiniteLocallyFreeOfRank` and `SheafOfModules.IsFlat`. Its premise supplies
   finite free trivializations on a cover of the union; locally tensoring is a
   finite sum of the identity, and stalkwise exactness proves the stated global
   exactness. An empty family gives the empty scheme and the zero category;
   rank zero gives the zero tensor functor. Different ranks on different opens
   and arbitrarily many opens cause no problem. This is an ordinary module
   flatness lemma, strictly a part of the original derived argument, not a
   renamed concentration theorem. Read the complete comparison proof: its
   K-flat counit applies to the resolved complex, exactness is transported along
   the adjunction-uniqueness isomorphism, and the final homology isomorphisms have
   the required direction in every integer degree. Its choices occur inside a
   theorem proof, not in a new definition. Repeated LeanFinder, Loogle and grep
   searches with exact tensor functors and locality terminology, and searched
   the project, upstream module sources, and DAG for existing results. Existing
   `LocallyFreeAffine`/`FiniteDescent` results concern flat sections on affine
   opens, not this sheaf tensor functor; `isZero_restrict_sup` treats a binary
   union, not the arbitrary cover here. No exact duplicate or short proof of
   the remaining flatness lemma was found. The lower theorem's docstring and
   node supply its source and full mathematical proof. Verdict: pass, keep the
   one explicitly documented open lemma.

4. Read the main proof from the conclusion downward: Mathlib's single-degree
   truncation supplies the single object, degree-i homology identifies its
   coefficient, and connectivity plus natural-degree vanishing supplies all
   integer bounds. The explicit supremum contains S by the local hypothesis;
   the private helper proves vanishing on an arbitrary cover by separatedness,
   including the empty cover. No object is chosen from an unproved mere
   existence theorem in a definition. Proof-only imports are plain imports.
   Tested deletion of `QuasicoherentKernel` in a scratch comparison copy: Lean
   then cannot synthesize `PreservesFiniteLimits (restrictFunctor W.ι)`, so the
   import is necessary and retained. The other proof imports provide the
   directly used resolution, vanishing, truncation, and supporting theorems.
   Read `dag/units/sk-thm-picard-perfect.json`: its finite-free local description
   route and its realized fields are untouched. The report now names every old
   direct proof dependency removed, while distinguishing this from closure
   pruning. Verdict: pass; no module is claimed pruned from the closure.

5. Compared each public theorem's literal signature with its node's
   `lean.statement`: all three match. The existing node changes only `proof`,
   `proof_deps`, and `proof_origin`. Its four new steps follow the explicit
   union, flatness/vanishing, integer-degree comparison, and single-object
   identification in Lean. The new comparison node records the actual
   adjunction, K-flat resolution, counit, and homology composition; the flatness
   node records precisely the remaining theorem. Checked sources, dependency
   unions, searches, creation records, blueprint ancestry, module paths, and
   chapter/unit fields of both new nodes. The original blueprint file is absent
   here, so provenance is checked against the original node's recorded source
   paragraph and expanded argument, as disclosed above. Verdict: pass.

Changed only this report: completed the old proof-dependency accounting and
added this independent reading, including the axiom qualification and the
necessary-import test. No Lean proof or statement needed repair.
