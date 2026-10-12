## What changed

The proof of `AlgebraicGeometry.exists_moduleExtensionByZero_stalk_morphism` now
whiskers the chosen adjunction unit through the slice-site equivalence, module
stalk functor and restriction of scalars, then composes with the restriction-stalk
comparison. `stalkFunctor_map_germ_apply` and that comparison's germ formula give
the required value. The existing signature and public imports are unchanged.
The only added import in the item is the proof-only import
`Sheaf.Algebra.Homology.ModuleRestrictionStalkLinear`.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_moduleExtensionByZero_stalk_morphism` (one
original hole). Its proof depends on the new restriction comparison below.
Added and left: `AlgebraicGeometry.exists_moduleRestrictionStalk_morphism`, in
`Sheaf.Algebra.Homology.ModuleRestrictionStalkLinear`, node
`lem-sc-module-restriction-stalk-linear` (one new hole).
This is a decomposition: one hole closed, one added, net zero. It is not a
complete axiom-free proof of the original item. No sorry remains in the item's
module, and no definition is added. The rejected component theorem from the first
worker is removed, together with its new module and node; it is not delivered.

## No longer needed

None of the original proof dependencies or imports is pruned: the proof still
uses `lem-sc-derived-open-restriction-adjunction-exact` and
`def-pc-module-stalk-functor`. The first worker's undelivered
`Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMorphismComponents` and
`lem-sc-module-extension-by-zero-stalk-morphism-components` were removed as a
restatement, not counted as pruning of the repository.

## Where the brief, the DAG or earlier work was wrong

The first worker's component theorem had exactly the original content: a family
of linear maps, its naturality, and the same germ formula are precisely a natural
transformation with that formula. Packaging this family did not reduce the
mathematical obligation. The earlier report's claim of a strictly simpler split
was wrong. The replacement isolates restriction alone for arbitrary module
sheaves on X, with no extension-by-zero functor or adjunction unit. The actual
unit-induced map and its germ formula are now derived in Lean.

## New nodes

`lem-sc-module-restriction-stalk-linear` states only the natural linear
restriction-stalk comparison, with its germ formula. Its module is
`Sheaf.Algebra.Homology.ModuleRestrictionStalkLinear`. The natural-language proof
constructs the additive comparison from the final neighborhood functor, checks
scalar compatibility on a common neighborhood, and verifies naturality on germs.
It leaves no invertibility obligation and is strictly a part of the original
node's argument. No change record is needed: no existing interface is changed.

## Second reading by R1

1. Compared the item's delivered module with the repository using `diff` and
checked the exact theorem signature: it is byte for byte unchanged. Its original
public imports, universe and visibility remain unchanged. Only a proof-only
import and the proof body changed. The new module has one new public theorem.
2. Both modules compile through `lcompile.py --all` without errors or warnings.
The item contains no sorry; the only new sorry is the entire proof of the named
restriction theorem. There are no axioms, unsafe declarations, opaque shortcuts,
extern declarations or data definitions. Axiom probes allow only propext,
Classical.choice, Quot.sound and sorryAx from open statements.
3. Read the restriction statement clause by clause: X is an arbitrary ringed
space, W an arbitrary open, x any point in W, and F any module sheaf on X. The
scalar map is the inverse of the ring restriction-stalk isomorphism. Its formula
uses every neighborhood in W and every section on its open image. For W empty
there is no hx; for W = X it is ordinary restriction; zero modules and zero rings
need no exception. The germ formula determines every component uniquely, so no
arbitrary witness defines exported data. The docstring gives the construction,
scalar check and naturality proof, and the matching node is present. LeanFinder,
Loogle and grep found the additive comparison and scheme-only comparisons, not
the general linear statement; LeanSearch was unavailable and is recorded as such.
Searched the repository using restriction/stalk variants and inspected its
inverse-image and change-of-rings comparisons: neither states this restriction
comparison for the present functors.
4. The original proof now follows its planned unit-on-stalks route, using the
proved module stalk functor and Mathlib's germ-map formula. The new dependency
isolates only the restriction comparison. All original proof dependencies remain
used, so `No longer needed` is complete. The unit is `sk-thm-picard-duality`;
its realized statement and step arrays are empty, and this below-unit reduction
changes none of its route or records. All original public imports are required
by the item's signature; the new proof import is plain `import`.
5. Updated the original node's proof, proof_deps and proof_origin to match the
whiskering/composition proof, leaving its statement, statement dependencies and
Lean signature untouched. The new node records the precise Lean signature,
source, full proof steps, proof dependency union, search digests, creation and
blueprint ancestry, chapter and unit. Neither an existing definition nor a target
statement changed.

Changed on second reading: removed the equivalent component restatement; added
the genuine restriction-only dependency and categorical/germ reduction; corrected
the report to count the result as a decomposition; repaired the node proof route.
An attempt to close the restriction comparison encountered expensive elaboration
of the slice-equivalence's underlying stalk identification; the delivered named
hole and complete proof description retain that remaining work.

Source check: the new restriction lemma is supported by [Stacks, Section 6.31](https://stacks.math.columbia.edu/tag/009Z), Lemma 6.31.1 (3) and Definition 6.31.2 (4). Corrected its source citation: Tag 01AK concerns exactness of extension by zero, not the restriction comparison. Both explicit `#print axioms` checks returned exactly propext, Classical.choice, Quot.sound and sorryAx.
