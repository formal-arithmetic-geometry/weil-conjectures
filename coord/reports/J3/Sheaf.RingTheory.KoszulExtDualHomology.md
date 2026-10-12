## What changed

Second reading rejected the first worker's split. Its scalar-compatible additive
comparison is equivalent to the original linear-equivalence conclusion, and its
separate additive-comparison theorem was unused. Removed
`KoszulExtDualHomologyAux.lean` and both provisional `new-koszul-ext-*` nodes.

The target module now eliminates `exists_koszul_projective_resolution`, substitutes
its equality of chain complexes, and applies the generic
`ProjectiveResolution.exists_ext_signed_dual_homology_equiv`. The component
isomorphisms are identities; their differential compatibility is proved by
unfolding `koszulDualComplex` and `koszulDualBoundary`. These two new statements
are in their own modules, with complete source-based proof docstrings and nodes.
Only proof imports were added to the existing module. No existing signature,
visibility, definition, or target statement changed. No change record is needed.

## Proved and sorry left

Closed the original hole in
`ExteriorAlgebra.exists_koszul_ext_dual_homology_equiv`
(node `lem-sc-koszul-ext-dual-homology`) by the stated reduction.

Added exactly two named holes:
- `ExteriorAlgebra.exists_koszul_projective_resolution`
  (node `new-j3-koszul-projective-resolution`): only the Koszul augmentation,
  quasi-isomorphism and projectivity; no Ext or dual complex.
- `CategoryTheory.ProjectiveResolution.exists_ext_signed_dual_homology_equiv`
  (node `new-j3-ext-signed-dual-homology`): only the generic comparison once a
  projective resolution and its signed dual have already been supplied; no ideal,
  Koszul sequence, regularity, augmentation construction, or exterior basis.

This is a decomposition, not a completed proof: one original hole closed and two
new holes added, net minus one hole relative to the repository item. The target
still depends on `sorryAx`. The provisional two holes from the first worker were
removed, rather than delivered. None of the new holes could be closed by the
already packaged pinned-library comparisons alone: the Koszul augmentation and
the module-valued quotient/component comparison are still to be implemented.

All three modules compile cleanly with `lcompile.py --all`. Scratch copies with
`#print axioms` for all three declarations report only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`.

## No longer needed

No repository dependency module is pruned. All four old proof dependencies remain
used transitively: the Koszul complex, regularity, and exterior-power basis feed
the projective-resolution node, and the signed dual definition is used directly
by the target's differential calculation. The target's direct `proof_deps` now
names the two new nodes and `def-sc-koszul-dual-complex`.

The removed Aux import and its two nodes belonged only to the rejected provisional
sandbox version. Removed an unused proof import of
`Mathlib.CategoryTheory.Abelian.Projective.Ext` from the generic statement module;
its future proof can import that comparison API when implemented. Existing public
imports are needed for the unchanged target signature and its instances.

## Where the brief, the DAG or earlier work was wrong

The first worker did not decompose the argument: existence of a scalar-compatible
additive equivalence contains the entire original conclusion. The additive-only
hole was unused. Neither new node had a self-contained mathematical statement with
its hypotheses, and the target DAG node did not record the proposed proof.
Those faults are repaired by splitting the two distinct steps already present in
the original plan, retaining the plan's finite free resolution route.

Searches were run afresh with different wording through `msearch.py`: LeanSearch
was unavailable (recorded as such), LeanFinder found the standard projective
resolution and Ext/cohomology-class primitives, Loogle found the component
`toSingleEquiv`, and grep checked the pinned Mathlib sources. Loogle's current
index also returned `extLinearEquivCohomologyClass`, but that declaration and the
corresponding scalar quotient API are absent from this pinned Mathlib version.
The old `ProjectiveResolution.isoExt` computes the distinct left-derived functor
`Ext R C n`, not this statement's `CategoryTheory.Abelian.Ext`; it cannot be used
as the required equivalence without a further comparison.
Repository and upstream source searches found no existing Koszul projective
resolution or the generic signed module-valued homology comparison.

## New nodes

`new-j3-koszul-projective-resolution`, module
`Sheaf.RingTheory.KoszulProjectiveResolution`, records the original plan's first
step with its old dependencies: quotient augmentation, positive homology
vanishing, and finite exterior bases. It does not assert any Ext comparison.

`new-j3-ext-signed-dual-homology`, module
`Sheaf.CategoryTheory.ExtSignedDualHomology`, records the second step independently
of Koszul data. It requires actual degreewise isomorphisms and an explicit signed
differential compatibility, rather than asserting that a desired comparison
exists without those inputs. Its proof specifies the maps on cycles, boundaries,
and scalars using the pinned Mathlib comparison primitives.

## Second reading by J3

1. Compared the complete original and delivered target module with `diff` and
   checked its declaration header verbatim. All original hypotheses, universes,
   names, visibility and the linear-equivalence conclusion are byte-for-byte
   unchanged. There are no delivered definitions or statement changes.
2. Compiled every module locally in import order. There are no compiler errors
   or warnings and no forbidden declaration forms. The only delivered sorries
   are exactly the two named theorems above. Scratch axiom probes for all three
   declarations show only the permitted three axioms and those unresolved holes.
   No data definition is selected from an existence theorem: P is eliminated
   inside a theorem proving a proposition, and the local resolution record is
   rebuilt explicitly from its fields with the prescribed Koszul complex.
3. Read both new statements against Stacks 0BQZ's finite free total-Hom argument,
   plus the actual pinned Mathlib `extAddEquivCohomologyClass`, `extMk_surjective`,
   `extMk_comp_mk₀`, `Ext.smul_eq_comp_mk₀`, and `Cochain.toSingleEquiv` formulas. The resolution statement is valid also
   for r=0, where I=0 and the augmentation is an isomorphism, and for I=top,
   where the quotient is zero. The generic statement is valid for n=0, with
   no incoming boundary, for zero modules and for characteristic two, where the
   sign is one. Its docstring gives explicit inverse maps on cycle classes and
   identifies boundaries and scalar multiplication. Fresh searches found no
   exact pinned-library or upstream replacement. Both are separate parts of
   the argument; the rejected scalar-compatible restatement is gone.
4. Followed the two steps from the target downward. Kept the finite free Koszul
   resolution route, reused the existing dual-complex definition, and supplied
   the actual differential compatibility proof. Inspected
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step arrays
   are empty, and this item is a supporting node, so no realized unit node is
   bypassed. The old basis and regularity dependencies remain in the new
   resolution node; no old dependency becomes unreachable by this delivery.
5. Read all three delivered node records against the final Lean modules. The
   existing node's proof and dependencies now describe the actual reduction;
   its statement and all protected fields stay unchanged. The two new nodes
   have self-contained statements, complete Lean records, the item's chapter
   and unit, provenance, and genuine logged searches; their proof_deps are the
   union of their proof steps' uses. The generic node uses existing Mathlib
   primitives directly and its elementary steps describe the component and
   quotient computations rather than hiding a second Koszul theorem.

Changed: replaced the equivalent-restatement split and unused additive hole with
resolution and generic signed-dual comparison statements, wrote a genuine target
reduction, corrected the target DAG route, completed the new nodes and proof
accounts, removed the unused import, and corrected the hole/progress accounting.
