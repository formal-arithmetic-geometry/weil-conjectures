## What changed

Proved `AlgebraicGeometry.exists_open_generic_geometric_irreducibility_shrink`
with its signature and visibility unchanged. The proof constructs an affine base
neighbourhood and an affine source chart meeting the generic fibre, proves the
chart generic fibre geometrically irreducible using Mathlib's open-immersion
instance, intersects two generic neighbourhoods, and transfers irreducibility to
every geometric fibre by taking the closure of a continuous dense image.

Two proof-only imports were added: `GenericOpenGeometricFibreDensity` and
`AffineSourceGeometricIrreducibilityShrink`. Their two statements isolate the
fibre-density shrinking argument and the affine algebra argument of Stacks 0559.
The parent node's proof and dependencies now follow the Lean proof. No existing
statement, definition, public import, or downstream module was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_open_generic_geometric_irreducibility_shrink`
(node `lem-sbc-generic-geometric-irreducibility-shrink`). Its module has no sorry.

Added exactly two public named theorem holes, each the entire proof in its own
module, with source and complete proof in words:

- `AlgebraicGeometry.exists_open_geometric_fibre_dense_of_open`
  (`lem-sbc-generic-open-geometric-fibre-density`): density of an existing open
  in all geometric fibres, rather than irreducibility of those fibres.
- `AlgebraicGeometry.exists_open_affine_source_geometric_irreducibility_shrink`
  (`lem-sbc-affine-source-geometric-irreducibility-shrink`): the affine source
  case with image inside an affine base chart. This carries the remaining
  field-extension and hypersurface algebra argument, rather than reducing an
  arbitrary source to the affine case.

This is a decomposition: one upper hole closed and two lower holes added, net -1,
not a claim of a sorry-free proof of the geometric shrinking theorem.

All three modules compile through the launcher in import order. Edge cases were
checked from the statements: an empty source is excluded by geometric generic
irreducibility; nonreduced and nonseparated schemes remain allowed; field tests
quantify over arbitrary extensions; zero-dimensional and purely inseparable
examples are covered by the affine proof. The affine chart inclusion into an
arbitrary source is not assumed quasi-compact: the affine-source theorem uses
its factorization through an affine target open, where finite type follows from
local finite type and affineness. No data is defined using an unproved existence
statement; the chart witnesses are eliminated inside a proposition proof.

## No longer needed

None. No original imports were removed and the parent had no named proof
dependencies to prune. Both new proof imports are used. The unit record has no
realized node for this theorem; the slicing unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The parent node was marked split with four non-elementary steps but no named
proof dependencies; its Tag 054X and affine algebra arguments had no Lean
statements to apply. This delivery supplies two proper intermediate statements
and proves their combination, including the affine chart construction.

The existing docstring is retained unchanged, while the updated node describes
the actual proof. No mathematical statement error was found. Mathlib searches
found only generic-point, dominance, and integral-space results; LeanSearch
returned an internal server error and is recorded as unavailable. Stacks Tags
0559, 054X, 0557, and the field-extension openness reference were read online.
Blueprint searches for nowhere density and absolute irreducibility found no
matching imported node. The ancestor script did not follow this created module
item, so the new nodes retain the parent node's recorded ancestor `sbc-lem-slicing`.

## New nodes

`lem-sbc-generic-open-geometric-fibre-density`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-generic-open-geometric-fibre-density.json`,
states geometric fibre density for a source open with geometrically irreducible
generic fibre (Stacks 054X). Its Lean module is
`Sheaf.AlgebraicGeometry.GenericOpenGeometricFibreDensity`.

`lem-sbc-affine-source-geometric-irreducibility-shrink`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-affine-source-geometric-irreducibility-shrink.json`,
states the affine source case with affine target image (Stacks 0559, second
proof; 0557). Its Lean module is
`Sheaf.AlgebraicGeometry.AffineSourceGeometricIrreducibilityShrink`.

No change records are needed because all existing interfaces are unchanged.

## Second reading by N1

1. **Interfaces — pass.** Compared the existing module with the repository using
   `diff -u`: only two plain proof imports and the theorem body changed. Its
   signature, visibility, original public imports, and docstring are byte for byte
   unchanged. The two other modules are new. The existing node changes only
   `proof`, `proof_deps`, and `proof_origin`; no target or definition changes.
2. **Proof and axioms — pass as a decomposition.** Compiled all three modules in
   import order through `lcompile.py`, without errors or warnings. Read every line
   of the chart construction, the two pullback maps, and the dense-image closure
   proof. There are exactly the two reported named theorem sorries and no data
   definitions or forbidden declarations. Scratch-copy `#print axioms` probes for
   all three declarations show only `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx`. The parent remains dependent on the two open statements.
3. **Split statements — pass.** Read both docstrings and their nodes against
   [Stacks 054X](https://stacks.math.columbia.edu/tag/054X),
   [0559](https://stacks.math.columbia.edu/tag/0559), and
   [0557](https://stacks.math.columbia.edu/tag/0557). Density is a separate
   conclusion; the affine statement restricts the source and its base image,
   allowing a real affine algebra proof. Neither is a renamed copy of the parent.
   Nonemptiness excludes empty generic charts; W=X gives the identity-density
   case; over a field the assertions are immediate. Nilpotent bases are handled
   by reduction, finite purely inseparable extensions by universal
   homeomorphisms, and arbitrary residue-field extensions by universally open
   field-base-change projections. The affine-base factorization is finite type
   without assuming that its inclusion into T is quasi-compact. New searches with
   different wording (nowhere-dense closed generic fibre; localization of an
   absolutely irreducible algebra), Loogle, and grep found no replacement.
   Loogle did not recognize the geometry identifier; its failure was not treated
   as evidence of absence. Direct searches in Sheaf and upstream source found
   related smooth-fibre results, which require hypotheses unavailable here.
   Neither remaining algebraic geometry argument can be closed in a few minutes
   from the available declarations.
4. **Route and pruning — pass.** The parent first uses Mathlib to construct the
   affine chart and prove its geometric generic irreducibility, then uses the
   two stated intermediate results, and concludes with Mathlib topology. Both
   proof imports are necessary. The old parent `proof_deps` was empty, so there
   is nothing to list as pruned. The unit `sk-prop-normal-form` has empty realized
   statement and step lists; this reduction changes no unit route.
5. **DAG — pass after import repair.** Verified every Lean signature against its
   node's verbatim `lean.statement` and every `proof_deps` against the union of
   step uses. New nodes contain source, proof in words, search records, creation,
   blueprint, chapter, unit, and Lean attachment fields. The parent's four steps
   match the actual chart/density/affine/closure proof.

Second-reading changes: added plain proof-dependency imports to the two new
unfinished modules, as required by the project's plan-import rule: density
imports `GenericFlatFinitePresentation`; the affine case imports that module
and `GenericOpenGeometricFibreDensity`. These expose no new public interface.
Added this review and its independent search/axiom evidence. No proof or
statement required repair, no further hole was closed, and no node was pruned.
The final count remains one original hole closed, two holes added, net -1: a
verified decomposition, not a sorry-free proof.
