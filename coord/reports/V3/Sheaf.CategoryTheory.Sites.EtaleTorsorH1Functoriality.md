## What changed

Proved the body of `CategoryTheory.Sheaf.Torsor.etale_torsor_h1_functoriality`, preserving
its complete signature and existing docstring. Added two proof-only imports for strictly
geometric construction statements, each in its own new module with its own DAG node.
Updated the original node to match the actual Lean argument.

For pullback, the already proved injective-sequence classification represents the torsor
as lifts of a global quotient section. The new geometric fibre comparison supplies the
inverse-image sheaf isomorphism and its action compatibility. The main module itself
proves compatibility of the boundary class, using exact-functor transport of Ext extension
classes, the proved degree-zero pullback formula, and associativity of Ext composition.

For coefficients, the new existence lemma supplies the sheafified orbit torsor. The proof
constructs the natural equivariant map `t ↦ q(t, 0)` from the presentation equations and
applies the already proved `classH1_eq_map_of_equivariant`. No pushout-extension or general
derived delta-functor theorem is needed.

## Proved and sorry left

Original hole closed:
`CategoryTheory.Sheaf.Torsor.etale_torsor_h1_functoriality`
(node `lem-sc-etale-torsor-h1-functoriality`). No sorry remains in the item's module.

Two holes added, both public named theorems with entire proofs `by sorry`:

- `CategoryTheory.Sheaf.Torsor.etale_inverse_image_lifting_torsor`
  (`lem-sc-etale-inverse-image-lifting-torsor`), in
  `Sheaf.CategoryTheory.Sites.EtaleInverseImageLiftingTorsor`.
- `CategoryTheory.Sheaf.Torsor.etale_contracted_product_exists`
  (`lem-sc-etale-contracted-product-exists`), in
  `Sheaf.CategoryTheory.Sites.EtaleContractedProductExists`.

This is a decomposition, not an unconditional proof of the target: one upper hole is
closed and two strictly geometric lower holes are added. Neither lower theorem mentions
H¹, its class map, or the cohomological equality being proved. The main module proves both
cohomological equalities with actual Lean calculations.

All three modules compile locally without warnings. Final server/preflight validation is
performed by the required `deliver3.py --no-push` dry run.

## No longer needed

Removed these five proof imports, and their corresponding direct proof dependencies:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
  (`lem-weil-pbc-cohomology-pullback-functorial`).
- `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`
  (`lem-weil-pbc-pullback-cohomology-long-exact-ladder`).
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
  (`lem-weil-pbc-right-derived-universal-delta-functor`).
- `Sheaf.CategoryTheory.Sites.EtaleTorsorInverseImageExtension`
  (`lem-sc-etale-torsor-inverse-image-extension`).
- `Sheaf.CategoryTheory.Sites.EtaleTorsorPushoutExtension`
  (`lem-sc-etale-torsor-pushout-extension`).

The free-abelian canonical-extension presentation, its inverse-image generator comparison,
and the pushout presentation/identification of canonical extensions are not needed by this
proof. These modules might still be needed elsewhere: this report prunes only this route.
The original four public imports remain unchanged. The degree-zero pullback module remains.
The second reading also removed the redundant direct public import of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance` from the new
inverse-image module: its required declarations are already public through `GlobalSections`.
This does not prune that module from the transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The existing inverse-image extension theorem takes `ExtensionPresentation` as an argument;
it does not construct one. The existing pushout theorem takes the contracted-product
presentation and both extension presentations as arguments; it does not construct them.
These are missing geometric existence interfaces in the planned route, rather than false
statements. The source library already proves general equivariant-map H¹ naturality, which
makes the full pushout-extension argument unnecessary.

Read the Stacks source at https://stacks.math.columbia.edu/tag/03AJ (the torsor of lifts and
canonical classification) and https://stacks.math.columbia.edu/tag/03AH (torsor axioms).
The local literature tex files are absent on this machine. The new arguments specialize
the fibre and quotient constructions described in the existing DAG nodes; their detailed
proofs are explicitly recorded as written by this worker. The unit's statement and steps
are unchanged; its `realized` lists are empty, and this reduction is below the unit level.

Searches used Lean Finder, Loogle, ripgrep, and LeanSearch through the prescribed wrapper.
LeanSearch returned HTTP 500 and is recorded as unavailable, not as a successful no-match
search. No exact geometric construction statement was found in Mathlib or either library
root. Blueprint searches for inverse image torsor, lifting torsor, and contracted product
found no duplicate of either new statement.

## New nodes

`lem-sc-etale-inverse-image-lifting-torsor`: preservation of the fibre of a short exact
sequence over a global section under inverse image, with unit-equivariance. This strictly
geometric statement replaces the stronger full canonical-extension comparison. The proof
uses finite-limit preservation and the underlying-sets/addition/unit comparison for the
abelian inverse image. Edge cases checked: identity f, a trivial torsor, a zero kernel,
and the empty scheme. The middle object need not remain injective; only exactness is used.
Its Lean module is `lean/Sheaf/CategoryTheory/Sites/EtaleInverseImageLiftingTorsor.lean`.

`lem-sc-etale-contracted-product-exists`: existence of a torsor satisfying precisely the
existing contracted-product quotient presentation. Locally, choosing a section t₀ of T
identifies the orbit quotient with G′; hence it is a torsor, and sheafification supplies the
universal property. Edge cases checked: φ=id, φ=0, G′=0, a trivial torsor, and the empty
scheme. With φ=0 the quotient is locally G′; with G′=0 it is the terminal sheaf.
Its Lean module is `lean/Sheaf/CategoryTheory/Sites/EtaleContractedProductExists.lean`.

No definition, existing statement, or target signature changed. No change record is needed.

## Second reading by V3

1. PASS. Diffed every delivered module against the repository. The two supporting modules
   are new; the existing target theorem's signature is byte-for-byte unchanged. Its
   docstring and the four existing public imports are unchanged. No definition or existing
   statement changed, so no change record is required. No open change record names this item.
2. PASS. Compiled all three modules locally without warnings. Scanned every delivered
   source: precisely two `sorry` tokens, each the entire proof of its reported public
   theorem; no hollow definitions or forbidden declarations. Compiled a scratch copy with
   `#print axioms` for all three theorems: each uses only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The original theorem therefore remains conditional on the
   two explicitly open geometric lemmas, not an axiom-free completed target.
3. PASS. Read both split-off statements and their complete docstring arguments against
   the torsor, lifting-sheaf, and contracted-product presentation definitions. The inverse
   image comparison follows from finite-limit preservation and the abelian/set unit
   comparison. Identity pullback recovers the given equivariant isomorphism; zero kernel
   yields the terminal torsor, and the empty scheme causes no exception. The orbit relation
   has the correct minus sign: with a local base point t0 and t=g+ᵥt0, its coordinate is
   h+φ(g). Thus φ=id recovers T, φ=0 yields the trivial G'-torsor, and G'=0 yields the
   terminal sheaf, including on the empty scheme. Both statements are geometric parts of
   the argument and neither asserts its H¹ equality. Independent searches used Lean Finder
   for change of structure group, Loogle for sheafPullback/pullback and Torsor/quotient,
   and ripgrep for orbit, contracted product, lifts, and inverse-image torsor across both
   library roots. Mathlib supplies general finite-limit preservation, but no exact geometric
   statement; the existing extension theorems require presentations not constructed there.
   Neither remaining construction is a short application of a found theorem.
4. PASS. Read the target proof from its conclusion downward. The pullback calculation
   really transports the Ext boundary class and its degree-zero section; the coefficient
   calculation constructs the natural equivariant map q(t,0) and uses the already proved
   upstream classH1 naturality. All five removed direct dependencies are listed under
   No longer needed. The unit sk-prop-ext-invariance has empty realized statement/step lists;
   its statement and all three steps stay untouched. Pruning is below that unit. Removed
   one redundant import from the new inverse-image module, and recompiled the set.
5. PASS. Checked all three node records, their Lean declarations and verbatim signatures,
   sources, chapter/unit, origins, and required new-node fields. Each proof_deps is exactly
   the union of its proof steps' uses. The existing node changes only stage-3-owned fields.
   Added the independent Loogle results to the new nodes and corrected elementary flags
   on steps invoking construction/naturality theorems or sheafification.

Changes made by this reading: removed the redundant TopologicalInvariance import from
EtaleInverseImageLiftingTorsor; supplemented new-node searches; corrected proof-step flags;
expanded this report. The proof bodies and mathematical statements needed no repair.
The existing target docstring records the older canonical-extension route; the actual
shorter route is documented in the updated DAG and this report, leaving that API docstring
unchanged as required. Declaration counts: one original hole closed and two lower holes added (difference -1).
This is a decomposition; the ledger determines progress in the targets' import closure,
including any transitive pruning, against its pinned baselines. The required dry run and delivery
perform the final server compilation and preflight.

Validation: `deliver3.py V3 Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality --no-push`
printed OK after local/server compilation and preflight (review class CODEX for the two
new modules and nodes).
