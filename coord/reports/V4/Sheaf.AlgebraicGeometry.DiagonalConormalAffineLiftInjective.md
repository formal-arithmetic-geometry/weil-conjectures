## What changed

Proved `AlgebraicGeometry.diagonalConormal_affine_lift_injective` with its signature,
visibility and docstring unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.DiagonalConormalAffineIdealClassCore` and
`Sheaf.AlgebraicGeometry.DiagonalConormalAffineIdealClassQ`.
The first supplies tensor coordinates and actual kernel-section lifts; the second supplies
an A-linear cotangent equivalence compatible with the pullback unit. The normalization
hypothesis identifies the equivalence on differential generators with D. Mathlib
`CommRingCat.KaehlerDifferential.ext` then identifies the supplied linear map with this
equivalence, giving injectivity. Updated the item's DAG proof and dependencies accordingly.

The module compiled without errors or warnings using lcompile.py. Source checked:
[Stacks 08S2](https://stacks.math.columbia.edu/tag/08S2), final affine calculation, and
[Stacks 01R3](https://stacks.math.columbia.edu/tag/01R3), affine conormal sections.
No separation, nonemptiness, smoothness or finite type assumption was introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.diagonalConormal_affine_lift_injective`
(node `stage3-diagonal-conormal-affine-lift-injective`). No sorry remains in the item's
module, and no holes or declarations were added. The proof uses existing stated
dependencies; their downstream proof obligations are not claimed as closed here.

## No longer needed

No existing imports removed; no module is claimed pruned from the target closure.
The item no longer needs to apply `lem-weil-pbc-diagonal-immersion`,
`lem-weil-pbc-affine-conormal-sections-existence`, or
`lem-pc-module-pullback-adjunction` directly: the existing core and cotangent comparison
carry that affine geometry and unit compatibility. These nodes remain available
transitively and are not globally pruned. `def-sc-diagonal-conormal` remains a statement
and transitive dependency, rather than a direct proof step.
The surjective ideal class map and the affine derivation span theorem are not imported
or used. The affine section comparison, chosen-section theorem and global diagonal
isomorphism are also not used, avoiding their dependency on this item.

## Where the brief, the DAG or earlier work was wrong

The planned geometric calculation has since been exposed by the existing core and Q
modules, so no new statements are necessary. The plan is realized through these
interfaces with a real generator comparison in this module. No mathematical error or
interface change was found. The unit `sk-thm-picard-duality` has no realized statement
or proof steps assigned to this node; its route was not changed.
The local Stacks source path is absent on this machine, so the cited tags were read
online. Searches via msearch.py: Lean Finder returned
`CommRingCat.KaehlerDifferential.ext`; Loogle reported unknown identifier for
`KaehlerDifferential.ext`; grep found Mathlib uses of the categorical extensionality
lemma. Its source signature and proof were read before use.

## Earlier second reading (a previous round; superseded)

Read the delivered module and node. The proof preserves every hypothesis and the exact
injectivity conclusion. The core lemma supplies the ring equivalence, projection identities,
and kernel lifts; the Q lemma supplies the A-linear cotangent equivalence and unit formula.
The normalization equation is applied to the explicitly constructed difference section, and
`CommRingCat.KaehlerDifferential.ext` is applied only to the two maps with the same domain and
codomain. The final `c.injective` is therefore exactly the desired Function.Injective e.
No new theorem, weakened statement, or bypass of a unit-level step was introduced.

The second reader localized the added namespace and notation openings to the proof;
there is no interface change and no change record is needed.


## Second reading by V4

1. **Unchanged statements — pass.** Compared the sole delivered module with the
   repository using diff and checked the theorem signature byte for byte. Its
   hypotheses, conclusion, universe, visibility and docstring are unchanged. No
   definition or target statement changes. The two new imports are proof-only.
2. **Proof and axioms — pass.** Compiled the module and a scratch copy with
   `#print axioms AlgebraicGeometry.diagonalConormal_affine_lift_injective` using
   lcompile.py. No errors or warnings; no sorry or forbidden declaration in the
   delivered module. The axiom output is `propext`, `Classical.choice`, `Quot.sound`
   and inherited `sorryAx`; existing downstream obligations remain open. The
   section lift is used only inside a theorem proof, with no new data definition.
3. **Split statements — pass, none added.** There are no new declarations, modules,
   nodes or holes. Read the existing core and Q comparison statements and checked
   that the hypotheses supplied here match them. For an empty chart, all rings
   and modules are zero; the difference and injectivity argument still apply.
   No separatedness, nonzero-ring or smoothness assumption is used.
4. **Route and pruning — pass.** Read the normalization definition and Mathlib's
   categorical differential extensionality proof. The section of
   `1 ⊗ a - a ⊗ 1` gives precisely the required sign; normalization and the
   comparison unit formula identify the two maps on every differential. Their
   equality gives injectivity of the original map. Independently searched the
   repository for affine diagonal comparisons and Loogle for
   `KaehlerDifferential, Function.Injective`; no shorter applicable theorem was
   found. Both added imports are used. The No longer needed section names all
   four old proof dependencies removed from the direct route. The unit's realized
   statement and step lists are empty and unchanged, so no unit step is bypassed.
5. **DAG agreement — pass.** Parsed the old and delivered node records: only
   `proof`, `proof_deps` and `proof_origin` differ. The three proof steps describe
   the coordinate/lift construction, generator comparison and extensionality as
   written, and the union of their uses equals proof_deps. No new node is needed.

**Second-reading changes.** Localized the additional `CategoryTheory.Limits` and
`TensorProduct` openings inside the proof, restoring the original module-level
openings. Removed the now-unnecessary change record and corrected its report
reference. The mathematical proof was retained. One original hole is closed,
zero holes added, and no module is claimed globally pruned.
