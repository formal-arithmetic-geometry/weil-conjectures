## What changed

Repair of the landing-tool return: removed the duplicate private theorem
`TopCat.Sheaf.constantSubsheaf_canonical_stalks` from the new source-coordinate
module. Its existing call now resolves to the original theorem imported with
`import all Sheaf.Topology.ConstantSubsheafStalkBound`. Removed the direct
`Mathlib.CategoryTheory.Limits.Connected` import, which only served the deleted
proof. Updated the source-coordinate node to record this existing dependency.
The second-reading section below records the earlier delivery; the repaired
version requires the independent reader to check this replacement.

The unchanged statement `TopCat.Sheaf.constantSubsheaf_quotient_stalk_iso` now has a complete proof from integer coordinates. It chooses an active index, proves its label is b+1, uses the prescribed section value to compute the stalk map on the unit generator, and applies a proved private bijectivity lemma. Two new modules isolate source and quotient coordinates. The source coordinate theorem is proved using canonical constant-sheaf stalk coordinates and the already-proved extension-by-zero germ comparison. The quotient coordinate theorem is the remaining part of steps 3–4, independent of q, for any monomorphism l with zero source stalk. No signatures or definitions of existing declarations changed. No adaptations or change records are needed.

Compilation: all three modules compile together, without errors or warnings, through lcompile.py --all. Edge cases: x in U supplies a genuine active index, so n=0 and U empty give vacuous assertions; b=0 still gives the nonzero label 1; source coordinates require x in V contained in U, excluding empty V. Quotient coordinates hold for arbitrary mono l because its zero source stalk makes the projection an isomorphism.

## Proved and sorry left

Closed the original hole `TopCat.Sheaf.constantSubsheaf_quotient_stalk_iso` (node `lem-sc-constant-subsheaf-quotient-stalk-iso`) by a genuine reduction. Proved the new `TopCat.Sheaf.abelianOpenExtension_integer_germ_coordinates` (node `lem-sc-abelian-open-extension-integer-germ-coordinates`) with no sorry. Added one remaining hole: `TopCat.Sheaf.constantSubsheaf_quotient_germ_coordinates` (node `lem-sc-constant-subsheaf-quotient-germ-coordinates`). This is a decomposition, with one original hole closed and one strictly intermediate hole added, not a claim that the target is axiom-free.

## No longer needed

Removed the duplicate canonical-stalk helper and the source-coordinate module's
direct `Mathlib.CategoryTheory.Limits.Connected` import. The original helper in
`Sheaf.Topology.ConstantSubsheafStalkBound` is now used directly; that module and
its node `lem-sc-constant-subsheaf-stalk-bound` are needed, not pruned.

Removed the item's direct proof imports `Sheaf.Topology.AbelianOpenExtensionByZeroStalks` and `Sheaf.Topology.PresheafModuleStalkFunctor`. The former remains needed transitively by source coordinates; its node `lem-sc-topological-extension-by-zero-stalks` is not globally pruned. The latter and its node `def-weil-pbc-module-stalk` do not supply a proof declaration for this item's concrete abelian-group stalk maps; the definition node stays among statement dependencies. The old proof_deps also contained `def-sc-abelian-open-extension-by-zero` and `def-weil-pbc-constant-sheaf`; both leave the direct proof_deps but remain statement dependencies with their public imports retained. Together with the two nodes named above, this accounts for every old proof dependency removed from the item. No module is claimed globally pruned. New proof imports are only the two coordinate modules and Mathlib's concrete-category bijectivity criterion.

## Where the brief, the DAG or earlier work was wrong

The DAG's module-stalk definition does not supply the cyclic-generator argument or a packaged abelian-sheaf exactness lemma fitting this statement. The missing argument is now a separately stated quotient-coordinate theorem with its full proof in words. The canonical constant-stalk proof was already present privately in ConstantSubsheafStalkBound; the returned delivery duplicated it, which was refused. The repair removes that duplicate and uses the existing theorem through `import all Sheaf.Topology.ConstantSubsheafStalkBound`, preserving its visibility and leaving its module and users unchanged. The unit's statement and route are unchanged. LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle and local/project/Mathlib grep searches were performed.

## New nodes

`lem-sc-abelian-open-extension-integer-germ-coordinates`: proved source coordinates in `Sheaf.Topology.AbelianOpenExtensionIntegerGermCoordinates`, combining the canonical constant-stalk construction with the extension-by-zero germ comparison.

`lem-sc-constant-subsheaf-quotient-germ-coordinates`: the needed intermediate cyclic quotient generator statement, in `Sheaf.Topology.ConstantSubsheafQuotientGermCoordinates`, with one named sorry and a complete natural-language proof. It has no hypothesis or conclusion about q and does not restate the target. No change record: no existing interface changed.

## Earlier second reading (a previous round; superseded)

1. Interfaces: PASS. Compared each delivered module with the repository. The two
coordinate modules are new. Extracted and compared the original theorem signature
byte for byte: identical. Public imports of the existing module are identical;
only proof imports, a proved private helper, and the original proof changed.
No existing definition, statement, visibility, or other module was adapted.
The existing node differs only in proof, proof_deps, and proof_origin.

2. Proofs and axioms: PASS as a decomposition. Compiled all three modules in import
order using lcompile.py --all: no errors or warnings. Compiled scratch copies with
#print axioms for both private helpers and all three public theorems. Source integer
coordinates and both private helpers use only propext, Classical.choice, Quot.sound.
The original theorem and quotient coordinates additionally use sorryAx, exactly as
reported. The only delivered sorry is the named quotient-coordinate theorem.
There are no axioms, unsafe/opaque declarations, foreign implementations, hollow
definitions, or definitions selecting an arbitrary witness of an open theorem.

3. Split statements: PASS. Read both new signatures and the quotient proof docstring
against Stacks 0A38's final paragraph (https://stacks.math.columbia.edu/tag/0A38).
On a one-point space with one active open, the assumptions identify K with the
subgroup (b+1)Z and the quotient with K, so the displayed section has unique integer
coordinates. With multiple active opens, injectivity into the ambient integers
identifies their equal germs; surjectivity of the coproduct map ensures they span.
Inactive opens contribute zero stalks. b=0 gives label 1; n=0, empty U, or empty V
in the source-coordinate theorem cannot satisfy the required point membership.
Arbitrary mono l with zero source stalk gives the same quotient stalk by exactness.
The quotient lemma isolates target coordinates without q or q compatibility; it
is strictly part of the argument, not the target under another name. Its source,
complete proof in words, and matching node are present. Independent LeanFinder,
Loogle, Mathlib grep and project/upstream rg searches using cokernel/generators/
cyclic/zsmul terminology found no exact public replacement. Mathlib already supplies
the germ formulas, monomorphism preservation and general exactness machinery; the
remaining assembly is not a few-minute closure and stays explicitly open.

4. Route and pruning: PASS after report repair. Checked the actual generator choice,
label equality, source coordinates, quotient coordinates, germ-map equation and
integer-coordinate bijectivity argument from the top down. Proof imports are plain
imports; statement imports remain public. Removed dependencies are now all listed,
including those retained as statement dependencies or used transitively. No globally
pruned module is claimed. dag/units/sk-thm-curveestimate.json realizes
thm-sc-proper-cohomology; this item and its splits lie below that unit statement and
change none of its realized route. The result is one old hole closed, one hole
added, hence net zero holes: a decomposition, not an axiom-free proof.

5. Nodes: PASS after metadata repair. The original node's steps and dependencies
match the implemented reduction. New nodes have their source, proof steps,
dependency union, proof origin, searches, creation provenance, blueprint ancestry,
chapter, unit and Lean records. The new source-coordinate lemma is proved, and
its node records the extension-stalk dependency. The quotient-coordinate node
records the remaining planned argument. Both new lean.statement fields now contain
the multiline signatures verbatim.

Changes made by this reader: added the plain source-coordinate proof import to the
open quotient-coordinate module, matching its node's planned dependency; corrected
new-module author attribution to V3; made new-node Lean signatures verbatim and
recorded independent searches; completed the removed-dependency accounting above.
No proof body or existing declaration signature required repair.

## Second reading by V3

1. **Interfaces:** PASS. Compared the delivered target module with the repository version. The target theorem statement is byte-for-byte unchanged; only proof imports, a private helper, and the proof body differ. The two coordinate modules are new and introduce the exact signatures recorded in their nodes. No existing definition or public declaration was adapted.

2. **Proofs and axioms:** PASS as a decomposition. All three modules compile with `lcompile.py --all` without errors or warnings. The target theorem and source-coordinate theorem are proved; the quotient-coordinate theorem is the sole named `sorry`, exactly as listed above. No definitions contain `sorry`, and no forbidden declarations occur. The proof's concrete-category bijectivity argument uses only the permitted foundational axioms, with the open quotient-coordinate theorem accounting for `sorryAx` transitively.

3. **Split statements:** PASS. The quotient-coordinate statement is a genuine intermediate cyclic-generator assertion: it is independent of `q`, has strictly simpler conclusion than the target, and is used to prove bijectivity. The source-coordinate statement is likewise the integer-coordinate property of an extension-by-zero stalk. Both have complete source and proof descriptions and matching DAG nodes; no duplicate public declaration was introduced.

4. **Route and pruning:** PASS. The proof uses the source-coordinate and quotient-coordinate modules, the existing canonical stalk bound transitively, and the concrete bijectivity criterion. The unit route is preserved. Removed direct imports and proof dependencies are recorded in `## No longer needed`; no globally pruned module is claimed.

5. **Nodes:** PASS. The target node's proof and dependencies match the Lean proof, and both new nodes contain the corresponding module, declaration, verbatim signature, source, proof steps, dependency lists, provenance, and creation metadata. No statement or definition change record is required.

Changes made in this second reading: none beyond this review record; the delivered files already compile and satisfy the interface and DAG checks.
