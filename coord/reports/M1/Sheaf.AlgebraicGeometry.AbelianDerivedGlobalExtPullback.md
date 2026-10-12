## What changed

Proved `AlgebraicGeometry.Etale.exists_addEquiv_derivedGlobal_ext_pullback` with its original signature. It constructs the source equivalence from the canonical single-complex comparison and the compatible Ext/classical pair supplied by the first new lemma; the target equivalence also uses the exact inverse-image/single-complex isomorphism. Two map equations through classical right-derived base change are combined by cancelling the comparison isomorphisms, then evaluating on an element.

Added `Sheaf.AlgebraicGeometry.SheafHRightDerivedPullback` and `Sheaf.AlgebraicGeometry.DerivedUnitClassicalPullback`. Both are new modules; no existing supporting module is adapted.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.Etale.exists_addEquiv_derivedGlobal_ext_pullback` (one original hole). No sorry remains in the item. Added holes: `AlgebraicGeometry.sheafHRightDerivedIso_pullback` and `AlgebraicGeometry.derivedUnit_classicalPullback` (two new holes). This is a decomposition, not a completed proof of the import closure: one hole closed minus two added gives net −1 before any separately measured pruning. The assembly theorem still depends on `sorryAx` through those two lemmas.

Two new named statements remain `sorry`:

- `AlgebraicGeometry.sheafHRightDerivedIso_pullback`, node `lem-weil-pbc-sheafH-right-derived-pullback`: Ext versus classical derived pullback, with no derived adjunction unit in its conclusion.
- `AlgebraicGeometry.derivedUnit_classicalPullback`, node `lem-weil-pbc-derived-unit-classical-pullback`: derived-unit versus classical derived pullback, with no Ext group or cohomologyMap in its conclusion.

These are distinct proper parts of the original comparison argument, not renamed versions of the original existential theorem. Degree zero, zero sheaves, the empty scheme, identity morphisms, and composition with a nontrivial automorphism of an additive group were checked conceptually: in particular arbitrary choices of additive equivalences cannot satisfy the identity, so the Ext lemma supplies a compatible pair, and the derived lemma uses specified canonical comparisons.

## No longer needed

Removed the direct imports `Sheaf.AlgebraicGeometry.EtaleInverseImageExact` (node `prop-weil-pbc-inverse-image-exact`, retained through the new Ext/classical module) and `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist` (node `prop-weil-pbc-kinjective-resolutions-exist`) from the item. The direct `EtaleSheafHExtDerivedComparison` import is also removed; its module and node remain needed through the Ext/classical lemma. The direct `CohomologyPullbackDerivedUnit` import is replaced by the new derived/classical interface; that module and node are still needed transitively, not pruned globally. The node `def-weil-pbc-cohomology-pullback` is also no longer a direct proof dependency of the item, but remains a dependency of the Ext/classical lemma and its public definition remains used. The nodes `lem-weil-pbc-kinjective-hom-derived` and `lem-weil-pbc-ext-via-injective-resolution` are no longer direct dependencies of the item's assembly but remain dependencies of the new Ext/classical node. No claim is made that these tools leave all targets' closure.

The unbounded/functorial K-injective existence theorem is unnecessary for this bounded-below assembly; the existing chosen injective resolutions in the Ext comparison suffice. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan did not provide a usable public interface for its specified Ext comparison: the comparison theorem gave only `Nonempty` of a natural isomorphism, which does not impose compatibility across different schemes. Its proof's concrete comparison was private. The new Ext/classical lemma therefore asserts existence of two compatible isomorphisms together, with the proof in words specifying their common resolution construction. It does not assert compatibility of arbitrary additive equivalences.

The missing compatibility is factored through the classical right-derived base-change map. Source read: Stacks cohomology.tex Lemma 01F8 (`lemma-functoriality`), equations 01F9 and 01FA, and Remark 01FB (`remark-explain-arrow`), at the local source copy. The three search kinds were run; LeanSearch was unavailable with HTTP 500 and is recorded as unavailable. LeanFinder and Loogle found no exact map comparison, and Mathlib grep found no such statement. Blueprint searches for Ext comparison and derived unit found no duplicate of either new statement.

An initial visibility-only adaptation was removed after the delivery checker required a supporting-module claim. The final delivery does not adapt another existing module or change any definition or statement.

## New nodes

`lem-weil-pbc-sheafH-right-derived-pullback` states the compatibility of a pair of compatible Ext/classical isomorphisms with classical derived base change. Its proof plan computes both sides on the same resolutions and identifies cocycles by evaluation at 1.

`lem-weil-pbc-derived-unit-classical-pullback` states the comparison of the derived-unit map with classical derived base change through canonical single-complex isomorphisms. Its proof plan uses the existing derived-unit description and the universal characterization of base change.

No change record is needed: no existing interface is changed.

## Second reading by M1

1. **Unchanged interfaces: pass.** Read the repository/sandbox diff of every delivered
   module. Only `AbelianDerivedGlobalExtPullback` existed in the repository; its theorem
   signature is byte-for-byte identical, as checked from `theorem` through the final
   conclusion before `:= by`. Its docstring is unchanged. There are no changed definitions,
   adapted existing supporting modules, or change records. The two other modules contain
   only new theorems.
2. **Lean proof and trust: pass as a decomposition.** Compiled all three modules locally
   in import order. Compiled separate scratch copies with `#print axioms` for all three
   declarations: each uses only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The assembly has no local hole; `sorryAx` comes from the two explicitly listed new
   named theorems. Each new theorem has exactly `:= by sorry`, a source/proof docstring,
   and its matching node. No definition, axiom, unsafe, opaque, implementation override,
   or foreign-code escape is introduced. The assembly cancels the Ext comparisons in
   the correct direction, then evaluates the morphism equality at `x`.
3. **Split statements and searches: pass after one prose correction.** Read Stacks
   `cohomology.tex`, `lemma-functoriality` (01F8),
   `equation-functorial-derived` (01F9), `equation-functorial` (01FA), and
   `remark-explain-arrow` (01FB), plus `sites-cohomology.tex`,
   `remark-before-Leray` (08J6). Read the actual `cohomologyMap` and
   `cohomologyMap_apply` definitions: exact inverse image of an Ext class is precomposed
   with the inverse constant-sheaf comparison. Under evaluation at 1 this gives the
   section-unit map with the same direction as `e` in both new lemmas. Exact inverse
   image preserves the source resolution; the bounded-below injective target resolution
   is K-injective, giving the comparison map and its homotopy uniqueness. The Ext
   lemma is existential, so it does not assume arbitrary isomorphisms are compatible.
   The derived lemma has specified canonical comparisons, no Ext group and no choice
   of an additive equivalence. Degree zero gives the ordinary section map; zero sheaves
   and the empty scheme give zero groups; identity morphisms give identity maps through
   the canonical comparisons. A nontrivial automorphism of a comparison group is not
   imposed by either statement. These are different, strictly partial map comparisons,
   assembled in the original module, rather than a renaming of its existential theorem.
   Repeated LeanFinder searches with “constant integer sheaf”, “natural transformation”,
   and “identity exact functor”; Loogle for `rightDerivedBaseChange` (unknown upstream
   identifier); and Mathlib grep for single-complex/base-change comparisons. Also searched
   `lean/Sheaf`, upstream Lean, and DAG node statements for Ext/global-sections and
   classical/derived pullback comparisons. No duplicate was found. The proven
   `nonempty_sheafH_extDerivedIso` provides only a within-scheme natural isomorphism;
   its concrete comparison is private, and its public conclusion supplies no
   across-scheme pullback equation. The generic `rightDerivedBaseChange_app` gives the
   transport formula but does not identify its identity-functor derived component with
   the derived adjunction unit; closing that comparison requires further coherence work,
   not a few-line application. Corrected the new Ext node's statement to assert the
   existence Lean actually states; the common resolution construction is its proof,
   not an additional property of its witnesses.
4. **Top-down route and pruning: pass.** Read the original proof dependencies and the
   full `sk-thm-p1.realized` route. This item is below its realized unit statements and
   steps, and the strict-local exchange step remains on the route. The two comparison
   lemmas preserve the resolution/derived-unit argument. All seven old direct proof
   dependencies are accounted for in `No longer needed`: none remains direct, six are
   retained as supporting dependencies, and the unbounded K-injective existence result
   is unnecessary. This is direct dependency pruning; no global module-pruning or
   positive net progress is claimed. Public imports in all delivered files supply
   signatures; imports of supporting Sheaf theorems are plain `import`. Restored
   `EtaleInverseImageExact` as a plain proof import in the new Ext/classical module,
   matching that new node's planned proof dependency.
5. **DAG/Lean agreement: pass.** Compared each node's recorded Lean signature against
   its file, including the two explicit formulas for `e`, the inverse-image single
   comparison, and the classical base-change components. The original node changes
   only `proof`, `proof_deps`, and `proof_origin`; its two assembly steps name precisely
   the two new lemmas used in Lean. New nodes carry their source, searches, creation,
   blueprint ancestor, chapter/unit, and complete Lean records. Read the statements of
   the Ext-resolution and K-injective-comparison Mathlib leaves and the exactness and
   derived-unit nodes: they provide the ingredients their proof plans cite. The new
   Ext node's construction wording has been aligned with the existential Lean statement.

Second reading changed the new Ext module's planned exactness import, the new Ext node's
prose statement, and the report's hole accounting and complete direct-dependency pruning
list. It changed no existing declaration signature and no assembly proof. One original
hole is closed syntactically and two genuinely smaller named holes are added: decomposition,
net −1 holes, with no claim of a sorry-free import closure.
