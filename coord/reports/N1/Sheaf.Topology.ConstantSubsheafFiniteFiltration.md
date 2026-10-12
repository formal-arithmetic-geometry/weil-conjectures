## What changed

Repair of the landing return for reviewed head 3eb8f7cfe: the reviewer passed the
proof, but the landing timed out waiting for the shared merge lock. No proof defect
was reported. Rebuilt the delivery on current sheaf-dag through deliver3.py, with
fresh local and server compilation and preflight checks; this worker performs only
the dry run and leaves pushing to the second reader.

Proved `TopCat.Sheaf.constantSubsheaf_finite_filtration` by induction on a uniform bound for the nonnegative generators of the integer stalk images. The original theorem signature and docstring are unchanged. A proved private helper handles the zero bound using stalk monicity and the zero-stalk criterion, and handles a successor bound by appending one stage with `Fin.snoc`. The proof transports all arrows by explicit isomorphisms, proves monicity, and transports cokernels with `cokernel.mapIso`; it supplies every short-exactness, compact-open, initial-zero, and terminal-isomorphism witness.

Added two modules with source-documented intermediate statements: `Sheaf.Topology.ConstantSubsheafStalkBound` (finite generation implies a uniform stalk bound) and `Sheaf.Topology.ConstantSubsheafPeelLayer` (one layer decreases that bound while retaining finite generation and gives the quotient presentation). Neither states a finite filtration. The original module combines them by genuine natural-number induction; the layer theorem cannot replace that induction by an application.

Added proof-only imports for these two modules, finite tuples, and abelian-group zero/monicity facts. The second reading replaces the original public stalk-results import by a public import of its extension-by-zero definitions and removes the unused direct stalk-results import. Locally disable the unused-existential-binder linter for the original declaration, whose signature must remain unchanged. No definitions, target statements, or other existing declarations were changed. Updated the parent's proof route and added matching nodes for the two intermediate statements. Local compilation of all three modules is clean.

## Proved and sorry left

Proved the original one sorry: `TopCat.Sheaf.constantSubsheaf_finite_filtration`, node `lem-sc-constant-subsheaf-finite-filtration`. Its private induction helper is also fully proved.

Also proved `TopCat.Sheaf.constantSubsheaf_stalk_bound` and its four private helpers. The bound uses finite ranges of locally constant functions on compact generating opens, preservation of epimorphisms and coproducts by stalks, and cyclicity of integer subgroups. It requires neither gcd closure nor compact intersections.

Exactly one sorry remains in the delivery, a new public theorem with proof exactly `:= by sorry`:

- `TopCat.Sheaf.constantSubsheaf_peel_layer`, node `lem-sc-constant-subsheaf-peel-layer`, in `Sheaf.Topology.ConstantSubsheafPeelLayer`.

These are reductions, so the original theorem still transitively depends on the layer sorry. Its docstring gives the complete normalization/gcd/gluing argument and their Stacks 0A38 source places.

Edge cases checked: the empty generating family gives bound zero; an empty space has vacuously zero stalks; a zero-bound sheaf is handled by the actual Lean proof; at a one-point space the layer is either zero or `(b+1)Z` and its presentation is respectively identity-to-zero or zero-to-`Z`; disjoint opens with values 2 and 3 use gluing on W and V, not a nonexistent section 3 of K on all of U; an absent layer allows L=K and U=V; arbitrary integer stalk identifications differ from canonical ones by signs and preserve all subgroups aZ. Intersections used in gcd closure are nonempty finite-index intersections, so compactness of X itself is never assumed.

## No longer needed

Removed redundant proof-only imports `Mathlib.CategoryTheory.Limits.IsConnected` and `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` from the bound module; all modules still compile. No existing DAG node is globally pruned. The parent's direct proof dependencies on `def-weil-pbc-constant-sheaf`, `lem-sc-topological-extension-by-zero-stalks`, and `lem-sc-abelian-sheaf-short-exact-stalkwise` move into the intermediate statements' proofs and plans; they remain necessary downstream, rather than being bypassed. The extension-by-zero definitions remain public; the unused direct import of Sheaf.Topology.AbelianOpenExtensionByZeroStalks is removed from the filtration module and retained as a proof-only import in the bound module. Proof-only imports of connected colimits, local surjectivity, locally constant functions, integer subgroup cyclicity, and extension-by-zero stalks support the proved bound.

Deletion and relabelling of repeated stages in the old final step are unnecessary: the Lean statement requires monic arrows, not strict inclusions. The proof keeps zero quotient layers, which are already permitted in the source's integer-indexed construction.

## Where the brief, the DAG or earlier work was wrong

The DAG called normalization, gcd closure, gluing, and the filtration construction elementary without stating the needed Lean interfaces. Existing constant-sheaf and extension-stalk declarations do not themselves construct that filtration. The delivery exposes the bound and one-layer construction as separate nontrivial obligations rather than moving the whole theorem under another name.

The original docstring is preserved, including its corrected gluing argument. Its last deletion step is stronger than needed by its Lean statement. The compact-open finite-generation hypothesis is retained for the smaller subsheaf in the layer lemma: a stalk bound alone would not guarantee compact generator loci.

The cited `literature/stacks-project/cohomology.tex` is absent from this local read-only mirror. Read the canonical source at https://stacks.math.columbia.edu/tag/0A38 and the parent node's prior review instead. LeanFinder and source grep found no exact filtration, bound, or layer theorem; LeanSearch returned HTTP 500 and is honestly recorded as unavailable. Loogle confirmed the zero-stalk criterion used in the base case. Blueprint searches for the finite filtration and positive stalk generators found no duplicate.

## New nodes

`lem-sc-constant-subsheaf-stalk-bound` formalizes the proved uniform integer bound, without compact-intersection assumptions or any filtration. It cites the constant-sheaf, extension-by-zero, and stalk notions, the extension-stalk theorem, and the Mathlib leaves for sheafification stalks and local surjectivity, and its source is the first paragraph of Stacks 0A38.

`lem-sc-constant-subsheaf-peel-layer` formalizes one gcd-closed threshold layer with bound decreased from b+1 to b and finite generation preserved. It supplies one short-exact quotient presentation, without induction or any finite filtration. It retains the original stalk and short-exactness lemmas in its proof plan. Both nodes stay in `sec-curve-estimates`, unit `sk-thm-curveestimate`, and serve the finite-filtration clause of the original blueprint ancestor. No unit statement or realized step is bypassed. The second reading adds `coord/changes/constantSubsheaf_finite_filtration-imports.md` for import visibility; no existing statement or definition changes.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered original module with the repository by diff and separately checked the existing theorem signature byte for byte: identical. No existing definition or statement changed. The import visibility repair has its own change record. The two added modules contain new intermediate statements only.
2. Compiled all three modules locally without warnings or errors. Source inspection found exactly one sorry, the named public layer theorem, and no forbidden declarations or hollow definitions. Scratch-copy `#print axioms` checks cover the original theorem, its private induction helper, the bound theorem and all four bound helpers, and the layer theorem. The bound and all its helpers use only propext, Classical.choice and Quot.sound. The induction and final theorem additionally use sorryAx from the layer; the layer itself uses sorryAx. This is a reduction, not a completed target proof.
3. Read the layer statement and its complete docstring argument against [Stacks 0A38](https://stacks.math.columbia.edu/tag/0A38). It is true and strictly one step of the argument: it constructs L and a quotient presentation, with bound b, but no filtration. Checked zero sheaves, empty spaces and generator families, one-point aZ (a=b+1 gives L=0; a<=b permits L=K), absent layers, and opens carrying 2 and 3 with a gcd-1 overlap. A stalk-coordinate change is multiplication by a sign, preserving aZ. New LeanFinder search for “integer subsheaf compact open generators quotient maximal stalk layer” found only module generators and scheme localization results; Loogle checked integer subgroup cyclicity; source searches with subsheaf/integer/constant/stalk/bound found no duplicate bound or layer result. The open layer requires substantial normalization, subobject and gluing formalization and cannot be closed in a short repair.
4. Read the zero case and every Fin.snoc/Fin.lastCases transport in the induction: monicity, old and new cokernels, short-exact complexes, compact opens, zero initial stage and terminal isomorphism are supplied. The bound proof uses existing Mathlib stalk/sheafification, locally constant finite-range, coproduct and cyclicity results. No shorter proved filtration route was found. All proof-only imports are plain imports after the repair. The old direct dependencies on the constant-sheaf definition, extension stalks and stalkwise short exactness are all listed under No longer needed and retained downstream in the intermediate nodes; none is globally pruned. The unit sk-thm-curveestimate still realizes thm-sc-proper-cohomology and has no realized steps to bypass; no unit record was changed.
5. Read all three node records against the Lean. Each proof_deps equals the union of the proof-step uses. The parent records the actual bound/induction/layer route; the bound records its proved route, and the open layer records its literature proof plan. Both new nodes have source, searches, created, blueprint ancestry, chapter, unit and verbatim Lean-statement records. No node statement has changed.

Changed the original module's import visibility as described above, with change record `coord/changes/constantSubsheaf_finite_filtration-imports.md`. The sole direct importer, Sheaf.Topology.NoetherianExtensionByZeroReduction, already imports the stalk module publicly, so it needs no adaptation. Clarified the layer's docstring and node proof to explicitly discard zero sections before flipping signs and to use nonempty sets of indices for finite intersections, so the argument never assumes X itself compact. No proof term required repair. Local scratch axiom checks passed; delivery verification follows through deliver3.py.


## Earlier second reading (a previous round; superseded)

This is a fresh independent reading of the delivered files, not an adoption of the
previous round's review above.

1. **Interface preservation: pass.** Read the complete repository/sandbox diff of
   ConstantSubsheafFiniteFiltration. A separate byte comparison confirms that the
   existing theorem signature, from its name through its return type, is identical.
   Its docstring is unchanged. The only visible import change is covered by
   coord/changes/constantSubsheaf_finite_filtration-imports.md. Rechecked the sole
   direct importer, NoetherianExtensionByZeroReduction: it already publicly imports
   AbelianOpenExtensionByZeroStalks. No target, existing definition or statement changes.
2. **Proof and trust: pass as a reduction.** Fresh lcompile.py --all compiled all three
   delivered modules cleanly (3.2, 7.0 and 5.8 seconds). Read every proof, including the
   canonical-stalk colimit comparison, local-surjectivity argument, bounded nonzero
   coproduct component and cyclic subgroup calculation. Independently compiled scratch
   copies with #print axioms for every theorem, including all five private helpers.
   The bound and its four helpers have only propext, Classical.choice and Quot.sound
   (the integer-hom helper uses only propext and Quot.sound). The filtration helper,
   final theorem and layer additionally have sorryAx. Source scan finds exactly one
   sorry: the named public constantSubsheaf_peel_layer. No forbidden declaration or
   hollow definition occurs. Thus the parent proof body is closed, but its mathematical
   obligation remains open through the layer; no axiom-free target closure is claimed.
3. **Intermediate statements: pass.** Read Stacks 0A38 at
   https://stacks.math.columbia.edu/tag/0A38, especially its normalization, gcd and
   filtration paragraphs. The bound is a strict preliminary fact and is now proved.
   The remaining layer has no filtration conclusion and removes only one threshold;
   natural-number induction is still required. Its docstring supplies the source and
   full argument. On V a small generator forces the attained gcd to be at most b,
   hence L_x=K_x; on U minus V all surviving values are b+1, and outside U both
   stalks vanish. Zero generators must be discarded and intersections have nonempty
   index sets, as the delivered docstring explicitly requires. Tested an empty space,
   no generators, b=0, a one-point subgroup aZ, an absent top layer, and two opens
   carrying 2 and 3 with a nonempty overlap. The gcd-1 overlap lies in V and kills
   the quotient there, so gluing works even though 3 need not be a section of K
   over all of U. Arbitrary stalk coordinates differ from canonical coordinates by
   signs and do not change aZ. Fresh LeanFinder query "integer valued sheaf subobject
   finite compact supports successive quotients" returned condensed/module finiteness
   and scheme localization results, no layer or filtration theorem. Fresh Loogle
   Int.subgroup_cyclic confirms the elementary subgroup input; launcher grep for
   integer.*(filtration|subsheaf)|stalk.*bound and independent rg of both library roots
   found no replacement. Formalizing the open layer requires the normalization,
   subobject and gluing constructions and is not a short repair.
4. **Top-down route and pruning: pass.** Checked the zero-bound monicity argument,
   Fin.snoc endpoints, all Fin.lastCases branches, arrow isomorphisms and cokernel.mapIso
   directions. They construct exactly the unchanged witnesses. Each plain import
   serves the proof; public imports supply the signatures and abelian instances.
   Compared the old proof_deps against No longer needed: all three old dependencies
   are accounted for and survive in intermediate proofs/plans. None is globally pruned.
   Read dag/units/sk-thm-curveestimate.json: its realized statement remains
   thm-sc-proper-cohomology and its realized steps are empty. This subsidiary reduction
   neither changes that route nor bypasses a unit realization. No shorter proved
   library route was found.
5. **DAG agreement: pass.** Read all three node records beside the Lean. Programmatically
   checked each proof_deps against the union of its proof-step uses, and each stored
   Lean statement against the actual whitespace-normalized declaration. All agree.
   The parent records the actual bound/base/peel/append argument; the bound records
   its proved finite-range route; the layer records its open literature construction.
   Both new nodes have source, search results (including honest service failures),
   created, blueprint ancestry, chapter, unit and full Lean records. Existing node
   statements are unchanged.

Changes in this reading: appended this independent review and ran fresh compilation,
search and axiom checks. No proof or metadata repair was needed. Scratch axiom copies
remain only under scratchpad and are excluded from delivery. The earlier round's
import visibility repair and change record are retained. Delivery dry run and push
are performed next through deliver3.py.

## Earlier second reading (a previous round; superseded)

Fresh independent reading of the current delivery after the merge-lock timeout.

1. Compared the full existing-module diff and checked its theorem signature byte
   for byte against the read-only repository: unchanged. Its docstring is unchanged.
   The sole public-import replacement has the existing change record; the only direct
   importer, NoetherianExtensionByZeroReduction, already publicly imports the stalk
   module. No existing definition, statement or target was altered. Verdict: pass.
2. Fresh lcompile.py --all compiled all three modules cleanly. Read the bound proof,
   its four private helpers, and every base/append/cokernel transport of the induction.
   Fresh scratch copies printed axioms for all eight theorem declarations: the bound
   and its helpers have only propext, Classical.choice and Quot.sound (the integer-hom
   helper uses only propext and Quot.sound); the layer, induction helper and filtration
   additionally have sorryAx. The only source sorry is the reported named public layer
   theorem, with its documented proof and node. No forbidden declarations or hollow
   definitions occur. Verdict: pass as a reduction, not an axiom-free target closure.
3. Independently read https://stacks.math.columbia.edu/tag/0A38 and the layer docstring.
   Gcd closure attains each positive stalk generator, so removing values above b+1
   keeps K. On V the attained gcd is at most b, making L_x=K_x; on U minus V all
   retained values are b+1, and outside U both vanish. The equal integer sections on
   the value-b+1 opens glue on W before their quotient class glues with zero on V.
   Arbitrary integer stalk isomorphisms differ from canonical coordinates by signs.
   Checked empty spaces/families, b=0, one-point aZ, an absent layer, disjoint value-2
   and value-3 opens, and their gcd-1 overlap. Nonempty index sets avoid any compactness
   assumption on X. The layer constructs one decrease, not a filtration restatement.
   Fresh LeanFinder search for removing the largest cyclic stalk generator returned
   only scheme localization results; Loogle checked Int.subgroup_cyclic; launcher grep
   for integer layers/subsheaves, cyclic stalks and constant filtrations found no result.
   Independent rg on both library roots found no replacement. The remaining construction
   needs normalization, subobjects and gluing; it cannot be closed by a short repair.
   Verdict: pass.
4. The proof follows the bound, zero-stalk criterion, one-layer lemma, induction and
   Fin.snoc route. It supplies all original monicity, cokernel, complex, compact-open
   and endpoint witnesses. Imports serve signatures or proofs with the prescribed
   visibility. All three old direct proof dependencies are accounted for under No
   longer needed and remain downstream; none is globally pruned. Read the unit record:
   sk-thm-curveestimate still realizes thm-sc-proper-cohomology and has no realized
   steps to bypass. No unit record changed. Verdict: pass.
5. Checked all three nodes beside their Lean modules. Programmatic checks confirmed
   every stored Lean signature and each proof_deps union against the proof-step uses.
   The parent statement is unchanged; its route matches the actual induction. The
   bound route matches its proved argument; the layer records the open literature
   construction. Both new nodes contain the required source, search, creation,
   blueprint, chapter, unit and Lean records. Verdict: pass.

Changes in this reading: appended this review and performed fresh compilation,
axiom, source, search and metadata checks. No proof, import or node repair was needed.
Fresh axiom scratch copies are confined to scratchpad and excluded from delivery.
The existing import change record is retained. Delivery checks and push follow through
 deliver3.py.

## Second reading by N1

1. Compared the delivered filtration module with the repository version: the existing
   theorem signature and docstring are unchanged; import visibility changes are recorded
   in `coord/changes/constantSubsheaf_finite_filtration-imports.md`. Verdict: pass.
2. Compiled all three modules locally; there are no errors, warnings, forbidden
   declarations, hollow definitions, or unnamed `sorry`s. The sole remaining sorry is
   the named peel-layer theorem and its node. Verdict: pass as a documented reduction.
3. Checked the two new statements against Stacks 0A38 and edge cases (zero and empty
   sheaves, one-point cyclic stalks, and an absent layer). Both are true and strictly
   weaker than the finite-filtration target. Verdict: pass.
4. The proof follows the bound, peel-layer, induction, and `Fin.snoc` route; all
   quotient, monicity, short-exactness, compactness, and endpoint witnesses are present.
   Imports and the unit route are pruned and preserved as documented. Verdict: pass.
5. Checked all three DAG nodes against the Lean declarations and proof dependencies;
   statements and recorded routes agree. Verdict: pass.

No proof or metadata repair was needed in this reading; this section completes the
required independent review record.
