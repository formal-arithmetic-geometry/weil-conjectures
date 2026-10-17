## What changed

Reconstructed the proof of
`AlgebraicGeometry.Scheme.Modules.exists_affine_finiteType_pullback_zero_test`
against the current post-sync source library. The retained sandbox contained only dispatcher
markers, not the returned delivery's Lean files or report. The current library had the theorem
with its original signature and one `sorry`.

The theorem now takes a finite spanning set using `finite_sections_of_finiteType`. The composite
of the section map of delta with the adjunction unit is a linear map; its kernel contains the
spanning set and hence all sections. On each affine subopen, the bijective comparison
`exists_tensorPullback_affine_sections`, its naturality, and tensor induction prove the
pulled-back component zero. Sheaf separatedness on the cover by affine subopens proves the
claim on arbitrary opens.

The two proof imports now name the source modules
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` and
`WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections` directly. Both old Sheaf modules
were retired to re-export wrappers in the e47efb5a5 sync. The proof uses the current linear
component `(δ.val.app (op V)).hom`, rather than treating the underlying additive section
map `(δ.app V).hom` as a linear map. The final restriction argument explicitly identifies
the evaluated module-naturality equation with its underlying additive section equation before
rewriting. These are concrete proof/API repairs, not an unchanged rebase.

The declaration's signature, visibility, public imports, and existing docstrings are unchanged.
The four-step proof follows the current node exactly, so no DAG fields or change records are
needed. Both new proof import directions passed `import_direction.py may`.

Validation: the item compiled cleanly through `lcompile.py` in 4.7 seconds against the published
post-sync library, and compiling it to the sandbox overlay succeeded in 6.7 seconds.
Its only direct consumer, `Sheaf.AlgebraicGeometry.FinitePresentationZeroMapAffineOpen`, compiled
unchanged against that overlay in 6.0 seconds. A scratch copy with `#print axioms` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`; in particular, no transitive sorry remains in
this theorem's proof. The required final check is
`deliver3.py N1 Sheaf.AlgebraicGeometry.AffineFiniteTypePullbackZeroTest --no-push`.
Only the item and this report are delivered; consumer/axiom checks remain in the scratchpad.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.Scheme.Modules.exists_affine_finiteType_pullback_zero_test`
(node `lem-pc-affine-finite-type-pullback-zero-test`).

Holes added: zero. Holes remaining in the item: zero. New modules and split-offs: zero.
This is a proof from the existing affine-section and finite-generation API, not a decomposition.

The proof covers the empty open by the same sheaf cover argument, and the zero module or empty
spanning family by the kernel/span argument. No nonempty, finiteness, or flatness hypothesis
was added to the morphism or its source scheme.

## No longer needed

Removed proof import `import all Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`, replacing
it with an ordinary proof import of the current source module. Access to private declarations
is unnecessary: `finite_sections_of_finiteType` is public in that module.

Removed proof import `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`, replacing it with
the current source module. These retired wrappers add no mathematical dependency. No mathematical
proof dependency was bypassed: both existing dependency nodes remain needed, as do module sheaves
and their sheaf axiom. No additional node or module is claimed pruned from the whole target closure.

## Where the brief, the DAG or earlier work was wrong

The return identifies a delivery prepared before the upstream e47efb5a5 sync. Both dependency
nodes now point to the source modules, while the current item still imported the retired Sheaf
wrappers (one with `import all`). The repaired proof uses the post-sync source APIs directly.
The current DAG proof plan remains valid and is implemented without new intermediate statements.

Contrary to the repair brief's description, the sandbox did not contain a retained delivery,
node copies, or report when this repair started. The proof was rebuilt from the current source
and current node rather than reusing unavailable pre-sync files. The read-only
`review_packet.py --stage 3` lookup also reported that the returned delivery branch was absent,
so it could not recover the pre-sync proof. The final delivery tool rebases the
resulting proof change on the current sheaf-dag base.

Searches through `msearch.py` (LeanFinder, Loogle, grep) and direct `rg` found no shorter theorem
with this full conclusion. The finite-generation and affine-comparison declarations supplied
by the current source give the planned direct proof; no fresh axioms or theorem statements
were introduced.

## Earlier second reading (a previous round; superseded)

Independent second reading, 2026-10-17, with the delivered module, its repository diff,
the item node, both affine dependency nodes and their current source modules open.

1. **Visible declarations: pass.** The diff changes only the theorem body and the two
   ordinary proof imports. The sole declaration's entire signature, visibility and
   docstring are byte-for-byte unchanged. In particular, the finite set is chosen before
   `G`, `δ`, `X` and `g`; `G` requires only quasi-coherence, and `g` is arbitrary. The
   hypothesis uses the same chosen adjunction unit on `V`, and the conclusion covers every
   `W ≤ g ⁻¹ᵁ V`. There are no definition changes or forced adaptations, so no change
   record is required. I also read the sync return in `coord/returns/N1.md`: the current
   ordinary source imports and linear `.val.app` components address its obsolete-API
   issue without changing the interface.

2. **Proof and trust: pass.** I independently compiled the item through `lcompile.py`
   (4.8 seconds), compiled the scratch copy with `#print axioms` (7.0 seconds), and checked
   the unchanged direct consumer against the sandbox output. The printed axioms are
   exactly `propext`, `Classical.choice`, `Quot.sound`; there is no `sorryAx`, including
   transitively. The delivered file contains no `sorry`, forbidden declaration or kernel
   bypass, and no line exceeds 100 characters. The kernel argument really kills all
   sections: `hs` identifies the span with top, rather than merely assuming the listed
   generators generate after pullback. Tensor induction then proves zero on arbitrary
   tensors, and the final evaluated naturality equation has the restriction direction
   needed for separatedness.

3. **Split-offs and edge cases: pass.** There are no new declarations, modules, nodes or
   holes. The local `k` and `haff` are proved parts of the argument, not renamed copies
   of the item. For an empty spanning family, `hs` forces the section module to be zero;
   the kernel argument still applies. For empty `W` the affine-cover coverage condition
   is vacuous and sheaf separatedness still applies. Neither the affine comparison nor
   the tensor induction introduces flatness, quasi-compactness or a nonempty condition.

4. **Route and pruning: pass.** I read Properties `lemma-finite-type-module` (Tag 01PB),
   Schemes `lemma-spec-sheaves` and `lemma-quasi-coherent-affine`, and the uniqueness
   argument in Sheaves `lemma-sheaf-subset-stalks`. Finite type and quasi-coherence supply
   precisely the finite affine section module used here. The comparison's surjectivity,
   naturality and pure-tensor formula supply precisely the affine vanishing step. The
   subsequent cover is by all affine subopens of `W`; it does not assume intersections
   are affine. Independent LeanFinder, Loogle and grep queries through `msearch.py`, plus
   `rg` on both library roots, found no replacement for the full conclusion. Related
   Mathlib vanishing results concern structure sheaves or inverse limits; related local
   affine-vanishing helpers are private. All four imports have a purpose: the two public
   imports supply the signature, and the two ordinary imports supply the finite-sections
   and tensor-comparison theorems. The report names both removed wrappers; no old
   `proof_deps` entry becomes unused. I read `sk-thm-picard-semicon.json` and its blueprint
   section: its `realized` lists are empty, and this lower-level repair changes none of
   its statement, steps or dependency route. No whole-closure module pruning is claimed.

5. **DAG agreement: pass.** The existing node's four steps match, respectively,
   `finite_sections_of_finiteType` and `Module.Finite.fg_top`, the span/kernel argument,
   `exists_tensorPullback_affine_sections` with tensor induction, and affine-basis
   coverage with module naturality and sheaf separatedness. Its three `proof_deps`
   remain used, and its Stacks-based `proof_origin` still describes the argument.
   Dependency node records already name the two current `WeilConjectures` modules.
   Therefore no node fields require editing and there are no new-node fields to audit.

Second reading changed only this report, adding the independent checks above. The Lean
proof and dependency records were correct and were retained. Holes closed: one; holes
added: zero; split off: zero.

## Second reading by N1

1. **Declarations and signatures:** Compared the sandbox module with the repository copy.
   The theorem signature is byte-for-byte identical; visibility, docstring, and public
   imports are unchanged. Only its proof and two proof-only import paths differ. No
   definition or statement was altered. Verdict: pass.

2. **Proof and trust:** Compiled the module with `lcompile.py`; searched for forbidden
   declarations and `sorry`; checked line lengths. The proof compiles with no warnings and
   has no forbidden constructs or remaining holes. A scratch copy, verified to equal the
   item plus only `#print axioms`, reports exactly `propext`, `Classical.choice`, and
   `Quot.sound`, with no transitive `sorryAx`. Verdict: pass.

3. **Split-offs and edge cases:** No split-off statements or new nodes were added. The
   finite-span, affine tensor, and sheaf-separation arguments cover zero modules, empty
   spanning sets, and empty opens without extra hypotheses. Verdict: pass.

4. **Route and pruning:** Checked the proof against the node's four planned steps and
   searched Mathlib and the library for a shorter exact result, using independent
   LeanFinder, Loogle, grep, and direct `rg` queries. The closest search results concern
   structure-sheaf limit descent or general generators; none replaces this conclusion.
   Read the finite-sections theorem and affine comparison, including its naturality and
   pure-tensor formula. The kernel argument kills every original section; tensor induction
   therefore kills each affine component. Naturality then gives precisely the restrictions
   needed for separatedness on the cover of all affine subopens. No affine-intersection
   assumption occurs. The two ordinary source imports are proof-only and both remain
   needed; no old dependency node is bypassed. Verdict: pass.

5. **DAG agreement and unit route:** The node's statement, proof dependencies, proof
   origin agree with the Lean proof. Both affine dependency nodes already point to the
   current source modules. Read the unit record and blueprint section: its `realized`
   statement and step lists are empty, and this lower-level proof does not change the unit
   route. No DAG edits or change records are required. Verdict: pass.

Changed only this report by adding this second-reading record; the Lean proof was retained.
