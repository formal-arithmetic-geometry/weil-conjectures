## What changed

In `lean/Sheaf/AlgebraicGeometry/AffineGlobalHomBaseChangeMap.lean`, proved
`AlgebraicGeometry.exists_canonicalTensorHomAdjunction` from the already imported
`AlgebraicGeometry.exists_canonicalDerivedTensorHom` and Mathlib's
`CategoryTheory.Adjunction.mkOfHomEquiv`. The construction uses the canonical family
`schemeDerivedTensorHomEquiv`, specializes its three-variable naturality to the two
naturality laws required by `Adjunction.CoreHomEquiv`, and builds an adjunction for
each fixed tensor factor. Its inverse Hom equivalences are exactly that family, so
the existing representative characterization transfers unchanged. The counit equation
follows from `Adjunction.homEquiv_symm_id` and the same equality of equivalences.
The inherited module-category derived-category instance is retained to preserve
the existing theorem signature; the unused-section-variable linter is disabled only
for this declaration, since omitting that instance would alter its public signature.
Also wrapped the pre-existing overlong REPAIR comment. No imports, statements or
definitions changed. The proof follows the declaration's existing natural-language
plan, so there is no change of route or new DAG node. The second reader records this
partial proof and its canonical-family dependency in the existing DAG node.

Source read: Stacks `cohomology.tex`, `lemma-internal-hom` (Tag 08DJ), in the local
review copy `/home/ubuntu/c1-stacks-review/cohomology.tex`, lines 10601–10645.
The canonical family and its naturality were read in
`Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom`; the generic adjunction constructor
and its counit identity were read in Mathlib `CategoryTheory/Adjunction/Basic.lean`.
Searches run through msearch: Loogle for `Adjunction.mkOfHomEquiv` (unknown identifier),
Lean Finder for construction of a tensor/internal-Hom adjunction (eight generic
monoidal-closed hits), and grep for `tensorHom.*Adjunction|canonicalDerivedTensorHom`
(no service hits). Direct source searches found the Mathlib constructor and the
existing canonical family used here.

## Proved and sorry left

Closed one of the three original holes:
`AlgebraicGeometry.exists_canonicalTensorHomAdjunction`.
This is a proof from existing named declarations, with zero new holes, rather than
a decomposition into new statements. It still depends on the existing hole
`AlgebraicGeometry.exists_canonicalDerivedTensorHom` through the canonical family;
that module remains a downstream proof item.

Two original holes remain unchanged in this module, both recorded under node
`def-pc-affine-global-hom-base-change-map`:

- `AlgebraicGeometry.exists_affineDerivedExtension`.
- `AlgebraicGeometry.exists_globalHomPullbackComparison`.

No holes added. The current delivery is partial, as permitted for a module with
several sorries. It makes no claim to have normalized the derived scalar-extension
adjunction or repaired the shared pullback counit.

## No longer needed

None. No imports removed and no nodes or modules pruned. The canonical tensor-Hom
family remains necessary: its existence is used to supply naturality and the
representative normalization. The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The definition node has empty `proof` and `proof_deps`, whereas the module contains
three named existence obligations with complete proof sketches. For the closed
obligation, the existing canonical-family statement supplies all needed mathematical
content; only the natural-Hom-bijection assembly and counit identification were missing.
The other two obligations are untouched. The pre-existing REPAIR header and
`coord/hollow-definitions.md` identify remaining normalization work for
`affineDerivedExtensionAdjunction` and `canonicalPullbackAdjunction`; this delivery
does not resolve those distinct obligations or change any data selection.

## Earlier second reading (a previous round; superseded)

1. **Statements and interfaces.** Compared the delivered module with the repository version. All existing declaration signatures and definitions are byte-for-byte unchanged; only the proof body, a wrapped comment, and a local linter option were added. The two remaining `sorry`s are exactly the reported named obligations.

2. **Proof and axioms.** Compiled the delivered module with `lcompile.py`; it compiles without errors. The proof of `exists_canonicalTensorHomAdjunction` uses `Adjunction.mkOfHomEquiv`, the canonical Hom-equivalence family, its naturality, and the standard counit identity. No axiom, unsafe, opaque, extern, or implemented-by declaration was added. The explicit `#print axioms AlgebraicGeometry.exists_canonicalTensorHomAdjunction` scratch check compiled in 56.1 seconds and printed exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the last comes from the existing canonical-family obligation. The launcher's dry run also passed its all-declarations axiom probe and preflight. An earlier scratch copy combining the axiom print with a large type print timed out; the simpler axiom-only check passed without changing any compilation limit.

3. **Split-off statements.** No split-off theorem or new node was added. Checked identity specializations of both naturality laws; the argument also applies to zero objects and uses no perfectness or QCoh assumption. A direct search for `CoreHomEquiv` and `mkOfHomEquiv_homEquiv` confirmed the generic Mathlib constructor; library tensor-Hom adjunctions on complexes or homotopy categories do not replace the pinned derived-family statement. The two open existence theorems remain named and documented in the module, with their original DAG node.

4. **Pruning and route.** No import is proof-only newly introduced or removed. The canonical derived tensor-Hom family remains the sole dependency of the closed proof. The existing unit route is unchanged.

5. **DAG agreement.** Updated the existing item node's `proof`, `proof_deps`, and `proof_origin` to record the partial proof and its dependency on `def-pc-canonical-derived-tensor-hom-bijection`; no statement or definition fields changed.

Second-reading changes: the existing node's proof metadata and the report. I retained the first worker's proof, wrapped repair comment, and scoped linter annotation without rewriting them.

## Second reading by P3

1. **Visible statements and definitions — pass.** Independently compared the sole
   delivered module against the repository with `diff -u`. Every existing signature
   and definition body is unchanged. The changes are the tensor-Hom existence proof,
   its scoped unused-section-variable linter setting, and wrapping a repair comment.
   No target or hypothesis changed and no change record is needed.

2. **Proof and axioms — pass for the partial delivery.** Read the two naturality
   specializations against `IsCanonicalDerivedTensorHom` and Mathlib's
   `Adjunction.CoreHomEquiv`; their directions agree. The inverse-family equality
   transfers the full representative characterization, and `homEquiv_symm_id`
   gives exactly the stated counit. Independently compiled the scratch copy with
   `#print axioms AlgebraicGeometry.exists_canonicalTensorHomAdjunction`: exit 0 in
   48.7 seconds, with only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter is inherited from the canonical-family dependency. The only two local
   sorries are the named, documented original obligations listed above. No prohibited
   declarations or sorry in a definition were added. Existing normalization repairs
   for selected adjunction data remain explicitly open; they were not hidden or
   changed by this delivery.

3. **Split statements and small cases — pass.** No new statement or hole was split
   off. Identity substitutions in either naturality law recover the identity law;
   zero objects require no extra hypothesis. Reviewed the existing representative
   characterization and uniqueness statement used to justify the canonical family's
   selection. A fresh msearch grep for `CoreHomEquiv|homEquiv_symm_id`, and direct
   searches of the library and Mathlib, confirm the generic adjunction constructor
   already used by the proof. The underived sheaf adjunction and tensor-pullback
   adjunctions do not supply this fixed derived Hom-equivalence characterization.

4. **Shortest route, imports and pruning — pass.** The proof uses the existing
   canonical family directly and only adds the generic adjunction assembly. No new
   imports appear. The canonical-family import is required in the theorem statement
   as well as the proof. The old node's `proof_deps` was empty, so there is no omitted
   old proof dependency to prune. No module is pruned. Read the unit record
   `sk-thm-picard-duality`: its existing `realized` fields and chapter route are
   untouched by this local assembly.

5. **DAG agreement — pass.** Compared both node records. Only `proof`, `proof_deps`,
   and `proof_origin` differ, accurately recording a partial proof through
   `def-pc-canonical-derived-tensor-hom-bijection` and the two remaining obligations.
   The Lean statement and all other node fields agree with the repository. There
   are no new nodes to audit.

Second-reading changes in this round: appended this independent review and its fresh
verification evidence. Retained the correct Lean proof and the existing DAG update.
