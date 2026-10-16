## What changed

Replaced the sole local hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_scalarRoute_model`
without changing its signature, public imports, or definitions. The proof now
constructs a simultaneous K-flat model, transports the scalar/tensor component
equality to the original derived object by naturality, and postcomposes with the
model target before applying the existing tensor-route computation.

The new module is `Sheaf.Paper.IntegralResidueScalarGeometryBridge`. Its single
open theorem is restricted to K-flat representatives whose ordinary pullback is
K-flat. The second reader narrowed the first worker's arbitrary-representative
bridge and proved the missing descent in the item. A private, proved generic
helper `existsKFlatPullModel` constructs the required model from the existing
functorial flat resolution. It introduces no public data or new hole.

Only the item, this new module, their node records, and this report are delivered.
The two new item imports are proof-only. Both imports of the bridge occur in its
statement and are public.

## Proved and sorry left

Original local holes: 1. Closed by a reduction:
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_scalarRoute_model`
(node `new-integral-residue-scalar-route-model`).

Added holes: 1:
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorGeometry_component`
(node `new-integral-residue-scalar-geometry-component`). It is the only sorry in
the delivered sources. The private model-construction helper and naturality
descent have complete Lean proofs.

This is a decomposition: one hole closed and one added, net zero; it is not a
net proof. The pre-existing `integralResidue_tensorRoute_model` and its hole are
unchanged. The remaining obligation is the balanced tensor and scalar-counit
calculation on the resolving class, not the arbitrary-complex descent or the
final model-map computation. Its theorem docstring gives the proof in words.

## No longer needed

Removed the item's direct proof-only imports of
`Sheaf.Paper.IntegralResidueOrdinaryMonoidal`,
`Sheaf.Paper.IntegralResiduePullSquare`, and
`Sheaf.Paper.IntegralResidueTensorPresentation`. Their public interfaces are
already supplied by the retained statement imports.

The old direct proof dependencies
`new-integral-residue-derived-pull-square`,
`new-integral-residue-tensor-presentation`,
`new-integral-residue-ordinary-monoidal`, and
`def-weil-pbc-integral-residue-tensor-pull-presentation` are now delegated through
the bridge and tensor-route nodes. The last also remains a statement dependency.
They remain transitively needed. No whole module is pruned from the target closure.
No top-level tool approval is removed.

## Where the brief, the DAG or earlier work was wrong

The aggregate `integralResidue_tensorGeometry` imports this item, so importing it
here would create a cycle. The delivered bridge uses no aggregate theorem and
has no edge back to it. The first worker instead left the full component on all
representatives as one hole. The second reading reduced that obligation to
K-flat representatives with K-flat pullback and proved the resolution and
naturality argument explicitly, using Mathlib's `Monoidal.commTensorRight`.

The original report's bridge docstring omitted the derived normalization and
resolution issues. The replacement docstring explains the two K-flat hypotheses,
canonical counit normalizations, balanced coequalizer check, and cancellation.
The arbitrary original P is never assumed K-flat; no flatness of the residue
coefficient is assumed. The argument includes zero complexes, zero coefficient
objects, identity morphisms, and empty schemes: it cancels canonical isomorphisms
and presentation epimorphisms, never nonzero scalars.

The source was checked in Bhatt--Scholze, arXiv:1309.1198v2:
[Remark 6.8.15 and the proof of Lemma 6.5.9(5)](https://arxiv.org/pdf/1309.1198).
These give the pullback and tensor context. Proposition 6.8.11(3) concerns
constructibility and does not supply this specific normalization calculation;
it is removed from the new node's source claim. The explicit balanced-tensor
argument is identified as an agent argument, not a verbatim theorem of the paper.
No target, existing signature, or definition changes. The unit route remains.

## New nodes

`new-integral-residue-scalar-geometry-component` records the sole new open theorem
in `lean/Sheaf/Paper/IntegralResidueScalarGeometryBridge.lean`. Its statement now
requires both source and image K-flatness, its proof plan follows the canonical
counits and balanced presentation, and its Lean record exactly matches the new
signature. Its record includes all three required search methods and the second
reader's additional searches. The only overlapping aggregate declaration imports
the item and cannot be used here. No change record is needed: only this new
statement and existing proof bodies are changed.

## Second reading by A2

1. Compared every delivered module with the repository. The only existing public
   declaration's signature is byte-for-byte identical, and its docstring and
   public imports are unchanged. The added generic helper is private and proved.
   There are no changes to definitions, targets, or modules held by other groups.
   Verdict: pass.
2. Compiled both final sources through lcompile.py, including scratch copies with
   explicit `#print axioms`. No errors or warnings. The helper uses only
   `propext`, `Classical.choice`, and `Quot.sound`; the component and item also use
   the expected `sorryAx`. The bridge's named theorem is the only delivered
   sorry. No forbidden declaration form or hollow definition occurs. Verdict:
   pass as a decomposition, not as an axiom-free completed theorem.
3. Read the split statement against the concrete tensor, scalar-mate, and
   coefficient-pullback definitions. Narrowed it to source and image K-flatness;
   those hypotheses make the ordinary models compute the derived tensors and
   require no flat residue coefficient. Checked zero complexes and identity
   maps, and checked that presentation epimorphisms and canonical isomorphisms
   still justify the argument for zero objects and empty schemes. The item
   supplies these hypotheses on a constructed replacement and proves descent;
   they are not added to its original signature. Read the cited source and
   corrected its scope. Additional LeanFinder, Loogle, and grep searches found
   generic counit and resolution tools, but no usable existing exact component;
   the aggregate imports this item. Verdict: the remaining statement is true
   and a calculation on the resolving class, not an arbitrary-complex restatement.
4. Checked the top-down reduction, retained statement imports, proof-only new
   imports, and all four old proof dependencies. All removed dependencies are
   named above and remain transitively needed. No module leaves the closure.
   Read `dag/units/sk-thm-properbasechange.json`: its statement and all three
   `realized.steps` are retained. Verdict: pass.
5. Checked both node records with their Lean modules open. The existing node
   changes only `proof`, `proof_deps`, and `proof_origin`. Each proof-dependency
   list is exactly the union of the steps' uses. The new node has its source,
   complete proof plan, search records, provenance, blueprint origin, chapter,
   unit, and verbatim Lean statement including both K-flat hypotheses. Verdict:
   pass.

Changed in the second reading: restricted the bridge to the resolving class;
proved simultaneous K-flat model construction and naturality descent; used the
existing monoidal natural isomorphism instead of adding a duplicate tensor
comparison helper; repaired the bridge's proof docstring and source attribution;
updated both proof plans and completed the removed-dependency report. Both final
modules and explicit axiom probes passed. The proof helper is generic so that
elaboration of the flat-resolution construction does not repeatedly unfold the
large concrete module categories; no file or proof is split across extra modules.
