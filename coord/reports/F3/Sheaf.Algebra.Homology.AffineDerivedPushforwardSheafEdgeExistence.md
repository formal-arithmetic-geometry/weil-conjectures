## What changed

In `Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeExistence`, proved
`AlgebraicGeometry.exists_affineDerivedPushforwardSheafEdge_existence` by the zero natural
transformation (`exact ⟨0⟩`). The theorem asserts only `Nonempty` of a natural-transformation
type. Mathlib's functor-category zero morphisms supply an actual construction, with no
choice from an unproved existence result and no additional hypothesis. The signature,
visibility and existing docstring are unchanged. The second reader removed a redundant public import. An inline comment makes
clear what the proof witnesses. Updated the node's proof, proof dependencies, and origin.

LeanFinder found `CategoryTheory.Limits.instHasZeroMorphismsFunctor` and `zero_app`;
Loogle's initial instance-name query returned no match; msearch grep and direct reading of
Mathlib's `CategoryTheory/Limits/Shapes/ZeroMorphisms.lean` confirmed the instance. Reading
the existing planned comparison theorem confirmed that its stronger isomorphism is not
needed for this statement. The proof applies equally to zero rings, all integer degrees,
and zero complexes: it uses no nonzero or boundedness assumption.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.exists_affineDerivedPushforwardSheafEdge_existence`
(node `lem-pc-affine-derived-pushforward-sheaf-edge-existence`).
No `sorry` remains in the delivered module. No holes or declarations were added.
This is a direct proof, not a decomposition. Single-file lcompile passed without warnings.

## No longer needed

For this node, neither planned proof dependency is needed:

- `lem-pc-affine-morphism-hi`, module
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`.
- `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`, module
  `Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology`.

Both edges are removed from this node's `proof_deps`. Neither module was imported in the
original item, and neither is added. Removed the redundant public import `Mathlib.Algebra.Category.ModuleCat.Abelian`;
the module compiles with only `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`,
which supplies the definitions used by its statement. These
nodes may still be needed elsewhere; this report does not assert global unreachability.
The unit `sk-thm-picard-semicon` has empty `realized.statement` and `realized.steps` lists,
so this local simplification bypasses no realized unit statement or step.

## Where the brief, the DAG or earlier work was wrong

The planned K-injective comparison is unnecessary for this bare existence theorem.
Its docstring describes a canonical affine edge, but its type specifies no canonicality,
invertibility, or normalization. The zero natural transformation meets its exact type.
The docstring is preserved; the proof and this report explicitly identify the witness.

STATEMENT-DISPUTED (outside this item's delivery):
`AlgebraicGeometry.affineDerivedPushforwardSheafEdge_compatibility` in
`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCompatibility` quantifies over
*every* natural transformation of this type, including zero. The source argument only
establishes compatibility of the constructed canonical comparison. For the identity
ring map over a nonzero field, the tilde functor and a nonzero module in a single degree,
choosing ε = 0 makes the left side zero, whereas the derived unit for the identity
pushforward, transported through the displayed homology isomorphisms, is nonzero. Thus
arbitrary-edge compatibility cannot be justified by the cited argument. This delivery
does not import or use that theorem, and does not alter that separately held module.
A correction should bind compatibility to the constructed comparison, rather than infer
it from bare existence. The second reader and maintainer should review that decomposition.


## Second reading by F3

1. Compared the delivered Lean module and node with the repository versions. The
   existing theorem signature, visibility, definitions, and docstring are byte for
   byte unchanged. Only the proof, one import, and the permitted node proof fields
   changed. Verdict: pass.
2. Compiled the module using lcompile, then compiled a scratch copy with
   `#print axioms AlgebraicGeometry.exists_affineDerivedPushforwardSheafEdge_existence`.
   The only axioms are `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
   No sorry or forbidden declaration remains. Verdict: pass.
3. No new or split-off statement was added. Zero is a natural transformation
   for these functors, including over zero rings and in every integer degree.
   Read Mathlib's functor-category zero-morphism instance and `zero_app`, and
   searched the project for the affine-edge declarations. The witness is actual
   constructed data, not data selected from an unproved existence result. Verdict: pass.
4. The zero witness is the shortest route for the unchanged bare existence type.
   Confirmed both removed proof dependencies are listed under No longer needed.
   Removed the redundant public ModuleCat.Abelian import and recompiled. Read
   dag/units/sk-thm-picard-semicon.json: realized.statement is empty and its one
   realized.steps entry is empty. This local proof changes no unit step. Verdict: pass.
5. The node's proof, empty proof_deps, and proof_origin agree with the Lean proof.
   The node diff changes only those three allowed fields. Verdict: pass.

Second reading changed only the redundant public import and this report. Closed
1 existing hole, added 0 holes. The separate compatibility theorem's universal
quantification over arbitrary transformations is a substantive concern, already
reported above; no proof or statement of that separately held module was changed.

The import removal is recorded in
`coord/changes/AffineDerivedPushforwardSheafEdgeExistenceImports.md`. The sole direct
importer privately imports this module and already publicly imports ModuleCat.Abelian.
Compiled scratch copies of that unchanged importer and its compatibility dependency
against the modified existence module with lcompile.py --all; all passed. No consumer
adaptation is needed. The scratch copies are excluded from the delivery.
