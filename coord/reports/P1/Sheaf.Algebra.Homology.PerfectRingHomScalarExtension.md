## What changed

Replaced the sole sorry in
`Sheaf.Algebra.Homology.PerfectRingHomScalarExtension` with a compiling reduction.
The proof obtains normalized termwise internal-Hom isomorphisms, supplies them to a
finite-support assembly theorem for each degree, and applies Mathlib's
`HomologicalComplex.Hom.isIso_of_components` to the existing chain map. The original
signature, visibility, and docstring remain unchanged.

Added proof-only imports of `Sheaf.Algebra.Homology.FiniteProjectiveRingHomExtension`
and `Sheaf.Algebra.Homology.BoundedRingHomExtensionDegree`. These are separate parts
of the original argument, with no new definitions or arbitrary data chosen from
existence. The first theorem concerns a pair of module sheaves and no complex; the
second assumes normalized termwise isomorphisms and proves invertibility of an
arbitrary map in one degree, without assuming projectivity or differential compatibility.
The existing DAG node now records this proof route.

## Proved and sorry left

Closed the item's hole `CategoryTheory.perfectRingHom_scalarExtension_isIso`
(node `lem-pc-perfect-ring-hom-scalar-extension`). No sorry remains in the item.
This is a decomposition, not a complete proof free of sorry dependencies:
one upper hole closed, two strictly smaller holes added, net minus one.

The delivery adds precisely these two sorry declarations:

- `CategoryTheory.finiteProjectiveRingHom_extension_exists`, node
  `lem-pc-finite-projective-ring-hom-extension`, module
  `Sheaf.Algebra.Homology.FiniteProjectiveRingHomExtension`.
- `CategoryTheory.boundedRingHom_extension_degree_isIso`, node
  `lem-pc-bounded-ring-hom-extension-degree`, module
  `Sheaf.Algebra.Homology.BoundedRingHomExtensionDegree`.

Both have public statements, exact `by sorry` proofs, sources, and complete proof
plans in their docstrings. Both are true for zero rings and zero source modules.
The assembly statement also handles an empty bounding interval (a>b), arbitrary
unbounded Q, and non-flat B. Its supplied term comparisons remove all need for
projectivity within that statement. No definitions or existing statements changed.

All three modules compile against the shared build. The final target proof has no
warning after removing an unnecessary local instance declaration: Lean already
uses the named local component-isomorphism hypothesis in instance synthesis.

## No longer needed

None. No original imports were removed, and no original mathematical step was
bypassed. `PerfectRHomBaseChangeMap` remains a public statement dependency, and its
transitive `HomComplex` dependency remains required. The original node's two
proof-dependency entries `def-pc-perfect-rhom-base-change-map` and
`def-pur-hom-complex` are now reached through the new lemmas rather than listed as
the immediate proof-dependency leaves of the target. They are not pruned modules.
No unit statement or realized step is bypassed; the unit's realized arrays are empty.

## Where the brief, the DAG or earlier work was wrong

The original node's first two non-elementary proof steps cite definitions only;
those declarations construct the data and products but do not state their
finite-projective or finite-support scalar-extension properties. These steps
therefore cannot be closed just by applying the recorded dependencies. The delivery
states precisely these two parts and combines them with a real Lean proof.

Searches used the required msearch tool and are logged in searches.jsonl.
LeanSearch returned HTTP Internal Server Error, recorded as unavailable rather than
as a negative result. LeanFinder found `IsBaseChange.linearMapRightBaseChangeEquiv`
and `IsBaseChange.pi`; Mathlib source search found `TensorProduct.piRight` and
`Module.isBaseChange_map_of_finite_free`. Reading the latter shows a finite-free
source result; `Module.FinitePresentation.isBaseChange_map` needs B to be flat and
cannot be used here. The ordinary finite-product result already has the existing
Mathlib-leaf node `lem-weil-pbc-tensor-finite-product`, cited by the new proof plans.
No existing declaration found supplies the required normalized sheaf transport.
The blueprint search found finite-projective derived tensor-Hom lemmas in the
six-functor coefficient setting; their derived categories and coefficient
hypotheses differ from these ordinary ring-site module statements.

The cited Stacks source files are not installed in this machine's literature tree.
Read the official online sources for Tags 0A6A, 0ATK, and 0BYN instead. Tag 0A6A
reduces via the evaluation theorem 0ATK; the degreewise argument in the item's
existing docstring is an expanded finite-projective computation, rather than a
verbatim proof paragraph of 0A6A. The new nodes identify this expansion honestly.
There is no mathematical statement correction or forced adaptation.

## New nodes

`lem-pc-finite-projective-ring-hom-extension` realizes original step 1: a normalized
isomorphism for ordinary internal Hom of a finite projective module sheaf. It has
no boundedness, Hom-complex, derived-category, or K-flatness hypothesis. Its plan
uses finite-coordinate tensor distribution and the finite-projective retraction,
then transports along the prescribed sheafification and object identifications.

`lem-pc-bounded-ring-hom-extension-degree` realizes original step 2: finite-support
assembly in one degree, assuming the termwise isomorphisms as inputs. Its plan
truncates the product by zero factors, commutes scalar extension with the finite
product, and uses pure-tensor generation and joint detection by projections to
identify the resulting isomorphism with the supplied map. It assumes no
projectivity and no chain-map compatibility.

No change record is needed because no existing interface or statement changed.

## Second reading by P1

1. **Existing interface unchanged: pass.** Read all three delivered modules and diffed
   PerfectRingHomScalarExtension.lean against the repository. The only changes there
   are two plain proof imports and the replacement of its sole `by sorry`. The complete
   theorem signature, universes, public visibility, hypotheses hb/hp/hf, conclusion,
   and existing docstrings are byte-for-byte unchanged. No definitions, target files,
   or other existing modules are delivered; no change record is required.

2. **Kernel and holes: pass as a decomposition.** Compiled all three modules with
   lcompile.py in import order, without errors or warnings. A scratch copy with
   `#print axioms` for perfectRingHom_scalarExtension_isIso,
   finiteProjectiveRingHom_extension_exists and boundedRingHom_extension_degree_isIso
   reports exactly propext, Classical.choice, Quot.sound and sorryAx for each.
   The item has zero textual sorry; each new theorem has exactly one, as its whole
   named public proof. There is no axiom, unsafe, opaque, implemented_by, extern,
   anonymous hole, or definition with a hole. The item uses the existential term
   comparisons only as proof hypotheses; it constructs no data from an arbitrary
   existence witness. In any case their normalization determines each comparison
   uniquely, since pure tensors generate both modules and slice evaluation detects
   sections. The shared Hom products and projections come from the same
   homComplex_exists witness, whose limiting-fan property fixes the product up to
   its projection-preserving isomorphism. That theorem is now proved in the repository.
   This delivery still closes one upper hole and adds two lower holes (net -1);
   none of the three statements is certified free of sorry dependencies.

3. **Split statements and edge cases: pass.** The first lemma is solely a module
   statement: finite projectivity of M gives the retract of a finite free module,
   with arbitrary N and arbitrary ring map. F needs only the specified object
   equalities because neither the conclusion nor its normalization uses F.map.
   The second lemma assumes precisely the termwise normalized isomorphisms rather
   than asserting finite projectivity again. Its target is a single-degree arbitrary
   sheaf map t; no differential compatibility is assumed or used. The ht equation
   is exactly d.homMap_pure in the actual reduction. The one-object bottom topology
   makes the sheafification unit invertible; the identity slice evaluation detects
   the internal-Hom section. Thus generation by pure tensors forces t to equal the
   finite-product comparison. Checked M=0, N=0, P=0, Q=0, rank-zero free modules,
   identity ring extension, the quotient Z -> Z/2Z (non-flat), B=0, and the zero-ring
   source (which forces B=0). For a>b, every P term is zero and both Hom-degree
   objects are zero; for unbounded Q only the finitely many P indices contribute.
   No counterexample or missing hypothesis was found. Both docstrings give the
   construction, transport, normalization, and uniqueness argument, and both have
   matching nodes. Neither lemma restates the complex-level item.

   Independent msearch searches used different queries about Hom from finitely
   generated projectives, finite-support products, and the component-isomorphism
   criterion; rg searched both Lean roots and Mathlib. Read the returned extension
   adjunction tools, Module.isBaseChange_map_of_finite_free and
   Module.FinitePresentation.isBaseChange_map: the latter requires flatness of B,
   so it cannot supply this general statement. Additional useful existing tools
   are dualTensorHomEquiv and lTensorHomEquivHomLTensor in
   Mathlib.LinearAlgebra.Contraction (their actual hypotheses include finite
   projective M), plus the extension/restriction adjunction. These shorten the
   ordinary-module part for the next prover; they do not provide the normalized
   sheaf transport or the finite-support Hom-product comparison as stated here.
   ModuleCat.tensorEquivHomDual and affineFiniteProjectiveHomModel have different
   conclusions. Neither new hole can be closed in a few minutes using those tools.
   Read the official [Stacks 0A6A](https://stacks.math.columbia.edu/tag/0A6A) and
   [0ATK](https://stacks.math.columbia.edu/tag/0ATK): the report correctly labels the
   finite-projective computation as an agent expansion, not a verbatim source proof.

4. **Shortest upper reduction, imports and pruning: pass.** The proof directly
   supplies hp p and hf p to the termwise theorem, hb and d.homMap_pure to assembly,
   then uses HomologicalComplex.Hom.isIso_of_components. The named hcomponents is
   available to instance synthesis, as confirmed by the successful compile and the
   checked Mathlib signature. The two new imports are plain imports used only in
   this proof; PerfectRHomBaseChangeMap is the public dependency of all signatures.
   Every import is used. No module is pruned. Both original proof_deps,
   def-pc-perfect-rhom-base-change-map and def-pur-hom-complex, remain needed
   transitively through the new lemmas; the No longer needed section names both.
   Read dag/units/sk-thm-picard-duality.json: realized.statement=[] and
   realized.steps=[[]]. The reduction expands the original module and finite-product
   steps and bypasses no realized unit node or chapter route.

5. **DAG agreement: pass.** The existing node differs only in proof, proof_deps and
   proof_origin; its three steps match the three operations in the Lean reduction.
   For every delivered node, proof_deps equals the union of step uses. Each new
   node has self-contained statement, statement dependencies, cited source, full
   proof plan, agent proof origin, three search kinds (including the honestly
   unavailable LeanSearch service), split status, creator, blueprint ancestry,
   correct parent chapter/unit and a complete lean record. Each new lean.statement
   is byte-for-byte the theorem signature in its module. The finite-product leaf
   lem-weil-pbc-tensor-finite-product really records Mathlib TensorProduct.piLeft.

Changes by the second reader: added this review and the independent search evidence.
No Lean or node repair was needed; no additional hole was closed or added.
