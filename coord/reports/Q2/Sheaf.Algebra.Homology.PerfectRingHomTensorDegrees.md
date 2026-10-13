## What changed

Reduced `CategoryTheory.perfectRingHom_tensorDual_degree_exists` to two distinct
steps of its existing argument: existence of the signed evaluation morphism, with
no boundedness or projectivity assumption, and invertibility of every normalized
morphism for bounded finite-projective P. The original theorem applies the second
step to the first and uses `asIso` to preserve the normalization.

The three existing definitions were extracted into
`Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition`, publicly imported by
the original module. This avoids a cycle for the two new proof modules. No existing
signature, universe, or visibility changed. The evaluator body was refactored to
use the typed projection interface, avoiding a slow raw-witness expression; the
proved private `single_projection_evaluation` verifies the equivalent degree
transport. The other two defining bodies are unchanged. New proof imports are
`Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeMap` and
`Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeIsIso`.

## Proved and sorry left

Closed the original hole in `CategoryTheory.perfectRingHom_tensorDual_degree_exists`
(lem-pc-perfect-ring-hom-tensor-degrees), by decomposition rather than a sorry-free
proof. Added two named holes:

- `CategoryTheory.perfectRingHom_tensorDual_degree_map_exists`
  (lem-pc-perfect-ring-hom-tensor-degree-map).
- `CategoryTheory.perfectRingHom_tensorDual_degree_isIso`
  (lem-pc-perfect-ring-hom-tensor-degree-isiso).

No holes remain in the original module or the extracted definition module.
Hole accounting: one closed, two added, net minus one; no sorry-free proof of the
original theorem is claimed.
The original differential and tensor-dual isomorphism modules compile unchanged
against the extracted interface (3.7 and 3.6 seconds respectively).
The two new theorem statements cover zero complexes, the zero ring, empty support,
and unbounded Q. Invertibility requires all the original assumptions on P.
The existence statement introduces none of these assumptions and asserts no inverse.
For unbounded P the construction maps an infinite coproduct to a product and makes
no claim that this map is invertible; the boundedness hypothesis is retained exactly
where the inverse requires finite support.
The invertibility statement assumes normalization of a given morphism and constructs
no new evaluation map; it does not merely repeat the original existence theorem.

## No longer needed

No modules or imports are pruned. The original public import is retained to preserve
its exported interface. The old direct proof dependencies
`def-pc-perfect-rhom-base-change-map`, `def-pur-hom-complex`,
`lem-pc-perfect-ring-dual-term-flat`, and `def-pc-tensor-complex-sheaves` are no longer
direct steps of the parent proof: they remain needed in the extracted interface and
the two split-off arguments. The parent now directly uses only the map-existence
and invertibility nodes. No old dependency is dropped from the argument or import
closure, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan supplied definitions, but no declaration implementing the construction of
the signed degreewise morphism or finite-support invertibility. Those are the two
new items. Mathlib dualTensorHomEquiv supplies the finite-projective module block,
not the sheaf comparison or the total-degree coproduct/product assembly.

The local literature path cited by the node is absent on this machine. Read the
primary Stacks sources online at https://stacks.math.columbia.edu/tag/0A6A and
https://stacks.math.columbia.edu/tag/0ATK; the precise signed one-object interfaces
are the expanded chain-level argument already recorded in the parent node, rather
than a literal theorem in those tags. LeanSearch was unavailable (Internal Server
Error); LeanFinder, Loogle and local grep returned no exact sheaf-complex comparison.

## New nodes

`lem-pc-perfect-ring-hom-tensor-degree-condition`: the three existing explicit
normalization definitions in their own interface module; the evaluator uses an
equivalent typed projection and degree transport to avoid a slow definition.

`lem-pc-perfect-ring-hom-tensor-degree-map`: assemble signed bilinear evaluations
using sheafification, the Hom product universal property, and tensor coproduct
universal property. No finiteness condition is needed.

`lem-pc-perfect-ring-hom-tensor-degree-isiso`: reflect isomorphisms at the unique
object, reduce to the finite-projective dualTensorHomEquiv blocks, discard the zero
factors, and use a finite biproduct after reindexing p=-r.

Change record: `coord/changes/perfect-ring-hom-tensor-degree-interface.md`.

## Second reading by Q2

1. Compared the delivered original module with the repository version using `diff`.
   All four existing declaration signatures, universes and visibility are unchanged;
   the theorem signature is byte for byte unchanged. The three relocated definitions
   are covered by `coord/changes/perfect-ring-hom-tensor-degree-interface.md`.
   The tensor section map and normalization body are unchanged. For the evaluator,
   unfolded `ringHomComplexProjection` and checked that it selects the same projection
   family. The proved generic transport lemma identifies its projection at `-r+r`
   followed by `singleObjXIsoOfEq` with the old degree-zero projection followed by
   `singleObjXSelf`. No evaluation function or target meaning changes. Checked the
   downstream declaration users: only this module and PerfectRingHomTensorDifferential;
   the reported 338 transitive importers retain the same interface. Verdict: pass.

2. Compiled all four delivered modules in import order through `lcompile.py`, without
   errors or warnings. Scanned their code: exactly the two reported public named
   theorem holes, no holes in definitions, and no forbidden declarations or attributes.
   Ran `#print axioms` in a scratch module for all three definitions, both new lemmas,
   and the original theorem. Definitions use only propext, Classical.choice and
   Quot.sound; the theorems additionally use sorryAx, as expected for this decomposition.
   The existential map witness is used only within the theorem proof; no data-valued
   definition chooses it. Verdict: pass as a decomposition, not a completed proof.

3. Read both new lemma signatures, full proof docstrings and nodes. Construction
   asserts only a normalized morphism and uses the tensor/coproduct/product universal
   properties without boundedness. Invertibility starts with a given normalized map;
   finite projectivity makes each module block invertible, and bounded support makes
   the remaining product and coproduct the same finite biproduct. Neither lemma alone
   restates the original isomorphism-existence claim. Tested the argument on zero P,
   zero Q, zero ring, empty support, a one-degree finite-projective P, arbitrary Q,
   and unbounded P for the construction alone. Signs are units even in characteristic
   two. The normalization determines every block since pure tensors generate and
   evaluation on the one-object site's slice detects localized maps. Verdict: true,
   necessary, strictly separate parts of the original argument.
   Fresh searches used LeanFinder for a bilinear evaluation pairing into internal Hom,
   Loogle for TensorProduct.lift, and grep for dual/tensor/Hom isomorphisms. Read the
   library's HomTensorDegreewise, HomComplexDualTotalComparison and upstream
   Monoidal/Dual: they provide currying or a different termwise dual, not this signed
   normalized comparison for the chosen Hom complex. The proved private dualTermIso
   in PerfectRingDualTermFlat is useful for the invertibility step but does not close
   it. No split-off lemma has a direct existing replacement or a minutes-long proof.
   Checked the primary sources [0A6A](https://stacks.math.columbia.edu/tag/0A6A) and
   [0ATK](https://stacks.math.columbia.edu/tag/0ATK): these are the derived evaluation
   results underlying the parent argument, not literal statements of the new interfaces.

4. Read the proof from its conclusion downward: map existence plus IsIso followed by
   asIso is the direct reduction, with no added assumption or normalization loss.
   Both new theorem imports are plain imports; the interface imports are public
   because signatures use their declarations. Kept the old public import to preserve
   visibility. Checked every old proof dependency under No longer needed, and read
   dag/units/sk-thm-picard-duality.json: its realized fields are empty and unchanged;
   the existing chapter/unit route is untouched by this reduction below the unit.
   Verdict: pass; no module pruning and no net reduction in holes.

5. Compared all four node records with the Lean declarations. The parent proof uses
   exactly the two new theorem nodes, with proof_deps equal to the uses union. New
   nodes carry sources, complete proof plans, dependency records, three search kinds,
   split status, creation data, blueprint ancestry, chapter/unit and Lean records.
   The definition node records the three moved declarations. Verdict: pass.

Second reading changed only report precision, one doubled space in the original
proof, and a stray leading space in the construction docstring and matching node
proof text. No mathematical statement, defining body, proof route or hole changed.
