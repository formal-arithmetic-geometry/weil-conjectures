## What changed

Replaced the sole sorry in
`Sheaf.RingTheory.RingKrullDimLeOfFaithfullyFlatOfIsLocalHom`, declaration
`RingHom.ringKrullDim_le_of_faithfullyFlat_of_isLocalHom`, by the three-step proof
already planned in node `lem-sc-faithfully-flat-local-dimension`.
Under `f.toAlgebra`, `hf.flat` supplies module flatness and Mathlib's
`Algebra.HasGoingDown.of_flat` supplies going down. The forward direction of
`RingHom.FaithfullyFlat.iff_flat_and_comap_surjective` supplies surjectivity.
The already proved `ringKrullDim_le_of_goingDown_of_surjective` gives the result.
All original signatures, visibility, imports, docstrings and node records stay unchanged.
The existing proof and proof dependencies describe precisely this argument.

## Proved and sorry left

Closed: `RingHom.ringKrullDim_le_of_faithfullyFlat_of_isLocalHom`
(node `lem-sc-faithfully-flat-local-dimension`), the module's only hole.
Added holes: none. Remaining holes in the delivery: none.
This is a proof, not a decomposition: the dimension lemma is already proved and
the other two inputs are Mathlib theorems. The delivery dry run checks all axioms.

## No longer needed

None. The existing proof-only import
`Sheaf.RingTheory.KrullDimension.GoingDown` is used. The three public Mathlib
imports supply the statement's dimension, local-ring and faithful-flat notions.
All three planned dependency nodes are used; no node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The general going-down dimension lemma has already
been proved, so no new intermediate statements are required. The local-ring and
local-homomorphism hypotheses are unnecessary for this argument but are preserved.
The unit `sk-thm-br` has no realized node requiring another route; this proof keeps
the planned going-down and surjective-spectrum route in full.
Searches: LeanFinder for faithful-flat dimension found the flat-going-down and
faithful-flat spectrum-surjectivity inputs; Loogle confirmed
`Algebra.HasGoingDown.of_flat`; repository and Mathlib searches found no shorter
packaged faithful-flat dimension theorem.

## Second reading by K2

1. Compared the sole delivered Lean module with the repository using `diff -u`.
   The only difference is replacement of the theorem's `sorry` with its proof.
   The existing signature, visibility, imports and docstrings are byte-for-byte
   unchanged. No definition, target statement or other module changes. Pass.
2. Independently compiled the delivered file with `lcompile.py`: no errors or
   warnings. Searched its Lean source for holes and forbidden declarations:
   none. Compiled a scratch copy with
   `#print axioms RingHom.ringKrullDim_le_of_faithfullyFlat_of_isLocalHom`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   Read the general dimension lemma and the Mathlib flatness, going-down and
   spectrum-surjectivity inputs. The chosen algebra structure is the actual
   construction `f.toAlgebra`; there is no choice from an unproved existence
   statement. Pass.
3. No statements or nodes are split off, and no holes are added. The proof
   handles arbitrary dimension, including infinite dimension, through the
   general chain-lifting lemma. The local hypotheses are preserved even though
   this argument works for general faithfully flat ring maps. Pass.
4. Independently searched `lean/Sheaf`, `lean/WeilConjectures` and Mathlib's
   RingTheory sources for `ringKrullDim` with flatness/faithful flatness and
   dimension inequality names. No shorter packaged theorem was found. The
   existing proof-only import is used, and each public import supplies a notion
   in the statement. All three old proof dependencies are used; pruning is
   empty. Read `dag/units/sk-thm-br.json`: its realized statement and step lists
   are empty, and the proof retains the planned going-down/surjective-spectrum
   route below that unit. Pass.
5. Read the item node and all three dependency nodes. The proof steps,
   `proof_deps` and documentary `proof_origin` agree with the Lean argument:
   flat going down, faithfully flat spectrum surjectivity, then the proved
   general dimension inequality. No node update is needed. Pass.

Changes by the second reader: this review section only; the Lean proof and
metadata needed no repair. Independently confirmed one hole closed and zero
holes added.
