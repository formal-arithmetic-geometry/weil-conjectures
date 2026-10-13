## What changed

Completed CategoryTheory.torOne_surjective_flat_middle with its signature unchanged. Added the fully proved generic presentation lemma CategoryTheory.tensor_cycles_flat_cokernel in Sheaf.RingTheory.TensorCyclesFlatCokernel, imported only for the proof. Also imported Mathlib.Algebra.Homology.ShortComplex.ModuleCat for its explicit cycle comparison. The new lemma factors the augmented tensor presentation through its image, uses flat-quotient tensor injectivity and tensor right exactness, and expresses a lifted kernel element as a finite sum. The main proof transports cycles to Tor through projectiveResolution.isoLeftDerivedObj and proves the pure-tensor formula term by term using derived naturality. No definitions or existing signatures changed.

## Proved and sorry left

Closed the sole original hole: CategoryTheory.torOne_surjective_flat_middle (lem-weil-pbc-tor-one-surjective-flat-middle). Also proved CategoryTheory.tensor_cycles_flat_cokernel (lem-weil-pbc-tensor-cycles-flat-cokernel). No sorry remains in either delivered module; no holes added or split off. Local compilation of both modules succeeds. The delivery tool checks all declaration axioms.

## No longer needed

Removed the redundant proof-only Mathlib.LinearAlgebra.TensorProduct.Finiteness import from the new cycle module: its declarations are already available through Flat.Basic. No modules pruned. All original planned mathematical dependencies remain used, directly or through the proved cycle lemma. The Tor quotient tensor-right-exactness argument is unnecessary: after lifting cycles, their homology classes and naturality give explicit preimages directly. No separate Tor quotient base-change construction or boundary comparison lemma is needed. The old direct proof dependencies lem-weil-pbc-tensor-right-exact and lem-weil-pbc-flat-quotient-tensor-injective move to the new cycle lemma; the main node no longer directly depends on them. Both remain transitively used and neither is globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The current signature uses the canonical actions from the already landed interface repair and is the statement proved here. The second reader removed the superseded STATEMENT-DISPUTED marker. The literature checkout is absent on this machine, so the Tag 00MM statement and proof were read from the official Stacks page. Searches of the library, DAG and blueprint found no existing exact cycle-lifting statement. LeanFinder returned flat tensor exactness results; Loogle returned the exact flat-quotient injection used; grep found cancelBaseChange. LeanSearch was unavailable (HTTP Internal Server Error), recorded accurately in searches.jsonl.

The new cycle lemma includes arbitrary exact presentations, with no projectivity assumption and no Tor or boundaries. Edge cases checked mathematically: B=A gives the coefficient-one expression; z=0 permits the empty finite sum; d=0 makes every element a cycle; the zero-ring case has only zero elements. Flatness is used precisely to preserve the inclusion of the image module after tensoring. Its entire proof compiles without sorry.

## New nodes

lem-weil-pbc-tensor-cycles-flat-cokernel: a fully proved, strictly intermediate cycle-lifting result realizing the kernel paragraph of Tag 00MM. It is not a restatement of Tor surjectivity: the main proof still constructs cycle representatives, transports homology classes, and proves compatibility with the canonical Tor map. No change record is needed because existing interfaces are unchanged.

## Earlier second reading (a previous round; superseded)

The second reader should compile both delivered modules and inspect the unchanged target signature. The intermediate theorem is strictly about cycle lifting for an arbitrary exact presentation; it does not restate Tor surjectivity. Its proof uses only the stated tensor exactness, flat injectivity, scalar tower equivalences and finite tensor spanning. The main theorem then applies it to a projective resolution and checks the canonical base-change map by pure-tensor computation and homology naturality.

## Second reading by T2

1. Compared both delivered modules against the repository. The new cycle module
   is absent there. The existing module differs only in proof-only imports, the
   surjectivity proof and its local elaboration option, and documentation.
   All existing declaration signatures, visibility, and definitions are
   byte-for-byte unchanged. No statement or definition change record is needed.
   Read the landed canonical-interface change record; this delivery preserves it.
   Verdict: pass.

2. Compiled both modules through lcompile.py in import order. No sorry or
   forbidden construct occurs in either source, including definitions. Scratch
   #print axioms checks for tensor_cycles_flat_cokernel and
   torOne_surjective_flat_middle show only propext, Classical.choice and
   Quot.sound. The delivery probe also checks every declaration. All data is
   constructed: the image, kernel, scalar actions and balanced tensor lift;
   cycle representatives are witnesses used solely in theorem proofs.
   Verdict: pass.

3. No unproved statement is split off. Read the new cycle theorem and its full
   proof: tensor right exactness yields exactness after the first extension,
   flatness preserves the image inclusion after the second, and right exactness
   lifts the resulting kernel element. Tensor associativity and commutativity
   give precisely the stated coefficient formula. Checked zero elements, d=0,
   B=A and zero-ring cases; the hypotheses do not silently require projectivity
   or flatness of B. Its node's recorded Lean signature matches verbatim.
   Independent LeanFinder and grep searches found ker_lTensor_eq and
   kerLTensorEquivOfSurjective; the former requires the tensor factor to be flat
   and the latter concerns a surjection with flat target, so neither replaces
   the cycle theorem for the arbitrary first differential. Loogle found no Tor
   surjectivity theorem. Library searches found no duplicate. Verdict: pass.

4. Read Stacks Tag 00MM and checked the proof from Tor downward: homologyπ
   supplies a cycle, the cycle theorem supplies a finite sum of lifted cycles,
   and leftDerived_app_eq and homologyπ_naturality identify the canonical map's
   image term by term. This avoids a separate quotient exactness argument.
   The existing public imports support the public Tor types and canonical data;
   the added imports are proof-only. Removed one redundant import in the new
   module. No longer needed lists both former direct node dependencies and
   explains their continued transitive use. Read dag/units/sk-thm-p1.json:
   this auxiliary algebraic lemma is below its realized steps, and no realized
   unit statement or step is bypassed or changed. Verdict: pass.

5. Compared the existing node with the repository: only proof, proof_deps and
   proof_origin changed. The dependencies match the exact augmented resolution,
   new cycle lemma, canonical action laws and naturality argument. The new node
   has its source, self-contained statement, searches, complete proof steps,
   dependency union, provenance, blueprint, chapter, unit and Lean record.
   Both sources have the required module headers and exposure section.
   Verdict: pass.

Second-reading changes: removed the redundant TensorProduct.Finiteness import,
removed the obsolete dispute marker after checking the landed repair, rewrote
only the surjectivity docstring's final paragraph to match the direct homology
argument, and clarified the report's pruning and review evidence. No proof
term, existing signature or definition changed.
