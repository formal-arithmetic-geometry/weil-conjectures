## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.CoherentIdealPatchingExactSequence` with a complete Lean reduction.
Its existing signature and all public imports are unchanged. The proof obtains a
property-independent generic embedding, then selects the subobject satisfying `P` using
`hG`. It proves coherence of the ideal pushforward and its prescribed finite biproduct,
proves that the biproduct vanishes outside the closed image, and constructs the canonical
mono-cokernel short exact sequence. It proves the quotient support bound and its zero
ξ-stalk using surjectivity of stalk cokernel projections. The first term is the selected
module itself, so the required isomorphism is the identity and no isomorphism invariance
of `P` is assumed. The zero-middle case uses exactly `P(0)`.

Added the separate module
`Sheaf.AlgebraicGeometry.CoherentIdealPatchingGenericEmbedding`, containing only the
remaining geometric embedding theorem. It does not mention `P`, the property-bearing
subobject hypothesis, or a short exact sequence. It also leaves coherence and support
of the middle term to the proved code of the original module. Updated the original DAG
node to match this reduction, and gave the new theorem a complete node and proof in words.
No existing statement, definition, visibility or other module was changed.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.coherent_ideal_patching_exact_sequence`:
1 of the original 1 syntactic holes is closed, by a compiling Lean proof.
Added 1 hole:
`AlgebraicGeometry.Scheme.Modules.coherent_ideal_patching_generic_embedding`
(`lem-weil-pbc-coherent-ideal-patching-generic-embedding`), in its own module, with proof
exactly `:= by sorry`.
This is a decomposition, not a sorry-free proof or a net reduction in holes: 1 closed,
1 added, net 0. No other theorem or definition in the delivered files contains `sorry`.
In particular, property selection, mono cancellation, generic surjectivity, coherence,
biproduct support and all cokernel-sequence conclusions have actual Lean proofs.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`;
- `Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion`;
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`;
- `Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk`;
- `Sheaf.Paper.SchemeTheoreticSupport`.

The complete list of old direct `proof_deps` removed from the parent node is:

- `def-pur-sheaf-tensor-product`;
- `lem-weil-pbc-coherent-generic-point-ideal-inclusion`;
- `lem-weil-pbc-finite-type-module-support-closed`;
- `lem-weil-pbc-integral-scheme-ideal-generic-stalk`;
- `lem-weil-pbc-module-iso-on-stalks`;
- `lem-weil-pbc-quasi-coherent-ideal-intersection`;
- `lem-weil-pbc-scheme-sober`;
- `lem-weil-pbc-scheme-theoretic-support`;
- `pqf-lem-coherent-ft-locnoeth`.

These are not claimed as globally unnecessary mathematical results: the finite-type
criterion is used through existing coherence results, and the other geometric results
remain in the new embedding node's proof plan. No blueprint unit or realized step is
bypassed. No whole mathematical module is certified pruned by this delivery.
The old saved attempt's uncommitted geometric-core and property-step nodes were discarded;
they were circular and had no declarations in the saved Lean file.

Added proof-only imports for the new embedding, general coherent closure, affine
quasi-coherent pushforward, quasi-coherent kernels, and the Mathlib stalk/additive and
module-short-complex APIs actually used. Kept closed pushforward stalks, stalk exactness,
finite coherent pushforward and locally Noetherian submodule closure, all used explicitly.

## Where the brief, the DAG or earlier work was wrong

The saved report said the theorem was proved by two intermediate declarations, but the
saved Lean file contained neither declaration and still had the original `sorry`.
Its two saved nodes referred back to the parent theorem as their proof dependency;
this is circular. They were replaced, rather than reused. The saved report also wrote
the second reader's section; the replacement report leaves that section to the reader.

The previous tool-failure diagnosis was not reproduced: the current delivery tool checks
a legitimate decomposition. Its first dry run instead identified the short declaration
name in the new node; this was corrected to the fully qualified Lean declaration name. The replacement theorem performs real property
selection and exact-sequence construction rather than handing the full statement to a
new name. The geometric lemma was checked on the zero ideal, a field, and a nonreduced
ambient scheme with an integral closed subscheme. For I=0 the zero alternative applies;
for a nonzero I its generic stalk is the entire generic field, so a positive sum can
contain the generically full ideal multiple. The annihilator used is that of the coherent
cokernel, and is generically the unit ideal. No arbitrary witness from an unproved
existence theorem defines data: all witnesses are used only inside proposition proofs.

`tools/blueprint_refs.py ancestor` returns no ancestor for the original node because its
`created.item` names a module rather than a node. The original node already records the
ancestor `thm-weil-pbc-finite-etale-lifting` and the devissage chain; the new node preserves
that recorded ancestor and extends its chain. Blueprint searches for `ideal multiple`
and `01YL` found no imported blueprint node with this statement. The auxiliary source
lemmas on affine pushforward and quasi-coherent kernels are existing proved generic tools.

## New nodes

`lem-weil-pbc-coherent-ideal-patching-generic-embedding` states the geometric preparation
from Stacks Tag 01YL, third proof paragraph and intersection argument. For every ideal on
the integral closed source, a positive sum of its pushforward is either zero or receives
a mono from JG, generically bijective, where J is a quasi-coherent ideal with unit generic
stalk. The proof plan constructs the common intersection ideal, its embedding into G,
then the coherent cokernel's annihilator and the factorization of ideal multiplication.
Every non-elementary step names existing nodes; no dependency points back to the parent.
Mathlib searches used LeanFinder, Loogle and source grep; LeanSearch was attempted and
returned Internal Server Error, recorded as unavailable. No change record is required.

## Second reading by H1

Independent second reader, 2026-10-13; neither delivered Lean proof was written by this
reader. Checked the module, both node files, the repository originals, the dependency
statements, and `dag/units/sk-thm-p1.json`.

1. **Existing interface: PASS.** The diff changes only proof imports and the original
   theorem body. Compared the entire existing theorem signature as bytes: identical.
   All six original public imports, declaration visibility, hypotheses, conclusions,
   and definitions are unchanged. The original node changes only `proof`, `proof_deps`,
   and `proof_origin`. No change record or forced adaptation is needed.
2. **Lean proof and axioms: PASS as a decomposition.** Independently ran
   `lcompile.py --all` on both delivered modules: clean compilation, 2.7 s and 12.6 s.
   Compiled scratch copies with `#print axioms` for both public theorems: exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; no other axiom.
   Read the reduction, including the zero-middle branch, the cancellation proving
   generic surjectivity, the literal middle biproduct, and both quotient stalk arguments.
   The only new hole is the named geometric embedding theorem with `:= by sorry`.
   No forbidden declaration mechanism or holed definition occurs. Existential geometric
   witnesses are eliminated inside a proposition proof; no definition chooses arbitrary
   data from the unproved theorem. Scratch probes and their artifacts were removed.
3. **Split statement: PASS.** The new theorem has no arbitrary property P, no
   property-bearing subobject hypothesis, and no short exact sequence; it is strictly
   the geometric preparation. Read its complete proof in words against
   [Stacks 01YL](https://stacks.math.columbia.edu/tag/01YL) and
   [Stacks 01YE](https://stacks.math.columbia.edu/tag/01YE).
   Taking the actual annihilator of the coherent cokernel replaces the source's power
   of a support ideal and gives the required factorization. For I=0 use the zero
   alternative with r=1. For X=Z=Spec(k), G=k^d with d>0 and I=OX, take J=OX and r=d.
   For the nonreduced example X=Spec(k[epsilon]/epsilon^2), Z=Spec(k), the generic
   annihilation hypothesis forces G to be a nonzero finite k-vector space; the same
   construction works. For a domain and nonzero I, intersection with the generically
   full ideal remains nonzero and generically full. Integral Z is nonempty, so there
   is no empty-source exception. Independently repeated LeanFinder, Loogle and grep
   searches with different words (logged in searches.jsonl): no existing theorem
   provides this embedding. LeanFinder returned finite-generator APIs, Loogle no hits,
   and grep unrelated algebraic annihilator results. Read the generic ideal inclusion,
   integral generic stalk, scheme-theoretic support and neighboring filtration and
   property modules; they provide parts of this construction, not the whole statement.
   Completing the geometric factorization in Lean is substantial work and was not
   claimed closed in this reading.
4. **Route and pruning: PASS after report repair.** The proof starts at the original
   hole and proves the nongeneric remainder directly with existing coherent closure,
   closed pushforward, and stalk exactness results, plus Mathlib's canonical cokernel
   complex. Every new proof-only import is plain `import`; all remaining imports have
   a concrete signature or proof use. The auxiliary module's public imports provide
   the types and definitions appearing in its new signature. The parent is below
   the unit level; none of its removed dependencies is a realized statement or step
   of sk-thm-p1. Its geometric dependencies remain in the new lemma's plan, and no
   chapter or unit route is bypassed. Added all nine removed old direct DAG dependencies
   to `## No longer needed`; removing direct imports is not a claim of global pruning.
5. **Nodes and Lean: PASS.** For both nodes the union of proof-step `uses` equals
   `proof_deps`, and every cited node exists. The new node's recorded Lean statement
   is verbatim its declaration signature; its module, qualified declaration, source,
   searches, creation fields, chapter, unit and blueprint ancestry are present and
   agree with the code. Its plan has no edge back to the parent theorem. The parent
   node records precisely the new reduction, and its statement and other fields stay
   unchanged. The new theorem has its own matching DAG node and complete sourced
   docstring proof. No unit record needs a change.

**Second-reader changes:** completed the report's list of removed direct proof
 dependencies and appended this independent review. No Lean or node edit was necessary.
The delivery remains a decomposition: one original hole closed, one strictly simpler
hole added, net zero; no whole module is certified globally pruned.
