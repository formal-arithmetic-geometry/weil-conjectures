## What changed

Replaced `AlgebraicGeometry.alternatingCechSheafComplex_affineComparison` with a
proof factoring through global sections and the natural affine tilde-Gamma counit.
The existing signature and public imports remain identical. Added proof imports of
`AlternatingCechSheafAffineSections` and `AlternatingCechSheafAffineQuasicoherent`.
The construction of the complex isomorphism and composition of the two functors
are proved in the item; the section-complex identification remains in a new module.
The second new module
proves the termwise quasi-coherence obligation completely.

## Proved and sorry left

Closed: `AlgebraicGeometry.alternatingCechSheafComplex_affineComparison`
(node `lem-pc-s3-alternating-cech-sheaf-affine-comparison`). This is a decomposition,
not a sorry-free proof: one upper hole closed, one lower hole added (net 0 among
delivered declarations; the ledger determines import-closure totals).

Also proved, without adding a hole:
`AlgebraicGeometry.alternatingCechSheafComplex_affineQuasicoherent`
(`lem-pc-s3-alternating-cech-sheaf-affine-quasicoherent`). Its private finite-product
helper is also proved.

Added holes:

- `AlgebraicGeometry.alternatingCechSheafComplex_affineSections`
  (`lem-pc-s3-alternating-cech-sheaf-affine-sections`). It assumes neither separatedness,
  affine opens nor quasi-coherence and compares the actual section differentials.

No sorry remains in the item. No data definition, target signature or existing
interface changed. The only selected isomorphism is eliminated inside a proof;
no definition chooses data from an unproved mere existence statement.

## No longer needed

No existing imports removed. Removed the unused exploratory proof import
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` from the new
quasi-coherence module: the affine counit and tilde product preservation suffice.
Old direct proof dependencies no longer used directly by the combining proof:
`def-pc-s3-alternating-cech-sheaf-construction` and
`lem-pc-s3-alternating-cech-sheaf-terms`. Both remain transitively needed through
the new lemmas; their modules are not pruned.
No old dependency is eliminated from the closure:
the term lemma is needed by the quasi-coherence subproblem, the affine tilde-Gamma
adjunction is used by the combining proof, and the construction and affine model
remain statement dependencies. No unit step is bypassed. The qcqs-pushforward
lemma `pqf-lem-pushforward-qcoh` is additionally used as a generic tool, via
`Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`: only its quasi-coherence
conclusion is used for the affine morphisms from intersections. This does not
replace any unit step, and the unit has no more specific usable pushforward interface.

## Where the brief, the DAG or earlier work was wrong

The term comparison exposes only a degreewise `Nonempty` isomorphism, without a
face-naturality assertion. Thus its signature alone cannot implement the original
plan's differential compatibility. The new section-comparison lemma isolates this
compatibility without requiring a choice of unrelated degreewise isomorphisms.
`moduleSpecΓFunctor` has no available additive instance; its additivity is proved
by `rfl` locally, and embedded as a proved `letI` in the new section lemma's type.
The source-library affine-pushforward theorem was attempted, but the dry run
found an import cycle through `DirectImage.FiniteFreeComplex` and the proper-flat
Čech model back to this item. It was replaced with the acyclic, already proved
qcqs-pushforward interface. This import failure only appeared after the delivery
tool fetched the current source tree; the first direction check used the older tree.
LeanSearch returned Internal Server Error for both new-node queries (unavailable).

The first compile failed because the shared published build had not yet included
`AlternatingCechSheafConstruction.olean`; the normal build refresh supplied it.
The counit construction compiles with ordinary heartbeats. Explicitly applying
`Functor.mapHomologicalComplexCompIso` avoids expensive unfolding of the composed
functor at the final comparison. Empty index families, absent tuple types, negative
degrees, the empty scheme and the zero ring satisfy both new statements.

## New nodes

`lem-pc-s3-alternating-cech-sheaf-affine-sections`, in
`Sheaf.AlgebraicGeometry.AlternatingCechSheafAffineSections`: the section-complex
identification, including signed restrictions. Source: Stacks Tags 01FM and 02KG.

`lem-pc-s3-alternating-cech-sheaf-affine-quasicoherent`, in
`Sheaf.AlgebraicGeometry.AlternatingCechSheafAffineQuasicoherent`: termwise
quasi-coherence of affine pushforward, fully proved using the existing term comparison,
the qcqs-pushforward theorem specialized to affine morphisms, and finite-product
preservation by tilde.
Source: Stacks Tags 02KG and 02KH. No change records are needed.

## Second reading by F2

1. Compared the delivered item with the repository using `diff -u`: only two plain
   proof imports and the theorem body changed. The existing signature, visibility,
   docstring and all public imports are byte-for-byte identical. The other two
   modules are new; there are no definition or interface changes to existing code.
   Verdict: pass.
2. Compiled all three delivered modules in dependency order through `lcompile.py`:
   no errors or warnings. Searched every delivered module for forbidden declarations
   and holes: exactly one `sorry`, in the reported public section-comparison theorem;
   no definitions or anonymous/private declarations contain holes. Scratch copies
   with `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound` for
   `alternatingCechSheafComplex_affineQuasicoherent`, and those plus `sorryAx` for
   `alternatingCechSheafComplex_affineSections` and the original comparison.
   The selected section isomorphism is used only within a proof of `Nonempty`;
   no data definition extracts an arbitrary witness from an unproved theorem.
   Verdict: pass as a decomposition, not a completed axiom-free comparison.
3. Read both new statements, their complete proof docstrings, the actual presheaf
   and section differentials, and the corresponding nodes. The remaining hole is
   the section/differential identification for arbitrary module sheaves; it neither
   asserts nor repeats the affine tilde comparison. The separate quasi-coherence
   assertion is fully proved. Checked r=0, singleton and two-element families,
   empty opens, degrees past the tuple bound, negative degrees, the empty scheme
   and the zero ring. Empty products and extension terms are zero; in the first
   nontrivial differential the two face signs are +1 and -1 on both sides.
   Repeated searches using different words with leanfinder, loogle and grep;
   inspected `CechModuleSheafComparison`, `AdditiveAlternatingCechCoordinates`
   and upstream Čech declarations. The former compares an all-tuple complex,
   while the latter starts from the section complex and supplies no comparison
   to the sheafified complex here. Neither closes the remaining naturality proof
   directly. Verdict: true, strictly simpler obligations; no short replacement found.
4. Checked the actual counit naturality and composition-isomorphism proof from the
   top down, and the finite-product and negative-degree branches of quasi-coherence.
   All imports are used: plain imports supply proofs, public imports supply types
   and constructions in signatures. Every old proof dependency is either still
   direct or retained transitively; corrected the pruning report to name the two
   dependencies removed from the direct list. No module is pruned. The unit record
   `dag/units/sk-thm-picard-f-representable.json` has pre-existing empty `realized`
   arrays; this delivery neither changes that record nor bypasses its route or
   an existing realized node. Verdict: pass; the incomplete legacy unit mapping
   is recorded here rather than claimed complete.
5. Compared old and delivered node records and matched every proof step to Lean.
   The combining node uses the two new lemmas and the affine counit; the new
   quasi-coherence node records the term lemma and qcqs pushforward interface.
   Both new nodes have source, searches, provenance, chapter/unit, creation,
   blueprint and Lean records. The remaining hole has its own matching node.
   Verdict: pass.

Changes by the second reader: clarified in the new section lemma's docstring and
node proof that sheafification preserves finite products by additivity and finite
biproducts; recorded the independent searches on both new nodes; corrected the
old-direct-dependency accounting in `## No longer needed`; added this review.
No Lean proof or signature was rewritten and no additional hole was introduced.
