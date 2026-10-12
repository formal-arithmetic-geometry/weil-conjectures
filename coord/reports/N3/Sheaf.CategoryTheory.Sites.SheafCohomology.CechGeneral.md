## What changed

Removed the refused earlier reduction from the delivery candidate. Its four Lean
files, four node copies, and report are preserved under scratchpad/rejected-attempt,
which deliver3.py does not deliver. In particular, no theorem asserting the
unsupported large-site acyclic model is introduced.

The delivered CechGeneral module keeps every signature, universe, visibility,
import, and theorem body unchanged. Added a STATEMENT-DISPUTED comment at
CategoryTheory.Sheaf.exists_cechDoubleComplex_general: the claimed generality
has not been justified by its cited injective-resolution proof. This is a request
to review that generality, not a claim of a verified counterexample or a proof
of its negation. No target signature or definition is changed.

Compiled the node's entire planned composition in scratchpad/ResolutionRoute.lean
with an explicit InjectiveResolution F and equal universes. The proof constructs
Sheaf.cechResolutionDoubleComplex I X pi, then applies the existing columns and
total declarations; it compiles. Applied exactly that composition to the original
hypotheses in scratchpad/OriginalRoute.lean. The compiler rejects it with:

```
failed to synthesize instance of type class
  HasInjectiveResolution F
failed to synthesize instance of type class
  Category.{w, u} C
```

The next error identifies pi as a family of v-universe morphisms where the
selected equal-universe construction expects w-universe morphisms. These failures
are distinct: solving the coefficient-size bookkeeping does not supply a resolution.
The scratch files are experiments, not delivered library modules or new holes.

## Proved and sorry left

Original holes closed: none. New holes added: none. The one unchanged hole is
CategoryTheory.Sheaf.exists_cechDoubleComplex_general
(node stage3-cech-general-double-complex). This candidate records a statement/source
review dispute; it does not claim to prove or decompose that theorem.

The refused previous attempt closed this hole syntactically by introducing three
new holes. None of those new holes is part of this delivery. In particular,
Sheaf.exists_cechAcyclicCohomologyModel is not being smuggled back into the library
under a different name.

A further compiling scratch experiment, SmallEvaluation.lean, proves that under
HasExt.{w} every original abelian sheaf G has w-small values G(X). The argument
uses the free-abelian/sheafification/Yoneda adjunction to identify G(X) with
Hom(Z[X],G), then Ext.homEquiv0 to exhibit a surjection from the w-small Ext0
onto G(X). Thus the earlier reader's size concern can be narrowed: if a genuine
resolution in the original sheaf category is supplied, its individual evaluated
terms can be shrunk. This does not prove that such a resolution exists, and is
not claimed as a closure of the assigned hole.

## No longer needed

No repository import, module, or DAG node is globally pruned by this delivery.
The three original proof imports remain: CechResolutionDoubleComplex,
CechResolutionColumns, and CechResolutionTotal. They implement the equal-universe
composition successfully tested above and are not declared unnecessary merely
because the independent-universe step is unresolved.

The previous candidate's new modules CechAcyclicModel, CechColumnsGeneral, and
CechRowCollapse, and its three new nodes, have been removed from the candidate.
They were never established as a valid delivery. Their removal is cleanup of a
refused proposal, not claimed ledger progress or global pruning.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original node's instruction to choose a universe-lifted
injective resolution and transport along ULift skips resolution existence in the
original category of v-small sheaves on an arbitrary large site. HasExt is
smallness of shifted localized Hom types. The recorded three proof dependencies
all take an explicit injective resolution and use equal coefficient/index
universes; none supplies the missing resolution. Mathlib's standard
HasExt.standard works in sufficiently large universes for every abelian category,
so HasExt cannot be treated as another name for enough injectives.

Read the cited sources directly:
[Stacks 03AZ](https://stacks.math.columbia.edu/tag/03AZ) constructs the ordinary
Grothendieck spectral sequence;
[03AW](https://stacks.math.columbia.edu/tag/03AW) assumes an injective abelian sheaf
for its Cech vanishing;
[03F6](https://stacks.math.columbia.edu/tag/03F6) transfers injectivity from sheaves
to presheaves. None constructs the previous attempt's large-site resolution model
or its asserted small diagram replacement.
[Stacks 00VG, Remark 7.6.3](https://stacks.math.columbia.edu/tag/00VG) explicitly
excludes big sites from its site convention. Merely citing 03AZ therefore does
not justify all independent universes in this Lean statement.

No counterexample to the original theorem was established. In particular, compiler
failure is not evidence that the theorem is false. What is established is that the
recorded plan, with exactly the supplied hypotheses and recorded dependencies,
does not produce the claimed theorem, and the previous split's word proof assumed
the missing construction. I have preserved the original hole and exposed the
source/generality dispute instead of presenting that assumption as a true lemma.

The next mathematical obligation is a source-backed argument constructing a
cohomology model for this large-site Ext theory, or a justified review of the
intermediate statement's generality and all affected callers. The compiling
small-evaluation argument above removes termwise shrinking as an independent
obstacle once a resolution in the original coefficient category is available.


## Second reading by N3

1. Interface preservation: compared the sole delivered Lean module with the
   repository by `diff -u`. The only difference is the four-line
   STATEMENT-DISPUTED comment immediately before
   CategoryTheory.Sheaf.exists_cechDoubleComplex_general. Every declaration,
   signature, universe, section variable, attribute, import and proof body is
   unchanged. No change record or adapted module is needed. Verdict: pass.

2. Proof and trust: independently compiled CechGeneral.lean with lcompile.py
   (exit 0). A scratch copy with `#print axioms` reports exactly propext,
   Classical.choice, Quot.sound and sorryAx. Inspected the whole candidate:
   its sole hole is the original named theorem reported above; it contains
   no definitions, new holes, axioms, unsafe/opaque declarations or foreign
   implementations. This is a dispute delivery with zero holes closed, not
   a completed proof or a decomposition. Verdict: accurate accounting; the
   theorem remains unproved.

3. Split statements: none are delivered. Checked the delivery tree: the three
   rejected split modules and their nodes occur only under scratchpad, outside
   deliver3.py's Lean and node selection. Recompiled SmallEvaluation.lean
   separately (exit 0); it proves only termwise smallness and does not supply
   an injective resolution. No existence witness from an unproved theorem is
   introduced. Verdict: no unsupported split survives.

4. Route and pruning: read CechResolutionDoubleComplex, CechResolutionColumns
   and CechResolutionTotal in full, the upstream equal-universe comparison,
   and dag/units/sk-thm-picard-cech.json. The construction takes an explicit
   InjectiveResolution F; both comparisons use coefficient/index universe v.
   Independently recompiled ResolutionRoute.lean (exit 0) and OriginalRoute.lean
   (expected failure: HasInjectiveResolution F, Category.{w, u} C and the
   morphism-universe mismatch). Searched lean/Sheaf and lean/WeilConjectures
   for enough-injectives, resolution and existing comparison declarations.
   Mathlib's GrothendieckAxioms/Sheaf.lean supplies the relevant sheaf
   Grothendieck-category result under SmallCategory or EssentiallySmall,
   absent here. DerivedCategory/Ext/Basic.lean defines HasExt by smallness
   of shifted localized Hom types and proves HasExt.standard without enough
   injectives. No direct resolution theorem applicable to the original
   hypotheses was found. Read Stacks 03AZ, 03AW, 03F6 and 00VG Remark 7.6.3
   directly: their arguments do not fill this size/resolution gap. Neither
   failed synthesis nor those source conventions prove the Lean statement
   false. The comment correctly reports an unsupported proof plan, explicitly
   without claiming a counterexample. The unit's realized entries are empty;
   its route, all three planned proof imports and all public signature imports
   remain unchanged. No old proof dependency is claimed pruned. Verdict:
   justified proof-plan dispute, no mathematical refutation established.

5. DAG consistency: read stage3-cech-general-double-complex.json and matched
   its HasExt, sheafification, finite-wide-pullback and covering assumptions
   and both column/total conclusions against Lean. No Lean proof was changed,
   so the node's existing proof/proof_deps/proof_origin remain its unresolved
   plan, with the gap explicitly recorded here. No new node or unit rewrite
   is needed for a comment-only dispute. Verdict: unchanged plan accurately
   identified as incomplete, not claimed realized.

Second reading changed only this review section. The original theorem and its
hole are retained; no target or intermediate statement was weakened. The
candidate is suitable only as a report of the existing proof-plan dispute.
