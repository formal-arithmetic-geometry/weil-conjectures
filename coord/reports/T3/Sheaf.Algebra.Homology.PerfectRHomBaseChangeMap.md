## What changed

Repair of the latest failed landing: added PerfectRingHomTensorDegrees and
PerfectRingHomTensorDifferential (under Sheaf.Algebra.Homology) to the change record's
Users table. The table now covers thirteen existing modules: the held item and twelve
downstream users. Refreshed claim holders from the current checkout; the downstream
modules are unclaimed. No Lean source or DAG statement changed in this repair.
The delivery tool rebuilds the delivery on freshly fetched origin/sheaf-dag.

In Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap, proved
CategoryTheory.ringRHomBaseChangeData_exists from the existing
SheafOfModules.derivedChangeOfRings and the new supporting import
Sheaf.Algebra.Homology.NormalizedRingHomExtension. The proof unpacks the existing
extension and derived functor, chooses normalized chain maps for each P,Q, and fills
all ten structure fields. Relocated RingSiteModules, ringSiteMap,
ringHomComplexProjection, ringHomEvaluate,
ringExtensionComplex and ringExtensionPure into the supporting module, with signatures,
bodies, visibility and docstrings unchanged. The original module re-exports them.
Updated def-pc-perfect-rhom-base-change-map's proof route and dependencies.
Second reading made DerivedChangeOfRings and KFlatResolution proof-only imports,
added the public LeftDerived import required by the structure signature, removed the
redundant direct KFlatTensorQuasiIso import (re-exported by the supporting module),
and replaced unused Mathlib.Algebra.Module.FinitePresentation with the precise
Mathlib.RingTheory.Finiteness.Defs import used by Module.Finite.

## Proved and sorry left

Latest repair verification: both delivered modules compiled with lcompile.py --all
(supporting module 36.4 seconds; item 8.9 seconds). The byte-identical originals of
PerfectRingHomTensorDegrees and PerfectRingHomTensorDifferential then compiled in
import order against the delivered overlay (41.5 and 2.7 seconds). The shared compiled
snapshot initially lacked Degrees; compiling that unchanged original in the scratch
overlay supplied it for Differential. This required no source adaptation.
A fresh six-definition scan found thirteen existing users and no missing Users rows.
Earlier downstream verification below belongs to the previous review round.

Repair verification: both delivered modules compiled cleanly with lcompile.py --all
(36.0 and 9.0 seconds). All ten byte-identical downstream originals compiled against
the delivered outputs. The five previously omitted users compiled in 1.6–2.2 seconds;
the other five compiled in 1.7–32.6 seconds. No downstream adaptation is necessary.

Closed: CategoryTheory.ringRHomBaseChangeData_exists
(def-pc-perfect-rhom-base-change-map), the only original sorry in this module.
No sorry remains in the item's module.

Added: CategoryTheory.normalizedRingHomExtension_exists
(lem-pc-normalized-ring-hom-extension), in its own new module.
This is a decomposition: one hole closed and one strictly smaller chain-level hole added;
net hole reduction is zero. The new statement supplies no derived functor, counit,
left-derived universal property, or K-flat counit isomorphisms. Those fields are obtained
by the real Lean proof from the existing derivedChangeOfRings theorem.
The two previously proved theorems in the original module are unchanged.
Both delivered modules compile cleanly with lcompile.py --all (supporting module
47.7 seconds; original module 12.0 seconds). The delivery dry run also passes
its axiom probe. Compiled the unchanged originals of BaseChangeRHomPerfect,
BoundedRingHomExtensionDegree, FiniteProjectiveRingHomExtension, PerfectRingHomKFlat
and PerfectRingHomScalarExtension against the sandbox outputs; all five compile cleanly
in 2.3–3.2 seconds and need no adaptation.

## No longer needed

Removed direct import Sheaf.Algebra.Homology.KFlatTensorQuasiIso: the supporting
module publicly imports it because its definitions use onePointRingSheaf.
Removed Mathlib.Algebra.Module.FinitePresentation, replacing it by
Mathlib.RingTheory.Finiteness.Defs: the statement uses Module.Finite, not finite presentation.
DerivedChangeOfRings and KFlatResolution remain imported privately for proofs.
All six old proof_deps remain used; no DAG node or target-closure module is pruned.
The removed direct imports do not constitute module pruning in the sorry ledger.

## Where the brief, the DAG or earlier work was wrong

The latest landing check found two additional downstream users absent from the
previous repair: PerfectRingHomTensorDegrees and PerfectRingHomTensorDifferential.
Both now appear in the Users table. A fresh scan of all six relocated definitions
finds thirteen existing modules, all covered by that table.

The existing final proof step explicitly left normalized data existence unfinished.
The derived half of this construction was already available in derivedChangeOfRings;
only the chain-level normalized Hom map must remain a new item.
The local checkout lacks the untracked Stacks source files, so read Stacks Tag 0A6A
and Section 0E1V online. The chain-level tensor calculation expands the construction
of the displayed derived map; it is marked agent-written rather than claimed to be
verbatim from the source's proof.

The Mathlib searches were actually run with msearch.py: LeanFinder returned ordinary
scalar-extension/tensor-map lemmas, Loogle returned ModuleCat.extendScalars and its
adjunction, and the targeted Hom-complex/change-of-rings grep returned no hits.
LeanSearch returned Internal Server Error, recorded as unavailable. Blueprint searches
for base-change-RHom and scalar-extension found no matching imported node.

Edge cases for the new statement: the zero ring, zero complexes, nonflat B/A, and
unbounded complexes all satisfy the tensor evaluation construction. Infinite products
cause no obstruction: one maps from the scalar extension of a product to the product
of scalar extensions, and never asserts this map is an isomorphism. For phi the
identity, the formula reduces to ordinary evaluation. No arbitrary witness is chosen
inside a definition; the only new choice is within a theorem proving Nonempty data,
and the normalization determines each chain map by pure tensors and product coordinates.

## New nodes

lem-pc-normalized-ring-hom-extension: a chain-level normalized comparison on the
one-object bottom-topology site for arbitrary complexes. Its module is
Sheaf.Algebra.Homology.NormalizedRingHomExtension. It has no derived category or
perfectness hypothesis and proves only a proper part of RingRHomBaseChangeData existence.
The node and the theorem docstring give the balancing, product and differential arguments.
Change record: coord/changes/ring-hom-extension-shared-definitions.md.
No existing module besides the held item was edited; no forced adaptations are needed.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules against the repository with diff and declaration
   tables. All 16 original declaration statements and visibility settings are identical.
   All six relocated definitions have identical bodies and docstrings. The relocation
   and public-import adjustments are declared in the change record; no target meaning
   or definition changes. Verdict: pass.
2. Compiled both modules through lcompile.py --all. Only
   CategoryTheory.normalizedRingHomExtension_exists has sorry, exactly as a named theorem.
   No prohibited declarations or hollow definitions occur. The delivery axiom probe checks
   every declaration; the explicit scratch #print axioms checks the principal theorems
   and definitions. Imported unfinished results can contribute sorryAx. Verdict: pass.
3. Read the split theorem, its full tensor-balancing and differential proof, its node,
   HomComplex's actual product/projection specification, and the scalar-extension data.
   For phi=id the formula is ordinary evaluation; zero rings and zero complexes give
   zero maps. Nonflat examples (Z to Z/2) need no exactness, and unbounded products need
   only a map into the target product. Normalization determines each map by pure-tensor
   generation and jointly monic product projections. The theorem omits all derived
   functor/universal-property/counit fields, so is a strictly smaller step rather than
   a restatement. Independent LeanFinder search for "canonical scalar extension
   comparison for internal Hom complexes", Loogle on ModuleCat.extendScalars, and
   grep/rg searches of Mathlib, upstream and Sheaf found no theorem supplying this
   normalized chain map; ordinary scalar-extension adjunction lemmas cover only the
   term-level construction. It cannot be closed in a few minutes with those lemmas.
   Checked Stacks Tags 0A6A and 0A8X; the explicit chain calculation is correctly
   labelled agent-written. Verdict: pass.
4. The top-level proof really unpacks derivedChangeOfRings and assembles all ten fields;
   it does not assume the original data-existence assertion under another name.
   All old proof dependencies are still used. The unit sk-thm-picard-duality has empty
   realized statement/step lists; this below-unit construction bypasses no realized
   unit node and changes neither its statement nor its route. Corrected the proof-only
   public imports and removed the redundant/heavier imports listed above. Verdict: pass.
5. Checked that the old node's updated proof uses exactly its proof_deps, and that the
   new node has matching Lean signature, source, complete proof steps, dependency union,
   searches, created/blueprint/chapter/unit and lean fields. No unauthorized existing
   node fields change. Verdict: pass.

Changes by the second reader: import visibility/minimality repairs, the additional
Loogle search record in the new node, and this report.
No statement, definition, proof body, split theorem, or proof-dependency route changed.
This remains a decomposition: one original hole closed, one chain-level hole added,
net hole reduction zero.

Verification after the import repairs: the principal module compiles in 8.8 seconds;
the delivery dry run prints OK. The nine explicit #print axioms checks compile in
2.3 seconds and list only propext, Classical.choice, Quot.sound and (for theorems
using named open results) sorryAx. In particular all four checked shared definitions
have no sorryAx. The five byte-identical downstream originals compile against the
repaired delivered outputs in 2.4–3.4 seconds. No forced adaptation is needed.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository version and parsed all 16
   original declarations. Every original statement and visibility is unchanged;
   the six relocated declarations also retain their bodies and docstrings exactly.
   The relocation and public-import changes are covered by the change record.
   Its Users table covers all eleven modules found by a fresh declaration-use
   search (the held item and ten downstream modules). Verdict: pass.
2. Independently compiled the delivered set with lcompile.py --all: supporting
   module 39.0 s, item 9.8 s, no errors or warnings. The only delivered sorry is
   CategoryTheory.normalizedRingHomExtension_exists, a named theorem with its
   node and full proof docstring. No prohibited declarations or hollow definitions
   occur. Re-ran the nine explicit #print axioms checks against the current sandbox
   overlay: only propext, Classical.choice, Quot.sound and sorryAx occur. Only the
   split theorem and the data-existence theorem use sorryAx among these checks.
   Verdict: pass.
3. Read the split statement against the actual HomComplex product-limit and
   differential specifications and the change-of-rings definitions. Tensor
   balancing gives the stated evaluation formula for arbitrary complexes; checking
   coordinates gives the two differential terms with the same sign. Zero rings,
   zero complexes, identity extension and nonflat Z to Z/2 cause no exception.
   Infinite products require only a map into a product. Pure tensors span because
   all presheaves on this bottom-topology site are sheaves, so the sheafification
   unit is invertible. Together with product projections and internal-Hom
   naturality on the one-object slice, this also determines the comparison map;
   no arbitrary existence witness is used as undefined data. The split omits the
   derived functor, universal property and counit fields and is strictly smaller
   than the original existence statement. Fresh LeanFinder search for 'extension
   of scalars natural comparison between Hom complexes evaluation tensor', Loogle
   on ModuleCat.extendScalars, and grep plus local rg searches found termwise
   tensor/adjunction infrastructure but no duplicate normalized chain map.
   RingHomExtensionTransport provides only a termwise transport and imports the
   held item, so cannot directly discharge the new theorem without a cycle.
   The full remaining chain construction is not a few-minute proof. Read the
   primary sources https://stacks.math.columbia.edu/tag/0A6A and
   https://stacks.math.columbia.edu/tag/0A8X; the expanded chain calculation is
   correctly labelled agent-written. Verdict: pass as a decomposition.
4. The upper proof genuinely unpacks derivedChangeOfRings and fills eight derived
   extension fields before supplying the two chain-map fields from the split
   result. It is not a renamed application of the original statement. Imports
   needed only for proofs are private. No old proof dependency is unused; no
   target-closure module is pruned. The unit sk-thm-picard-duality has empty
   realized statement and step lists, and this change preserves its route.
   Verdict: pass.
5. Compared the old node diff and the new node with the Lean. Existing edits are
   confined to lean, proof, proof_deps and proof_origin. The new node's signature,
   source, proof, dependency union, searches, creation data and blueprint agree
   with the split theorem. Verdict: pass.

Changes in this reading: added this independent review and rebuilt the scratch
axiom check against the current sandbox outputs instead of the old scratch overlay.
No delivered Lean or node repair was needed. One original hole is closed and one
strictly smaller hole added, for net zero; neither a sorry-free proof of the entire
construction nor module pruning is claimed.

Final compatibility verification: all ten byte-identical downstream originals compile
against the current delivered overlay (1.7-30.0 s each). One check overlapped the
start of the delivery tool's rebuild, which temporarily removed the supporting
artifact; rerunning it and the remaining checks after that rebuild passed cleanly.
The delivery dry run printed OK and passed its full declaration axiom probe and
preflight. No downstream adaptation is necessary.

## Second reading by T3

Independent reading of the latest repair, including the two newly listed tensor users.

1. Compared the item with the repository using diff, then parsed the union of both
   delivered modules. All 16 existing declaration signatures are byte-identical;
   visibility is unchanged. Apart from ringRHomBaseChangeData_exists, every existing
   body and docstring is unchanged, including all six relocated definitions.
   The relocation and import changes are covered by the existing change record.
   A fresh source search finds exactly its thirteen Users rows. Verdict: pass.
2. Recompiled both delivered modules with lcompile.py --all (38.8 s and 9.5 s),
   without errors or warnings. The only delivered sorry is the named theorem
   CategoryTheory.normalizedRingHomExtension_exists. There are no forbidden
   declarations and no holes inside definitions. Recompiled the nine explicit
   scratch #print axioms checks against the current delivered overlay (2.1 s):
   only propext, Classical.choice, Quot.sound and sorryAx occur; sorryAx occurs
   only for the split theorem and ringRHomBaseChangeData_exists. Verdict: pass.
3. Checked the split statement against the actual product-limit and differential
   fields of homComplex_exists and the actual objects/maps of derivedChangeOfRings.
   Tensor balancing constructs evaluation in each coordinate, and its two
   differential terms agree, including the sign. Identity extension, zero rings,
   zero complexes and nonflat extension Z to Z/2 require no extra hypothesis.
   Unbounded complexes require a map into a product, not preservation of products.
   Pure tensors generate on this bottom-topology site; coordinate evaluation
   determines the internal Hom maps and product maps. Choice occurs in a theorem,
   and the normalization determines the chosen chain map, rather than choosing
   arbitrary data from bare existence. The split omits all derived-functor,
   universal-property and counit fields: it is strictly part of the argument.
   Fresh LeanFinder search for 'base extension evaluation morphism internal Hom
   cochain complexes tensor product', Loogle on ModuleCat.extendRestrictScalarsAdj,
   msearch grep and rg over Sheaf, upstream and Mathlib find ordinary tensor/Hom
   evaluation and scalar-extension adjunctions, but no duplicate chain-map theorem.
   RingHomExtensionTransport imports the held item and cannot close this split
   without a cycle. The full remaining construction is not a few-minute proof.
   Read https://stacks.math.columbia.edu/tag/0A6A and
   https://stacks.math.columbia.edu/tag/0A8X; the expanded chain argument is properly
   identified as agent-written. Verdict: pass as a decomposition.
4. Read the upper proof top down: eight fields come from the established derived
   change-of-rings theorem, and only the two chain-map fields use the split theorem.
   All six old proof dependencies remain used, and the report correctly claims no
   pruned node or module. Proof-only imports are private; the retained public imports
   support signatures or the relocated definitions. sk-thm-picard-duality has empty
   realized statement/step lists; this change bypasses no realized unit step and
   preserves the unit route. Verdict: pass.
5. Existing node edits are exactly proof, proof_deps, proof_origin and lean.
   The new node has the matching Lean statement, full proof, source, dependency
   union, searches, creation record, blueprint, chapter/unit and lean fields.
   Its proof route matches the construction left to formalize. Verdict: pass.

Changes in this reading: added this current independent review and fresh verification
artifacts under scratchpad only. No Lean source, statement, definition, node or change
record needed repair. Closed CategoryTheory.ringRHomBaseChangeData_exists; added
CategoryTheory.normalizedRingHomExtension_exists. One original hole closed and one
strictly smaller hole added; net reduction zero. No pruning is claimed.

Current compatibility verification: all twelve byte-identical downstream originals
compiled together in import order against the delivered overlay (2.7-50.8 s each),
including PerfectRingHomTensorDegrees and PerfectRingHomTensorDifferential.
No forced source adaptation is necessary.
