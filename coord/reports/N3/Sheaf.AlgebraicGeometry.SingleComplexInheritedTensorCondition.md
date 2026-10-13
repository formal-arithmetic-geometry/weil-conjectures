## What changed

Corrected the interface of `AlgebraicGeometry.singleComplexInheritedTensorCondition`
to bind the canonical tensor comparison `τ` and its characterization `hτ`. Its
conclusion now concerns that map, as in Stacks 0DJA(1), the unchanged natural-language
DAG statement, and the existing caller `SingleComplexBaseChangeCriterion`. The
monoidal existence clause remains and is proved from the existing core monoidal
model. This is an intermediate-statement correction under item step 5 and
coord/brief-stage3.md section 4, requiring independent CODEX review, not a proof
of the old assertion for every arbitrary strong monoidal structure.

Replaced the whole-proof hole with a complete compiling combination of two parts:

- `SingleComplexBaseChange.singleComplex_tensor_stalk_coordinates` gives input
  coordinates, K-flat stalk complexes, flatness of the fibre-product stalk over
  the tensor-product ring, and a comparison-map identity in arbitrary output
  coordinates. It assumes no isomorphism condition on the input map.
- `ModuleCat.localizedTensorComparison_inheritance` supplies the purely algebraic
  tensor inheritance. The item proves its input isomorphism hypothesis from
  `h_stalk` using homology of composition, applies the lemma, rewrites by the
  coordinate identity, and composes with the two coordinate isomorphisms.

These two statements, in separate new modules, are strictly different parts of
0DJA(1), not renamed copies of the item. Their docstrings contain their sources
and full proof arguments. In particular the ring argument uses the cohomological
isomorphism locus and generation by shifts of A; it does not posit a strict
complex of A tensor_R B modules representing a derived mixed tensor.
All supporting abbreviations use actual scalar extension, total tensor and
homology functors. No data is chosen from a new existence hole, and there is no
hole in a definition. The module retains its old public imports and adds a public
import of CanonicalPullbackTensorComparison for the predicate in the corrected
signature. Its proof import is SingleComplexTensorStalkCoordinates.

Updated the existing node's lean record, proof, proof_deps and proof_origin. Its
natural-language statement and all unit/chapter records stay identical. The
unit sk-thm-picard-semicon has no realized statement or step attached to this node;
this remains the single-complex tensor-inheritance step of the ancestor route.

The change record is
`coord/changes/N3-singleComplexInheritedTensorCondition-canonical.md`.
It contains the exact old/new signatures and all 379 transitive importers with
holders. The downstream --uses scan and whole-library word search found no
application of the theorem outside its defining module. No existing downstream
proof needs adaptation, and none was edited. No target declaration or definition
changes meaning or signature.

Sources read: Stacks perfect.tex, equation-bc preceding 0DJ8, and 0DJA(1),
including its proof by tensor transitivity; the source text is present in the
sandbox scratchpad from the earlier attempt. Read the cohomology-model,
K-flat-coordinate, balanced-model, canonical-comparison and core-monoidal-model
interfaces, the caller's statement, and derivedModuleFreeGeneration (09PB).
LeanFinder and Loogle searches plus source rg did not find the full comparison
inheritance or stalk-coordinate identity. Earlier genuine search records for
the two new nodes remain in searches.jsonl; unavailable LeanSearch responses
are recorded as unavailable, not as negative search results.

## Proved and sorry left

The corrected declaration `AlgebraicGeometry.singleComplexInheritedTensorCondition`
has a complete Lean proof with no direct sorry. One direct hole is closed in the
corrected module and two lower holes are added: this is a decomposition, with
local direct-hole delta 1 minus 2 = -1, not an unconditional proof.

Every sorry in the delivered sources is one whole public theorem proof:

- `ModuleCat.localizedTensorComparison_inheritance`, node
  `lem-pc-localized-tensor-comparison-inheritance`;
- `AlgebraicGeometry.SingleComplexBaseChange.singleComplex_tensor_stalk_coordinates`,
  node `lem-pc-single-complex-tensor-stalk-coordinates`.

Existing imported lower holes are untouched. The old universally quantified
arbitrary-monoidal-instance assertion is retired by the interface correction;
it is not established and must not be counted as proved. The new theorem is the
canonical source assertion, proved conditionally on the two named parts above.
No arbitrary-tensorator independence premise remains in the delivery.

Edge cases of the two new statements checked mathematically: zero complexes and
zero rings, empty X', identity base change, unbounded complexes, non-flat A/R,
and an arbitrary non-isomorphism phi. The algebra lemma needs flatness of C over
A tensor_R B, not of A over R. Its localizing-generation proof handles unbounded
inputs by a semi-free filtration and telescope, without a convergent spectral
sequence assumption. The coordinate lemma gives only map identities and K-flat
coordinates, independently of any comparison invertibility assumption.

All three modules compile through lcompile.py. The deliver3.py dry run supplies
compilation, axiom probes and mechanical preflight verification. The theorem
proof still rests on imported sorries; standard axioms alone are not claimed.

## No longer needed

Removed the original proof import `Sheaf.Algebra.Homology.DerivedTensorTransitivity`
and this item's edge to `lem-pc-derived-tensor-transitivity`, whose declaration
`DerivedCategory.exists_derivedTensor_transitivity` lacks the promised flat
comparison-map clause. This is pruning of the item's direct edge, not a claim
that the old module is globally unreachable. Mixed associator and balanced
model nodes remain part of the ring lemma's comparison-naturality argument.

Removed the earlier sandbox module `SingleComplexTensoratorIndependence` and
its node `lem-pc-single-complex-tensorator-independence`, and its proof import.
These were never landed. The canonical source/caller interface needs no
arbitrary-tensorator comparison. The corrected theorem accepts τ,hτ directly;
its proof also needs no use of exists_canonicalPullbackTensorComparison.
Every retained/new proof import supplies an actual part of the proof. Existing
public imports remain.

## Where the brief, the DAG or earlier work was wrong

The existing DAG statement and Stacks 0DJA(1) use the canonical map. The old Lean
interface instead quantified over every strong monoidal structure on the fixed
pullback. The caller already uses τ with IsCanonicalPullbackTensorComparison.
The earlier attempted bridge asserted that an arbitrary tensorator's ratio
could descend through free resolutions to the mixed comparison. Its source and
proof did not justify that assertion; it has been removed rather than reused.
I do not claim a counterexample to the old arbitrary-instance assertion.
The interface correction here is explicit, with a change record, and is not
presented as a proof of the old stronger quantified statement.

The node's old plan calls a flat cohomological clause of
exists_derivedTensor_transitivity that its actual Lean statement does not have:
it supplies only existence of a chain associator conjoined with True. The new
ring statement supplies the missing comparison inheritance without editing
that other group's module.

The earlier ring proof's phrase 'extend the balanced model to C' could incorrectly
suggest a strict chain-level A tensor_R B module construction. The revised
proof uses the genuine tensor-ring actions on cohomology and their long exact
sequences, flat scalar extension, and free-module generation. It does not need
that strictification. There are no forced adaptations or edits of held modules.
The obsolete second-reading section from the earlier attempt was removed; a
fresh independent second reading is required for this changed delivery.

## New nodes

`lem-pc-localized-tensor-comparison-inheritance`, module
`Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritance`, states the flat
mixed-ring cohomology comparison inheritance for two A-K-flat complexes, a
specified C-chain map, arbitrary canonical cohomology models and a scalar
extension tensor isomorphism pinned on each summand. Its proof in words uses
natural canonical comparisons and free-module generation. This is the algebra
part only.

`lem-pc-single-complex-tensor-stalk-coordinates`, module
`Sheaf.AlgebraicGeometry.SingleComplexTensorStalkCoordinates`, gives canonical
comparison coordinates and their exact conjugation identity, including stalk
flatness and K-flatness but no comparison-isomorphism hypothesis. This is the
geometric identification part only.

Both records have their source, search evidence, full proof steps and dependency
union, Lean signature, creation and blueprint ancestry. The sole interface
change record is `coord/changes/N3-singleComplexInheritedTensorCondition-canonical.md`.


## Second reading by N3

Independent second reader, 2026-10-13. I did not write the candidate proof.

1. **Interfaces and visible changes.** Compared the item with the repository using
   `diff -u`. Its sole existing theorem signature changes exactly as recorded in
   `coord/changes/N3-singleComplexInheritedTensorCondition-canonical.md`: the
   arbitrary monoidal-instance tensorator is replaced by the pinned canonical
   family tau and its predicate. This is an intermediate interface correction,
   not a proof of the old universally quantified assertion. No existing definition
   or target is edited. Repeated the downstream --uses scan and whole-library
   declaration search: 379 transitive importers, no application outside this module.
   The caller already binds the canonical family. Verdict: explicit CODEX-class
   correction; no accidental statement change or forced adaptation.

2. **Kernel checks and holes.** Compiled all three files in import order with
   lcompile.py, without errors or warnings. Inspected every delivered declaration:
   exactly two whole named theorem holes, as listed above, no hole in a definition,
   no axiom, unsafe, opaque, implemented_by or extern, and lines at most 100 columns.
   A scratch module printed axioms for the item, both new theorems, and all three
   new supporting definitions. The theorem proofs use only propext, Classical.choice,
   Quot.sound and sorryAx; the three definitions use only the permitted three.
   The scratch file was removed. Verdict: sound conditional reduction, not a
   sorry-free proof or positive net-hole progress. The old assertion remains unproved;
   the corrected assertion is decomposed into two lower obligations.

3. **New statements and sources.** Read Stacks 0DJA(1) and its tensor-transitivity
   proof in the local perfect.tex, the actual cohomology-model equations, canonical
   comparison predicate, coordinates and K-flat stalk criterion. The ring lemma
   fixes arbitrary P,N,t: its isomorphism locus in E is cohomological and closed
   under sums because C is flat over A tensor_R B. Shifts of A reduce to the input,
   and derivedModuleFreeGeneration handles unbounded E. The model action equations
   pin the tensor-ring action; no strict mixed derived complex is assumed. The
   geometric lemma identifies maps, supplies K-flat stalks and flat localization,
   and assumes no comparison invertibility. These are distinct proper parts of the
   argument. Checked zero inputs/rings, identity base change, empty Xprime,
   non-flat A over R and an arbitrary non-isomorphism phi: none invalidates either
   statement. Repeated LeanFinder with a cohomology/flat-coefficient formulation,
   Loogle with homologyMap and IsIso, Mathlib grep and source rg using comparison,
   localization and inheritance vocabulary. The hits cover ordinary flat tensor
   and homology maps, not these two statements; the library localization lemmas
   vary coefficient localizations, not tensoring by E. Neither hole has a short
   closure by the available declarations. Verdict: true, source-supported and
   strictly simpler obligations, not renamed restatements of the item.

4. **Route and pruning.** Read the original transitivity declaration: it supplies
   a chain associator with True, not the required flat cohomology-map inheritance.
   Its removal and the entire old proof_deps list are accounted for in No longer
   needed. Read the unit record: realized statement and sole step are empty; no
   unit/chapter route is bypassed. Checked each public import against signature
   needs (including BifunctorShift, which defines CochainComplex.mapBifunctor),
   and the item uses a plain proof import for the coordinate lemma. Verdict:
   appropriate top-down algebra/geometric reduction and complete direct-edge pruning;
   global unreachability of the old module is not claimed.

5. **DAG agreement.** Compared the existing node fields: only lean, proof,
   proof_deps and proof_origin differ. Its natural-language statement is unchanged.
   Checked all three proof-step dependency unions, referenced node existence,
   new-node source/search/creation/ancestry fields and Lean signatures. The item's
   proof establishes the input module comparison by homologyMap_comp, applies
   algebraic inheritance, then conjugates by the coordinate isomorphisms, exactly
   as recorded. Verdict: metadata agrees with the Lean and the unchanged unit.

Second-reading changes: replaced “extension by zero” in the new coordinate
lemma's proof description by “termwise skyscraper complexes”, matching the
existing KFlatStalkCriterion proof; added this independent review. No Lean
signature, proof body or node field was changed by the second reader.
