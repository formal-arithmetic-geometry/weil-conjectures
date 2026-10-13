## What changed

The existing `Scheme.Modules.exists_flatBaseChange_affine_dictionary` statement is
byte-for-byte unchanged. Its proof obtains the source comparison and passes both its
bijective linear map and its pure-tensor normalization to the repaired target component,
then assembles the witnesses and conjunctions. The two component imports are proof-only.

New modules `Sheaf.AlgebraicGeometry.FlatBaseChangeAffineSource` and
`Sheaf.AlgebraicGeometry.FlatBaseChangeAffineTarget` state the source and conditional target
parts. The target helper originally quantified over arbitrary additive eH: this was false.
Its repaired hypotheses require a bijective B-linear source lift with the source
normalization, exactly the data obtained by the source helper. No existing declaration
outside the item is changed, and no definition is introduced or changed.

Both new theorems now have complete natural-language constructions in their docstrings,
and both new nodes have self-contained statements, verbatim Lean signatures, actual
searches, and explicit proof dependencies. Proof-plan imports are private imports; the
public imports supply only the definitions and classes in the signatures.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_affine_dictionary`
(node `lem-weil-pbc-flat-base-change-affine-dictionary`) now has a Lean proof of its
unchanged statement, conditional on the two components below.

Holes added:
- `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_affine_source`, node
  `new-flat-base-change-affine-source`;
- `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_affine_target`, node
  `new-flat-base-change-affine-target`.

This is a decomposition: one upper hole closed, two strictly smaller component holes
added, net -1 for these declarations. It is not a sorry-free proof of the mathematics and
is not claimed as positive ledger progress. There is no hole in a definition. The source
has no target conclusion; the target assumes the full normalized source data and concludes
only the target comparison. The parent performs the existential elimination and assembles
all four conjuncts; neither helper restates the whole parent conclusion.

## No longer needed

None. No original public import was removed. Every node in the original proof_deps is
still used in the component construction plans: affine charts and module pullback,
restricted resolutions, flat Ext comparison, qcqs higher-image quasi-coherence, affine
vanishing, normalized Leray edges, higher-image presheaves, affine pullback section
bijectivity, source module/Ext comparison, module/abelian comparison, and the module h-map.
The parent's direct proof_deps are now the two component nodes; this is not pruning those
original dependencies from the overall route. No module is claimed pruned.

The source additionally uses the existing affine pullback sections construction (the
original bijectivity dependency alone does not construct the map). The repaired target
uses the independent separated flat cohomology and Mayer-Vietoris gluing tools to extend
a normalized source change of coordinates. These are generic tools, not a replacement of
any step of unit sk-thm-p1.

## Where the brief, the DAG or earlier work was wrong

The first target helper was too strong. In degree zero with f and g identity on Spec K,
F the structure sheaf, and K = Q(t), take the canonical degree-zero comparison composed
with the additive field automorphism t ↦ -t. The target formula would require a K-linear
map to act by this non-K-linear inverse automorphism, which is impossible. Requiring the
normalized B-linear source lift excludes this case. This fault was only in an unlanded
new helper; the parent signature and the library definitions are unchanged.

For the repaired target, let e0,a0,b0 be the canonical section-complex comparisons and
c the independent flat Ext base-change equivalence. The map
b = b0 o c o a0 inverse o a o c inverse is B-linear and bijective. Source normalization
at 1 tensor xi gives a(1 tensor xi)=a0(1 tensor e0(eH inverse xi)); cancellation and
canonical class-map compatibility give the target formula. This avoids assuming that eH
itself is linear, and uses no resolution-defined beta or the parent dictionary. It does
use flat cohomology invertibility, unlike the original canonical-choice proof plan; that
additional tool use is recorded explicitly in the target node and the parent docstring.

The original helper docstrings supplied no proof in words, their node statements were
not self-contained, and their proof dependencies were empty. Those defects are repaired.
The mathematical comparisons remain open, rather than being presented as completed work.

## New nodes

`new-flat-base-change-affine-source`: existence of the source comparison and its normalized
bijective tensor-section lift only. It follows the source half of the original affine
Leray and module/abelian comparison route.

`new-flat-base-change-affine-target`: existence of the target comparison conditional on a
normalized bijective source lift. Its docstring proves the change-of-coordinates argument
and explains the independent qcqs flat Ext base-change induction used to transport it.

No change record is needed: no previously landed signature or definition changed.

## Second reading by N3

1. Compared every delivered module with the read-only repository. Only the parent exists
   there; its full theorem signature is byte-for-byte identical. The only parent changes
   are proof-only imports, a local heartbeat allowance, its proof, and the proof docstring.
   The two helper modules are new. No target, existing definition, or external module changes.
2. Compiled the three modules in import order with lcompile.py. Exactly the two named new
   helper theorems contain sorry. No axiom, unsafe, opaque, implemented_by, extern, or
   definition with sorry occurs. Explicit axiom probes are recorded below after final
   validation; sorryAx is expected because the component statements remain open.
3. Rejected the arbitrary-additive-eH target helper by the identity/degree-zero example
   above, and repaired it by passing source a, bijectivity, and normalization. Checked the
   new conditional target by the explicit conjugation formula, including empty opens,
   zero coefficients, degree zero, and non-faithful flat scalar extension (no descent of
   eH-linearity is used). The source component is exactly the source half. Both docstrings
   now explain their complete mathematical constructions. Repeated searches with different
   leanfinder, loogle, and grep queries using msearch.py; inspected the existing module/Ext
   comparison, affine pullback sections, Leray edge, and DirectImage.Sections declarations.
   They supply parts, but none supplies these D-normalized dictionaries outright. No
   component can be closed in a few minutes by applying an existing matching declaration.
4. Kept the target-downward reduction. All original plan dependencies survive in the new
   component plans; no unused original node or module is omitted from the report. New
   proof-plan imports are private. Inspected dag/units/sk-thm-p1.json realized: the item
   realizes no unit-level step being replaced, and its additions are generic comparison
   tools. No unit record or chapter route changes.
5. Checked the parent's proof against its two direct proof_deps; checked both new node
   signatures against the Lean, and filled their statement dependencies, source,
   natural-language proof steps, proof_deps, proof_origin, searches, blueprint origin,
   creation data, chapter/unit, status and lean records. Dependencies match the deferred
   constructions rather than claiming either component is proved.

Second-reading changes: repaired the false target quantification, passed normalized source
witnesses in the parent proof, supplied both docstring proofs and full DAG records,
repeated searches (including the required LeanSearch service, which returned Internal Server Error),
documented the decomposition and lack of pruning, and fixed line lengths.

Final local axiom validation: an independently compiled scratch copy with explicit
`#print axioms` for all three delivered declarations reports exactly `propext`,
`Classical.choice`, `Quot.sound` and `sorryAx`. No other axiom occurs. The scratch copy
was removed before delivery. The first dry run reached the delivery fetch and failed
because the project server's SSH connection timed out; this is a transport failure,
not a Lean error, and the dry run is being retried.

Sources read for this review: [Stacks 02KH](https://stacks.math.columbia.edu/tag/02KH),
[01E4](https://stacks.math.columbia.edu/tag/01E4),
[03FD](https://stacks.math.columbia.edu/tag/03FD), and
[01XJ](https://stacks.math.columbia.edu/tag/01XJ). LeanSearch was unavailable; its failure
is recorded without a mathematical absence verdict, with the successful other searches
retained. The preflight's required search categories are LeanSearch, Loogle/LeanFinder,
and grep; all categories are now recorded.
