## What changed

Replaced the sole sorry in RootNormalizationLocalizationComparison with a complete Lean
proof from two strictly smaller geometric intermediate theorems. Added the modules
RootCoverNormalizationCartesian and AffineLocalizationPullbackStalk, each containing
one public named theorem, its source and full proof in words. Existing signatures and
public imports stay identical. A proved private helper transports the supplied
AdjoinRoot localization certificate across the polynomial equality by equality elimination.
The proof registers T.isFinite explicitly, obtains qcqs by affine composition and base
change, proves finiteness by the cartesian square, checks denominator avoidance using
hcontract, computes the extended root ideal with map_under and map_root, and specializes
the general structural-germ identity to the root. The node now follows this proof.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.root_normalization_localization_comparison
(lem-sbc-root-normalization-localization-comparison). Its proof contains no sorry.
There are no retained holes in the original module.

Added holes:
- AlgebraicGeometry.Scheme.root_cover_normalization_cartesian
  (lem-sbc-root-cover-normalization-cartesian): the cartesian geometric comparison,
  with no selected point, finite-normalization conclusion or root-germ assertion.
- AlgebraicGeometry.Scheme.exists_lift_stalkEquiv_of_isLocalization
  (lem-sbc-affine-localization-pullback-stalk): point and stalk lifting for an arbitrary
  affine localization square, independent of torsors, DVRs and normalization.

This is a decomposition: one upper hole closed and two lower holes added, net -1.
All three delivered modules compile individually through lcompile.py. No signature,
visibility, definition or target is changed. Neither new theorem chooses data for a definition.

## No longer needed

Removed the direct proof import Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange
from the original module; its theorem and node remain needed transitively through
RootCoverNormalizationCartesian, so neither is globally pruned. No other preexisting
module or node is pruned. All added proof imports are used. The second reading also removed redundant public imports
Mathlib.AlgebraicGeometry.PullbackCarrier and Mathlib.RingTheory.Localization.Ideal
from the new AffineLocalizationPullbackStalk module: Stalk already provides the signature API. Existing public imports
are preserved because this delivery changes no public interface.

## Where the brief, the DAG or earlier work was wrong

Step 3 of the original DAG had no named declaration despite containing substantial
point-lifting and stalk-localization geometry. This is now a generic independent item.
Step 2 also needed transport of the normalization comparison across root and cover
pullback identifications; the existing stalk-normalization theorem alone did not state
that transport. The cartesian intermediate isolates precisely that work.
GaloisCover.isFinite is not automatically registered as an instance; it must be supplied
locally for the affine composition used to establish qcqs. The branch hypothesis is
retained throughout; no component-selection shortcut is used.

Edge cases checked: the general localization lemma assumes an actual point, excluding
empty X; a denominator mapped to zero cannot satisfy disjointness at that point. With
M={1}, it reduces to stalk transport through a cartesian isomorphism. It uses no reducedness,
domain, Noetherian or normality assumptions. The root cartesian lemma still assumes the
DVR and irreducible pi, which identify the punctured trait with its fraction-field spectrum,
and hbranch is essential to identify the entire generic pullback. Trivial finite G has
Nat.card G=1 and causes no additional restriction. Unit sk-prop-input-spreading is unchanged.

## New nodes

lem-sbc-root-cover-normalization-cartesian is stated in
Sheaf.AlgebraicGeometry.Morphisms.RootCoverNormalizationCartesian and isolates the
point-independent cartesian comparison of the normalizations. Its sole planned project
proof dependency is lem-sbc-normalization-stalk-base-change, which is already proved.

lem-sbc-affine-localization-pullback-stalk is stated in
Sheaf.AlgebraicGeometry.Morphisms.AffineLocalizationPullbackStalk and isolates the
localization point/stalk comparison with compatibility for every base element.
Its planned proof uses Mathlib prime correspondence, localization transitivity and
stalk-map naturality. Neither node restates the original theorem. No change record
is required: all existing signatures and public imports remain identical.

## Second reading by C2

1. Compared the original module with the repository using diff. Its existing theorem
   signature and docstring are byte for byte unchanged; all existing public imports
   remain unchanged. There is no definition change, target change or forced adaptation.
   The private polynomial-transport helper is proved by equality elimination. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py, without errors or
   warnings. The only direct sorries are root_cover_normalization_cartesian and
   exists_lift_stalkEquiv_of_isLocalization, both reported above. There are no axioms,
   unsafe/opaque/extern/implemented_by declarations, or definitions selecting data from
   unproved existence. Explicit scratch #print axioms checks and the delivery probe
   verify the permitted standard axioms plus sorryAx from the two open lemmas.
   Verdict: pass as a decomposition, not a net proof gain.
3. Read both new statements, their complete docstring arguments, and their nodes.
   The cartesian lemma isolates normalization transport before selecting a point;
   it needs neither hfin, hx nor hcontract, and asserts neither finiteness nor a
   root-germ identity. The general localization lemma assumes only a localization
   square and denominator avoidance, with no torsor or normalization data. Both are
   true and strictly separate parts of the argument, not restatements of the item.
   Checked the zero-ring/empty-spectrum exclusion by the supplied point and avoidance,
   the identity localization M={1}, and the trivial group with Nat.card G=1.
   Independent LeanFinder searches for flat preimmersions/local ring isomorphisms
   and normalization commuting with prime localization, a Loogle query, and rg on
   Mathlib, lean/WeilConjectures and lean/Sheaf found no exact existing replacement.
   Mathlib's preimmersion base-change and flat-stalk APIs offer a possible future
   proof of the general lemma, but do not close it directly. Verdict: pass.
4. Read the proof top down. It independently establishes qcqs, transports finiteness
   by base change, derives denominator avoidance from the contraction equality,
   computes the extended root ideal using map_under/map_span/map_root, and obtains
   the requested root-germ identity by specializing the generic compatibility.
   The old proof dependency NormalizationStalkBaseChange remains used transitively
   by the cartesian lemma; its node is not pruned. Read sk-prop-input-spreading.json:
   its realized entries are empty, and no realized node or unit step is bypassed.
   Verdict: pass; neither remaining geometric proof closes in a short direct step.
5. Matched the three node declarations, proof steps, proof_deps and proof_origin
   against Lean. The original node changes only allowed proof fields. Both new
   nodes carry sources, docstring proof plans, searches, provenance, chapter/unit
   and Lean records. Replaced their flattened lean.statement fields with the actual
   multiline signatures verbatim. Verdict: pass.

Second-reading changes: removed two redundant public imports from the new generic
localization module; corrected its companion root-cartesian module's copied author
credit to C2; removed trailing whitespace from the original module's new proof;
made both new nodes' recorded signatures verbatim. No mathematical statement or
proof argument changed. One original hole closed, two strictly smaller holes added,
net -1; no globally pruned module. Final dry-run and push results are recorded by
those tools.
