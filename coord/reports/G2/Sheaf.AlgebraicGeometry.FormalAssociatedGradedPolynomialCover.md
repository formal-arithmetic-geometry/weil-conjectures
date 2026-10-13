## What changed

Proved AlgebraicGeometry.formalAssociatedGraded_polynomial_cover with its entire original
signature unchanged. Two new modules contain fully proved auxiliary theorems:
FormalPolynomialPowerLifts constructs ideal-power evaluation lifts by affine range
calculations and sheaf gluing; FormalPolynomialQuotientSpan proves local spanning by
lifting quotient sections and expanding homogeneous polynomials into monomials.
The item combines them and proves restriction, addition, multiplication and constants
using injectivity of the recursively constructed power inclusions.
Repair of the landing return: removed the duplicate private power_mono and
power_injective from the item and quotient-span module. In the power-lifts module,
generalized them in place to arbitrary monic structure-module maps as public
formalPolynomial_power_mono and formalPolynomial_power_injective. All three proofs
reuse this one pair. Also exposed formalPolynomial_extendedIdeal_affine in power-lifts
and removed its duplicate from quotient-span, which now imports power-lifts.
Only proof imports were replaced in the item. No definitions or existing interfaces changed.
The existing node now records the actual proof and dependencies. The unit's route is unchanged.

## Proved and sorry left

Closed the sole original hole: AlgebraicGeometry.formalAssociatedGraded_polynomial_cover
(lem-weil-pbc-formal-associated-graded-polynomial-cover).
Also fully proved AlgebraicGeometry.formalPolynomial_power_lifts
(lem-weil-pbc-formal-polynomial-power-lifts) and
AlgebraicGeometry.formalPolynomial_quotient_span
(lem-weil-pbc-formal-polynomial-quotient-span). Added no holes; none remain in any delivered
module. This is a proof, not a decomposition into new sorries.
The three delivered modules compile together without errors or warnings through lcompile.py.
#print axioms for each of the three public theorems reports exactly propext, Classical.choice
and Quot.sound, with no sorryAx.
Edge cases are retained: degree zero uses the identity power inclusion, empty generators
are covered by the homogeneous ideal-power identity, an empty family uses the same affine
neighbourhood, and empty schemes/opens and zero rings require no additional assumptions.

## No longer needed

Removed the item's direct proof imports of
WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine and
Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections. These are used in
both proved auxiliary modules and therefore remain necessary transitively. Replaced them
with proof-only imports of FormalPolynomialPowerLifts and FormalPolynomialQuotientSpan.
Removed the quotient-span module's direct proof import of
WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine; its affine calculation
now reuses formalPolynomial_extendedIdeal_affine via the proof import of
FormalPolynomialPowerLifts. Removed duplicated private power helpers from both the
cover and quotient-span modules and the duplicate extendedIdeal_affine from
quotient-span. No node or module in the original proof route is pruned: every original dependency remains
needed through the actual proof or one of its auxiliaries. The power-lift module imports
the actual ideal-power and ideal-module definitions directly, without importing the
associated graded/formal-module interface it does not use.

## Where the brief, the DAG or earlier work was wrong

The landing return correctly identified duplicate private power_mono and
power_injective proofs. They were consolidated and generalized as described above;
no existing library theorem signature or visibility changed. The two auxiliary
modules are new modules of this unlanded delivery. No mathematical error was found. The original plan fits the existing
signatures. For monomial spanning, the proof uses the equivalent Mathlib declaration
Ideal.mem_span_pow_iff_exists_isHomogeneous rather than directly rewriting
Ideal.span_pow_eq_map_homogeneousSubmodule. Intersections of affine opens were never
assumed affine: injectivity compares restrictions directly on each intersection.
LeanSearch returned Internal Server Error; the unavailable query is recorded accurately.
The cited Stacks .tex files are absent in this read-only clone; Tags 0884 and 087Z were
read from the official Stacks website. The polynomial refinement and the affine/gluing
details are written by the agent and recorded as such, rather than attributed as verbatim
claims of those lemmas.

## New nodes

lem-weil-pbc-formal-polynomial-power-lifts corresponds to the fully proved theorem in
lean/Sheaf/AlgebraicGeometry/FormalPolynomialPowerLifts.lean. It states only existence of
ideal-power representatives with prescribed evaluation images; it assumes no graded
algebra structure and does not repeat the polynomial-cover conclusion. The representatives
are unique by the proved monicity argument.

lem-weil-pbc-formal-polynomial-quotient-span corresponds to the fully proved theorem in
lean/Sheaf/AlgebraicGeometry/FormalPolynomialQuotientSpan.lean. It assumes given evaluation
lifts and proves only local spanning of their quotient images, with no multiplicativity,
unit or naturality conclusion. Both nodes inherit the original chapter and unit and carry
actual search records. No change records or forced adaptations are needed.

The second reading below records the previous, returned version; the repaired
helper consolidation and generalization require a fresh independent reading.

## Earlier second reading (a previous round; superseded)

1. Interface: compared the complete delivered item with the repository by diff. The
existing theorem signature and docstring are byte-for-byte unchanged; public imports,
definitions and visibility are unchanged. Only its proof, private proof helpers and
proof-only imports differ. Corrected an extra space immediately before `:= by` to
restore literal signature identity. No change record or forced adaptation is needed.

2. Proof: independently compiled all three modules in import order with lcompile.py,
without errors or warnings. Scratch copies with `#print axioms` for
AlgebraicGeometry.formalAssociatedGraded_polynomial_cover,
AlgebraicGeometry.formalPolynomial_power_lifts and
AlgebraicGeometry.formalPolynomial_quotient_span each report only propext,
Classical.choice and Quot.sound. No delivered theorem contains sorry; no unsafe,
opaque, axiom declaration, extern, implemented_by or kernel-check bypass occurs.
The existential lifts are obtained from a fully proved theorem and uniquely determined
by their images, using the proved sectionwise injectivity. No definition chooses
arbitrary data from an unproved existence statement.

3. Auxiliary statements: read both new signatures, their docstrings and nodes against
the actual proofs. The power-lifts theorem assumes precisely a ring, ideal, scheme,
morphism and finite generating family; its conclusion is an evaluation preimage on
all opens. Its affine calculation uses ideal_comap_appLE and ideal_top_ofIdealTop;
positive degrees use the affine power-range clause, and degree zero is the identity.
The gluing proof compares restrictions on arbitrary intersections by injectivity,
not by assuming those intersections affine. The quotient-span theorem adds only
given lifts and their image formula; it assumes no graded algebra compatibility.
Its quasi-coherence and quotient-surjectivity applications use the kth power module,
and its linear-map span argument projects actual lifts. The coefficient-one monomial
argument permits section-ring coefficients even though polynomials are over A.
Neither auxiliary restates the item, and both are fully proved, leaving zero split-off
holes. Tested the argument at k=0, r=0 (positive powers zero), I=0, I=top, zero rings,
empty opens/schemes, and s=0: no positivity, nonemptiness or Noetherian assumption is
silently used. Both docstrings give complete proofs and have matching source/node ids.
Read Stacks [0884](https://stacks.math.columbia.edu/tag/0884), proof of
lemma-vanishing-projective, and [087Z](https://stacks.math.columbia.edu/tag/087Z):
they provide the associated graded context; the polynomial refinement is correctly
recorded as the agent's argument rather than the literal statement of either tag.
Independent LeanFinder search used "Sections of a quasi coherent ideal power admit
unique preimages under the inclusion and homogeneous monomials generate its quotient
on affine neighbourhoods"; it returned affine ideal/localization results, no exact
replacement. Loogle confirmed Ideal.mem_span_pow_iff_exists_isHomogeneous, already
used. A new msearch grep used "power.*injective|injective.*power|homogeneous.*span|
span.*homogeneous"; rg of lean/Sheaf, lean/WeilConjectures and the upstream checkout
found related power-range and polynomial-presentation results, no exact auxiliary.
Read Mathlib Homogeneous.lean lines 650–675: the two ideal-span identities support
the existing proof directly. No shorter replacement was found.

4. Route and pruning: followed the item downward through the two auxiliaries to the
original affine ideal-extension and ideal-times-affine-sections declarations. All
five clauses of the unchanged conclusion are proved: restriction and addition by
injectivity, multiplication by hmul and injectivity, constants by hunit, and local
spanning by the quotient-span theorem. Proof-only imports remain proof-only.
Checked every import against its signature or proof uses. In particular, removing
the Quasicoherent import from scratch copies of either auxiliary fails at
SheafOfModules.isQuasicoherent_unit, so it is necessary despite indirect imports.
The original proof_deps all remain used directly or through auxiliaries; no old
node/module is pruned. The direct imports replaced are completely listed under
No longer needed. Read dag/units/sk-thm-p1.json realized: no realized statement or
step is replaced, and the unit record is unchanged.

5. Metadata: compared the existing node fields: only proof, proof_deps and
proof_origin changed. Each proof_deps is the union of the step uses. The old affine
extension and affine-section dependencies remain in both auxiliary nodes. New nodes
have complete creation, source, blueprint, search, chapter/unit and Lean records;
their verbatim signatures match the Lean declarations. Their proof steps describe
the induction, affine calculation, gluing and monomial/span arguments actually
written. Source ancestry and the unit are retained. Verdict: the complete delivery
passes the second reading.

Changed only the signature's extra space and added this independent review; no
mathematical proof repair was necessary. Removed all temporary scratch copies.


## Second reading by G2

1. Interface: independently diffed the existing item against the read-only repository.
The existing theorem signature is byte-for-byte identical, including whitespace.
Its existing docstring, public imports and visibility are unchanged; only its proof,
proof-only imports and a declaration-local elaboration option changed. There are no
changed definitions, forced adaptations or change records. Verdict: pass.

2. Proof: independently compiled all three repaired modules in import order through
lcompile.py without errors or warnings. Scratch copies with #print axioms checked the
cover, both main auxiliary theorems, and the shared public power_mono, power_injective
and extendedIdeal_affine helpers. Every check reports only propext, Classical.choice
and Quot.sound. There is no sorry, forbidden declaration or kernel bypass in any
module. Choices in power_lifts come from proved existence, with sectionwise injectivity
also proving uniqueness. No data are taken from an unproved theorem. Verdict: pass.

3. New statements: read the generalized monicity/injectivity statements and proofs,
both auxiliary statements, their docstring proofs and all new node records. The
monicity induction works for an arbitrary monic structure-module map; it uses only
identity, the given mono, image inclusions and composition. The affine extension
helper computes the actual pulled-back ideal. Evaluation lifts and quotient spanning
are distinct parts of the argument, and both are fully proved. Examined k=0, r=0,
I=0, I=top, zero rings, empty opens/schemes and s=0: each is covered without extra
hypotheses. In particular the degree-zero monomial is constant one, and coefficients
in the section ring multiply monomials defined over A. Independent LeanFinder search
for monic sheaf maps and recursive ideal powers returned the already-used
PresheafOfModules.injective_of_mono but no replacement for the recursive power
argument. Loogle confirmed Ideal.mem_span_pow_iff_exists_isHomogeneous. msearch grep
and local rg searches found no public replacement for the new helpers or auxiliaries;
existing private power_mono lemmas specialize to ideal-sheaf data and cannot be reused.
The repaired modules share one generalized pair, with no duplicate local power proof.
Verdict: pass; zero split-off holes.

4. Route and pruning: traced the cover downward through power_lifts and quotient_span
into the affine ideal extension and ideal-times-quasi-coherent sections theorems.
All five conclusions are obtained directly: restriction and addition by injectivity,
multiplication from hmul and injectivity, constants from hunit and degree zero, local
spanning from the affine quotient argument. Overlaps need not be affine: injectivity
compares the two restricted lifts on the intersection itself. Each import supplies
statement data or proof ingredients; proof-only imports are plain imports. Every old
proof dependency is still used directly or through the auxiliaries, so no old node or
module is pruned. No longer needed lists the replaced direct imports. Checked
sk-thm-p1.json realized; the unit route is retained and its record is unchanged.
Verdict: pass.

5. Metadata: the existing node differs only in proof, proof_deps and proof_origin.
All three recorded primary signatures occur verbatim in their Lean modules. Each
proof_deps equals the union of its proof-step uses. Read the new nodes' creation,
source, blueprint ancestry, chapter/unit, search and Lean fields; the step descriptions
match the actual affine, induction, gluing and monomial/span proofs. Agent-written
refinements are identified as such. Verdict: pass.

Second reading changed only this report by appending the fresh independent review.
No mathematical proof or interface repair was necessary. Removed the scratch axiom
copies before delivery. Closed one original hole, added none; both new auxiliary
statements and all shared helpers are fully proved.
