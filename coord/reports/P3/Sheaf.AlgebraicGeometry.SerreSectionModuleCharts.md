## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Proj.serreSectionModuleCharts` with a complete Lean assembly of
three strictly smaller chart calculations. The original signature is unchanged.
The new modules are `SerreSectionModuleChartAdditive`,
`SerreSectionModuleChartScalar`, and `SerreSectionModuleChartRestriction`, all
under `Sheaf.AlgebraicGeometry`; they are imported only for the proof.

The additive lemma constructs a chart for one fixed homogeneous polynomial and
provides its denominator characterization. The scalar lemma calculates only on
homogeneous scalar and module representatives. The restriction lemma calculates
only on homogeneous module representatives. Neither compatibility lemma
constructs charts or assumes the conclusion of the original theorem.

The assembly chooses the chart family, uses the existing
`AlgebraicGeometry.serreSectionModuleComparison` to obtain homogeneous numerators,
and uses Mathlib `HomogeneousLocalization.Away.mk_surjective` for arbitrary
scalars. `LocalizedModule.mk_smul_mk` and `pow_add` finish the scalar clause.
The new private, completely proved `fractionChange_eq` clears denominators using
`LocalizedModule.mk_eq`, converts the clearing power of f into a power of g via
`g^e=a*f`, and proves the restriction formula for arbitrary (possibly
nonhomogeneous) representatives. The helper works over any commutative ring and
module, without a domain or positivity assumption.

Updated the parent's proof and proof dependencies to this assembly. Each new
module has one public theorem with `:= by sorry`, a source and full proof in its
docstring, and a matching new DAG node. There are no new definitions or statement
changes. The unit route is preserved: the parent is below
`lem-sc-p1-graded-resolution`, and all three calculations remain in its original
unit `sk-thm-picard-duality`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Proj.serreSectionModuleCharts`
(node `lem-sc-p1-serre-section-module-charts`). No `sorry` remains in the item's
module. The private helper `AlgebraicGeometry.Proj.fractionChange_eq` is fully
proved, including the independence of arbitrary fraction representatives.

This is a decomposition, not a proof without remaining assumptions: one upper
hole is closed and three strictly smaller holes are added (local net: -2; this
is not a claim of positive ledger progress):

- `AlgebraicGeometry.Proj.serreSectionModuleChartAdditive`, node
  `lem-sc-p1-serre-section-module-chart-additive`.
- `AlgebraicGeometry.Proj.serreSectionModuleChartScalar`, node
  `lem-sc-p1-serre-section-module-chart-scalar`.
- `AlgebraicGeometry.Proj.serreSectionModuleChartRestriction`, node
  `lem-sc-p1-serre-section-module-chart-restriction`.

The existing hole in `AlgebraicGeometry.serreSectionModuleComparison` is used and
unchanged; this delivery does not claim to close it. All four delivered modules
compile together in import order without warnings. The main assembly has been
checked after replacing the general compatibility statements by their strictly
homogeneous calculations and after removing redundant imports.

Edge cases of the new statements were checked mathematically: f=0 gives an empty
chart and zero localization; denominator exponent zero uses the zeroth twist and
right unitor; G=0 gives the zero chart; g=0 gives zero target localization; if a or
f is zero in the restriction relation, g=0 follows from e>0 over the polynomial
domain. For nonzero f,g,a, homogeneous degree uniqueness gives e*b=c+d. No finite
generation hypothesis is introduced, and the compatibility lemmas need neither
coherence nor an internal grading. The arbitrary-numerator extension is proved
in Lean rather than left among these holes.

## No longer needed

Removed the direct proof import
`WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules` from the
item. Its declarations remain available through the existing public import
`WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist`; its module is still
transitively needed. Removed from the parent's direct `proof_deps`:
`def-sc-degree-zero-module-fractions`. It is retained transitively through
`lem-sc-p1-serre-section-module-chart-additive`, so no original mathematical
dependency node is eliminated:
`def-sc-degree-zero-module-fractions` is now used in the additive chart theorem
and remains in the parent's statement dependencies. The comparison and twisting
sheaves remain needed. The three new modules are reduced to the imports their
statements use, plus the comparison proof import for the additive chart.

No unit statement or unit proof step is bypassed; no module is claimed to leave
the targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or mathematical error was found. The comparison theorem
has only existence and annihilation clauses, so it cannot directly supply the
additive chart and its two compatibility formulas. The needed quotient and
homogeneous calculations have now been made explicit as separate items.

The original proof's restriction step requires an extra denominator-independence
argument because the conclusion quantifies over arbitrary y in M, not just
graded numerators. That argument is now completely formalized. The scalar clause
needs no additive extension: every element of the homogeneous localization has
an equal-degree fraction representative, supplied by Mathlib.

The local checkout does not contain the cited Stacks source files. The cited
Proposition 0BXD was read on the Stacks Project website at
https://stacks.math.columbia.edu/tag/0BXD; the new fraction calculations expand
the existing node's numbered steps and are marked as agent expansions.
LeanSearch was unavailable; LeanFinder, Loogle, Mathlib/source searches and
blueprint duplicate searches were completed and recorded.

## New nodes

`lem-sc-p1-serre-section-module-chart-additive` states the canonical additive
chart on one fixed positive-degree standard open, with injectivity, range and
an iff characterization by homogeneous denominator clearing. Its proof is the
parent's step 1, using the existing comparison for existence and annihilation.

`lem-sc-p1-serre-section-module-chart-scalar` states the fraction calculation for
one homogeneous scalar a/f^l and one homogeneous numerator y/f^m, conditional on
the denominator characterization. Its proof is the parent step 2. Passing to
arbitrary scalars and arbitrary sections is proved in the item's module.

`lem-sc-p1-serre-section-module-chart-restriction` states only the restriction
calculation for a homogeneous numerator, conditional on the characterizations of
the two charts. Its proof is the homogeneous part of parent step 3. Passing to
arbitrary numerator representatives is proved in the item's module.

No change record is needed: no definition, existing statement, or public import
of the item was changed.

## Second reading by P3

1. **Visible declarations: pass.** Compared all delivered modules with the read-only
   repository. Only the parent module existed there; its theorem signature is byte
   for byte unchanged, including the arbitrary numerator in the restriction clause.
   Its public imports are unchanged. There are no changed definitions, existing
   hypotheses or conclusions, and hence no statement change record is required.
2. **Proof and trust: pass as a decomposition.** Compiled all four files in import
   order with lcompile.py, without errors or warnings. The sole parent hole is closed;
   the three new public named theorems contain exactly the reported three holes.
   No definitions or forbidden declarations were added. Scratch-copy `#print axioms`
   checks found only propext, Classical.choice, Quot.sound and sorryAx in the parent
   and the three open lemmas; the private fractionChange_eq has only the three standard
   axioms. It clears equality using g^(e*q), with the common factor a^(q+m+n), and
   does not assume a domain, homogeneous numerators, or e>0.
3. **Split statements: pass.** Read each signature, natural-language proof and node.
   The additive theorem supplies one fixed chart and its normalization; scalar and
   restriction theorems calculate on homogeneous representatives only, assuming
   normalization. Each is a strict part of the parent argument, not a renamed parent.
   Checked f=0, g=0, G=0, denominator exponents zero, and zero scalar numerator;
   when g is nonzero, g^e=a*f forces a,f nonzero and degree uniqueness gives e*b=c+d.
   No internal-grading or coherence assumptions are needed for the two conditional
   compatibility calculations. Independent searches used LeanFinder for sheaves of
   graded modules on Proj with scalar compatibility, Loogle for twistMul, and rg for
   localization/section maps, tensor charts, multiplication and restriction formulas.
   The hits concern the structure sheaf, twisting sheaves, or different associated
   module constructions; none closes these chart lemmas. Reviewed the cited final
   paragraph of https://stacks.math.columbia.edu/tag/0BXD; the new calculations are
   explicitly agent expansions of its canonical comparison. None of the three holes
   has a direct proof that can be completed in a few minutes with the available API.
4. **Route and pruning: pass after report repair.** The assembly uses comparison,
   Away.mk_surjective, mk_smul_mk, and the fully proved denominator-change helper.
   Every public import supplies statement vocabulary; new chart imports are private
   proof imports. Twist.Modules is already publicly re-exported by Twist. The removed
   direct degree-zero-fractions proof dependency is now explicitly listed above and
   retained transitively in the additive lemma. No unit route is bypassed: the unit
   realized fields are unchanged, and the decomposition stays below graded-resolution.
   No module is claimed pruned from the target closure.
5. **DAG agreement: pass.** Each recorded Lean statement exactly matches its file;
   each proof_deps is exactly the union of the proof steps' uses. Checked sources,
   agent proof origins, creation metadata, searches, chapter, unit, blueprint and Lean
   records of all three new nodes. The parent's steps describe the actual assembly,
   including its extension from homogeneous to arbitrary numerator representatives.

Second reading changed only this report: explicitly listed the removed direct
proof dependency and made the net -2-hole decomposition accounting explicit;
added the independent review and verification evidence. No Lean repair was needed.
