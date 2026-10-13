## What changed

Replaced the sole sorry in `AlgebraicGeometry.IsCurve.additive_cohomology_tensor_kernel`
without changing its signature or its existing docstring. The proof transports the
specified beta to the existing ordinary structure-module base-change map, using
`TensorProduct.AlgebraTensorModule.congr` and tensor extensionality. The proved
`Scheme.Modules.H.baseChange_bijective_of_isSeparated` supplies injectivity, and
injectivity of the tensor equivalence finishes the kernel argument.

Added two modules and nodes. `AdditiveCohomologyBaseChangeSquare` proves the scalar
linearity of an untensored comparison square from the coordinate-normalized
additive square. This proof chooses each sheaf scalar endomorphism supplied by
hscalar, rewrites its cohomology action, and builds the linear equivalences.
`AdditiveCohomologyPullbackComparison` states the remaining geometric comparison,
with no scalar module structures assumed on the etale cohomology groups. It
contains one named sorry with a complete proof description. It concerns arbitrary
commutative base rings and every cohomological degree; it asserts neither tensor
exactness nor injectivity, and does not take beta as an argument.

Added proof-only imports of `AdditiveCohomologyBaseChangeSquare` and
`FlatCohomologySeparated` in the item. The square module has a proof-only import
of `AdditiveCohomologyPullbackComparison`. Updated the item's proof DAG to this
route. No existing public import, statement, definition, instance or visibility
changed. No other existing module was adapted.

## Proved and sorry left

Closed `AlgebraicGeometry.IsCurve.additive_cohomology_tensor_kernel`, node
`lem-pbc-additive-cohomology-tensor-kernel`: one of one original holes closed by
reduction. There is no sorry left in the item.

Proved the new
`AlgebraicGeometry.Scheme.Modules.exists_additive_cohomology_baseChange_square`,
node `lem-pbc-additive-cohomology-base-change-square`, from the additive comparison.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_additive_cohomology_pullback_comparison`,
node `lem-pbc-additive-cohomology-pullback-comparison`. This is a decomposition,
not a complete proof of geometric base change: one original hole closed and one
new hole added, net zero. Existing dependencies may still rest on their own
sorries; none of those existing holes were changed here.

All three delivered modules compile together through lcompile.py, without
warnings. The linear square and kernel combination are complete Lean proofs.
The dry-run delivery performs the declaration/axiom probes and preflight.

## No longer needed

No original import was removed, and no module or node is claimed pruned.
The item's old direct planned dependencies are no longer direct dependencies:
`lem-pc-flat-cech-base-change` and `lem-pc-flat-cech-cohomology-square` are used
through the existing separated flat-base-change theorem, while
`lem-pc-affine-cech-inverse-image`,
`lem-sc-etale-qcoherent-source-comparison-natural`, and
`lem-sc-etale-tensor-unit-sections-natural` remain planned dependencies of the
new geometric comparison. These are relocation of dependencies, not pruning.

No imports of the old individual Cech lemmas were added to the item because its
proof uses the existing theorem that combines them. All added imports are used
by their respective statements or proofs.

## Where the brief, the DAG or earlier work was wrong

The DAG's geometric comparison step is not immediately furnished by its stated
interfaces. `exists_etaleTensorSectionsSheaf_source_comparison_natural` supplies
an additive equivalence for a fixed canonical sheaf, natural in module
endomorphisms. It does not state naturality across a change of scheme, or compare
the arbitrary coordinate-presented G and Gprime with those canonical sheaves.
The affine inverse-image lemma compares ordinary module cohomology cycle classes;
it does not itself bridge to the specified small-etale Ext pullback. The new
additive comparison records this gap explicitly, including the sectionwise
isomorphisms, coefficient universes and displayed cartesian transport.

The existing separated flat-base-change theorem already performs the Cech
isomorphism and exact-tensor combination, so those steps need not be duplicated
in this item. It is used as a general tool from the Picard framework; the unit's
Artin-Schreier route and all nodes realizing the unit's own steps are preserved.

Checked the new statement on the empty scheme, affine schemes in positive
degrees, degree zero, the identity base change, zero base rings, and nonflat base
changes. Empty/affine higher cohomology is zero. Degree zero is the structural
section pullback; in an identity square the coordinate isomorphisms conjugate q
to that pullback. A zero ring forces its scheme to be empty. Nonflat base change
still has the untensored comparison and its naturality; no tensor equivalence
or injectivity is asserted there. The given cohomological module actions are
used only in the proved linearization lemma, where the hscalar formulas force
compatibility. These checks reveal no false strengthening of the remaining
comparison.

Read Stacks Tags 03P2 and 02KH online; the local literature checkout contains
only its tracked lists on this machine. The label of 03P2 was checked in the
Stacks etale-cohomology.tex source. LeanFinder/Loogle returned generic algebraic
tools, grep found no Mathlib geometric comparison, and LeanSearch returned
Internal Server Error, recorded as unavailable. Searched the project comparisons
and blueprint references; no existing declaration supplies the missing combined
normalized pullback square. The derived degree-one scalar comparison in
`AdditiveCohomologyComparison` supplies a single-scheme endomorphism comparison,
not this cross-scheme normalization.

## New nodes

`lem-pbc-additive-cohomology-pullback-comparison` is the remaining coordinate-normalized
additive geometric square, in
`lean/Sheaf/AlgebraicGeometry/Curve/AdditiveCohomologyPullbackComparison.lean`.
Its source is 03P2, etale-cohomology-theorem-zariski-fpqc-quasi-coherent, together
with the untensored comparison of 02KH. It is strictly the geometric-comparison
part of the argument: no beta, tensor kernel, flatness or module actions on
etale cohomology occur in its inputs. Its proof plan keeps the existing unit
section, coefficient comparison, pullback-unit and affine inverse-image nodes.

`lem-pbc-additive-cohomology-base-change-square` is the proved linearization of
that additive square, in
`lean/Sheaf/AlgebraicGeometry/Curve/AdditiveCohomologyBaseChangeSquare.lean`.
Its only proof dependency is the preceding comparison; all scalar glue is
written in Lean. Both nodes inherit chapter sec-proper-base-change and unit
sk-thm-p1 from the item. No change record is required because no existing
interface changed.

## Second reading by E2

1. **Existing interface: pass.** Diffed the delivered kernel module against the
repository version. Its declaration signature and complete existing docstring
are byte-for-byte unchanged. The diff consists of two plain proof-only imports
and the replacement proof. The two other modules are new; no existing definition,
instance, public import or visibility changes, and no change record is needed.

2. **Lean proof and trust: pass, conditional on the reported open comparison.**
Recompiled all three files in import order with lcompile.py: no errors or
warnings. Independently compiled a scratch import with `#print axioms` for
`AlgebraicGeometry.IsCurve.additive_cohomology_tensor_kernel`,
`AlgebraicGeometry.Scheme.Modules.exists_additive_cohomology_baseChange_square`,
and `AlgebraicGeometry.Scheme.Modules.exists_additive_cohomology_pullback_comparison`.
Each reports only propext, Classical.choice, Quot.sound and sorryAx. The only
literal sorry delivered is the named pullback-comparison theorem. There are no
definitions in the delivery, no forbidden declarations, and no chosen data is
installed in a definition. The equivalence witnesses are eliminated only inside
proofs of propositions. In the kernel proof, hcomm agrees on b tensor x by hbeta
and he; ordinary base-change injectivity kills t z, and t.injective kills z.

3. **New statements and decomposition: pass.** Read Stacks
[03P2](https://stacks.math.columbia.edu/tag/03P2),
`etale-cohomology-theorem-zariski-fpqc-quasi-coherent`, particularly the affine
acyclicity and separated affine-cover argument, and
[02KH](https://stacks.math.columbia.edu/tag/02KH),
`coherent-lemma-flat-base-change-cohomology`, particularly the separated Cech
argument. The coordinate assumptions identify each sheaf with the additive
structure sheaf; they do not require ring compatibility from the coordinates.
The comparison transports the ordinary structural scalars, rather than assuming
an arbitrary cohomology action is structural. The separate, proved linearization
uses each hscalar witness and its H-map formula to establish exactly that fact.
Quasi-compactness supplies a finite cover, separatedness over the affine spectrum
supplies affine intersections, and arbitrary base change preserves those affine
intersections. Nonflat base changes still give the untensored pullback square;
flatness enters only the existing tensor base-change theorem in the kernel proof.
Checked n=0 (section pullback), affine schemes with n>0 (zero groups), empty
schemes, zero rings, and the identity square with independently chosen natural
coordinates (the normalized q is conjugated by those coordinates). The open
comparison asserts no beta, tensor isomorphism or injectivity, so it is strictly
the geometric part, not a restatement of the kernel theorem. The scalar
linearization is a short proved consequence, not an additional hole.

Independently searched with msearch LeanFinder for "Naturality of etale Zariski
cohomology comparison for the structure sheaf under arbitrary scheme base change",
with Loogle for `LinearEquiv.toAddEquiv`, and with grep for
`Etale.*H|H.*Etale|zariski.*comparison`; these found section naturality and generic
algebra tools, not the required cross-scheme comparison. Also searched the
project and upstream algebraic-geometry and etale sources. Read
`EtaleQcoherentSourceComparisonNatural`, `EtaleTensorUnitSectionsNatural`,
`AffineCechInverseImage`, and `AdditiveCohomologyComparison`. The first supplies
endomorphism naturality on a fixed scheme, and the affine Cech lemma supplies
ordinary inverse-image compatibility. Neither states the missing normalized
small-etale-to-ordinary cross-scheme square. Closing that hole requires this
naturality argument; it is not a few-minute application of the existing APIs.

4. **Route and pruning: pass.** Read `FlatCohomologySeparated` and the definitions
of H.baseChangeLinear and H.baseChange. The former already performs the affine
Cech/tensor homology argument, so reusing it avoids duplicating that proof.
The unit sk-thm-p1 and its realized fields are untouched; its characteristic-p
Artin-Schreier route still uses additive structure-sheaf cohomology base change.
All new public imports provide types or instances in their statements; the new
proof-only imports supply the two lemmas actually applied. No original public
import can be dropped from this existing interface. `No longer needed` lists all
five old direct proof dependencies: two occur through the separated theorem and
three remain in the open geometric comparison's plan. None is claimed pruned.

5. **DAG and report: pass.** The existing node changes only proof, proof_deps and
proof_origin. Its new dependencies are precisely the linear square and the
separated flat-base-change theorem used by Lean. The square node records the
hscalar rewrite and additive-to-linear upgrade written in its proof. The open
comparison node records the coefficient, unit-coordinate and ordinary Cech
interfaces as planned steps, with the cross-scheme compatibility still open;
its statement matches every hypothesis and all three conclusions in Lean.
Both new nodes carry source, statement dependencies, proof plan, search records,
creation provenance, blueprint ancestry, chapter/unit and matching lean records.

**Changes made by the second reader:** added this independent review and its
verification/search evidence. No Lean or node repair was necessary. This remains
one original hole closed by reduction and one new hole added, net zero, with no
module pruned; the open geometric comparison is explicitly not claimed proved.
