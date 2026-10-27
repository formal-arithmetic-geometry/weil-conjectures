## What changed

Return repair: removed the duplicate private theorem `tensorPullback_invertible`.
The inverse theorem now uses `((invertible_pullback_tensor f).1 M).2` directly
from the existing public library theorem, imported privately from
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`.
The duplicate declarations named by the return are private and cannot be used by
an ordinary proof import. This public result supplies exactly their conclusion.
No public declaration signature or definition body changes in this repair.

Replaced the inverse theorem's single hole with a proof assembled from four distinct
chart calculations. The Lean proof constructs the line isomorphism by factoring two
epimorphisms with the same kernel through each other. It proves the coefficient-one
frame, all scalar normalization and overlap ratios, and the equality of the pulled
line isomorphisms by evaluating normalized adjunction units and cancelling the quotient.
It derives the scheme morphism equalities from the existing fraction-map uniqueness theorem.

Moved the seven unchanged public definitions to LineQuotientChartInverseData and publicly
re-exported them from the original module to avoid an import cycle. The theorem's signature
is unchanged. The change record is
coord/changes/line-quotient-chart-definition-module.md.

## Proved and sorry left

The original hole closed is
AlgebraicGeometry.ProjectiveBundleQuotientGeometry.line_quotient_chart_inverse_pullback.
Its replacement is a decomposition, not a claim that its mathematical dependencies are
sorry-free. The new public theorem lineQuotient_iso_charts is proved by symmetric-degree induction,
frame injectivity, linearity and restriction naturality; it has zero holes.
The proof includes proved private helpers for normalized section naturality,
composition, epimorphisms, recovery of the coefficient-one frame,
normalization from quotient compatibility, two-epimorphism factorization and pullback
compatibility. The map on away localizations and its value on every homogeneous
fraction are constructed explicitly from Localization.awayMap.

Three public holes are added, each exactly `:= by sorry` in its own module:

- AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_fraction_kernel
  (lem-trf-line-quotient-fraction-kernel): equality of kernels on fraction charts.
- AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_recovered_charts
  (lem-trf-line-quotient-recovered-charts): coefficients and charts for the quotient pulled
  along a given morphism.
- AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_pullback_charts
  (lem-trf-line-quotient-pullback-charts): fraction charts and homogeneous and generator
  coefficient naturality under
  arbitrary pullback. The localization formula is proved in the main module.

Each is strictly a part of the original argument and omits the other inverse identities
and line-isomorphism construction. No definition contains sorry or chooses arbitrary data
from an existence theorem. The line isomorphism is determined by its quotient equation
because the quotient is epimorphic.

Thus one original hole is closed and three strictly simpler holes are added (net -2).
The additional isomorphism-invariance theorem is proved, rather than left as a fourth hole.

Validation: lcompile.py --all compiled all six delivery modules at standard settings
(exit code 0). After the duplicate-theorem repair, all six modules compiled again (exit code 0);
the assigned inverse theorem compiled in 15.8 seconds. The seven
relocated definitions have unchanged signatures and bodies, and the assigned theorem
signature matches the shared source. There are no diagnostic files under lean/.

## No longer needed

The duplicate private `tensorPullback_invertible` declaration is removed. The
main node now cites `lem-weil-pbc-invertible-pullback-tensor`, whose proved public
theorem is applied directly, rather than reproving
`lem-weil-pbc-invertible-pullback-invertible`. The latter is removed from the
main node's proof dependencies and tool approvals; it remains available in the library.

The main proof removes direct proof imports of
WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing,
WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections,
WeilConjectures.AlgebraicGeometry.TensorPullback,
WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules,
Mathlib.AlgebraicGeometry.Gluing and Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic.
Their relevant geometric steps remain in the new chart nodes, so this is not a claim
that these modules can all be pruned from the targets' closure. In particular the affine
section, standard-open and twisting calculations are still needed below the chart nodes.
The former direct proof dependencies no longer used by the top-level assembly are:

- def-nagata-relative-proj
- def-per-projective-bundle-quotient-data
- def-trf-canonical-symmetric-graded-algebra
- def-weil-affine-spectrum
- def-weil-pbc-proj-twisting-sheaf
- lem-pur-sheaf-hom-cover-gluing
- lem-weil-pbc-module-pullback-affine-sections
- lem-weil-pbc-scheme-morphism-gluing
- prop-nagata-proj-standard-open

Their chart calculations, except hom-map gluing, are recorded under the smaller chart nodes.
No existing module is withdrawn. Hom-cover gluing in the top-level assembly is replaced
by abelian-category factorization and epimorphism cancellation; the kernel comparison
uses sheaf separation locally. Removed the now indirect top-level tool approvals
prop-nagata-proj-standard-open, lem-weil-pbc-module-pullback-affine-sections and
lem-pur-sheaf-hom-cover-gluing; the first two remain needed by the chart nodes.
The kernel comparison no longer needs hom-cover gluing or the epi-preservation node: 
local invertible maps and target sheaf separation suffice. The seven original public imports
are retained through
the shared-data module, together with Mathlib.AlgebraicGeometry.Scheme.

## Where the brief, the DAG or earlier work was wrong

The returned packet duplicated tensor-pullback invertibility in a private helper.
This repair removes the helper and applies the existing public theorem directly,
as required by the return at af9d41805. The two Bertini helpers named in the
return are private; no visibility change or adaptation to those modules is needed.

No false statement was found. A dependency audit found a pre-existing cycle between
prop-nagata-relative-proj-functoriality and lem-nagata-affine-proj-scalar-extension
(the longer path also passes through lemma-nagata-relative-proj-exists and
lem-nagata-proj-affine-restriction). The shared baseline has the same cycle; no new node
is on it, and this delivery does not change those records.

On launcher resume the sandbox reference metadata was reset:
the earlier start was 1792748782.0390408, and the resumed start is 1792773836.2271895
(the attempt identifier remains G3 / Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback).
Neither clock file was edited by this worker. The original proof steps suppressed the
separate chart
comparison interfaces. They are now stated explicitly instead of assuming that the
fraction-map existence theorem directly provides inverse or pullback compatibility.
The normalized comparison defined using leftAdjointUniq is expensive to unfold.
The first factorization construction using explicit kernels and epiDesc led to costly
instance unfolding in its scheme-module application. The replacement needs only the
normal-epimorphism interface: choose a cokernel presentation of each epimorphism and
use its universal property to factor through the other quotient. This is proved for
an arbitrary category with zero morphisms and normal epimorphisms. A proved private
theorem supplies the normal-epimorphism property on scheme modules, avoiding expansion
of the full abelian instance. The final assembly
chooses the isomorphism from its proved existence theorem and uses its quotient
equation. The epimorphic quotient uniquely determines that isomorphism, so this
choice satisfies the data-determinacy rule. It keeps the concrete cokernel
construction out of dependent normalization expressions. Section
identities are proved once and used explicitly, and local irreducibility prevents
unnecessary elaborator expansion. The base-map proof is passed directly from the chart
hypothesis, avoiding costly conversion through a local proof alias in pulledQuotient.
The final pullback cancellation uses Category.assoc explicitly rather than relying on
definitional associativity of concrete module maps. Empty charts, E=0, degree zero, arbitrary quasi-coherent
E, isomorphic frames and non-flat pullback are included in the statements and prose proofs.

## New nodes

lem-trf-line-quotient-fraction-kernel isolates the local equality of kernels; the global
isomorphism is constructed in the main proof rather than assumed in this node.

lem-trf-line-quotient-recovered-charts isolates the all-degree coefficient calculation
for a pulled quotient; the main proof separately recovers the morphism by uniqueness.

lem-trf-line-quotient-iso-charts isolates preservation of scalar coefficients and chart
formulas under a line isomorphism; the main proof supplies morphism uniqueness.

lem-trf-line-quotient-pullback-charts isolates the ring and scheme chart calculations
under arbitrary pullback; the main proof separately supplies the line-isomorphism equality.

def-trf-line-quotient-chart-inverse-data records the unchanged shared definitions moved
to their own module. It contains zero holes. The new statement nodes have separate source
results: local kernel comparison,
recovered chart coefficients, isomorphism invariance, and arbitrary base-change chart
formulas. They do not repackage the full inverse theorem.
All five nodes were searched using LeanSearch,
Lean Finder, Mathlib source grep and whole-blueprint searches.

Change record: coord/changes/line-quotient-chart-definition-module.md.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
