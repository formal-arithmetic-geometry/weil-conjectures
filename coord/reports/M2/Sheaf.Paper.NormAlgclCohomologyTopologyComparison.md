## What changed

The original theorem
`AlgebraicGeometry.ProEtale.NormAlgclComparison.isIso_derivedGlobalSections_comparison` is reduced
to the existing arithmetic comparison and one geometric normalization theorem. The proved private
helper `representationModel_iso` identifies two section-normalized condensations of the same
representation using the fully faithful internal-module/section-module functor, and checks
equivariance on all profinite sections. The main proof obtains the arithmetic comparison data,
transports its degree-zero assertion to each cohomology object of a bounded geometric complex, and
applies the already proved `DerivedCategory.prop_of_bounded` to the comparison's isomorphism
locus. The final commuting-square cancellation uses `DerivedCategory.isIso_iff` on the original
target localization. It does not require finite Galois cohomological dimension.

`Sheaf.Paper.NormAlgclGeometricComparison` records the geometric model and cohomology-level
coefficient square separately. Its conclusion supplies no comparison invertibility: that is proved
separately in the parent from the arithmetic theorem and finite devissage. The square's
normalization explicitly fixes the coefficient morphism on every section, the ordinary tensor
transformation, and the pulled-back module map. Comparing homology groups handles the different
morphism universes used by the existing arithmetic interface and the original target.

The coefficient constructions, including `comparison` and `derivedGlobalSections`, move verbatim
to `Sheaf.Paper.NormAlgclCoefficientMap`. The parent publicly reexports this module, so every
original declaration name, signature, visibility and body remains available. This extraction lets
the normalization theorem use the actual maps rather than compare large generic presentations. The
diagnostic trace for the earlier parent timeout expanded point-pullback ring multiplication during
that generic comparison. No source-library file or existing consumer changes. The
declaration-specific transparency settings for the private model-uniqueness proof stay local to
it. The parent's DAG proof now follows the implemented arithmetic/devissage/cancellation argument
and names the separate geometric obligation.

## Proved and sorry left

Closed upper hole:
`AlgebraicGeometry.ProEtale.NormAlgclComparison.isIso_derivedGlobalSections_comparison`
(`lem-sfb-norm-algcl-cohomology-topology-comparison`). Its body contains no `sorry`.

Added and remaining hole:
`AlgebraicGeometry.ProEtale.NormAlgclComparison.geometric_comparison_normalization`
(`lem-sfb-norm-algcl-geometric-comparison-normalization`). Its proof is exactly `by sorry`; its
docstring and node specify the sectionwise coefficient identifications, universal-derived-functor
comparisons, normalized invariant comparison, geometric projection/descent square, and passage
between localization universes.

This is a decomposition: one original hole closed and one separate geometric hole added, so the
packet has one remaining hole and net hole reduction zero. The existing arithmetic,
geometric-finite-scalar and Galois-descent theorem holes remain the responsibility of their own
nodes. No new definition chooses arbitrary data from an unproved existence theorem.

Validation: all three sandbox modules compiled in import order through `lcompile.py --all`. The
private representation-model proof, arithmetic propagation, and final cancellation compile.
Diagnostic traces were removed and long-line warnings corrected before delivery.

## No longer needed

The original public imports are retained by the shared coefficient module and reexported through
the parent. No node or module is withdrawn or claimed globally pruned. The parent's direct
references to `lem-sfb-geometric-condensed-finite-scalar-model` and
`lem-sfb-condensed-galois-global-descent` move into the new normalization node; both remain needed
there. The proof uses the proved source-library finite devissage and isomorphism-locus APIs, so it
does not introduce a new Postnikov-tower theorem or prove the already stated geometric/arithmetic
inputs. Redundant private imports of Mathlib's derived t-structure and the source
triangulated-functor module were removed after their APIs were supplied by the retained
source-library imports.

## Where the brief, the DAG or earlier work was wrong

The mathematical four-step plan is retained. Its existing Lean interfaces do not compose by a
single application: the geometric assertion uses arbitrary-algebraic-closure coefficient rings and
scalar-extension adjunctions, whereas the arithmetic assertion uses the published PadicAlgCl rings
and universally derived equivariant tensor models. The actual target also uses a smaller
localization universe for abelian groups. The normalization lemma makes these identifications
explicit instead of silently treating unrelated chosen functors or localized categories as
definitionally equal.

The rework row records an earlier transitive import quarantine involving
`ProjectiveLineGenusZero`. The current item source was present and compiled at the start of this
session; it was retained, not withdrawn or replaced by an empty module.

The current blueprint direct-images paragraph does not literally state this additional
norm-topology assertion. The original node already labels it an agent coefficient-topology
obligation with an external reference WANTED. The new node preserves that provenance and does not
claim the current blueprint proves more than it says.

## New nodes

`lem-sfb-norm-algcl-geometric-comparison-normalization`, in `dag/nodes/sec-six-functors-basics/`,
is attached to `Sheaf.Paper.NormAlgclGeometricComparison`. It states only the bounded geometric
representation model and the normalized cohomology comparison square, corresponding to steps 1 and
4 of the parent. Its proof dependencies are the existing normalized geometric finite scalar model
and ordinary condensed Galois descent. It retains the parent's chapter and unit route. LeanSearch,
Loogle, LeanFinder, Mathlib-source grep, source-library grep, and blueprint searches found no
duplicate normalization statement. No change record is needed because no existing statement or
definition changes.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
