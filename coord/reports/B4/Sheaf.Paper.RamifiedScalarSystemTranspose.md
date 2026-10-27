## What changed

Reduced `WeilConjectures.RamifiedScalarSystemTranspose.scalar_preserves` to two separate
assertions: normalization under scalar extension and preservation of the constructible
finite-Tor domain at each finite coefficient level. The latter is fully proved in
`Sheaf.Paper.FiniteFreeTensorCtf`; the former is the new theorem
`WeilConjectures.SemilinearSections.scalarSystems_normalized` in its own module. A fully proved
private lemma supplies finite freeness of each actual quotient inclusion by applying
finite_free_coefficient_extension. Its unrelated finite-field datum is discharged by an explicit
auxiliary prime field and algebraic closure; the prime is larger than l, so the required
distinct-characteristic condition holds. Local sheafification assumptions are cached inside the
proofs of constantRingSection, directOrdinary_existsUnique and restrictionOrdinary_existsUnique.
The generic essentially-small, Grothendieck-abelian pro-etale, and sheaf-tensor sheafification
instance entries are erased to avoid irrelevant searches for concrete ring sheaves. The later
system-calculus declarations respect transparency, and a local irreducibility setting protects
the large scalarData package. The instance-search bound is reduced from 4096 to 64. Sequential
checking avoids repeated large kernel expansions. Two proved specialized HasWeakSheafify
instances, ProEtaleCommRingSheafification and ProEtaleRingSheafification, cache Mathlib concrete
sheafification at the coefficient universe. They are public imports because public definitions
use these proof instances. They introduce no new chosen ring, sheaf or functor, and no holes.
Development options are removed from the delivery. The existing scalarEvaluation declaration is
moved before scalar_preserves so its isomorphism can be reused directly. The compatibility
record representation changes as described below. The main theorem statement and all six
equality accessor types stay the same. In quotient_square the finite-Tor proof is taken from the
canonical evaluation object, instead of projecting directly from the domain proof; proof
irrelevance identifies the two. The local transparency settings keep the large functor and
comparison definitions closed while checking the structures.

The six proof fields of FiniteCompatibility are packaged into the Prop structure
FiniteCompatibilityLaws, with the same Change data and six verbatim equations. The old accessor
names are proved projection aliases. This avoids repeated expansion of the large dependent data
record; its mathematical conditions are unchanged. The constructor now takes the laws as a
single proof package. The change record is
coord/changes/B4-ramified-finite-compatibility-laws.md, including the downstream and
declaration-use audit. No external consumer mentions this record directly. The eight coherence
proof fields of SystemAdjunction are likewise separated into SystemAdjunctionLaws over
SystemAdjunctionData. Its seven data/preservation fields and all eight original equations
remain. All fifteen accessor names remain as reducible data aliases or proved projection
aliases. The change record is coord/changes/B4-ramified-system-adjunction-laws.md. The direct
consumer does not mention this record either. Temporary verification modules compare the two
representations with verbatim copies of the original records. The coherence accessors infer
their conclusion from the fully applied law proof, avoiding duplicate elaboration of the large
equations. The ordinary direct-image and restriction identity comparisons use
LinearEquiv.ofBijective to package the bijective identity linear map; their uniqueness
statements are unchanged. The local systemCategory instance caches the original category
structure on ordinary derived systems. It changes no localization model or universe. The
verification probe compares this data with the canonical instance by rfl; the new definition
belongs to the existing parent node.

The full main-module artifact build passed the per-file compile guard. Separate temporary
verification modules compiled equivalences from verbatim copies of both old records to the
actual new records, and proved the category-cache equality by rfl. These verification modules
contain no sorry and are excluded from the delivery. The unchanged direct consumer,
Sheaf.SixFunctors.RamifiedScalarExceptionalLimit, compiled against the new main artifact.

## Proved and sorry left

Replaced the original hole `WeilConjectures.RamifiedScalarSystemTranspose.scalar_preserves` by a
complete proof from the new normalization theorem and fully proved finite-level theorem. This is
a decomposition, not a net hole reduction: one original hole closed, one strictly smaller hole
added. The new hole is `WeilConjectures.SemilinearSections.scalarSystems_normalized`, attached
to `lem-coef-scalar-systems-normalized`. It concerns only normalization on arbitrary sites and
does not assert the constructible finite-Tor conjunct.

The two untouched original holes are
`WeilConjectures.RamifiedScalarSystemTranspose.scalar_transition` and
`WeilConjectures.RamifiedScalarSystemTranspose.ramifiedScalarSystemTranspose`, both attached to
`lem-coef-ramified-scalar-system-transpose`. `AlgebraicGeometry.finiteFreeTensorCtf` and the
`WeilConjectures.RamifiedScalarSystemTranspose.arrow_finite_free` have no holes. The two additional proved instance theorems are
`AlgebraicGeometry.ProEtale.proetaleCommRingSheafification` and
`AlgebraicGeometry.ProEtale.proetaleRingSheafification`; neither contains a hole.
FiniteCompatibilityLaws and all six retained proof aliases contain no holes.
SystemAdjunctionData, SystemAdjunctionLaws and all fifteen retained accessors also contain no
holes. The new statements include equal-index reductions, zero rings and empty sites; no
nontriviality or nonempty-scheme hypothesis is used.

## No longer needed

The preservation step no longer needs `lem-weil-pbc-finite-type-over-noetherian` or
`lem-sf-finite-free-derived-scalar-calculus`; their obsolete top-level tool approvals are
removed. Removed unused proof imports `Sheaf.Paper.FiniteFreeSystemRestriction`,
`Sheaf.Paper.QcqsCompactSupportRealization`, `Sheaf.Paper.EtaleCoefficientSystemAdjoint`, and
`Sheaf.Paper.FiniteFreeDerivedScalarCalculus`. Also removed unused direct public imports
`Sheaf.Paper.CartesianSectionAdjointMates`,
`Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`,
`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, and `Sheaf.Paper.NormalizedDVRTower`. The
only direct consumer, `Sheaf.SixFunctors.RamifiedScalarExceptionalLimit`, explicitly imports
CartesianSectionAdjointMates itself, so it retains that interface. A comparison of the
consumer's public import closure before and after the change finds zero lost modules. DAG
dependencies serving the remaining system construction are retained. No module is withdrawn or
globally pruned.

## Where the brief, the DAG or earlier work was wrong

The old finite-level preservation step assumed a Noetherian scheme, while `scalar_preserves`
quantifies over every scheme. The new exact finite-free argument proves its finite-level
conjunct with the actual quantifiers. The generic strict-system normalization argument remains
an explicit independent item: finite-level constructibility alone does not establish the
cartesian condition. No data are chosen from an arbitrary unproved existence theorem.

## New nodes

`lem-coef-finite-free-tensor-ctf` realizes the fully proved theorem
`AlgebraicGeometry.finiteFreeTensorCtf`. Exact scalar extension preserves homology,
constructible etale origins and cohomological bounds; the derived tensor cancellation formula
and faithful exact restriction preserve the Tor interval.

`lem-coef-scalar-systems-normalized` realizes the sole new sorry,
`WeilConjectures.SemilinearSections.scalarSystems_normalized`. This is exactly the normalization
step of the parent proof. Transposing strict transitions gives scalar extension of the input
reductions conjugated by tensor reassociation. It is strictly smaller than scalar_preserves: it
contains no constructibility, Tor bounds or p-adic arithmetic. The separate compatibility
representation repair is recorded in coord/changes/B4-ramified-finite-compatibility-laws.md; it
adds no mathematical statement or hole. The corresponding system-adjunction representation
repair is recorded in coord/changes/B4-ramified-system-adjunction-laws.md and also adds no hole.

`lem-coef-proetale-commring-sheafification` exposes the proved Mathlib concrete CommRingCat
sheafification specialization in its own one-theorem module. It caches the existing
constant-coefficient construction and contains no sorry.

`lem-coef-proetale-ring-sheafification` exposes the corresponding proved RingCat specialization
in a separate one-theorem module. It likewise contains no sorry and introduces no new
mathematical assumption or independently selected object.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
