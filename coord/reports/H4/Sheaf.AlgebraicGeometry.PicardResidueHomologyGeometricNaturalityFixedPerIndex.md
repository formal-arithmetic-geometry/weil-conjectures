## What changed

Completed the proof of
`AlgebraicGeometry.Scheme.picard_residue_homology_geometric_naturality_fixed_positive_per_index`
by composing a shared geometric source comparison with a natural affine-model comparison.
The supplied model isomorphisms conjugate each geometric arrow into the arrow between
`Q.obj K` and `Q.obj (C i)`. Naturality applies to every chain representative of that arrow.

The affine part is proved, rather than postponed: explicit cycles modulo boundaries are
identified naturally with module-complex homology; the chart residue field is transported
to evaluation scalars; the affine reconstruction counit is natural and invertible on
strictly perfect complexes; K-flat pullback and field-spectrum sections then produce a
natural derived-residue comparison. The construction is packaged in nine proved new modules and definitions. The tenth new module isolates the remaining geometric direct-image comparison.

The item's existing corrected statement, public imports, and visibility are unchanged. The geometric split now uses the concrete canonical coefficient arrow `picardDerivedCoefficientMap`; its theorem statement and callers were updated together.
The item proof was adapted to the concrete arrow. Its node proof, proof dependencies, and proof origin
now describe the actual composition. Its existing D2 statement-change history is preserved.
The new field-spectrum comparison and local fibre functor have named computation interfaces
and irreducible implementations to avoid repeated expansion of large derived-functor terms.
All Lean checking uses lcompile.py, with no raised file time limit. The unchanged caller
`PicardResidueHomologyGeometricNaturalityFixed` also compiles against the new item.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.picard_residue_homology_geometric_naturality_fixed_positive_per_index`.
Its complete proof is conditional on the one geometric theorem listed below. This is a
decomposition, not a claim that the target import closure is now free of sorry. One hole is
closed and one is added, for net zero holes in this delivery.

Fully proved the following new theorems:
`picardCoefficientBaseMap_snd`, `picardCoefficientBaseMap_fst`, together with `derived_fiber_open_factorization`, `affine_residue_quotient_homology_naturality`,
`affine_residue_evaluation_homology_naturality`, `affine_perfect_sections_counit`,
`affine_perfect_residue_model_naturality`, and `affine_residue_model_naturality`.
The new definitions `picardDerivedCoefficientMap`, `derivedFiberCohomologyFunctor`, `openResiduePoint`,
`localDerivedFiberCohomologyFunctor`, and `residueTildeHomologyComparison` contain actual
constructions and no sorry. `localDerivedFiberCohomologyFunctor_eq` is proved.
All these declarations are in namespace `AlgebraicGeometry.Scheme`.

The delivery leaves exactly one new sorry:
`AlgebraicGeometry.Scheme.picard_derived_fibre_naturality`, in
`Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality`, node
`new-picard-derived-fibre-naturality`. It is strictly the geometric part: there is no affine
open, prime, perfect model, model isomorphism, or chain representative in its statement.
It still needs compatible, normalized comparisons from homology and field sections of a
derived direct image to fibre module cohomology, together with the equation identifying
its derived coefficient-unit map with ordinary cohomology pullback. Existing base-change
source transport and canonical single-pullback coherence supply the categorical square;
existing scalar-unit comparison supplies the final additive-sheaf comparison. The missing
glue is the normalization of the field-section/higher-direct-image comparison for changing
source schemes. Objectwise existence of additive equivalences does not prove that equation.

During this session a separate scratch proof constructed the geometric arrows using
`relativeMVUnit`, `relativeMVImageComp`, and `canonicalSinglePullbackMap`, as well as the
pulled-back target trivializations. It compiled up to the naturality equation. That scratch
proof is not delivered, since its arbitrary objectwise comparison choices cannot justify
the remaining equation. The delivered geometric theorem has its source and full
natural-language proof in its docstring and node.

The new statements were checked on zero complexes, nonzero boundaries, nonfree projective
summands, identity arrows, and empty index families. The quotient and derived-model proofs
are functorial on entire complex categories or the full strictly-perfect subcategory, so
these cases require no extra assumptions. The geometric statement fixes its source
comparison before choosing any target, including when the family is empty.

## No longer needed

The second reading made `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` a plain
proof import in the new quotient-comparison module, since its public statement
uses neither short complexes nor the concrete module homology implementation.

No original import was removed: the item originally had only statement imports and no
proof-dependency imports. No existing module is withdrawn in this delivery.

This route does not use the objectwise modules
`Sheaf.AlgebraicGeometry.PicardResidueSourceModelHomology`,
`Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison`,
`Sheaf.AlgebraicGeometry.PicardResidueHomologySourceFibreComparison`,
`Sheaf.AlgebraicGeometry.PicardResidueQuotientModelHomology`, and
`Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets`. Their nodes are
`new-picard-residue-source-model-homology`,
`new-picard-residue-homology-comparison-source-residue`,
`new-picard-residue-homology-comparison-source-fibre`,
`new-picard-residue-quotient-model-homology`, and
`new-picard-residue-homology-comparison-targets`. In particular, it does not need a second independent objectwise comparison
for each target, nor any lemma claiming that arbitrary additive comparisons are natural.
The proof uses natural isomorphisms on the full perfect subcategory instead. These are unused
alternative routes, not globally pruned modules; they may have other users and are not deleted here.

The new affine sections-counit proof also does not import
`PicardResidueSourceModelHomology`: its small chart-equivalence constructions are
proved locally, avoiding unrelated objectwise Picard comparisons.

## Where the brief, the DAG or earlier work was wrong

The route note describes an earlier false arbitrary-equivalence signature. The repository
already contains D2's corrected existential statement and its adapted caller. Rolling back
that correction would reintroduce the conjugation counterexample over the complex numbers.
This delivery keeps the corrected signature exactly and changes no statement used by a
target. There is no STATEMENT-DISPUTED declaration left to repair in the checked-out item.

An existence theorem for a separate source or target additive equivalence is insufficient
for naturality. Choosing an arbitrary target equivalence after choosing a source does not
force the coefficient square to commute. The delivered affine comparison is genuinely
natural, and the remaining geometric theorem explicitly requires a compatible family.
The original node's four prose steps had no proof-dependency attachments; the new route
records the actual declarations used, rather than treating those prose steps as already
available normalized comparisons.

The item-to-split interface changed from an arbitrary coefficient arrow to the concrete canonical `picardDerivedCoefficientMap`; the item proof was adapted in this delivery. No other existing interface changed, so no additional forced adaptations are needed.

## New nodes

`new-picard-derived-coefficient-map`: defines the canonical coefficient arrow between base-changed derived direct images, with both pullback projection equations proved.

`new-derived-fiber-cohomology-functor`: the real derived pullback, homology, field-section,
and scalar-restriction functor. Its object is the existing derivedFiberCohomology group.

`new-derived-fiber-open-factorization`: constructs the local residue point, local fibre
functor, and natural open-restriction factorization. Its point-composition and functor
computation API are proved.

`new-affine-residue-quotient-homology-naturality`: identifies the explicit quotient with
module homology and proves chain-map naturality by the cycle projection and short-complex
homology API. No perfectness or geometric hypothesis is imposed.

`new-affine-residue-evaluation-homology-naturality`: transports the quotient comparison
through the canonical chart residue-field isomorphism and exact scalar restriction.

`new-affine-perfect-sections-counit`: constructs a natural reconstruction counit using the
chart tilde/sections adjunction and proves invertibility on strictly perfect complexes.

`new-residue-tilde-homology-comparison`: constructs the actual natural field-spectrum
homology comparison using the exact sections equivalence, with no existence-based data hole.

`new-affine-perfect-residue-model-naturality`: proves a natural isomorphism on the full
strictly-perfect subcategory by K-flat derived pullback, affine reconstruction, and the
named field-spectrum comparison.

`new-affine-residue-model-naturality`: combines these isomorphisms, conjugates by supplied
models, and proves the equation for every representing chain map by categorical naturality.

`new-picard-derived-fibre-naturality`: the sole unfinished theorem, isolating compatible
geometric direct-image fibre comparisons. Its remaining work is described above. No affine
model calculation is left in it. No change record is required for these new declarations.

## Earlier second reading (a previous round; superseded)

The delivered modules compile in dependency order. The item proof uses the concrete coefficient arrow and the affine naturality theorem; the remaining geometric theorem is isolated in its own node with its proof obligations documented above.


## Second reading by H4

1. **Interfaces — pass.** Compared every delivered module against the repository.
   The per-index item is the only existing module delivered; its declaration signature
   and public imports are byte for byte unchanged. The signature comparison reports
   no changed statement. The other ten modules are new. No target or existing definition
   changes, and no forced adaptation is included. Restored the existing explanation of
   D2's corrected existential quantifiers.
2. **Proof and data — pass.** Read all eleven files and compiled the full set in import
   order through lcompile.py. Only `picard_derived_fibre_naturality` contains `sorry`;
   it is exactly a named public theorem with a source, complete prose proof and matching
   node. No forbidden declaration form or data-level sorry occurs. The new functor and
   homology-comparison definitions are constructions from actual functors and their
   universal comparisons. The coefficient arrow now uses the section-formula-pinned
   `exists_tensorPullbackAdjunction`, matching `canonicalSinglePullbackMap`, instead of
   choosing an unnormalized adjunction from bare `Nonempty`. A separate scratch file printed the axioms of all sixteen new or changed public
   declarations: the fourteen completed declarations use only `propext`,
   `Classical.choice` and `Quot.sound`; only the remaining geometric theorem and the
   item that applies it additionally use `sorryAx`. The delivery check also probes
   every declaration, including private helpers. Also compiled a scratch copy of the
   unchanged `PicardResidueHomologyGeometricNaturalityFixed` caller against the
   repaired sandbox modules, with no errors or warnings.
3. **Split theorem — pass.** The geometric theorem is strictly one part of the original
   argument: it has no affine neighbourhood, model, quotient, or representing chain map.
   Checked its geometric proof against [Stacks 0B91](https://stacks.math.columbia.edu/tag/0B91),
   [0BF2](https://stacks.math.columbia.edu/tag/0BF2) and
   [01XK](https://stacks.math.columbia.edu/tag/01XK). Properness gives quasi-compactness
   and separatedness; flatness and the invertible coefficient supply arbitrary derived
   base change. Immersions induce residue-field isomorphisms. The same fibre trivialization
   and its pullbacks give compatible comparisons. The empty family still requires and
   admits the source comparison; empty source fibres, zero complexes, identity arrows,
   nonzero boundaries and projective retracts cause no exceptions. Repeated LeanFinder,
   Loogle and grep searches with different wording, and searched both Sheaf and upstream
   sources. Existing field-section comparison results are natural in coefficients on
   one fixed source scheme, and do not close the changing-source normalization equation.
   This remaining theorem cannot be closed by a short application of those results.
4. **Reduction, imports and pruning — pass.** The upper proof first obtains the geometric
   comparison, then applies the proved affine naturality result to the explicitly
   constructed coefficient arrows and composes the equations. The affine comparison
   is proved through natural isomorphisms on the full strictly-perfect subcategory,
   not arbitrary objectwise comparison choices. Changed the new quotient module's
   proof-only `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` import from public to plain.
   The original node had no proof dependencies or proof-dependency imports, so none are
   silently omitted from `No longer needed`. The five alternative objectwise nodes
   named there are unused by this route, with no claim that they are globally unreachable.
   Read `dag/units/sk-prop-av-cube.json`: this reduction remains below the unit's cube
   argument and does not bypass any realized unit statement or step; its existing
   `realized` entries are empty and are not fabricated or changed here.
5. **DAG and accounting — pass.** Read all eleven node records against their modules.
   Every proof-dependency list is the union of its proof steps' uses, and every referenced
   node exists. New nodes carry their source, searches, creation, blueprint, unit,
   chapter and Lean records. The old node keeps its statement and D2 correction history.
   Added the directly constructed coefficient arrow to the item's third proof step
   and proof dependencies, and documented the pinned tensor comparison in its new node.
   Added the independent search results to the geometric node. Corrected the report to
   classify `picardDerivedCoefficientMap` as a definition, not a proved theorem.

The second reading changed the coefficient construction's adjunction normalization,
one proof-import visibility, the restored explanatory comment, corresponding DAG metadata,
and this report. It closed no additional holes. Accounting remains one old hole closed,
one strictly smaller geometric hole added: a decomposition with net zero holes.

Validation: the full repaired set compiled without errors or warnings; the separate
sixteen-declaration axiom check and unchanged caller check passed. The required
`deliver3.py --no-push` printed `OK` and passed preflight (CODEX, because this delivery
adds modules and nodes). The one remaining geometric theorem is explicitly reported above.
