## Worker report

The module `Sheaf.Paper.PerfectStrataUniformReductions` states
`AlgebraicGeometry.Scheme.perfect_strata_uniform_reductions`. Its sole proof is `sorry`.
It introduces no new Lean definition and makes no mathematical statement correction.
The repair adds an existing-definition DAG attachment for the two canonical constructions
used in the perfect-model hypothesis; it preserves the accepted Lean file byte for byte.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The Noetherian scheme is `(X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]`.
  These are exactly a finite affine cover with Noetherian coordinate rings; no dimension,
  separatedness, or invertible-characteristic assumption is imposed.
- `(d : AdicCoefficientDatum A)` contains the stated coefficient hypotheses, including
  finite positive quotients and their perfectness. The coefficient universe is `u+1`;
  the small site retains object universe `u+1` and morphism universe `u`.
- `K : d.derived X` is the derived category of modules over the actual inverse limit
  `d.completedRing X`. `d.finiteRing X n` denotes exponent `n+1`, so `n : ℕ` ranges
  over exactly all positive exponents, without an exponent-zero extra assertion.
- `S : FiniteLocallyClosedStratification X` is the recorded finite locally closed
  partition with its scheme immersions. No constructibility assumption is added.
- `J`, `U`, `f`, and `_hcover` retain an arbitrary given pro-etale covering family
  on each stratum. The index type is in the site object universe. Cover membership
  uses `ProEt.precoverage`, the actual weakly-etale/fpqc covering condition.
- `_hmodel` quantifies independently over every original member `U i j`. Its `P`
  belongs to the ordinary module derived category and satisfies the recorded
  `DerivedCategory.IsPerfectRingComplex`, hence has a bounded finite-projective
  representative. Restriction is `adicTowerPullback` followed by the recorded
  `ringedSiteDerivedRestrictionOfUniverses`, with the explicit standard slice
  localization. Both sides have exactly the same inverse-image coefficient ring.
- The right model first applies `CompletedConstantReduction.constantComplex` to
  `DerivedCategory.Q.objPreimage P`, localizes, and applies `pbcDerivedExtend`
  along `CompletedConstantReduction.base X d.ideal ≫ (pbcCompletedComparison X d).hom`.
  This is the actual derived scalar extension of the constant A-complex to B_X,
  restricted to U. The canonical immersion/slice coefficient identifications of
  the recorded proof identify it with B_U tensor_A^L P. No arbitrary coefficient
  map or assumed tensor comparison has been substituted. All constructions are
  existing; no helper copies of local restriction or completed realization remain.
- The first conclusion is `∃ a b : ℤ, a ≤ b ∧ ...`: the first universal clause
  makes the cohomology sheaf of K zero for `q < a ∨ b < q`, and the second makes
  the cohomology of `(d.reduction X n).obj K` zero for the same q, for every n.
  The existential bounds precede n, so they are simultaneous.
- The second conclusion uses `IsConstructibleProEtaleCoefficientModuleSheaf` on
  each reduced cohomology sheaf, after the canonical exact scalar restriction
  along `(pbcLevelConstantComparison X d n).hom`. This coefficient isomorphism
  identifies the continuous-function presentation with the ordinary constant
  quotient coefficient sheaf. The predicate is intrinsic, with a positive finite
  constructible partition and local finite constants; it has no etale-origin data.
- The final conclusion quantifies over every n, q, original stratum i, and original
  member j. It provides `M : ModuleCat (A ⧸ d.ideal ^ (n+1))`, `Finite M`, and a
  module-sheaf isomorphism on that precise slice. The left is the restricted
  reduced cohomology sheaf; the right is `adicLisseConstantModules ... M` restricted
  by the same inverse-image and slice functors. Finiteness as a set is equivalent
  to finite generation because the coefficient quotient is finite.
- No completion unit, completeness predicate, compatible tower witness, or etale
  origin appears in either hypotheses or conclusion.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`, its `derived`,
  `completedRing`, `finiteRing`, `reduction`, and positive-quotient finiteness.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, topology/precoverage.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  used by the recorded coefficient module categories.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and Q.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` (the existing general cohomology construction).
- `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`:
  `Scheme.IsConstructibleProEtaleCoefficientModuleSheaf` (existing intrinsic predicate).
- Existing scalar and restriction constructions are reexported by
  `Sheaf.Paper.BoundedConstructibleTower`, `Sheaf.Paper.CompletedConstantSheafReduction`
  and `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`.

The source was read directly using `pdftotext -layout` on the local Bhatt--Scholze
paper, Lemma 6.6.10 and Proposition 6.6.11, especially the definition of locally
constant perfect values and the reverse implication. The node explicitly extracts
only finite bounds and finite-level constructibility for its general adic datum.
Its full seven-step proof, including K-flatness, balancing, finite quotients,
finite selection, stratified detection, and the finite-stalk argument, is in the docstring.
Recorded proof-dependency modules are imported without `public`; the two currently
unstated proof lemmas (stratum restriction and local cohomological bounds) have no
module to import. They are proof prerequisites, not assumptions substituted into the
statement. Mathlib-leaf proof notions are supplied by the existing imports.

Edge cases checked before writing: empty X and zero strata are allowed by the
hypothesis stratification (the constructibility predicate can use one empty stratum);
empty members and empty index types obey the actual cover axiom; the zero complex
and zero perfect model are allowed; the zero quotient ring and ideal equal to the
unit ideal require no nontriviality instance; negative degrees, bounds a=b, n=0 as
exponent one, and all higher positive exponents are retained. No completeness of A,
locality of A, finite dimension of X, or residue-field hypothesis was added.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`: “Perfect local coefficient complexes on a finite
  noetherian stratification have uniformly bounded constructible reductions modulo
  all powers of an ideal”; eight hits about ordinary local cohomology, perfectoid
  approximation, and adic modules, no exact statement.
- `msearch.py ... loogle`: `"Sheaf", "IsBounded"`; zero hits.
- `msearch.py ... grep`: `stratif.*(perfect|bound)|perfect.*pro.?etale`; zero hits.
- `msearch.py ... leansearch`: “A finite stratification by perfect constant adic
  complexes gives common cohomology bounds for every quotient reduction”; eight
  ordinary adic-completion/condensed-limit hits, no exact statement.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id, `perfectStrata`, perfect/stratification/bound patterns and the
  proposed theorem name: no exact declaration. The integral characterization and
  adic-stratified-perfect modules have stronger/specialized hypotheses and include
  completeness and etale-origin assertions; neither is this statement. Their source
  was read to reuse the actual coefficient constructions, without importing a
  downstream characterization theorem that already uses this node in its proof.

No STATEMENT-DISPUTED issue was found. No mathematical statement, proof, or existing
dependency record is changed in this repaired delivery.

## New nodes

`def-weil-pbc-completed-constant-complex-base` is an `existing: true` definition node
for `CompletedConstantReduction.base` and `CompletedConstantReduction.constantComplex`
in `Sheaf.Paper.CompletedConstantSheafReduction`. The first is the canonical map
from the constant ring sheaf to the inverse limit of its positive-power quotient
sheaves, pinned by every quotient projection. The second applies the actual constant
module functor to every term, differential and chain map of an arbitrary cochain
complex. These are precisely the two constructions used by `_hmodel` in the item.
The source is Stacks, Modules on Sites, Constant sheaves, Tags 093J and 093M, and the
local perfect model in Bhatt--Scholze Proposition 6.6.11, reverse implication.
The node's statement cites the small pro-etale site, existing adic constant/completed
coefficient definitions, and cochain complexes; it requires no extra finiteness or
Noetherian hypothesis. Its `lean.statement` is the verbatim signature of `base`, and
`lean.declarations` records both definitions. No new module is supplied.

Searches for this attachment: LeanSearch on “The canonical map from a constant ring
sheaf to its adic completed constant sheaf and the degreewise constant sheaf functor
on cochain complexes” returned 8 generic constant-sheaf/adic-completion hits, including
`CategoryTheory.constantSheaf` and `AdicCompletion.of`; no exact combined interface.
Loogle on `"constantSheaf", "mapHomologicalComplex"` and Mathlib grep on
`constantComplex|adicLisseCompletedRing|CompletedConstantReduction` returned no hits.
Direct `rg` of `lean/Sheaf`, `lean/WeilConjectures`, and `dag/nodes` found the exact
existing constructions in CompletedConstantSheafReduction, with the DAG attachment
only to the theorem node `lem-weil-pbc-completed-constant-sheaf-reduction`; the new
node reuses those definitions as requested by R3. The already landed
`def-weil-pbc-completed-constant-realization-data` defines different finite realization
interfaces, not this pair. `tools/blueprint_refs.py search 'completed constant'`
returned three unrelated smooth-purity nodes, no matching definition; `ancestor`
returned `thm-weil-pbc-finite-extension`, recorded with the item's full via path.
The empty scheme, zero ring, I=0, I=A, zero and unbounded complexes all remain allowed;
positive exponents are indexed by n+1 in the existing Lean implementation.

## Repair of return e3263ad8c90b

- R1: removed the sandbox copy of `def-weil-derived-cohomology-sheaves`. The landed
  SfCommonStageWeilCohomology attachment, its twelve declarations and its importers
  are not changed. The accepted statement continues to use Mathlib's
  `DerivedCategory.homologyFunctor` directly, also named in the node's mathlib_match.
- R2: removed the sandbox copy of `def-weil-proetale-constructible-sheaf`. Its landed
  attachment and declarations are not changed. The accepted statement continues to
  use the existing intrinsic `IsConstructibleProEtaleCoefficientModuleSheaf`, as do
  other landed consumers; it does not need a record replacement.
- R3: added `def-weil-pbc-completed-constant-complex-base`, with `existing: true`,
  recording both canonical constructions, and added its id to the item's stmt_deps.
  Reopened the full signatures and docstrings, and Stacks 093J/093M. The base map
  is fixed by the quotient projections through a proved unique-existence theorem;
  constantComplex has actual functor data. The accepted Lean module is unchanged.
- Advisory: also added the already landed definition nodes
  `def-weil-pbc-bounded-constructible-tower`, `def-weil-pbc-adic-lisse-module`,
  `def-weil-pbc-ringed-site-derived-restriction`, and
  `def-weil-proetale-inverse-image` to stmt_deps, so the previously cited public
  scalar/restriction/constant constructions have explicit owning dependencies.
  A read-only traversal of all statement/proof edges confirms no added dependency
  reaches this item. No records or modules of these dependencies are changed.

## Second reading by NM

The dispatcher forbids starting other agents; independent review belongs to the
maintainer. This section records a separate in-thread rereading, not an assertion
that another worker reviewed the delivery. I reopened the complete node and the
Lean signature and checked: the two Noetherian scheme assumptions; every field of
the actual coefficient datum; completed rather than constant ambient coefficients;
all original stratum-cover indices; perfect models varying with j; explicit slice
localization; quotient-normalized derived scalar extension; a single interval
outside all n quantifiers; intrinsic constructibility after canonical coefficient
transport; and finite module models on each of the original slices.

The rereading removed two unnecessary wrapper definitions of realization and local
restriction, replacing them by the existing constructions directly in the signature.
The compiler's first failure was a missing standard localization on the slice;
this was supplied explicitly, without any universe equality hypothesis. No clause
was dropped or strengthened, and no statement correction was necessary.

Repair self-check: compared the saved item against the current read-only base and retained
only its Lean record plus the five added definition dependencies. The two returned
dependency files are absent from the repaired packet. Reread the new node against both
existing declaration bodies: quotient-projection characterization matches base, and
degreewise constants including chain maps match constantComplex. The new node states
no flatness or exactness theorem. Rechecked that the item's saved lean.statement is
verbatim from the unchanged theorem signature. The first saved-packet dry run passed;
that mechanical pass did not replace the three substantive repairs above.
