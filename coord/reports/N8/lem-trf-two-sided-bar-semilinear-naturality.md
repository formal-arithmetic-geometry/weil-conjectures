## Worker report

Stage 2, N8: state lem-trf-two-sided-bar-semilinear-naturality in
Sheaf.CategoryTheory.TwoSidedBarSemilinearNaturality. The stage-1 split is already
accepted and has no released repair note. The previous session had read its ten
steps but had started no compiler or delivery and saved no packet. This session
follows the launcher's explicit stage-2 resumption and the current stage-2 brief.
Only the item's lean record changes; there are no new DAG nodes or dependency
repairs, and the natural-language statement, proof, dependencies and review remain
unchanged. The stage-2 sandbox is the delivery tool's designated stage-2 directory.

All data definitions are real constructions. Index is the sigma type of a string
and its endpoint arrow; term and barTerm are Mathlib coproducts. delete is
precomposition by the simplex face functor. firstArrow and lastArrow are actual
arrows of the string, with firstArrow applying the coefficient map exactly when
the first vertex disappears. horizontalFace, verticalOperator, horizontalD,
verticalD and barD give all the displayed generator rules and alternating sums.
evaluate and forgetLast are the two actual edge coproduct maps. evaluationComplex
is Mathlib's alternating-face complex extended from natural chain degrees into
nonpositive integer cochain degrees, with its standard evaluationCoordinates.

Model records a commuting HomologicalComplex₂ and its coproduct coordinates,
zero positive bidegrees, the two unsigned differentials, the ordinary bar complex
and its coordinates and differential, and both chain augmentations. Its four
edge/off-edge fields pin every augmentation summand exactly. The totalization is
Mathlib HomologicalComplex₂.total with shape up ℤ. This gives the prescribed
horizontal plus (-1)^p vertical convention in bidegree (-p,-q): Mathlib's sign
is (-1)^(-p), equal to (-1)^p. Only p+q=-n contributes in degree n, so zero
positive bidegrees leave finitely many nonzero summands. Mathlib permits the
zero summands outside that finite diagonal; this is the canonical same total.
No arbitrary total complex or augmentation is substituted for these objects.

reindex is the explicit generator map V: send c to c composed with u, postcompose
the endpoint by k, and send its coefficient through θ. barReindex is the explicit
ordinary bar map. SemilinearMap records an actual double-complex morphism and
three chain maps, with coordinate formulas determining V, its total, t and b.
The t formula is θ at Q_q followed by F'(k_q), with scalar restriction inserted.
Its evaluationSquare and barSquare are equalities of chain maps with precisely
the stated source and target. operator_naturality explicitly includes all vertical
simplicial operators, so degeneracies are covered as well as alternating faces.

System supplies Model and SemilinearMap simultaneously for every small category,
commutative ring, coefficient functor, simplicial object and compatible u, ρ, θ, k.
Its identity and composition fields cover the double map, total map, evaluation
map and bar map in every degree. Equality of the underlying elements is equality
under the usual identity-on-groups restriction isomorphism. identityCoefficient
uses ModuleCat.restrictScalarsId. compositeCoefficient uses
ModuleCat.restrictScalarsComp, and the composite k is whiskerRight k v followed
by l; thus these clauses compare the actual intended maps. scalarRestriction
asserts the same four maps are isomorphisms for pure coefficient restriction,
with identity-on-coefficient generator formulas already imposed. This identifies
the double, total and both edge complexes, not just their cohomology groups.
system_exists states inhabitation; no definition chooses data from it. Model and
System are helper records for the very objects and laws of this item, rather
than independent input hypotheses or a new theorem assumed in lieu of the item.

restriction_exact includes preservation of every small coproduct, finite limits
and finite colimits (in particular kernels and images); restriction_quasiIso
asserts preservation of quasi-isomorphisms. restriction_inverse uses Mathlib's
actual mapDerivedCategory and localized quasi-isomorphism inverses.
localized_squares writes both squares through mapDerivedCategoryFactors.inv,
thereby giving the precise localization identifications instead of an unspecified
isomorphism. The chain identity/composition equalities continue after applying
localization, since localization is a functor; the canonical restriction
identifications are the same ones used by System and mapDerivedCategoryFactors.
No resolution, contracting homotopy, flatness or projective-preservation hypothesis
occurs. Neither edge is asserted to be a quasi-isomorphism for arbitrary Q.

Dependencies: the size-convention node is metatheoretic and is rendered by the
explicit universe u, small categories and ModuleCat.{u}; derived clauses quantify
over the standard permitted HasDerivedCategory.{u+1} choices. SimplicialObject,
its faces and natural transformations are the recorded Mathlib notion. The
recorded WeilConjectures.CategoryTheory.DoubleComplexTotal is publicly imported
for HomologicalComplex₂ and its total API; no first-quadrant filtration result is
applied to this nonpositive complex. DerivedCategory and its Q functor are the
recorded Mathlib notion. The exact-functor proof dependency is provided by
Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor, which is also a statement
import because localized_squares mentions mapDerivedCategoryFactors explicitly.
No imports of any downstream derived-colimit comparison or its existence theorem.

Sources read: Stacks sites-cohomology.tex, Tag 08PH
(example-morphism-categories, generator reindexing formula), Tag 08PD
(remark-morphism-fibred-categories, derived change-of-category map), and Tag 08Q9
(lemma-compute-by-cosimplicial-resolution, two augmentation comparison context).
The two-sided semilinear calculation is correctly identified as agent-written,
not claimed to occur verbatim in Stacks. Read the current latest blueprint's
lem-trf-local-term-locality proof for inherited ancestry; none of its contracting
correspondence theorem is used as a bar lemma. No SGA source is used.

Existing-declaration searches: rg for the exact blueprint tag and for two-sided
bar / twoSidedBar / bar semilinear over WeilConjectures and Sheaf finds no exact
statement. The nearby DerivedColimitBar and SimplicialDerivedColimitComputation
modules were read: their category-colimit system and comparison theorem do not
state the strict two-sided lemma, and the latter still has sorry. DAG and whole
blueprint searches for two sided bar and semilinear functoriality find no imported
duplicate. The siblings horizontal-augmentation, contractible-augmentation and
bar-scalar-restriction-coherence were read; none has a Lean record supplying this
construction. New namespace CategoryTheory.TwoSidedBar is absent upstream.

Actual msearch queries and results are in searches.jsonl. LeanFinder: "Semilinear
natural map of the two sided bar double complex indexed by strings ending at a
simplicial object commutes with evaluation and forgetful augmentations" returns
Dold-Kan projections/maps and classifyingSpaceUniversalCover module augmentation,
not this two-sided construction. LeanSearch: "Two sided bar construction
naturality with both edge augmentations and restriction of scalars" returns
ModuleCat restriction/extension adjunctions and bifunctor total-map naturality;
none states this lemma. grep "two.sided.*bar|bar.*semilinear|bar.*naturality"
returns zero hits. Loogle '"total", "mapIso"' returns HomologicalComplex₂.total.mapIso
and its component rules, read as the existing totalization API rather than an
exact match for the item. Every search was run, and all services answered.

Edge cases checked: a zero ring gives zero modules and all displayed maps still
exist; p=q=0 gives the un-signed evaluation/forgetful maps; differential leaving
index zero is zero; coincident image strings are summed by Sigma.desc, so u need
not be injective on objects or arrows; coefficient restriction along a nonflat
map remains exact on underlying groups; positive cochain degrees vanish; a
simplicial object in an empty category is simply not available, with no extra
nonemptiness assumption added. For a constant simplicial object in a discrete
two-object category the forgetful augmentation need not be a quasi-isomorphism;
the delivered statement does not claim that it is. No statement dispute remains.

Theorems are sorry-only, as required for stage 2: system_exists,
operator_naturality, restriction_exact, restriction_quasiIso, restriction_inverse
and localized_squares, all under CategoryTheory.TwoSidedBar. Each has the source,
blueprint tag and a full natural-language proof in its docstring. No data is sorry.
Compiler and dry-run results are recorded below after validation completes.

## Review by N8

I checked the source and each of the ten accepted proof steps against this
interface. Steps 1 and 9 become restriction_exact, restriction_quasiIso and the
canonical mapDerivedCategoryFactors in localized_squares; this uses exactly the
exactness hypotheses written in the exact-functor node. Steps 2 and 4 fix the
commuting double complex, its unsigned alternating differentials, and Mathlib's
signed total. Steps 3 and 4 are the explicit reindex and operator_naturality,
with θ naturality and k naturality used with their actual domains. Step 5 is the
t and b coordinate formulas for chain maps. Step 6 is Model's pinned edge maps;
at p=1 the two evaluations cancel, and at q=1 forgetting either face gives the
same string. Step 7 is exactly the two strict chain-map square fields. Step 8 is
System's four identity/composition laws, with compositeCoefficient using the
canonical coefficient identification. Step 10 is restriction_inverse and the
localized_squares statement, with no unjustified inversion of either augmentation.
I corrected the initial compile draft by importing Whiskering and opening its
Functor namespace; I made the derived-category choices explicit binders on the
derived clauses, without installing a second global instance. The positive
cochain vanishing and coproduct coordinates cover all bidegrees and summands,
so the records do not allow arbitrary unidentified comparison maps.

## Second reading by N8

No second worker was started. The direct-delivery brief assigns the independent
reading to the maintainer. The preceding N8 review is the author's self-review.

## Validation

The server wrapper compiled the complete module in both sandbox and library modes,
with no warnings or errors. The final library compile took 11.5 seconds. The
required deliver2.py --no-push then compiled it again and printed
"OK (dry run): commit 7164bcb9ff7 passes the preflight and compiles; nothing pushed".
A final comparison with live confirmed that only the lean field of the item
changes. The file has no line over 100 characters, 30 recorded declarations and
six named sorry-only theorem proofs. No other file or node is delivered.
