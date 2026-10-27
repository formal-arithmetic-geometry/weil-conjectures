## Worker report

The module `Sheaf.Paper.LisseFlatHomSiteComparison` states
`AlgebraicGeometry.ProEtale.lisseFlatHomSiteComparison`, with a `sorry` proof.
Its five auxiliary definitions spell out the conclusion and construct its actual
finite-coordinate maps. They postpone no data or proofs. The repair adds one definition-owner node with an `existing: true` record for
the unchanged published restriction constructions. There is no dependency-module
repair and no mathematical statement correction.

Hypotheses, in the order of the node:

- The fixed algebraic closure of a finite field is
  `D : WeilConjectures.FiniteFieldDatum.{u}`. Its fields record p, q, the finite
  base field and its algebraic closure, using the recorded global datum.
- The distinct coefficient prime is `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- The finite extension is `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The uniformizer, its valuation ring and
  quotient are precisely the recorded `Padic.coefficientExtensionRing l E n`,
  rather than a new coefficient construction. Positive n is `(n : ℕ+)`.
- S is `Scheme.{u}`, with `[S.Over (Spec (CommRingCat.of D.k))]` and
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on its structure map.
  The latter two together mean finite type.
- L is an ordinary `ModuleCat`-valued etale sheaf, with
  `[Scheme.IsFiniteLocallyConstantSheaf L]`. Over the finite coefficient ring this is
  locally constant with finite stalks, not a freeness hypothesis.
- `_hflat : ObjectProperty.flat L` is the exact tensor-flatness condition. The
  existing `Etale.flat_iff_forall_flat_sheafFiber_obj` identifies it with flatness
  of every geometric stalk. Thus this does not replace the hypothesis by local
  freeness or projectivity.
- N is the ordinary unbounded etale derived object, with the recorded
  `Etale.DerivedCategory.isBoundedConstructible` predicate. There is no finite
  Tor hypothesis on N and no choice of a bounded representative as input.

Conclusions, after expanding `lisseFlatHomSiteAssertion`:

- K is the existing `DerivedCategory.singleFunctor _ 0` applied to L: L in
  degree zero. F is the recorded comparison inverse image, derived termwise;
  H and G are the existing etale and pro-etale `derivedHom` bifunctors.
- The first conjunct is `IsIso (siteComparisonEvaluationHom ... K N)`, for
  precisely the previously defined evaluation transpose. No replacement arrow
  or arbitrary isomorphism is introduced.
- The second conjunct, expanded through `lisseFlatHomNaturality`, is the full equation for contravariance in the first
  variable and covariance in the second variable. It quantifies over actual
  morphisms `f : K' ⟶ K` and `g : N ⟶ N'` and uses the maps of H, G, and F.
  Its ambient naturality also restricts to the lisse and bounded constructible
  arguments in the node.
- The third conjunct supplies an actual etale cover and, on each member, a
  natural-number rank and an isomorphism from the restriction of L to the
  constant module sheaf on `Fin r → A`. This is the finite free module A^r.
- For every etale object U, the fourth conjunct asserts
  `siteHomRestrictionAssertion` with the canonical restriction square and
  both evaluation-normalized internal-Hom restriction maps. This includes
  invertibility of those maps and the equation identifying the restriction
  of this very beta with beta on U. It also asserts that equation on every
  successive slice V over U, using those same canonical maps. The existing
  restriction square is built from coherent ordinary inverse-image comparisons,
  rather than freely chosen isomorphisms of derived objects.
- `lisseFlatHomLocalAssertion` on each U quantifies over every rank r and every
  derived finite-free trivialization e. A chosen sheaf trivialization in the
  preceding clause induces such an e by the degree-zero functor and the
  standard constant-unit and finite-sum identifications. The helper
  `lisseFlatHomCoordinates` evaluates at each specified basis vector. After F,
  that vector is `ε_F ≫ F.map (Sigma.ι _ j ≫ e.hom)`; precomposition and the
  canonical `MonoidalClosed.unitIsoSelf` give the jth coordinate. Both coordinate
  maps are asserted invertible. Their equation conjugates the very beta to
  `piComparison F (fun _ : Fin r ↦ M)`, the canonical finite-power comparison.
  Finite products here are finite direct sums in the additive derived category.
  Universal quantification over e includes all changes of trivialization;
  conjugating the displayed equation by the two coordinate isomorphisms gives
  the transition equation for any two bases, including locally varying bases.
- The fifth conjunct gives constructibility of every cohomology sheaf of H(K,N).
- The sixth conjunct preserves each specified interval [a,b]: vanishing of all
  cohomology of N outside it implies vanishing of all cohomology of H(K,N)
  outside the same interval. It does not merely give some larger interval.
- The last conjunct is membership in the standard t-structure's `plus`, the
  recorded bounded-below condition.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its
  coefficient conventions.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, preserving the original coefficient
  constructions; its proof is supplied explicitly at the two finite-ring predicates
  in the final signature, using `n.property`. No finiteness hypothesis is added.
- `def-weil-scheme-morphism-properties` is a convention node with no declaration:
  its stipulated Mathlib morphism properties are used directly.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, `DerivedCategory.singleFunctor`,
  `DerivedCategory.homologyFunctor`, and the standard derived t-structure.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the recorded ordinary finite
  coefficient realization and pro-etale category interface. The theorem uses
  ordinary constant-A module sheaves on both sites, as the item specifies.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` and its six-functor imports:
  the canonical `comparisonUpperStar` and its exact derived functor.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` preserves the generic
  ringed-site constructions and ordinary etale `Etale.derivedHom`; the actual
  sheaf derived Homs are the recorded etale/pro-etale closed derived Homs.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible` and
  `Scheme.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison`:
  `siteComparisonEvaluationHom` and `siteComparisonDerivedMonoidal`.
- Added definition stmt_dep `def-sf-site-hom-restriction-comparison`, with an
  `existing: true` record for module
  `Sheaf.AlgebraicGeometry.SiteHomComparisonThick`: its actual restriction
  functors, canonical tensor structures and `siteHomRestrictionAssertion`.
  Neither theorem in that module is a statement dependency. The definition
  record lists exactly the 14 restriction constructions used by this interface.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual` and its public
  imports give the existing finite locally constant and flatness vocabulary.

All recorded proof dependencies with modules are imported as proof imports,
except where already needed publicly in the statement. The theorem docstring
retains all eight steps of the DAG proof, including good truncation, identification
of evaluation on tuples, descent of the zero cone, and the constructible tensor
refinement for the final cohomological assertion. Mathlib leaf dependencies need
no extra project module.

Edge cases checked: empty S (empty cover is allowed), empty cover members, L=0
(rank zero is allowed, with the empty finite power a zero object), N=0, a=b,
intervals not assumed to be minimal, all positive coefficient levels including
n=1, nonconstant ranks on disconnected S, iterated restrictions and arbitrary
basis changes. For A=Z/4 and N=Z/2[0], the statement imposes no finite Tor
condition; L=A[0] gives the identity and the unchanged [0,0] bound. The site
object/morphism universes remain those of the published small sites, and
coefficients and modules have the common u+1 size convention.

Searches made before writing:

- msearch LeanFinder: "comparison pullback derived internal Hom finite flat
  locally constant sheaf etale proetale" returned eight unrelated locally
  constant/continuous-map and module-pullback declarations, no match.
- msearch Loogle: "CategoryTheory.Sheaf, IsLocallyConstant" returned no match.
- msearch grep in CategoryTheory: "internalHom|internalHomComparison|IsLocallyConstant"
  returned internal Hom definitions and generic constructions, not this theorem.
- msearch LeanSearch: "inverse image derived internal Hom finite locally constant
  flat sheaf" returned sheafHom and unrelated condensed/locally constant results.
- rg of both `lean/WeilConjectures` and `lean/Sheaf` for evaluationHom,
  homSiteComparison and lisse/flat found the canonical evaluation comparison,
  the existing LisseDual and SiteHomComparisonThick interfaces and related
  finite-duality consumers. None states all this node's conclusions. The
  existing `isIso_finiteFreeHomComparison` takes globally finite-free bounded
  complexes; `derivedHomSheafComparison_isIso_lisse` concerns a different
  sheaf of derived morphisms, so neither is recorded as this node's theorem.
- Search for this node id in `lean/WeilConjectures` gave no declaration.

No STATEMENT-DISPUTED issue was found.

## Second reading by Q90

A separate reading of the node against the completed module checked the actual
conjunction, rather than just the main IsIso assertion. It confirmed the field,
coefficient and scheme binders, the lisse and stalk-flatness hypotheses, the
ordinary coefficient categories, every cover member's finite free value, the
canonical beta, both-variable naturality, and constructible cohomology in the
original interval. It specifically checked that local coordinates are constructed
from basis evaluation, rather than selected as arbitrary isomorphisms, and that
the restriction assertion includes both internal-Hom isomorphisms and its
comparison equation on successive slices. All ranks including zero and every
trivialization are quantified. Two namespace errors in the first coordinate draft
were repaired (`MonoidalClosed.pre` and `MonoidalClosed.unitIsoSelf`), and the cover
type was made explicitly `Scheme.Cover.{u} Scheme.etalePrecoverage X`. This is a
second pass by the dispatched worker; no additional agent was started, as required
by the dispatch brief.

The second pass also corrected the lisse predicate to its full recorded namespace,
`Scheme.IsFiniteLocallyConstantSheaf`.

The generic `lisseFlatHomFiniteFreeAssertion` packages the coordinate equation
before specializing categories. On the slice its comparison is written as
`(Functor.LaxMonoidal.ihomComparison F K).natTrans.app M` with precisely
`siteComparisonDerivedMonoidal` supplying F's structure. This is the definition
body of the recorded `siteComparisonEvaluationHom`, with the same arguments
and tensor structure; it is not a different comparison. Using that body avoids
expensive kernel conversion through the two published derived-Hom aliases.
`piComparison` is Mathlib's existing canonical finite-product comparison,
whose definition is exactly the tuple of mapped projections described above.

The final signature supplies `Padic.finite_coefficientExtensionRing l E n n.property`
explicitly as the Finite instance argument; it does not depend on typeclass search
recognizing a positive natural coerced from `PNat`.


## New nodes

`def-sf-site-hom-restriction-comparison` owns exactly these existing declarations
in `Sheaf.AlgebraicGeometry.SiteHomComparisonThick`, all in namespace
`AlgebraicGeometry.ProEtale`:

- `siteHomEtaleObjectHom` is the given etale object's structure morphism.
- `siteHomExactDerivedMonoidal` transports the actual residue-derived monoidal
  structure to exact termwise derived pullback.
- `siteHomEtaleRestrictionEvaluation` and `siteHomProEtaleRestrictionEvaluation`
  are the evaluation transposes for the supplied restriction tensor structures.
- `siteHomRestrictionSquareFor` derives the ordinary canonical square;
  `siteHomRestrictionSquareAssertion` defines the two invertibilities and exact
  comparison equation; `siteHomRestrictionAssertion` specializes that predicate
  to the canonical site evaluation maps.
- `siteHomEtaleRestriction`, `siteHomProEtaleRestriction`, and
  `siteHomRestrictionSquare` are the fixed-coefficient functors and square.
- `siteHomEtaleRestrictionMonoidal` and `siteHomProEtaleRestrictionMonoidal`
  supply their canonical transported structures.
- `siteHomEtaleRestrictionHom` and `siteHomProEtaleRestrictionHom` specialize
  the evaluation transposes to those canonical structures.

Its source is Stacks 08J9, 08JB and 07A4, read in
`literature/stacks-project/sites-cohomology.tex`, and the blueprint comparison
proof paragraphs 1--3. Its definition uses the already recorded derived
categories, ordinary coefficients, internal Hom, evaluation comparison,
comparison-pullback square and monoidal-category notions. No theorem of
invertibility or square commutation is moved into the definition: these are
conjuncts of the defined predicate. The general square predicate allows
arbitrary four categories and appropriately typed supplied maps; the site
specialization uses the actual canonical maps. The generic monoidal transport
retains precisely its flat-preserving exact strong monoidal left-adjoint
hypotheses, and the finite-ring slice specialization uses the canonical instances.

Fresh searches: msearch LeanSearch and LeanFinder for "canonical derived
internal Hom restriction comparison square for etale and proetale sites" both
returned eight hits, on cover-dense restriction, closed-category comparison and
ordinary sheaf pullback; no exact match. msearch grep
`ihomComparison|mapDerivedCategoryCompIso` in CategoryTheory returned 0 hits.
The raw returned names are retained in the new node's mathlib_searches.
Source rg finds these declarations in SiteHomComparisonThick alone, and DAG rg
finds only the theorem-owner node. `blueprint_refs.py search 'Hom restriction'`
returned 0 matches; `ancestor` identified
`lem-weil-finite-duality-site-comparison`. Hence the node records existing
published definitions rather than duplicating them. Its lean.declarations
excludes both sorry theorems and unrelated thick-locus and shift definitions.

## Repair of returned head 965188079cdb

The H2 finding is repaired by replacing the sole added theorem statement
dependency `lem-sf-site-hom-comparison-thick` with the new definition owner.
The nine original definition dependencies, complete mathematical statement,
proof, proof dependencies, and delivered Lean module are unchanged. Comparison
with the current main source showed that the saved item differs only in lean
and this added stmt_dep; no current-main changes are overwritten. The live
SiteHomComparisonThick source was also read with scompile.py --source and its
restriction definitions match the local source. No upstream file is delivered
or modified.

Second reading of this repair by Q90: checked the new TeX definition against all
14 complete declaration bodies and the verbatim primary signature, including
the contravariant theta inverse in the square, covariant theta on the second
argument, both IsIso conjuncts, explicit monoidal arguments in the generic
interface, and weakly-etale flat preservation in the finite-coefficient slice.
The existing:true record owns definitions only and is not a choose of either
sorry theorem. The item uses exactly those declarations. Empty schemes, zero
objects and rank zero introduce no new restriction; all preceding edge checks
and the maintainer's accepted clause-by-clause reading remain applicable.
