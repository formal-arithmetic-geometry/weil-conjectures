# Q02: lem-trf-tate-unit-coefficient-criterion

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-tate-unit-coefficient-criterion.json`: item, statement unchanged, split into four steps.
- `dag/nodes/sec-trace-formula/lem-trf-tate-gauss-multiplicative.json`: statement; unsplit, no exact Mathlib match. Multiplicativity for restricted multivariate series, including zero factors and trivial absolute values.
- `dag/nodes/sec-trace-formula/lem-trf-tate-unit-ball-polynomial-reduction.json`: statement; unsplit, no exact Mathlib match. Residue field, coefficient reduction homomorphism from the Gauss unit ball, and its open-unit-ball kernel.
- `dag/nodes/sec-trace-formula/lem-trf-complete-normed-ring-geometric-inverse.json`: statement; Mathlib leaf. `isUnit_one_sub_of_norm_lt_one`, `Units.oneSub`, `hasSum_geom_series_inverse`, and the complete-ring instance in `Mathlib/Analysis/SpecificLimits/Normed.lean:279,333,345,350`.
- `citations.json`: one verbatim statement quote for each of the seven step/node citation pairs.
- `searches.jsonl`: actual msearch output records; all searches recorded in the nodes were run. Earlier searches in the item are retained verbatim.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint tag, Gauss norm, gaussNorm, Tate algebra, restricted series and the unit criterion. No project declaration states this item. The Tate algebras appearing in Koszul docstrings are strictly commutative resolutions, a different notion. Also inspected the restricted-series sources under `lean/Sheaf/`; the existing presentation definitions do not prove the criterion.

## WANTED

WANTED: Siegfried Bosch, *Lectures on Formal and Rigid Geometry*, April 2008, Section 1.2, printed pp.8-10 (PDF pp.9-11), archival copy at `literature/bosch-formal-rigid-geometry-2008.pdf`, for the item and the two analytic nodes. The primary PDF is readable at https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf and was actually read online, including the Gauss-multiplicativity discussion, Proposition 3 and Corollary 4. The local archival copy is missing. No reference was downloaded or repository file changed.

## Findings and changes

The item's statement is correct and has not changed. Its empty proof was not a split. Its historical searches correctly distinguish formal-series invertibility from restricted-series invertibility. I retained them and added actual searches made for this delivery.

The source proof requires the inverse of a norm-one unit to have norm one before it can be reduced. Step 2 explicitly derives this from multiplicativity, rather than merely assuming that an inverse stays in the norm unit ball. The nonconstant coefficients being individually smaller does not by itself imply that their supremum is smaller for arbitrary families: steps 1 and 3 use restrictedness to prove attainment and thus the strict supremum inequality. Both are essential details for nondiscrete absolute values.

The live completeness node supplies submultiplicativity and completeness but does not state multiplicativity; I did not cite it for that stronger fact. The conditional Mathlib lemma `MvPowerSeries.gaussNorm_mul_eq_mul` requires a uniquely dominant convolution summand (`hdom` at GaussNorm.lean:247-249). The proof that suitable indices exist is not a one-line specialization from the restrictedness predicate. Thus Gauss multiplicativity remains a genuine new unsplit node, with this candidate explained in the search verdicts.

A potential new polynomial-unit node was discarded before writing because the existing `lem-trf-mvpolynomial-divisor-nonzero-constant` applies directly to a divisor of 1. The existing polynomial-domain node likewise makes a new domain leaf unnecessary. Generic complex-operator Neumann inversion is insufficient here, whereas Mathlib's complete-normed-ring lemma has exactly the needed hypotheses.

The item is a historical analytic prerequisite in the inherited Temkin normalization chain. I read the chapter/unit records and the latest `main-20261024` blueprint node `lem-trf-local-term-locality`. Its current proof route is contracting correspondences. This delivery changes no chapter, unit, target, or route, and uses no SGA source. Blueprint ancestor and whole-blueprint searches found no equivalent analytic node; `same_as` is empty for the item and each new node.

## Not duplicates

lem-trf-tate-gauss-multiplicative vs lem-trf-restricted-series-gauss-completion: the latter proves only a submultiplicative norm, completeness and regrouping; it does not assert equality of product norms.
lem-trf-tate-gauss-multiplicative vs lem-trf-affinoid-supremum-seminorm-calculus: the latter compares maximal-point values with the Gauss norm and itself depends on this unit criterion, so using it would be circular.
lem-trf-tate-gauss-multiplicative vs lem-trf-affinoid-quotient-norm-topology: the latter proves equivalence and completeness of quotient norms, not Gauss multiplicativity.
lem-trf-tate-gauss-multiplicative vs lem-trf-tate-weierstrass-norm-division: division/preparation for a distinguished series does not state unrestricted Gauss multiplicativity.
lem-trf-tate-unit-ball-polynomial-reduction vs lem-trf-affinoid-canonical-reduction-finite-type: finite generation of the spectral reduction of a reduced quotient over an algebraically closed base does not identify the integral Tate unit ball's coefficient reduction, its kernel, or the residue field over a general valued field.
lem-trf-tate-unit-ball-polynomial-reduction vs lem-trf-tate-reduction-norm-lifting: the latter assumes surjectivity on a canonical reduction and concludes norm-preserving lifts for a quotient; it gives neither the Tate coefficient reduction map nor its kernel.
lem-trf-tate-unit-ball-polynomial-reduction vs lem-trf-affinoid-distinguished-presentation: the latter constructs a presentation of an affinoid quotient; it does not state the unit-ball coefficient reduction theorem.
lem-trf-tate-unit-ball-polynomial-reduction vs lem-trf-tate-torsionfree-fibre-polynomial: a special fibre of a torsion-free formal model is a different construction from the norm-one Tate unit ball modulo the entire open unit ball, including nondiscrete valuation ideals.
lem-trf-tate-unit-ball-polynomial-reduction vs lem-trf-mvpolynomial-divisor-nonzero-constant: the latter is the reused polynomial divisor theorem, not an analytic reduction comparison.
lem-trf-complete-normed-ring-geometric-inverse vs lem-sfb-scalar-geometric-series: the latter treats only complex/real scalars, not arbitrary complete normed rings.
lem-trf-complete-normed-ring-geometric-inverse vs lem-sfb-banach-small-operator-invertible: the latter treats bounded complex-linear operators and gives bijectivity; the new leaf treats ring multiplication without any complex scalar structure.

I additionally searched every DAG node mentioning the same Bosch document and opened the relevant statements. Finite spectral equations, saturated submodule finiteness, closed quotient completeness, powerbounded integrality, adic submodule topology, normalization lifting, and quotient norms are separate conclusions, not either new analytic statement. No new node restates a clause of the unit criterion: multiplicativity and the polynomial reduction map are independent structural facts, and the generic inversion leaf does not assert the necessity of coefficient dominance.

## Review by Q02

I read `coord/delivery-errors.md` B through E in full, the stage-1 brief, the three blueprint levels in SETUP, GOAL, the chapter/unit records, and the actual latest blueprint node. I reviewed the item against Bosch Section 1.2 Corollary 4, printed p.10, and read the preceding coefficient-reduction and multiplicativity paragraphs on printed p.9 for both new analytic nodes. For the generic inversion leaf I read the pinned Mathlib source at lines 270-350: completeness supplies `HasSummableGeomSeries` at line 279, `Units.oneSub` at line 333 has the geometric sum as its actual inverse, and line 345 proves convergence. The new non-leaf files contain statements only, no hidden proof sketches or dependencies. They introduce all rings, norms, maps, and residue objects, cite their definition nodes, and have complete blueprint provenance.

Step 1 uses the exact live statement of `lem-trf-restricted-series-gauss-completion`: a finite Gauss norm with the ultrametric and product inequalities, its complete metric, and the restricted coefficient description. Its hypotheses hold because K is complete with the stated absolute value. I wrote out norm attainment with the finite exceptional set at b/2, and scalar norm equality is the supremum of the coefficientwise equality |ac|=|a||c|. This is elementary bookkeeping on an already established norm, not a new analytic lemma.

Step 2 uses the new multiplicativity statement exactly to obtain ||g||=||f||^{-1}, so normalization by an actual coefficient a gives BOTH F and G norm 1. It then uses the new reduction statement precisely as a unital ring homomorphism on that subring, not on all of the Tate algebra. This yields red(F) red(G)=1 over the residue FIELD explicitly supplied by the same statement. I opened `lem-trf-mvpolynomial-divisor-nonzero-constant`, whose statement applies to every integral domain and arbitrary variable set, and used it with a=1 and f=red(F). Its conclusion really says f=C(b); the displayed product forces b nonzero. No stronger polynomial unit theorem is being taken from it.

Step 3 uses the coefficient formula and residue-kernel description of the new reduction node. A norm-at-most-one coefficient has zero residue exactly when its norm is <1. The normalized constant has nonzero residue and hence norm 1, all other coefficients have zero residue. Attainment for the restricted tail then converts coefficientwise strict inequalities into a strict supremum inequality, including the zero-tail case. Scaling by a preserves precisely the desired ratio. This step proves the elementary consequence and is not a clause moved into a helper node.

Step 4 applies the existing completeness/norm statement and the new generic geometric-inverse leaf to h=1-c0^{-1}f. The strict hypothesis first proves c0 nonzero, so all divisions are legal. The equality ||h||=||f-c0||/|c0| follows coefficientwise from step 1. The complete normed-ring hypotheses hold, since an ultrametric norm also satisfies the ordinary triangle inequality. Finally f=c0(1-h) and g=c0^{-1}S give fg=1 by associativity and the scalar action. No inverse in the unrestricted formal-series ring is substituted for an inverse in T_r.

I tested r=0, f=0, nonzero constants, f=1-X (not a unit: tail norm equals the constant), and f=1-bX with |b|<1 (geometric inverse is restricted). For reduction and multiplicativity I also tested trivial valuations: restricted families then have finite support, so reduction is the identity polynomial map and multiplicativity becomes the usual polynomial Gauss norm. The arguments neither require a discrete value group nor an infinite residue field, and they work over imperfect or positive-characteristic fields. The generic inverse leaf allows noncommutative and zero rings and imposes no scalar hypothesis. No disputed statement was found.

The citations file was constructed by copying literal substrings from the seven cited statements and asserting membership in their source statements. The four proof steps have 531, 648, 464 and 576 characters, respectively; no non-elementary step exceeds 2000 characters. The two analytic structural claims are deliberately nodes rather than inline comparisons. No Lean was written and no compiler, Lake, or local DAG checker was run.

## Unfinished work

None for this one-level split. The two new analytic statement nodes intentionally remain unsplit for their future workers. The archival source request remains as disclosed above; it does not prevent reading the primary source online. The first remote dry run required a notion citation in the generic leaf. I added `def-weil-field` at its real norm codomain; this introduces no scalar-field hypothesis on B and the normed-ring axioms remain explicit. The required final remote dry run and direct delivery are the remaining mechanical actions.
