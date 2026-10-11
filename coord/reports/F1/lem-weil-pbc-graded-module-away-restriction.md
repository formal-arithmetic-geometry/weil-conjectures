## Worker report

The module states the restriction lemma for a graded commutative ring and graded module. It
introduces the ordinary localizations at homogeneous elements `f`, `g`, and `h`, and the
subsets of equal-degree fractions through `LocalizedModule.degreeZeroFractions`. The hypotheses
`hf`, `hg`, `hd`, and `hδ` render homogeneity and positive degrees; `he` and `he'` render the
relations `g^e = a f` and `h^e' = a' g`; `hsmul` renders compatibility of the graded module
action. The conclusion supplies the ordinary S-linear map and ring map, their fraction formula,
semilinearity, restriction to degree-zero fractions, identity/transitivity and the principal
localization comparison maps appearing in clauses (i)--(iv). The proof is intentionally `sorry`
for stage 2.

Dependency declarations used are `LocalizedModule.Away` from
`Mathlib.Algebra.Module.LocalizedModule.Basic`, `Localization.Away` as the ordinary localization
notion, `HomogeneousLocalization.Away` for degree-zero ring localization, and
`LocalizedModule.degreeZeroFractions` from `Sheaf.Algebra.Module.DegreeZeroFractions`.

Edge cases checked: positive degree hypotheses exclude degree zero homogeneous elements; the
localization types allow nilpotent denominators (the localized module may be zero); and the
indexing of module degrees includes all integers while equal-degree fractions use nonnegative
numerator degrees.

Searches made: `msearch.py leanfinder` for “restriction between degree zero localizations of a
graded module” (hits only ring `HomogeneousLocalization` maps); `msearch.py loogle` for
“HomogeneousLocalization, LocalizedModule” (no hits); `msearch.py grep` for
`LocalizedModule|awayMap` in `RingTheory/GradedAlgebra` (only ring localization declarations);
`rg` over `WeilConjectures` and `lean/Sheaf` (no matching restriction declaration, except the
separate `degreeZeroFractions` node). The existing DAG node `def-sc-degree-zero-module-fractions`
is cited for the equal-degree subset.

## New nodes

None.

## Dependency modules

None; the landed `def-sc-degree-zero-module-fractions` declaration is used directly.

## Second reading by F1

The Worker report above describes the first draft and is superseded by the repairs
below. I read the unchanged DAG statement, all four statement dependencies, the
Lean definitions/signatures they name, and Stacks Constructions, lemma-standard-open
(Tag 01M4). The pinned Stacks checkout was absent locally; I downloaded its exact
constructions.tex at commit a04446e57ec1fbc252a871afcec7752fb2807b14 into scratchpad.
The surrounding source assumes a graded commutative ring and positive homogeneous
standard-open denominators, and its module clause assumes an arbitrary graded module.
There is no Noetherian, field, characteristic, finite generation, or domain assumption.

Object/hypothesis/conclusion checklist (each verdict is exact):

- N-graded commutative S: `S`, `[CommRing S]`, `𝒜 : ℕ → AddSubgroup S`,
  `[GradedRing 𝒜]`. The original arbitrary set families did not give a ring grading.
- Z-graded S-module M: `M`, `[AddCommGroup M]`, `[Module S M]`,
  `𝓜 : ℤ → AddSubgroup M`, `h𝓜 : DirectSum.IsInternal 𝓜`, and `hsmul`.
  This is a direct-sum decomposition with the exact n+z action rule.
- Positive homogeneous f,g and optional h: the local index `F` consists of pairs
  `(element, degree)` with the two required predicates. All maps are indexed by F,
  so the identity and transitivity clauses use the same chosen maps. Degrees can
  differ; h is quantified only for the composition clauses, rather than assumed
  unnecessarily at the outset as in the worker's signature.
- Homogeneous multipliers and positive relation exponents: `Rel f g` has witnesses
  `e k a`, `0 < e`, `a ∈ 𝒜 k`, `g^e = a*f`. The original he/he' omitted homogeneity.
- Ordinary module and ring localizations: `N f = LocalizedModule.Away f M`,
  `L f = Localization.Away f`. These are the dependency declarations, not copies.
- Degree-zero ring: `R f = HomogeneousLocalization.Away 𝒜 f`, precisely
  def-nagata-homogeneous-localization-degree-zero's Mathlib declaration.
- Degree-zero module: `Z f : Submodule (R f) (N f)` has carrier exactly
  `degreeZeroFractions` from def-sc-degree-zero-module-fractions. The R-action is
  `Module.compHom` of the standard embedding `algebraMap (R f) (L f)`; its operations
  are inherited from N. Nothing is defined by sorry. In a genuine grading this
  equal-degree subset equals the node's x/f^m, x of degree m deg f: a nonzero
  denominator has a unique degree, and a zero denominator makes the localization zero.
- (i), unit and inverse: `IsUnit (algebraMap S (L g) f)` and bijectivity of scalar
  multiplication by f, with `f * (a/g^e) = 1` for every relation witness.
- (i), unique S-linear lambda: `lambda`, base-fraction equation, and universal
  equality `T = lambda` for every S-linear T agreeing on x/1.
- (i), formula and independence: the fraction clause is quantified over EVERY
  homogeneous relation witness e,k,a, using that a (the first draft shadowed it with
  an unconstrained universally quantified a). Unique lambda makes witness choice irrelevant.
- (i), ring map and semilinearity: `lambdaS` preserves the S localization maps;
  `lambda (r • x) = lambdaS r • lambda x`.
- (i), restriction and ring restriction: the coe equation for `rho` identifies it
  with lambda on Z; the val equation for `rhoS` identifies it with lambdaS on R.
  `rho` is an additive hom and satisfies the explicit rhoS-semilinearity equation.
- (ii), identity: all self-relations give pointwise identity for rho and rhoS.
  Transitivity: two relations give `Rel f h` and pointwise composition for rho/rhoS
  for every witness of that composite relation. The displayed exponent/multiplier
  equation h^(e*e')=(a'^e*a)*f is separately present.
- (iii), u: `U f g : R f` has val exactly g^(deg f)/f^(deg g). Its rhoS image is
  a unit. `thetaS` is a ring equivalence Localization.Away U -> R g; `theta` is
  an additive equivalence LocalizedModule.Away U (Z f) -> Z g. Their base-fraction
  formulas specify the induced maps, and the thetaS-semilinearity clause gives the
  required module isomorphism. The power-times-image formula is the node's inverse
  power formula without choosing an inverse representation: since rhoS(U) is a unit,
  rhoS(U)^k • theta(x/u^k)=rho(x) is equivalent to that formula.
- (iv), u' and compatibility: U f h is the same defined fraction for the third
  denominator. Its ring localization makes U f g a unit. `kappa` has the actual
  source and target second module localizations, is R f-linear, preserves x/1,
  and is unique with this property. The final pointwise equality is exactly
  rho(g,h) ∘ theta(f,g) = theta(f,h) ∘ kappa.

Selecting all canonical maps in a single family expresses the same uniqueness and
composition assertions as the node. No extra data assumptions are introduced;
uniqueness and classical choice identify this presentation with the node's pairwise
canonical constructions. The DAG statement and its proof were not changed.

Edge cases: F may be empty (e.g. only degree-zero components are nonzero); the
quantified families and all compatibility clauses then remain meaningful. Zero rings,
zero modules, nilpotent and zero denominators are allowed: localizations may be zero
and the fraction subsets still contain their zero class. Positive degree excludes
degree-zero chart elements but every fraction exponent, including m=0 and k=0,
is retained. Module grades range over all integers. No scheme is quantified here,
so an empty Proj imposes no additional hypothesis. S and M have independent arbitrary
universes u,v; no test-object universe or characteristic restriction appears.

Independent searches (2026-10-11): `msearch.py leanfinder` for "graded module degree
zero localization restriction transitivity principal localization" returned eight
ring-only homogeneous-localization hits. I opened HomogeneousLocalization.Away,
awayMap, and Away.isLocalization_mul: the latter two cover the special ring case
of a product denominator, not the general relation or modules. `msearch.py loogle`
for "HomogeneousLocalization.Away, LocalizedModule" returned zero hits.
`msearch.py leansearch` for "graded module localized degree zero restriction unique
maps composition" reported service unavailable (Internal Server Error); no verdict
is inferred from that unavailable search. `msearch.py grep` for
"LocalizedModule.*(grade|[Hh]omogeneous)|[Gg]raded.*LocalizedModule" returned zero hits.
Direct rg searches of Mathlib, WeilConjectures, and lean/Sheaf found the existing
fraction subset, graded localization exactness, and the upstream ring-only degreePart
and ring transition cocycle. I opened those candidate modules; none states this
restriction theorem for arbitrary graded modules. There is no full-name collision.

Mismatch repairs: replaced arbitrary subset families with real gradings; restored
homogeneous relation multipliers; removed the unnecessary global third-denominator
hypothesis; fixed the shadowed multiplier; supplied uniqueness and independence;
replaced the duplicated subset clause with actual restricted additive/semilinear
maps; added identity and transitivity; replaced the unrelated bare bijections with
the correctly typed principal-localization equivalences, unit and fraction formulas;
added the canonical kappa and commuting square; added header and ten-step proof
in the docstring. This delivery has no new definition nodes or dependency modules.
Every dependency is used through its existing definition. There is one named theorem
with its intentional sorry, and no theorem is proved in stage 2.

Verification: scompile.py compiled the whole module cleanly (2.5 seconds), with no
errors or warnings. All variables/universes are bound; node lean.statement is the
verbatim signature. The report's earlier "New nodes"/"Dependency modules" sections
remain applicable.
