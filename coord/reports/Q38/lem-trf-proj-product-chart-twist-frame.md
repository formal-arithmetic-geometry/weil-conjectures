## Worker report

Item: lem-trf-proj-product-chart-twist-frame. Module:
`Sheaf.AlgebraicGeometry.ProjProductChartTwistFrame`, main declaration
`AlgebraicGeometry.Proj.productChartTwistFrame`.

This is a statement-only delivery. Its sole theorem has proof `sorry`. The two
helper definitions `productChartFrameFraction` and `productChartInverseFrameFraction`
construct actual ordinary-localization fractions, with no postponed data or proofs.
They name the two fractions of this node, rather than introducing an independent notion.
No statement correction, dependency repair, or new DAG node is needed.

Source read: `literature/stacks-project/constructions.tex`, lines 1853–1910
(Tag 01MU, especially its first proof paragraph), and lines 1919–1944
(Tag 01MV, especially the displayed coefficient in its proof). These state the frame
`(a/b)^n = a^(2n)/(ab)^n` and the expression `f/1 = (b^n f/a^n)(a/b)^n`.
The full node and its six proof steps were read, together with both statement dependencies,
their records, and the source declarations described below.

Hypothesis and clause correspondence:

- The nonnegatively graded commutative ring is `{A : Type u} [CommRing A]`,
  `𝒜 : ℕ → AddSubgroup A`, `[GradedRing 𝒜]`. Additive subgroups encode a general
  ring grading, without an extra coefficient algebra. The universe `u` is explicit.
- `Proj 𝒜`, `basicOpen 𝒜 (a * b)`, `Localization.Away (a * b)` encode P, V, and R.
  These are the dependency constructions, without a copied Proj or twist.
- `d n α β : ℕ`, `hd : 0 < d`, `hn : 0 < n`, and `hα : α = β + d`
  encode precisely the four nonnegative indices and the two positive indices.
- `ha : a ∈ 𝒜 α` and `hb : b ∈ 𝒜 β` encode the homogeneous elements.
  The product h is written literally `a * b` throughout.
- `degreePart 𝒜 (Submonoid.powers (a * b)) j` is R_j. Its existing
  `IsFractionOfDegree` definition uses numerator and denominator degrees i and l in ℕ
  with `(i : ℤ) = l + j`. For a power denominator this is exactly i = j + t(α+β),
  with negative-degree numerators zero. Its separate zero element causes no difference:
  α+β > 0 here, so zero has a power-denominator representative in every degree.
  R_0 as scalar ring is `Away 𝒜 (a * b)`; `degreePart.zeroEquiv` is its existing
  identification with the degree-zero submodule of the ordinary localization.
- The first two `IsUnit` conjuncts assert that a and b become units in R. No
  nonzero or nonzerodivisor hypothesis is added.
- The existential `e` and `v` lie in the degree nd and degree -nd parts.
  Their first two equations identify them with the actual fractions
  `a^(2*n)/(a*b)^n` and `b^(2*n)/(a*b)^n`. Since a and b are units, these are
  exactly `(a/b)^n` and `(b/a)^n`. The equation `e * v = 1` makes v the inverse.
- `E : Away 𝒜 (a*b) ≃ₗ[Away 𝒜 (a*b)] degreePart … nd` is the R_0-linear
  isomorphism. The next equations specify `(E r).val = r.val * e` and
  `(E.symm t).val = t.val * v`. Commutativity gives the node's order e*r as well.
- For every positive-degree homogeneous g with `D_+(g) ≤ V`, the existential ρ
  is the canonical map A_h → A_g: its composition with A → A_h is A → A_g.
  The ordinary localization universal property determines this map uniquely.
  The existential ring map ρ₀ is its degree-zero restriction, also determined by
  its equation on `.val` (which is injective).
- F is the degree-zero-linear chart equivalence given by multiplying by ρ(e),
  with inverse multiplying by ρ(v). The final two equations in this block say
  that the forward maps and their inverses commute with localization. They are
  equations about E and F, not generic ring-map multiplicativity tautologies.
  These formulas also imply compatibility between any two nested subcharts:
  canonical localization maps compose uniquely and carry ρ(e), ρ(v) to the
  corresponding images. Degree preservation for the nd part follows from E
  being surjective and the forward compatibility equation.
- s is a section of the actual upstream `twist 𝒜 (0 + ↑(n*d))` on V. Its equation
  at every homogeneous prime specifies the fraction e, with denominator
  `(a*b)^n`. `pow_mem_primeCompl` is the existing proof that this denominator
  avoids the prime. No arbitrary generating section is assumed.
- Φ is a module-sheaf isomorphism from the restricted structure sheaf to the
  restricted twist on the open subscheme V. Restricting `Scheme.Modules.unit P`
  is canonically the structure sheaf of V (`Scheme.Modules.restrictUnitIso`).
  The equation quantified over every Q of V and every section r specifies Φ
  as scalar multiplication by the restriction of s. `restrictAppIso` identifies
  restricted-sheaf sections with sections on the image open in P, and
  `unitSectionsEquiv.symm` identifies unit-module sections with functions.
  Taking r = 1 says it sends one to e. Because Φ is an isomorphism, its inverse
  is the inverse multiplication map already specified on the chart fractions.
- For every f and `hf : f ∈ 𝒜 (n*d)`, the final existential c lies in the
  degree-zero ring. Its first equation is c = b^(2n)f/h^n. Its second equation
  is c*a^n = b^n*f; since a is a unit, this is exactly c = b^n*f/a^n.
  The third equation says c*e = f/1 in R.
- The final equation quantifies over every open U contained in V. Its left side
  is the canonical homogeneous section `unitToTwist hf` on one, restricted
  from P. Its right side is the restriction of `awayToSection … c` times the
  restriction of s. Thus it states the coefficient expression on V and every
  subopen, including nonaffine subopens. `basicOpenIsoAway` is the existing
  canonical R_0 ≅ Γ(V,O) identification underlying `awayToSection`.

Dependency declarations and imports inspected:

- def-pc-proj: Mathlib `AlgebraicGeometry.Proj` (ProjectiveSpectrum/Scheme),
  `ProjectiveSpectrum.basicOpen` (Topology), and `AlgebraicGeometry.projIsoSpec`
  (Scheme). Also read the audit's source declaration
  `AlgebraicGeometry.Proj.isAffineOpen_basicOpen_and_nonempty_iso` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`.
  The statement uses `Proj` and its scheme open `Proj.basicOpen`.
- def-weil-pbc-proj-twisting-sheaf: the actual `AlgebraicGeometry.Proj.twist`
  in `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`,
  `unitToTwist` in `.Twist.UnitToTwist`, and `twistPowSection` in
  `.Twist.TensorObj`. The first two are used directly. TensorObj also supplies
  `pow_mem_primeCompl` for the displayed value of the frame. Both statement
  imports are public, including the explicit UnitToTwist import required by
  module-mode visibility. Read the `.Twist.Sheaf` definition of locally
  homogeneous-fraction sections and the full homogeneous-localization source.
- The existing `HomogeneousLocalization.degreePart`, `degreePart.zeroEquiv`,
  `degreePart.mulUnitEquiv`, and `IsFractionOfDegree` in
  `WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`
  give the degree-part notion; this delivery uses that notion without redefining it.
- The proof imports are `WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties`
  (`Proj.standardOpenProperties`, proof node lem-weil-pbc-proj-standard-open-inclusion)
  and `Mathlib.Topology.Sheaves.SheafCondition.Sites`
  (`TopCat.Sheaf.restrictHomEquivHom`, `extend_hom_app`, `hom_ext`,
  `isIso_iff_isIso_basis`, proof node lem-weil-pbc-sheaf-morphism-on-basis).
  The source signatures and docstrings of those interfaces were read.

Edge cases checked before writing: zero ring; a = 0 or b = 0; ab nilpotent;
empty Proj and empty V; β = 0 (a degree-d element times a degree-zero element);
d = n = 1; positive but unequal degrees; zero divisors; f = 0; U empty or U = V;
and nonaffine U. In the nilpotent cases the localization is the zero ring and
all assertions hold on the empty chart. No integral domain, generation-in-degree-one,
Noetherian, invertibility-in-A, or affineness-of-U assumption is imposed.
No STATEMENT-DISPUTED issue was found.

Searches for an existing exact statement (2026-10-24):

- msearch.py leanfinder: “Multiplication by (a/b)^n trivializes the twisting sheaf
  O(nd) on D_+(ab) of Proj and gives coefficient b^n f/a^n”. Eight hits,
  including `sectionInBasicOpen`, `awayToSection`, `awayToSection_apply`,
  and `awayMap_awayToSection`; none states the full frame theorem.
- msearch.py loogle: `"Proj", "twist"`; zero hits.
- msearch.py grep: `degreePart|trivializ|twist` in
  `AlgebraicGeometry/ProjectiveSpectrum`; zero indexed hits.
- msearch.py leansearch: “The twisting sheaf on Proj is trivial on D_+(ab) by the
  generator (a/b)^n when deg a = deg b + d”; eight hits, structure-sheaf arithmetic,
  basic-open definitions and chart maps, with no exact match.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for homogeneous degree pieces,
  degreeZeroFractions, product-chart frame names, and twist trivializations;
  no full theorem. Read the nearby Twist/Transition, Twist/Modules,
  ProjTwistBasicOpenFractions, ProjTwistFractionRealization,
  ProjCommonDegreeTwistInvertible, and StandardProjTwistTensor modules.
  The common-degree invertibility result is different; it does not supply the
  explicit product-chart frame and coefficients. The basic-open fraction result
  supplies an additive chart embedding, not this frame theorem.
- rg for the item id in `lean/WeilConjectures` found no declaration.
  rg for all three proposed declaration names in Mathlib projective-spectrum
  sources, `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found no collision. The two fraction definitions name only this theorem's
  canonical elements, and do not duplicate a grading, localization, or twist.

Validation: scompile.py compiled the final module in sandbox mode and its actual
library module mode, cleanly (2.4 seconds each). The first probe identified the
needed explicit UnitToTwist import and the unit-section/function identification;
both were repaired with the existing interfaces. No file-local notation or
instances, unbound variables, new axioms, or proved theorem is present.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
