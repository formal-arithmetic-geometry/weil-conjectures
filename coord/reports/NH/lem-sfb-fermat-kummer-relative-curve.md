# NH: lem-sfb-fermat-kummer-relative-curve

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fermat-kummer-relative-curve.json`: item, split into nine proof steps; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-plane-hypersurface-cohomology.json`: new statement-only node, unsplit; not in Mathlib after the logged searches. It computes H0 and the dimension of H1 for an arbitrary nonzero positive-degree plane equation, including nonreduced equations. It is not a Fermat-curve smoothness or genus clause repackaged under another name.
- `citations.json`: every step/dependency pair, with a verbatim quotation from the cited statement.
- `searches.jsonl`: genuine search-command log; retained with the search results summarized in the nodes.

One new node, zero new Mathlib leaves. No Lean written or compiled. No unit or chapter records changed: this auxiliary node is not its unit's key statement.

## Attachments

None. Searching the project for the exact item id, Fermat, and the plane-cohomology/genus concepts found no declaration stating the item or the new node. The only project file matching Fermat is `WeilConjectures/RingTheory/SubsingletonH1CotangentOfCharP.lean`, whose occurrence is the finite-field Fermat identity in a different commutative-algebra argument. It does not construct a Fermat curve. Mathlib's projective Weierstrass constructions concern cubic elliptic curves; polynomial FLT is an assertion about polynomial solutions. Neither states this item.

## Literature

WANTED: de Jong, *Families of curves and alterations* (1997), §3.5, printed p.607, for lem-sfb-fermat-kummer-relative-curve. The local PDF named in the inherited source record is absent. The inherited reference to a publisher-PDF reading belongs to the creator's record, not to NH's checks.

I read `literature/stacks-project/curves.tex`, Section 0BYA (`section-plane-curves`), including its Fermat example, and the whole statement and proof of 0BYD (`lemma-genus-plane-curve`). I also read Algebra 00T7 (`lemma-standard-smooth`) with its determinant definition, and Properties 0358 (`lemma-normal-integral-sections`). The relative coordinate, map, and normalization arguments are written out in the item and marked agent-written; no missing de Jong argument is silently cited as a proof. No SGA source is used.

## What changed and what was wrong

The imported item had no proof. Its statement is consistent: the equation, coordinate x, two radical equations, and genus all agree. No statement dispute or correction is needed. I retained its hypotheses, including primitivity of the root of unity, although this particular geometric construction needs only that ell is invertible (and the numerical lower bound for genus).

I supplied an actual chart proof rather than creating a node for each conclusion. The new node is the independent structure-sheaf cohomology calculation for all plane hypersurfaces. H0 is needed before integrality is known, so a genus lemma assuming an integral curve would not suffice. The proof of 0BYD applies here without presupposing integrality of Z: nonzero F acts injectively on the polynomial ring, giving the exact sheaf sequence used in its proof. The source's equidimensional/no-embedded-point framework is not being used as an extra hypothesis without proof. The exact-sequence calculation itself works for every nonzero homogeneous F of positive degree.

I avoided using `lem-sc-smooth-normal`, which concerns curves over a field, to claim normality of the total space over a possibly singular higher-dimensional base. I also avoided taking a definition of normalization as a theorem that every normal finite cover is that normalization: step 9 proves the two inclusions of coordinate rings.

No previous sandbox split, report, citations, or searches existed when I began; the sandbox held dispatcher marker files only. The item's inherited Mathlib searches remain in it, and the searches performed by this worker are recorded separately in its search fields and in the log.

## Mathlib and blueprint searches

I ran the required leanfinder, loogle, grep and leansearch commands for both subjects. For the new node I also tried the second semantic phrasing about the structure sheaf of a degree-d hypersurface and a broader grep for cohomology/genus in AlgebraicGeometry. I read the returned signatures: they construct Proj/its structure sheaf or concern group, cotangent, etale, or elliptic-curve cohomology; none computes these coherent groups. The broader grep's actual source hits in `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean` define pro-etale ell-adic cohomology, which is a different coefficient sheaf and topology. There is no candidate that specializes in one line.

Whole-DAG searches included titles/statements for plane curves and hypersurfaces, genus, normality of smooth families, normal global sections, monic quotients, standard smoothness and function fields. Blueprint-reference searches for `plane curve`, `plane hypersurface`, `hypersurface`, `genus`, and `0BYD` found no blueprint node stating the new cohomology result. Existing monic-quotient, smooth-family, connectedness, function-field, and normal-sections nodes were reused. The ancestor tool returns `None` for this live-created chain; I retained the item's inherited null ancestor and extended its via chain exactly for the new node rather than inventing an imported ancestor.

## Not duplicates

lem-sfb-plane-hypersurface-cohomology vs lem-sfb-fermat-kummer-relative-curve: the former computes coherent H0 and H1 for every nonzero homogeneous plane equation, including singular and nonreduced ones, over any field; the item constructs a relative finite morphism and proves smoothness, integral fibre geometry and normalization for a specific Fermat equation. The cohomology lemma supplies an input to the proof, not its entire conclusion.

lem-sfb-plane-hypersurface-cohomology vs new-picard-residue-homology-naturality-fixed-positive: the existing node chooses comparisons in a residue-homology naturality problem; its 0BYD reference is a counterexample involving a cubic, not a plane-hypersurface cohomology theorem.

lem-sfb-plane-hypersurface-cohomology vs new-picard-residue-homology-geometric-naturality-fixed-per-index: the existing node chooses per-index comparisons and derived arrows for residue naturality; its 0BYD reference does not assert H0 or H1 for a plane equation.

lem-sfb-plane-hypersurface-cohomology vs new-picard-residue-homology-naturality-fixed: this is another residue-comparison existence assertion, including an empty family, and cites the cubic example only in its source-error discussion. It does not compute plane-hypersurface cohomology.

These are all existing nodes found by the shared 0BYA/0BYD tag search.

## Review by NH

I read the source passages listed above for the item and the one new node, and opened every cited node's actual statement. The following are the checks on the mathematical inferences, not just their dependency fields.

1. The Proj node really identifies standard opens with degree-zero localizations. The affine base-change node really identifies their pullbacks with tensor-product spectra and specifies both projections; tensoring the displayed integer polynomial presentations gives the rings over R. The scheme-morphism gluing node supplies gluing and uniqueness. I checked the ratios u=b/a and v=1/a and both target coordinates, so the overlap identity is y=1/x. There are no base points, since A=C=0 implies B=0 at a homogeneous prime.
2. The monic-quotient node supplies the actual power basis, not just integrality. Applying it twice gives ell-squared basis vectors on each target chart, so those rings are finite modules. The finite-local-on-target node states precisely that affine inverse images and finite ring maps on a cover suffice; I checked that these inverse images are exactly the two source opens.
3. The algebraic-closure node includes both existence of a closure and roots of nonconstant polynomials. Its hypotheses apply to the residue field of every target point. The point with finite coordinate t has the explicitly specified preimage, and infinity has [1:1:0]. This does not assume that target points are rational over the original ground field.
4. The standard-smooth definition requires a unit determinant for the first c variables. Reordering the variables as written makes the determinants ell*s^ell and epsilon*ell*t^ell. Both are units on their respective opens because ell is invertible and the inverted variable has an explicit inverse. The standard-smooth-is-smooth node supplies smoothness. The smooth-morphism node explicitly identifies the affine-local ring-map convention with scheme smoothness. The field dimension node states dimension at every point n-c, and here n=3,c=2. H-projectivity is the literal given closed immersion in the definition, not a claim that every projective morphism has a projective-space embedding under another convention.
5. The new cohomology statement applies before reducedness or integrality has been proved. For every residue-field extension the equation is still nonzero of the same positive degree, and [1:0:1] remains a point. Its H0 assertion and the existing connectedness/idempotents equivalence yield connectedness over every further extension; the field idempotent calculation is written explicitly.
6. The smooth-connected-family core gives integral total space with integrally closed local rings, exactly what the step uses. Its base hypotheses hold for U by assumption, and separately for each field L. Smoothness and geometrically connected fibres were established by the same explicit formulas over every L, so using the core over Spec L is legitimate. The geometric-integrality definition quantifies over all extensions; the argument indeed covers all of them, not just the original residue fields.
7. Genus is defined as the dimension of structure-sheaf H1 for a smooth projective geometrically irreducible curve. Those conditions are already available from steps 4 and 6. The new lemma computes that dimension. The estimate at ell=5 is 6, so the asserted lower bound 2 holds.
8. The affine function-field theorem explicitly covers any integral scheme, not only curves, and says the generic stalk is the fraction field of each nonempty affine open. It applies to U and to the source chart. The monic basis proves the injection of K[x]; hence the use of a rational function variable is justified. Localization at R minus zero does not change the fraction field. The two monic equations and the displayed coordinate generators give exactly K(x)(a,b), without replacing the field by an unspecified component.
9. I also checked the hypothesis that the normalization target is integral: its polynomial coordinate rings are domains, and any two nonempty target opens have nonempty, intersecting inverse images in the integral source. This gives reducedness and irreducibility explicitly and identifies the target function field with K(x) by the affine function-field theorem. The affine-Noetherian node applies to the chosen finite-type affine base charts and their finitely generated hypersurface algebras. The normal-sections node needs a locally Noetherian normal scheme and a quasi-compact open: the spectrum of each chart ring is Noetherian and normal by step 6 and is affine, so these hypotheses hold. It gives a product of normal domains; since the chart ring itself is a nonzero domain, the product has one factor. I checked both integral-closure inclusions: finite implies integral for these explicit monic algebras, and an element integral over the target ring is integral over the larger source ring via the same polynomial, so normality puts it in the source ring. The normalization definition includes affine integral closures and their localization compatibility, which makes the chart identifications glue.

I checked B--E of delivery-errors against these files. The new node is self-contained and statement-only, with actual searches and explicit definition dependencies. No argument is transferred wholesale into a node restating a Fermat conclusion. Every non-elementary invocation is a node citation; every citation quote is verbatim. The elementary parts are the displayed coordinate, determinant, idempotent and integral-equation calculations inside steps that also cite the non-elementary tools. All nine steps are shorter than 2000 characters, and none hides a separate unstated comparison lemma. Off-unit statements are declared as generic tools in split_report.tool_uses for the maintainer's review.

Small-case checks: for the new cohomology node, d=1 and d=2 give H1=0, d=3 gives dimension 1; nonreduced forms such as A^2 are intentionally included, and F=0 and d=0 are excluded. For the item, ell=5 gives genus 6, while characteristic dividing ell would kill the determinant and is explicitly excluded. Characteristic 2 with ell odd causes no issue because both signs are units. I tested x=0, x=1, infinity, and the global nonemptiness point. The argument allows singular normal U and does not require U to be affine globally or smooth over its ground field. The primitive-root hypothesis is preserved without strengthening it.

## Unfinished work

The initial full delivery dry run passed at 6139836bcdd. A subsequent self-check made explicit the integrality and function field of the normalization target, and the final dry run is rerun on that complete version.

No clause of the item's natural-language split remains open. The general cohomology lemma is deliberately a new unsplit node for the next stage-1 worker. There is no Lean-proof completion claim. Validation and delivery are performed with the required server tools.
