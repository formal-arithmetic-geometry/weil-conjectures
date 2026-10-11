## Worker report

The module `Sheaf.RingTheory.ReducedIdealsZeroIntersection` states
`Ideal.reduced_ideals_zero_intersection`, with its proof exactly `sorry`.
No definitions, additional nodes, or dependency modules are needed. Only the item's
`lean` field changes. No statement correction or disputed statement.

Source checked: Stacks Project, Varieties Remark 09NW,
https://stacks.math.columbia.edu/tag/09NW . The local literature source was absent,
so the remark was opened online. It states precisely the reduced-ring hypothesis,
covering hypothesis, and canonical A-module isomorphism used here.

Hypothesis and clause correspondence:

- A commutative ring A: `{A : Type u} [CommRing A]`, with arbitrary explicit universe `u`.
- Reduced A: `[IsReduced A]`; no Noetherian, domain, or nonzero assumption is imposed.
- Ideals I and J in A: `(I J : Ideal A)`.
- V(I) union V(J) equals Spec A: `hcover` is the union of
  `PrimeSpectrum.zeroLocus (I : Set A)` and `PrimeSpectrum.zeroLocus (J : Set A)`,
  equal to `Set.univ` on `AlgebraicGeometry.Spec (CommRingCat.of A)`.
  The underlying type of that affine scheme is definitionally `PrimeSpectrum A`.
- I intersection J = 0: the first conclusion is `I ⊓ J = ⊥`.
- B = A/J: the codomain ring is `A ⧸ J`, with its canonical A-algebra/module structure.
- IB: `Ideal.map (Ideal.Quotient.mk J) I`, the extension/image ideal in that quotient.
  Since the quotient map is surjective this is its actual image, namely `(I+J)/J`.
- The canonical map I -> IB is an A-module isomorphism: the second conclusion provides
  `e : I ≃ₗ[A] (Ideal.map (Ideal.Quotient.mk J) I)` and requires for every `x : I` that
  `(e x : A ⧸ J) = Ideal.Quotient.mk J (x : A)`. Thus the isomorphism is specifically
  reduction modulo J, rather than an arbitrary isomorphism of abstract modules.
- The notation IB = I/(I intersection J) is the usual canonical quotient description,
  not a literal equality of Lean types. The displayed equation specifies a surjection
  with kernel I intersection J; its being an equivalence together with the first clause
  renders exactly this identification. In particular, no unrelated abstract isomorphism
  or injectivity-only assertion replaces the canonical-map claim.

Dependency declarations read and used:

- `def-weil-affine-spectrum` is a Mathlib leaf; its `mathlib_match` records
  `AlgebraicGeometry.Spec`, `Mathlib.AlgebraicGeometry.Scheme`. Its full signature and
  docstring were read, and it appears explicitly in `hcover`. The supporting
  `Spec.topObj` in `Mathlib.AlgebraicGeometry.Spec` identifies its underlying space
  with `PrimeSpectrum A`; `Spec.map` and `Spec.homEquiv` were also read.
- Mathlib's `PrimeSpectrum.zeroLocus` (Spectrum.Prime.Basic), `Ideal.map` (Ideal.Maps),
  and `Ideal.Quotient.algebra` (Ideal.Quotient.Operations) supply vanishing loci,
  the image ideal, and the A-module structure. Their definitions/docstrings were read.
- Proof dependencies are described step by step in the theorem docstring, but not
  imported as hypotheses: zero-locus intersection identity, the prime-ideal radical
  criterion and reducedness, followed by the quotient map kernel/image argument.

Edge cases checked before writing: the zero ring (empty spectrum and all modules zero),
I = 0 or J = 0, and I = top (the covering forces J = 0 in the reduced ring) are all
included. For a field the covering forces at least one ideal to vanish. In
k[x,y]/(xy), I = (x), J = (y) give the nontrivial two-component example. Without
reducedness, k[epsilon]/(epsilon^2) with I = J = (epsilon) disproves the assertion,
confirming the need for the reduced hypothesis. No characteristic or finiteness restriction.

Searches performed with the mandated msearch.py (recorded in searches.jsonl):

- LeanFinder: "In a reduced commutative ring ideals I J whose zero loci cover the prime
  spectrum have zero intersection and I maps isomorphically onto its image in A/J".
  Eight hits: quotient-spectrum correspondence and unrelated primary decomposition
  results; none state the required conjunction and canonical module isomorphism.
- Loogle: `PrimeSpectrum.zeroLocus, Ideal`. Twelve hits include `zeroLocus_eq_univ_iff`,
  `zeroLocus_bot`, and `vanishingIdeal_zeroLocus_eq_radical`; no exact statement.
- LeanSearch: "Ideals I J in a reduced ring with V(I) union V(J) equal to Spec have
  intersection zero". Service unavailable, HTTP Internal Server Error; no verdict inferred.
- Mathlib grep: `zeroLocus.*univ|inf.*eq_bot|quotient.*[Bb]ijective` in RingTheory.
  Supporting zero-locus lemmas and unrelated intersection/quotient results; no exact match.
- Source project and Sheaf grep with the same broad pattern; blueprint-id search in
  WeilConjectures; name search for `reduced_ideals_zero_intersection` and
  `inf_eq_bot_of_zeroLocus` in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`. No existing declaration of this statement or name.
  The Sheaf conductor theorem only cites this lemma in its proof docstring and concerns
  sheaves on a scheme rather than the present affine ring statement.

Validation: server scompile.py succeeded cleanly in 1.6 seconds, with no errors or warnings.

## Second reading by C1

Independent second reading: opened the sandbox node and Lean module, the dependency
node `def-weil-affine-spectrum`, and Mathlib declarations supplying all objects below.
The local Stacks .tex is absent on this machine. Read the actual `varieties.tex`
from https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex,
at `remark-conductor`, and checked the tag mapping against
https://stacks.math.columbia.edu/tag/09NW (Remark 33.38.9).
The remark introduces its own reduced ring and two ideals; it does not assume
Noetherianity or dimension one despite its section title. Its additional conclusion
for projective modules is outside this node, so is correctly absent here.

Object, hypothesis and conclusion checklist, in node order:

1. Reduced commutative ring A: `{A : Type u} [CommRing A] [IsReduced A]`.
   PASS. Read `IsReduced` in Algebra/GroupWithZero/Basic.lean:191: every nilpotent
   element is zero. No domain, field, nontriviality or finiteness assumption.
2. Two ideals of that same A: `(I J : Ideal A)`. PASS; no hidden extra binders.
3. Affine spectrum of A: `AlgebraicGeometry.Spec (CommRingCat.of A)` in `hcover`.
   PASS. The dependency is a Mathlib leaf recording `AlgebraicGeometry.Spec`;
   read Scheme.lean:470 and Spec.lean:58. The scheme's underlying space is
   definitionally `PrimeSpectrum A`, not a spectrum over another ring or field.
4. Covering hypothesis V(I) union V(J) = Spec(A): `hcover`, using
   `PrimeSpectrum.zeroLocus (I : Set A) ∪ PrimeSpectrum.zeroLocus (J : Set A)`
   equal to `Set.univ` of this spectrum. PASS. Read zeroLocus at
   Spectrum/Prime/Basic.lean:137: it consists of primes containing the given set.
5. Intersection is zero: `I ⊓ J = ⊥`, the first conjunct. PASS: ideal meet is
   intersection and bottom is the zero ideal.
6. B = A/J: `A ⧸ J`, used in the target ideal and equality. PASS. It is substituted
   directly, with no independently quantified B or assumed algebra structure.
7. IB: `Ideal.map (Ideal.Quotient.mk J) I`. PASS. Read Ideal/Maps.lean:43:
   map is the ideal spanned by the image. The quotient map is surjective
   (Quotient/Defs.lean:124), and `mem_map_iff_of_surjective` (Maps.lean:350)
   confirms that here this is exactly the image ideal, (I+J)/J.
8. Canonical map is an A-module isomorphism: `∃ e : I ≃ₗ[A] ...` followed by
   `∀ x : I, (e x : A ⧸ J) = Ideal.Quotient.mk J (x : A)`. PASS. A linear
   equivalence includes surjectivity and injectivity; the equation fixes the
   canonical reduction map on every element. Read Quotient.algebra and
   Quotient.algebraMap_eq (Operations.lean:354,390): A acts by reduction modulo J.
   The image ideal uses restriction of those scalars. No arbitrary choice of
   A-module structure is a new hypothesis. Quantification over e follows A,I,J
   and the covering hypothesis, just as existence of the canonical isomorphism.
9. Quotient description IB = I/(I intersection J): PASS. This identifies the
   image with the quotient by the canonical map's kernel, not literal equality
   of types. Its kernel is I intersection J; the equation in item 8 fixes that
   map, and item 5 says its kernel vanishes. The statement therefore includes
   precisely this canonical identification without adding a separate object.

Edge cases: the zero ring is allowed, so an empty affine spectrum is covered and
both ideal modules are zero. I=0, J=0, I=top, J=top and I=J are covered; with
I=J the hypothesis forces that ideal to vanish. Over a field at least one ideal
is zero. The reduced ring k[x,y]/(xy) with ideals (x),(y) is a non-domain example
covered by the signature. The dual numbers with I=J=(epsilon) show reducedness
cannot be dropped. No characteristic restriction; `universe u` is explicitly
bound and arbitrary, including u=0. There is no indexed family or integer n,
so empty index sets and n=0 add no missing cases.

Independent searches (queries differ from the worker's; msearch logged them):

- LeanFinder: "Canonical linear equivalence from an ideal to its image modulo
  another ideal when their meet is bottom". Eight hits: power-ideal quotients,
  regular sequences and other special cases; no exact statement.
- Loogle: `Ideal.map, LinearEquiv`. Ten hits, including
  `Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow` and tensor/cotangent results.
  Their displayed signatures impose different hypotheses or concern different
  modules; none states this node.
- LeanSearch: "The quotient map modulo J restricts to a module isomorphism on I
  if I and J intersect trivially". Unavailable (Internal Server Error); no
  mathematical verdict inferred from the failure.
- msearch grep: `zeroLocus_inf|zeroLocus_eq_univ_iff|map.*inf.*bot`.
  Also direct rg over Mathlib RingTheory/Ideal and Spectrum/Prime with
  `zeroLocus.*(sup|inf|univ)|map.*(equiv|Equiv)|quotient.*(equiv|Equiv)`.
  Results give ingredients and other quotient equivalences, not the conjunction
  with this canonical map. Read the relevant map and spectrum definitions.
- Direct rg over WeilConjectures, repository lean/Sheaf and
  dag/lean_names_upstream.json with
  `cover.*spectrum|ideals.*intersection|reduced_ideals_zero_intersection|inf_eq_bot_of`.
  The conductor modules cite this node in proof docstrings and concern scheme
  sheaves; neither duplicates this ring statement. No existing declaration or
  declaration-name collision found.

No mismatch found. No Lean or node changes needed; appended only this independent
review. No new definition nodes, dependency modules or statement correction to
review. Both imports supply objects actually used. Module/declaration docstrings
carry the source and blueprint id; the declaration docstring follows each of the
node's three proof steps and names its two proof dependencies. There are no
new definitions, no hollow data and no proved theorem: the only proof is `sorry`.
The node's `lean.statement` is verbatim the signature before `:=`; all variables
and universes are explicitly bound. Single-file compilation and delivery preflight
are checked with the mandated launcher scripts before pushing.
