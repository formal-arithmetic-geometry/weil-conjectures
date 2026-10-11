## Worker report

The module `Sheaf.AlgebraicGeometry.SpecFieldPointResidueField` states all three
clauses of `lem-weil-pbc-spec-field-point-residue-field`, including the final
fraction-field specialization, in four named theorems. Every proof is `by sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.
The node copy changes only `lean`.

Hypothesis and conclusion correspondence:

* Clause (1): `(R : CommRingCat.{u})` is an arbitrary commutative ring, including
  the zero ring. `(p : PrimeSpectrum R)` is a prime ideal and includes the prime
  instance for `p.asIdeal`. The first conjunct identifies the scheme residue
  field with `IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)`, literally
  the residue field of the local ring R_p. `Ideal.ResidueField` is Mathlib's
  abbreviation for that same object, not a new definition. The second conjunct
  identifies the ring map with global sections, then germ, then residue, using
  `Scheme.ΓSpecIso` and the canonical `Scheme.Spec.residueFieldIso`.
  `algebraMap R p.asIdeal.ResidueField` is the composite through R_p by the
  scalar-tower instances. The third conjunct is `RingHom.ker ... = p.asIdeal`.
  The last conjunct is `IsFractionRing (R ⧸ p.asIdeal) p.asIdeal.ResidueField`.
  Its quotient algebra structure is Mathlib's canonical quotient-induced map;
  the quotient is a domain since the ideal is prime.
* Clause (2): `X : Scheme.{u}`, `U : X.Opens`, `hU : IsAffineOpen U`, `x : X`,
  and `hx : x ∈ U` render precisely the scheme, affine open, and contained point.
  R is taken to be the actual section ring `Γ(X, U)`, as in the node's
  `O_X(U)=R`; this binds no extra ring or arbitrarily chosen identification.
  The existential `p` and `hp : hU.fromSpec p = x` identify the corresponding
  prime under the canonical affine chart. `e` is the identification between
  κ(x) and κ(p). Its hom is explicitly the point-equality transport, the chart's
  residue-field map, and the affine residue-field isomorphism, in that order.
  Thus it is the canonical identification, rather than an arbitrary field
  isomorphism. The final equality factors `X.fromSpecResidueField x` as Spec of
  the canonical ring map `Γ(X,U) → κ(p)` followed by `e.inv`, then the affine-open
  inclusion `hU.fromSpec`. This states both the factorization and its ring-map
  description, not merely existence of a morphism with unspecified ring map.
* Clause (3): `R : Type u`, `[CommRing R]`, `K : Type u`, `[Field K]`, and
  `ψ : R →+* K` render the ring, field, and ring map. The induced morphism is
  written explicitly as `Spec.map (CommRingCat.ofHom ψ)`. Mathlib's
  `IsLocalRing.closedPoint K` is the unique point of Spec K (zero prime).
  The existential `q` and `hq` give the image point, and
  `q.asIdeal = RingHom.ker ψ` identifies it as the kernel. The morphism `l`
  is from κ(q) to K. Its equality uses `Scheme.Spec.residueFieldIso.inv`,
  transport along `hq`, and `Scheme.descResidueField (Scheme.stalkClosedPointTo s)`.
  The last map is exactly the field-map component of `Scheme.SpecToEquivOfField`,
  induced from s's local stalk map with the canonical identification of the
  residue field at the unique point of Spec K with K. It therefore specifies the
  induced map, not just some extension. `l.hom.comp (algebraMap R κ(q)) = ψ`
  says it extends ψ, equivalently the induced injection R/q → K; factoring
  through the surjective quotient map gives the equivalence. Clause (1) identifies
  κ(q) with the fraction field of R/q. The universal `l'` clause says this
  extension is unique among all ring maps κ(q) → K.
* Final specialization: `[IsDomain R]`, `[Algebra R K]`, and `[IsFractionRing R K]`
  mean R is a domain and K is a fraction field via the specified map, now written
  as `algebraMap R K`. Any ψ making K a fraction field supplies precisely this
  algebra structure (`ψ.toAlgebra`); conversely the algebra map is that ψ.
  Its injectivity follows from `IsFractionRing`, so the injective-map condition
  in the node is included, with no lost case. The conclusions explicitly give
  zero image ideal, `IsGenericPoint ... Set.univ`, and `IsIso` of the induced
  residue-field map into K. Through clause (1) this is κ((0)) → K.

Dependency declarations read and used:

* `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
* `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`.
* `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and its morphism category.

Also read the definitions/signatures/docstrings of `IsAffineOpen`,
`IsAffineOpen.fromSpec`, `Scheme.fromSpecResidueField`, `Scheme.residueFieldCongr`,
`Scheme.Spec.residueFieldIso`, `Scheme.descResidueField`, and `Scheme.SpecToEquivOfField`.
`Mathlib.RingTheory.LocalRing.ResidueField.Ideal` supplies `Ideal.ResidueField`, its
canonical quotient algebra, kernel formula, and fraction-field instance.

Edge cases checked mathematically before the final statement: the zero ring has
no prime points and admits no unital map to a nonzero field; thus clauses (1) and
(3) introduce no invalid point. Empty X or empty U cannot furnish x with hx, and
clause (2) is correctly vacuous. No reduced, integral, Noetherian, finite-type, or
separated hypothesis is imposed in the first three clauses. R a field, nonmaximal
primes, noninjective ψ, and characteristic p all have their expected residue-field
interpretation. The domain condition appears only in the fraction-field
specialization. All universes and variables are explicitly bound; no file-local
notation, instance, or private object is used.

Searches made (2026-10-11):

* `msearch.py ... leansearch "residue field of Spec at prime kernel field map fraction
  field and affine open canonical point factorization"`: unavailable, Internal
  Server Error (no mathematical verdict inferred).
* `msearch.py ... leanfinder "A morphism Spec K to Spec R maps its unique point to
  the kernel and induces the unique extension from the residue field"`: eight
  hits, including `Scheme.SpecToEquivOfField`, `Scheme.SpecMap_residue_apply`,
  and `Scheme.Spec_map_residue_apply`; pieces of the statement, no complete match.
* `msearch.py ... loogle "AlgebraicGeometry.Scheme.SpecToEquivOfField,
  Ideal.ResidueField.ringHom_ext"`: compound query did not establish a full match.
  Retried `loogle "AlgebraicGeometry.Scheme.SpecToEquivOfField"`: five hits,
  the equivalence and its projections; read their definitions and types. These
  provide the general point/field-map correspondence, not this node's explicit
  kernel, affine-open, fraction-field, and uniqueness assertions together.
* `msearch.py ... grep "residueFieldIso|ker_algebraMap_residueField|IsFractionRing"
  AlgebraicGeometry/ResidueField.lean`: five hits on the affine residue-field iso
  and its compatibility lemmas; read them. Direct source reads in
  `RingTheory/LocalRing/ResidueField/Ideal.lean` found the quotient fraction-field
  instance and kernel lemma. These establish subclauses only.
* `rg -n "spec_field_point_residue_field|SpecToEquivOfField|residueFieldIso|
  fromSpecResidueField"` in `WeilConjectures/` and `lean/Sheaf`: usages of the
  Mathlib constructions and unrelated tangent, fibre, and limit statements;
  no existing theorem with this complete statement.
* `grep -rn "lem-weil-pbc-spec-field-point-residue-field"` in `WeilConjectures/`:
  no upstream declaration tagged with the node.
* `tools/lean_names_upstream.py show lem-weil-pbc-spec-field-point-residue-field`
  plus name grep in `dag/lean_names_upstream.json`, Mathlib, upstream, and
  `lean/Sheaf`: no matching or conflicting declaration for the four chosen names.

The cited Stacks source was read from the local fetched copy
`/home/ubuntu/c1-stacks-review/{algebra,schemes}.tex`: Algebra lines 3330–3365
and Schemes lines 2400–2498. It agrees with the node; no statement fault or
STATEMENT-DISPUTED condition was found. Each theorem docstring carries the source
and the appropriate steps of the node's proof with its prerequisite node ids.

Validation: the four-theorem module compiled cleanly on the server in 1.8 seconds;
all proofs remain sorry. The final delivery dry run is run after writing the record.

## Second reading by K1

I independently opened the delivered node, all four theorem signatures, all three
statement-dependency nodes and their recorded Mathlib declarations. I read the
source discussion in `/home/ubuntu/c1-stacks-review/schemes.tex`, lines 2400–2498,
and `algebra.tex`, lines 3310–3370 (the fetched local Stacks copies). The former
introduces an arbitrary scheme and morphisms from arbitrary fields, with no
Noetherian, separated, or finiteness assumption. The latter defines the prime
residue field using localization and identifies it with the fraction field of
the prime quotient. These sources support the node as written. There is no
statement correction, no new definition node, and no dependency module to review.

Object/hypothesis/conclusion checklist, in the node's order:

1. Arbitrary commutative ring R and its spectrum: `R : CommRingCat.{u}` and
   `Spec R` in `spec_field_point_residue_field`. Verdict: exact. The ring is
   allowed to have zero equal to one.
2. Arbitrary prime p: `p : PrimeSpectrum R`; its ideal is `p.asIdeal`, with
   primality supplied by the bundled point. Verdict: exact; not restricted to
   maximal primes.
3. Scheme residue field equals the residue field of R_p: the `Nonempty` ring
   isomorphism to `CommRingCat.of (IsLocalRing.ResidueField
   (Localization.AtPrime p.asIdeal))`. The following compatibility equality
   uses the canonical `Scheme.Spec.residueFieldIso`. Verdict: exact. I opened
   this definition: it is induced by `Spec.stalkIso`, not an unrelated iso.
4. Canonical composite R → R_p → κ(p): `algebraMap R p.asIdeal.ResidueField`,
   with the equality to ΓSpec identification, germ, and scheme residue map.
   `Ideal.ResidueField` is literally the localization residue field; the
   scalar-tower algebra map is the asserted composite. Verdict: exact.
5. Kernel p and fraction field of R/p: `RingHom.ker ... = p.asIdeal` and
   `IsFractionRing (R ⧸ p.asIdeal) p.asIdeal.ResidueField`. I read the canonical
   quotient-algebra instance and its compatibility with the quotient map in
   `ResidueField/Ideal.lean`. Verdict: exact; no arbitrary algebra structure.
6. Scheme X, affine open U, and x in U: `X : Scheme.{u}`, `U : X.Opens`,
   `hU : IsAffineOpen U`, `x : X`, `hx : x ∈ U` in the affine-open theorem.
   R is exactly `Γ(X, U)`; writing the actual section ring implements the
   node's O_X(U)=R without introducing an extra identification. Verdict: exact.
7. Corresponding prime p and identification κ(x)=κ(p): existential `p`,
   `hp : hU.fromSpec p = x`, and `e` with its hom prescribed by inverse
   point-equality transport, `hU.fromSpec.residueFieldMap p`, and the affine
   residue iso. I opened `IsAffineOpen.fromSpec`: it is the canonical affine
   chart inverse followed by U's inclusion, an open immersion. Its image is U
   and it is injective, so this existential chooses exactly the corresponding
   prime. Verdict: exact, with the required canonical field identification.
8. Factorization of the canonical point map through U, with the specified ring
   map: the equality for `X.fromSpecResidueField x` to `Spec.map` of the canonical
   algebra map followed by `e.inv`, then `hU.fromSpec`. Verdict: exact; the
   directions follow contravariance, and the factor is explicitly specified.
9. Field K and arbitrary ring map ψ: `R : Type u`, `[CommRing R]`,
   `K : Type u`, `[Field K]`, `ψ : R →+* K` in the map theorem. The induced
   s is written as `Spec.map (CommRingCat.ofHom ψ)`. Verdict: exact; ψ need
   not be injective.
10. Unique field-spectrum point and image kernel: `IsLocalRing.closedPoint K`,
    `hq : Spec.map ... (IsLocalRing.closedPoint K) = q`, and
    `q.asIdeal = RingHom.ker ψ`. Verdict: exact; closedPoint of a field is zero.
11. Induced residue-field map into K: `l` is prescribed as the affine residue
    iso inverse, the inverse transport along hq, and `descResidueField` of
    `stalkClosedPointTo s`. I opened both definitions: stalkClosedPointTo is s's
    local stalk map followed by the canonical stalk-of-Spec-K identification;
    descResidueField is the induced map out of its residue quotient. Verdict:
    exact; this specifies the induced map rather than an arbitrary extension.
12. Extension of R/q → K and uniqueness: `l.hom.comp (algebraMap R ...) = ψ`
    and the universal equality for every `l'` with that composite. Since R → R/q
    is surjective and the quotient algebra map is canonical, this is equivalent
    to extending the induced injection from R/q. Clause (1) supplies the
    fraction-field identification. Verdict: exact, with quantifiers in order.
13. Domain, injective ψ, and fraction field via ψ: `[IsDomain R]`, `[Algebra R K]`,
    `[IsFractionRing R K]` in the generic theorem. The specified ψ is its
    `algebraMap R K`. Conversely any ψ from the node gives this algebra
    via ψ.toAlgebra, and injectivity follows from the fraction-field structure.
    Verdict: equivalent hypotheses, no missing arbitrary-map case.
14. Generic point zero and residue-field isomorphism: the image ideal equals
    `⊥`, `IsGenericPoint ... Set.univ`, and `IsIso (descResidueField
    (stalkClosedPointTo ...))`. This is the same induced field map as in (11),
    expressed on the scheme residue field; the affine iso transports it to
    κ((0)). Verdict: exact.

Edge cases: the zero ring has no prime, and no unital map to a field, so the
corresponding binders are correctly vacuous. Empty X or U cannot provide hx.
Field R, nonmaximal p, and noninjective ψ are included; no characteristic is
excluded. No index set or integer parameter occurs. All universes are explicit:
the arbitrary common universe u can contain R and K of any two given sizes,
and the scheme/section/residue carriers have the appropriate same universe.
There is no quantification over potentially too-small test objects. No hidden
Noetherian, reducedness, separatedness, finite-type, or finite-degree instance
occurs. Only the last theorem assumes a domain.

Independent searches (2026-10-11), using different queries from the writer:

* LeanFinder via msearch: "Affine chart evaluation to the residue field describes
  the canonical morphism from a point spectrum". Eight hits, including
  `fromSpecResidueField_apply`, `descResidueField`, and `SpecToEquivOfField`.
  I read their definitions and signatures; they are partial ingredients.
* Loogle via msearch: `Ideal.ResidueField`. Twelve hits, including its definition,
  canonical quotient algebra, fraction-ring instance, map, and field equivalence.
  I opened `ResidueField/Ideal.lean`, including `ker_algebraMap_residueField`,
  `algebraMap_quotient_residueField_mk`, and `ResidueField.ringHom_ext`. These
  provide individual algebraic clauses, not all four theorem statements.
* LeanSearch via msearch: "For a homomorphism from a commutative ring to a field
  the image prime is the kernel and the induced residue extension is unique".
  Service unavailable (Internal Server Error), recorded without a verdict.
* Direct rg with `ker.*residue|residue.*ker|generic.*residue|residue.*generic|
  fromSpec.*residue|residue.*fromSpec|spec_field_point_residue_field` across
  upstream WeilConjectures, repository lean/Sheaf, and dag/lean_names_upstream.json;
  and kernel/quotient/fraction-field/ext searches in pinned Mathlib. No full
  matching statement or conflicting name was found. I also opened the nearby
  `EtaleResidueTriples` and `WeilPbcNormalizationInResidueFieldExtension` modules:
  neither states this result. Upstream `exists_comp_ι_eq_fromSpecResidueField`
  asserts open factorization alone, without this node's canonical affine ring
  map, kernel, or unique fraction-field extension. The existing Mathlib
  `Spec.algebraMap_residueFieldIso_inv` is only one conjunct of clause (1).

H4 verdict: all notions use the existing recorded Mathlib objects; no private
copy or missing notion. H5/H6: no definitions, and exactly four sorry proofs.
H8/H9: module and declaration source/blueprint docstrings are present; the four
proof descriptions together carry the node's five proof steps, including the
canonical-map compositions and the final injectivity/surjectivity argument.
Names, topic, bound variables, imports, and line widths are acceptable.

Mismatches found: none. Changes: appended this independent review only; the Lean
module and node record are unchanged. The declaration reader confirms the node's
`lean.statement` is verbatim the normalized first signature and recognizes all
four recorded declaration names; no line exceeds 100 characters.

Validation: independently ran scompile.py on the delivered module. Server compile
succeeded in 1.8 seconds, exit 0, with no warnings or errors. Delivery dry run and
push follow this report.
