## Worker report

The module `Sheaf.RingTheory.NoetherNormalizationOverDomain` states
`Algebra.FiniteType.exists_finite_subalgebra_away`, with `sorry` as the entire proof.
No definitions or additional nodes are needed. The node is unchanged except for `lean`.

Source checked: Stacks Project, Algebra, Tag 07NA,
https://stacks.math.columbia.edu/tag/07NA (lemma-Noether-normalization-over-a-domain),
including the proof. The local literature checkout is absent on this machine, so the
source was read on the official Stacks website. The declaration docstring gives all
seven proof steps of the node and names their dependencies.

Hypotheses and clauses, matched individually:

- Integral domain R: `(R : Type u) [CommRing R] [IsDomain R]`.
- Commutative ring S and its specified map from R: `(S : Type v) [CommRing S]
  [Algebra R S]`. An algebra over commutative rings is precisely a unital ring map.
- The map is injective: `hinj : Function.Injective (algebraMap R S)`.
- It is of finite type: `[Algebra.FiniteType R S]`.
- A nonnegative integer d: `∃ (d : ℕ)`; this includes d = 0.
- Elements y_1,...,y_d of S: `(y : Fin d → S)` (zero-based indexing only changes labels).
- An R-subalgebra S' of S: `(S' : Subalgebra R S)`.
- Clause (1), evaluation is injective:
  `Function.Injective (MvPolynomial.aeval (R := R) y)`.
  `MvPolynomial.aeval` is the unique algebra map sending each variable to `y i`.
- Clause (1), its image lies in S': the witness
  `h : (MvPolynomial.aeval (R := R) y).range ≤ S'`.
  The range is exactly R[y_1,...,y_d]. The other maps in the factorization are
  actual inclusions, rather than arbitrary existential maps.
- Clause (2), finite generation over that image: the algebra structure is induced
  by `(Subalgebra.inclusion h).toRingHom.toAlgebra`, and the assertion is
  `Module.Finite (MvPolynomial.aeval (R := R) y).range S'`.
  This explicitly uses the image ring, not a possibly unrelated module action.
- Clause (3), a nonzero base element: `∃ f : R, f ≠ 0 ∧ ...`.
- The notation T_f is Mathlib's `Localization.Away (algebraMap R T f)`, namely
  localization at powers of the image of f. Its fraction relation is exactly the
  eventual equality after multiplication by a further power in the node.
- Clause (3), the specified fraction map is bijective: `Function.Bijective`
  of `IsLocalization.Away.map` for the inclusion `S'.val.toRingHom`.
  Its source is `Localization.Away (algebraMap R S' f)` and its target is
  `Localization.Away (S'.val (algebraMap R S' f))`.
  The target element equals `algebraMap R S f`, since `S'.val` is an R-algebra
  homomorphism. Writing the element this way lets the standard localization-map
  instance synthesize directly. This is S_f, and the map sends s/f^n to s/f^n.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: `Algebra.FiniteType`,
  `Mathlib.RingTheory.FiniteType` (class and docstring read).
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and `MvPolynomial.algHom_ext`,
  `Mathlib.Algebra.MvPolynomial.Basic`; `MvPolynomial.aeval` and `aeval_X`,
  `Mathlib.Algebra.MvPolynomial.Eval` (full signatures and docstrings read).
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs` (class and docstring read), imported
  transitively by `Mathlib.RingTheory.FiniteType`.
- Additional Mathlib infrastructure: `Subalgebra.inclusion` and `AlgHom.range`,
  `Mathlib.Algebra.Algebra.Subalgebra.Basic`; `IsLocalization.Away.map`,
  `Mathlib.RingTheory.Localization.Away.Basic`, and `Localization.Away`, the
  localization at the powers submonoid. No private copies are introduced.

Edge cases checked before writing:

- d = 0 and an empty family of algebra generators are allowed. For S = R,
  S' = R and f = 1 give the expected case.
- R is not assumed Noetherian, and S is not assumed a domain or reduced.
  Thus finite type examples with zero divisors and nilpotents are covered.
- The zero ring S cannot satisfy injectivity from a domain R; no extra
  nontriviality hypothesis on S was introduced.
- f = 1 is allowed; only f = 0 is excluded. Injectivity of R → S also makes
  the chosen f nonzero in S and S'.
- R and S have independent explicit universes u and v; the finite variable
  family and subalgebras impose no size restriction on either ring.

Searches made (2026-10-11):

- `msearch.py ... leansearch "Noether normalization over an integral domain"`:
  service unavailable (Internal Server Error); no mathematical verdict inferred.
- `msearch.py ... leanfinder "Noether normalization over a domain finite type
  injective algebra finite polynomial subalgebra after inverting nonzero element"`:
  eight results. The main hits are `exists_integral_inj_algHom_of_fg` and
  `exists_finite_inj_algHom_of_fg` (field base only); remaining hits concern
  finite generation, integral closure, quasi-finiteness, or essential finite type.
  None states the finite intermediate subalgebra assertion.
- `msearch.py ... loogle "Algebra.FiniteType, MvPolynomial, Module.Finite"`:
  no hits.
- `msearch.py ... grep 'noether.normalization|Noether.normalization' RingTheory`:
  only Mathlib/RingTheory/NoetherNormalization.lean. The field-case theorem's
  signature was read; it does not cover a domain base.
- `rg` for Noether normalization / normalization over domains in Mathlib,
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and project `lean/Sheaf`:
  found upstream `Algebra.FiniteType.exists_finite_aeval_away` in
  WeilConjectures/Mathlib/RingTheory/NoetherNormalization.lean. Its full docstring
  and signature were read: it states finiteness of localized evaluation and
  conditional injectivity, without an intermediate S' finite BEFORE localization.
  It is related but does not state this node. Other hits are dimension versions,
  geometric versions, and references in docstrings, not this statement.
- `grep -rn 'lem-weil-pbc-noether-normalization-over-domain'` in upstream
  WeilConjectures: no hits.
- `rg 'exists_finite_subalgebra_away'` in Mathlib, upstream WeilConjectures,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration.

Validation: server single-file compilation succeeded with no errors or warnings.
The initial localization target written as `algebraMap R S f` did not synthesize
its instance; spelling out the same element via the inclusion fixed elaboration.
No statement faults, corrections, or disputed clauses were found.


## Second reading by C1

I independently opened the delivered node and module, all three statement dependency
nodes and their recorded Mathlib declarations, the upstream normalization module, and
the related project module `FiniteSubalgebraFractionField.lean`.

Source: the local Stacks checkout is absent. I read the official
[Tag 07NA](https://stacks.math.columbia.edu/tag/07NA) and fetched the raw
`algebra.tex` from `https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex`,
reading `lemma-Noether-normalization-over-a-domain`, its entire proof, and the
chapter's Conventions section. Rings are commutative with identity, including the zero
ring. No standing Noetherian or characteristic assumption applies. The source's
factorization and finite intermediate algebra agree with the node. No statement correction
is present or required; there are no new definition nodes or dependency modules to review.

Object/hypothesis/conclusion list, matched to the Lean (H3):

1. Domain R: `(R : Type u) [CommRing R] [IsDomain R]`. Exact; excludes the zero
   base ring as the source does.
2. Commutative ring S and specified unital ring map from R:
   `(S : Type v) [CommRing S] [Algebra R S]`, with map `algebraMap R S`.
   Exact: any commutative-ring map supplies this algebra structure, and the
   statement uses that structure consistently.
3. Injectivity of that map: `(hinj : Function.Injective (algebraMap R S))`.
   Exact; no injectivity or domain hypothesis is imposed on any unrelated map or ring.
4. Finite type: `[Algebra.FiniteType R S]`. Exact: its `out` is finite generation
   of the top subalgebra, matching def-weil-pbc-finite-type-algebra.
5. Nonnegative integer d: `∃ (d : ℕ)`. Exact.
6. Elements y_1,...,y_d in S: `(y : Fin d → S)`. Exact; the change to zero-based
   labels has no mathematical effect.
7. R-subalgebra S' contained in S: `(S' : Subalgebra R S)`. Exact, with its actual
   inclusion `S'.val`; contains the image of R by the definition of a subalgebra.
8. Polynomial ring and evaluation in clause (1):
   `MvPolynomial.aeval (R := R) y`, with domain `MvPolynomial (Fin d) R`.
   Exact: `MvPolynomial` is the monoid algebra of finitely supported exponent vectors,
   and `aeval` evaluates coefficients through `algebraMap R S`, with `aeval_X` sending
   each variable to `y i`. I read `algHom_ext` for uniqueness too. These are the
   declarations of def-weil-pbc-mv-polynomial-ring, not private substitutes.
9. Injectivity in clause (1): `Function.Injective (MvPolynomial.aeval (R := R) y)`.
   Exact; this imposes polynomial independence over R, rather than only after localization.
10. Image containment in clause (1):
    `∃ h : (MvPolynomial.aeval (R := R) y).range ≤ S'`.
    Exact: `AlgHom.range` consists of actual evaluation images. This gives the
    required factorization by inclusions. The base inclusion is injective by `hinj`.
11. Finite module in clause (2):
    `letI := (Subalgebra.inclusion h).toRingHom.toAlgebra` followed by
    `Module.Finite (MvPolynomial.aeval (R := R) y).range S'`.
    Exact: `Subalgebra.inclusion` is the subtype inclusion, and the induced module
    action is multiplication by its image. `Module.Finite.fg_top` is finite generation,
    precisely def-weil-finitely-generated-module; no arbitrary scalar action is quantified.
12. Nonzero base element in clause (3): `∃ f : R, f ≠ 0 ∧ ...`. Exact.
13. Rings T_f: `Localization.Away (algebraMap R S' f)` and
    `Localization.Away (S'.val (algebraMap R S' f))`. Exact: localization at powers.
    I checked `Localization.mk_eq_mk_iff` and `Localization.r_iff_exists`: equality
    of fractions allows a further power annihilating the cross-product difference,
    including rings with zero divisors. The latter target element is the image of f
    in S because `S'.val` is an R-algebra homomorphism.
14. Bijectivity of the specified map in clause (3): `Function.Bijective` of
    `IsLocalization.Away.map` applied to `S'.val.toRingHom` and the image of f in S'.
    Exact: I read its definition as `IsLocalization.map`, which localizes that
    inclusion, so the map is the required fraction map, not an arbitrary isomorphism.

Quantifiers agree: R,S and the hypotheses precede d,y,S', the containment witness,
module finiteness, and f. The containment witness is a proof, not additional mathematical
structure. The intermediate algebra is finite before inverting f.

Edge cases: d=0 is allowed by `Fin 0`; no generators is allowed by finite type.
For S=R the expected witnesses are d=0, the top subalgebra, and f=1.
The zero S cannot meet injectivity from nontrivial R, so no source case is lost.
Nilpotents, base torsion and zero divisors in S are allowed: neither `IsDomain S`
nor regularity of f in S is assumed. All characteristics and non-Noetherian domains
are included. The explicit independent universes u,v restrict neither R nor S.
Empty schemes/zero objects are not objects of this ring statement.

Independent searches (different queries from the first reader):

- LeanFinder via msearch: `finite intermediate subalgebra polynomial algebra over domain
  isomorphic after localization` returned eight essential-finite-type and local finite-type
  results; none supplies polynomial independence and this finite intermediate algebra.
- Loogle via msearch: `Subalgebra, Module.Finite, Localization.Away` returned zero hits.
- LeanSearch via msearch: `finite subalgebra over polynomial ring inside finite type algebra
  over integral domain localization isomorphism` was unavailable (Internal Server Error);
  this is recorded as unavailable, with no mathematical verdict inferred.
- `rg` independently searched Mathlib's normalization module, all upstream
  `WeilConjectures`, and project `lean/Sheaf` for `finite_subalgebra`,
  `finite.*aeval.*away`, `normalization.*domain`, and `normalisation`.
  I read `exists_finite_inj_algHom_of_fg`: field base, so not this theorem.
  I read the full upstream `Algebra.FiniteType.exists_finite_aeval_away` signature:
  finite evaluation after localization, with no finite intermediate S' before localization.
  The project's `MvPolynomial.exists_finite_subalgebra_fraction_field` concerns a finite
  field extension of a power-series/polynomial fraction field in positive characteristic;
  its objects and conclusion differ. No existing declaration exactly states this node.

H5/H6/H8/H9: no definitions or instances are created; the sole theorem has only
`sorry` as proof. The module and declaration docstrings name Tag 07NA and the blueprint
id. The seven numbered proof paragraphs follow all seven node steps, including the
variable rescaling, clearing annihilators in S, monic equations for fx_i, and the
fraction-level injectivity and surjectivity argument. The three imports provide the
three pieces of infrastructure used. No line exceeds 100 characters. All variables
and universes are bound explicitly; namespace and file location follow conventions.
The node's `lean.statement` is verbatim equal to the file's theorem signature.

Mismatches found: none. Changes: appended this independent second-reading report;
left the correct Lean module and node unchanged. Server single-file compilation via
`scompile.py C1 lem-weil-pbc-noether-normalization-over-domain` succeeded with exit 0
in 1.5 seconds, without errors or warnings.
