## Worker report

The module `Sheaf.RingTheory.EtaleSectionIdempotentSplitting` states
`Algebra.Etale.exists_idempotent_splitting_of_algHom`. The sole proof is `sorry`.
No definitions, auxiliary theorems, new nodes, dependency modules, or statement corrections
are needed.

Hypothesis and clause correspondence:

- Commutative rings R and S and their structure ring map are `{R : Type u} {S : Type v}`,
  `[CommRing R] [CommRing S] [Algebra R S]`. The structure map is `algebraMap R S`.
  The universes are independent and explicitly bound.
- Étaleness of Spec S → Spec R is `[Algebra.Etale R S]`. This is the ring form permitted
  by brief-stage2 §3, ÉTALE RING MAPS. The dependency `def-weil-etale-morphism` records
  `AlgebraicGeometry.Etale` in `Mathlib.AlgebraicGeometry.Morphisms.Etale`; its
  `HasRingHomProperty @Etale RingHom.Etale` instance identifies the scheme property with
  ring étaleness on affines. `RingHom.etale_algebraMap` identifies it with `Algebra.Etale`.
  This uses the existing ring notion, without defining a second étale predicate.
- The R-algebra homomorphism s is `(s : S →ₐ[R] R)`; it automatically satisfies
  `s (algebraMap R S r) = r`, with no extra section assumption.
- The idempotent e is `∃ (e : S) (he : IsIdempotentElem e)`.
- Its image is `s e = 1`.
- The kernel assertion is `RingHom.ker s.toRingHom = Ideal.span {1 - e}`. This principal
  ideal is exactly `(1-e)S`.
- The complementary factor is Mathlib's `he.one_sub.Corner` from
  `Mathlib.RingTheory.Idempotents`, namely the elements `(1-e)*x*(1-e)`, with inherited
  ring operations and identity `1-e`. Since S is commutative and e is idempotent, this
  set equals `(1-e)S`, including the zero factor. This is the actual subring without
  ambient identity, rather than an unspecified abstract factor or a quotient substitute.
- Its R-algebra structure is existentially bound and pinned by
  `(algebraMap R he.one_sub.Corner r).1 = (1-e) * algebraMap R S r` for every r.
  This is precisely the natural algebra structure on the complementary ideal; it
  introduces no independent mathematical hypothesis.
- The product algebra isomorphism is `∃ Φ : S ≃ₐ[R] R × he.one_sub.Corner`, with
  `(Φ x).1 = s x` for every x: s corresponds to the first projection.
- The localization is `Localization.Away e` from
  `Mathlib.RingTheory.Localization.Away.Basic`. Its inferred R-algebra structure is
  the canonical composite R → S → S[1/e]. The algebra isomorphism is
  `∃ ψ : Localization.Away e ≃ₐ[R] R`, and
  `ψ (algebraMap S (Localization.Away e) x) = s x` for all x says it is induced by s.
  Because s(e)=1, the universal property supplies exactly this induced map.

Read the full signature and docstring of the dependency's scheme declaration and the
ring definition `Algebra.Etale`; read the corner definition and its CommRing instances.
The module imports the ring definitions it actually uses, not the scheme bridge used
only for checking equivalence of formulations. There are no unusable dependency records.

Sources: [Stacks 09XI](https://stacks.math.columbia.edu/tag/09XI), proof of (5) ⇒ (2),
first paragraph, gives the algebra product decomposition determined by the section;
[Stacks 00U8](https://stacks.math.columbia.edu/tag/00U8) supplies the idempotent localization.
The local Stacks TeX is absent on this machine, so these source places were opened online.
The declaration docstring carries all five proof steps and their DAG dependencies.

Edge cases checked before writing: no nonzero or domain hypothesis is used. If s is an
isomorphism, e=1 is permitted and its complementary corner is the zero ring; S[1]=S.
If R is the zero ring, any R-algebra S is the zero ring, and both factors and the
localization are zero rings. The product example S=R×T with s the first projection has
e=(1,0), corner (0,1)S=T and localization R. Arbitrary characteristic is allowed;
no invertibility of 2 is used. Independent universes do not exclude any ring pair.
No statement dispute or node fault was found.

Searches (2026-10-11):

- `msearch.py ... leansearch "An etale algebra with an algebra map to its base ring is
  a product and has an idempotent generating the kernel"`: UNAVAILABLE, HTTP internal
  server error; recorded as unavailable without a verdict.
- `msearch.py ... leanfinder "An algebra homomorphism from an etale R algebra S to R
  splits S as a product and identifies R with the localization at an idempotent"`:
  eight hits, principally StandardEtalePair maps and Algebra.Etale field classification;
  no exact statement.
- `msearch.py ... loogle "IsIdempotentElem, AlgEquiv, Localization.Away"`: zero hits.
- `msearch.py ... grep "toSpanSingleton|prodQuotientOfIsIdempotentElem" RingTheory`:
  quotient product equivalence and principal-ideal ingredients, no exact statement.
- `rg` in Mathlib RingTheory/Idempotents.lean finds `IsIdempotentElem.Corner` and its
  existing CommRing instance. No replacement construction is written.
- `rg` for the item id, `exists_algEquiv_prod_of_algHom`, and `toSpanSingleton` in
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json finds the upstream
  `Algebra.Etale.exists_algEquiv_prod_of_algHom` in
  `WeilConjectures.Mathlib.RingTheory.Etale.Section`. Its full statement and docstring
  were read. It supplies only an abstract complementary étale factor and the first
  projection, without the explicit idempotent, kernel or localization assertions;
  it is not an exact match for this node.
- `rg` for `Corner|corner|etale.*section|section.*etale` in lean/Sheaf finds no exact
  statement or alternative corner definition. `rg` for the proposed full declaration
  name in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json finds
  no collision.

Validation: server single-file compilation and `deliver2.py --no-push`; the dry run
is the last worker step. The independent second reader supplies the second-reading
section and performs the actual delivery.

## Second reading by M1

I independently read the sandbox node, its five proof steps, the full Lean module,
`def-weil-etale-morphism`, and the recorded Mathlib declaration and affine bridge.
The local Stacks checkout is absent. I read the source TeX from the official
stacks/stacks-project repository: `more-algebra.tex`,
`lemma-characterize-henselian-pair`, (5) implies (2), first paragraph, and
`algebra.tex`, `lemma-map-between-etale`,
`lemma-surjective-flat-finitely-presented`, and
`lemma-ideal-is-squared-union-connected`. I also opened the official tag pages
[09XI](https://stacks.math.columbia.edu/tag/09XI),
[00U8](https://stacks.math.columbia.edu/tag/00U8),
[00EH](https://stacks.math.columbia.edu/tag/00EH), and
[0A02](https://stacks.math.columbia.edu/tag/0A02).
09XI takes R = A/I and S = A'/IA' in this paragraph. Its henselian-pair assumptions
are used for lifting the decomposition afterwards, not for the section splitting
here. 00U7 and 00U8 confirm that the splitting argument needs only the arbitrary
commutative base ring, etale algebra, and algebra section used in this node.

My object/hypothesis/conclusion checklist, with the Lean correspondence:

1. R is an arbitrary commutative ring: `{R : Type u} [CommRing R]`. PASS; no field,
   domain, nonzero, Noetherian, or characteristic restriction.
2. S is a commutative ring with a specified ring map R to S:
   `{S : Type v} [CommRing S] [Algebra R S]`, map `algebraMap R S`. PASS; any unital
   commutative-ring map determines precisely such an algebra structure.
3. Spec S to Spec R is etale: `[Algebra.Etale R S]`. PASS. I read the dependency's
   actual scheme predicate `AlgebraicGeometry.Etale`, its
   `HasRingHomProperty @Etale RingHom.Etale` instance, `RingHom.Etale`, and
   `RingHom.etale_algebraMap`. These identify exactly the affine scheme property
   with the algebra predicate used here, as explicitly permitted by the contract.
   `Algebra.Etale` is formally etale plus finite presentation, the standard etale
   ring-map notion; this finite presentation is not an added assumption.
4. A homomorphism of R-algebras s from S to R: `(s : S →ₐ[R] R)`. PASS; R carries
   its identity algebra structure, so the algebra commutation law already says
   s composed with the structure map is the identity. Surjectivity is a consequence,
   not an extra binder.
5. An idempotent e in S: `∃ (e : S) (he : IsIdempotentElem e)`. PASS; the witness
   precedes all assertions and the same e occurs throughout.
6. s(e) = 1: `s e = 1`. PASS.
7. Kernel s = (1-e)S: `RingHom.ker s.toRingHom = Ideal.span {1 - e}`. PASS; the
   singleton span is exactly the principal ideal in the node.
8. The complementary ring is (1-e)S with its natural R-algebra structure:
   `he.one_sub.Corner`, with `∃ (_ : Algebra R he.one_sub.Corner)` constrained by
   `∀ r : R, (algebraMap R he.one_sub.Corner r).1 = (1-e) * algebraMap R S r`.
   PASS. I read `Subsemigroup.corner`, `IsIdempotentElem.Corner`, and all its ring
   instances in Mathlib/RingTheory/Idempotents.lean. Its elements are the actual
   subtype of values (1-e)*x*(1-e). Commutativity and idempotency identify this
   range with (1-e)S: each corner value is (1-e)*x, and each (1-e)*x equals its
   corner expression. Addition and multiplication are inherited, and the identity
   is 1-e. The displayed constraint uniquely fixes the algebra map, so existential
   packaging of this instance adds neither a hypothesis nor arbitrary structure.
9. S is isomorphic to R times that complementary algebra:
   `∃ Φ : S ≃ₐ[R] R × he.one_sub.Corner`. PASS. The product uses the corner algebra
   witness just bound; the node requires existence of such an isomorphism.
10. s corresponds to its first projection: `∀ x : S, (Φ x).1 = s x`. PASS; this
    quantifier lies inside the witness for the very same Φ.
11. S_e = S[1/e] is R-algebra isomorphic to R via s:
    `∃ ψ : Localization.Away e ≃ₐ[R] R`, together with
    `∀ x : S, ψ (algebraMap S (Localization.Away e) x) = s x`. PASS. Away localizes
    at the powers of e; the inherited base algebra is the composite R to S to S_e.
    The equality on every numerator pins ψ to the map induced by s, since s(e)=1.
    I also read `IsLocalization.away_of_isIdempotentElem`, whose kernel and
    surjectivity hypotheses give exactly this final clause.

Edge cases: e=1 is allowed and gives the zero complementary corner; no nontriviality
instance prevents it. The zero base forces the algebra S to be zero, and the corner,
product and localization remain valid zero rings (empty spectra). For s equal to
the first projection of S=R×T, e=(1,0) gives the complementary T and localization R.
An empty Spec S with nonzero R has no such section, correctly. Universes u and v
are independently declared, including when they differ; the product has their
maximum universe. No index set, n, finite-cardinality parameter, or division by 2
occurs. All characteristics are covered.

Independent searches (2026-10-11), using terms different from the first worker:

- LeanFinder via `msearch.py`: "An etale extension admitting a retraction to its
  base has an idempotent complementary ideal and localization isomorphic to the
  base". Eight hits, including `Algebra.FormallyEtale.iff_of_surjective`,
  etale localization facts and StandardEtalePair; no exact full statement.
- Loogle via `msearch.py`: `AlgHom, IsIdempotentElem, RingHom.ker`. Zero hits.
- `rg` for retraction/retract/splitting and idempotent splitting in Mathlib's
  Etale, Unramified, Idempotents and Localization, upstream RingTheory, and the
  project's RingTheory modules. No exact existing statement. The unrelated
  finite-algebra geometric-point splitting has additional finiteness and primes.
- I independently opened upstream
  `WeilConjectures/Mathlib/RingTheory/Etale/Section.lean`, including the signatures
  of `sectionMul`, `ker_eq_span_sectionMul`, and
  `Algebra.Etale.exists_algEquiv_prod_of_algHom`. The last gives only an abstract
  second factor with first projection s, not the named idempotent, exact ideal
  factor, kernel equality, or localization extension. It is not an existing match.
- `rg` for `exists_idempotent_splitting_of_algHom` in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json found no name collision. The first
  worker's LeanSearch failure is retained as unavailable, not a negative result.

H4/H5/H6/H8/H9/H12/H13: the module reuses all existing notions, defines no data,
proves nothing (the sole theorem proof is `sorry`), binds all variables and both
universes, and follows the topic, namespace, header and line-width conventions.
Both docstrings name the source and blueprint id. The declaration docstring follows
all five node proof steps: cancellation, finitely generated idempotent kernel,
complementary idempotent, explicit product map and inverse, and localization.
There are no new definition nodes, dependency modules, or statement corrections
to audit, and the usable dependency record needs no replacement.

Mismatches found: none. I kept the Lean, node statement and verbatim lean.statement
unchanged and appended this independent reading only. Server single-file compilation
succeeded (1.5 seconds), with no errors or warnings. The initial invocation used a
relative path from the repository instead of the sandbox; rerunning from the sandbox
resolved the path before compilation. Delivery dry run and actual push follow below.

Delivery validation: `deliver2.py --no-push` printed OK: the delivery passes the
stage-2 preflight and compiles. No repair was needed.
