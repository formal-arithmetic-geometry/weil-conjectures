## Worker report

The module `Sheaf.RingTheory.LiftMonicCoprimeFactorizationEtale` states
`Polynomial.exists_etale_lift_monic_coprime_factorization`, with a single `sorry` proof
and no new definitions. The node is unchanged except for its `lean` record.

Source checked: Stacks Project, More on Algebra, Lemma 0ALH and its proof,
https://stacks.math.columbia.edu/tag/0ALH . The local literature checkout is absent on
this machine, so the original source was read on the Stacks website. The module
contains the six proof steps recorded in the node, including its already documented
replacement of the universal factorization ring by its resultant localization.

Hypothesis and conclusion correspondence:

- A commutative ring: `{A : Type u} [CommRing A]`.
- An arbitrary ideal: `(I : Ideal A)`; no properness or radical hypothesis.
- A monic polynomial: `(f : A[X]) (hf : f.Monic)`.
- The two reduced factors: `(g₀ h₀ : (A ⧸ I)[X])`.
- Both reduced factors monic: `(hg₀ : g₀.Monic) (hh₀ : h₀.Monic)`.
- The factorization of the reduction of f:
  `hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀`.
- Generating the unit ideal: `hcoprime : IsCoprime g₀ h₀`. Mathlib defines this as
  existence of coefficients a,b with `a*g₀ + b*h₀ = 1`, exactly the two-generator
  unit ideal condition.
- Existence of a ring extension: existential `A'`, its `CommRing` structure, and
  `φ : A →+* A'`. The witness is allowed in the same universe as A: the proof's
  finitely generated universal algebra and its localization live in that universe.
- Étaleness of the morphism of spectra:
  `AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))`.
- The extended ideal IA': `let J : Ideal A' := I.map φ`.
- The canonical induced map: `let α := Ideal.quotientMap J φ Ideal.le_comap_map`.
  Its value on the class of a is the class of φ(a). This is not an arbitrary
  isomorphism unrelated to φ.
- This map is an isomorphism: `Function.Bijective α`. A bijective ring homomorphism
  is a ring isomorphism, without choosing extra inverse data.
- Lifted monic factors: `∃ g' h' : A'[X], g'.Monic ∧ h'.Monic`.
- Their product equals the image of f: `f.map φ = g' * h'`.
- First prescribed reduction: `g'.map (Ideal.Quotient.mk J) = g₀.map α`.
- Second prescribed reduction: `h'.map (Ideal.Quotient.mk J) = h₀.map α`.
  Both right sides apply the canonical quotient map coefficientwise.

Dependency: `def-weil-etale-morphism` records `AlgebraicGeometry.Etale` in
`Mathlib.AlgebraicGeometry.Morphisms.Etale`. Its full signature and docstring were
read: it asserts étaleness of the maps on rings for affine opens. The module imports
and uses this declaration directly. No dependency module or additional node is needed.
Other notions use Mathlib: `Polynomial.Monic`, `Polynomial.map`, `IsCoprime`,
`Ideal.map`, `Ideal.Quotient.mk`, and `Ideal.quotientMap`. The latter's definition
and `quotientMap_mk` were read in `Mathlib.RingTheory.Ideal.Quotient.Operations`.

Edge cases checked: A may be the zero ring and I may be the unit ideal. No
`Nontrivial` instance is required anywhere. When A/I is zero, its only polynomial
is monic and the coprimality condition holds; A'=A and the factors f and 1 give
the required trivial reduction. The case I=0 permits the identity extension and
the given factors themselves. A factor of degree zero is allowed (it is 1 in a
nonzero ring). In particular f=1 is allowed. There are no degree constraints,
Noetherian assumptions, primality assumptions, or Jacobson assumptions.

Searches made, all on 2026-10-11:

- `msearch.py ... leanfinder` query: "A coprime monic polynomial factorization modulo
  an ideal lifts to an etale algebra with identical quotient". Eight hits, including
  `Polynomial.instEtaleUniversalCoprimeFactorizationRing`, standard étale presentations,
  and `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`.
  The last only concerns a prime residue field; none states the arbitrary-ideal lemma.
- `msearch.py ... loogle` query: `Polynomial.map, IsCoprime, Algebra.Etale`.
  One hit: the same prime residue-field theorem, not this statement.
- `msearch.py ... grep` query: `0ALH|lift.*factorization|factorization.*quotient`,
  subdirectory RingTheory. Three hits: two power-series factorization references
  and the universal factorization map docstring. No arbitrary-ideal lifting theorem.
- `rg` on WeilConjectures and `lean/Sheaf` for `0ALH|lift.*factor|factor.*etale`:
  no source-repository match for this statement; project hits included
  `MonicFactorizationOfIdempotent`, `FactorizationLocallyNilpotent`, and étale section
  lifting. These have extra hypotheses and different conclusions, not this statement.
- `rg` on WeilConjectures for the exact node id: no hits.
- `rg` on Mathlib, WeilConjectures and `lean/Sheaf` for the chosen full declaration
  name: no hits, so the name does not duplicate an existing declaration.

Server single-file compile: clean, exit code 0, compiled in 1.8 seconds.
No disputed statement or node fault found. Independent second reading is left to
its assigned reader.

## Second reading by H1

I independently opened the sandbox node and module, the sole statement dependency
`def-weil-etale-morphism`, and its recorded Mathlib declaration. I read the original
Stacks `more-algebra.tex`, lines 1843–1897, label
`lemma-lift-factorization-monic` (Tag 0ALH), from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
as the literature checkout is unavailable here. I also read the rendered tag at
https://stacks.math.columbia.edu/tag/0ALH. The source introduces an arbitrary ring
and ideal; it imposes no local, Noetherian, proper-ideal, characteristic, or
finiteness hypothesis throughout this lemma.

My object/hypothesis/conclusion checklist, made from the node:

1. Commutative ring A: `{A : Type u} [CommRing A]`. PASS: arbitrary commutative
   unital ring, including the zero ring, with arbitrary universe u.
2. Ideal I of A: `(I : Ideal A)`. PASS: no additional constraint on I.
3. Monic f in A[x]: `(f : A[X]) (hf : f.Monic)`. PASS: Mathlib's monic predicate
   is the usual leading-coefficient-equals-one condition.
4. Reduction of f in (A/I)[x]: `f.map (Ideal.Quotient.mk I)`. PASS: the quotient
   homomorphism is applied coefficientwise, not evaluation or a residue-field map.
5. Two prescribed reduced factors: `(g₀ h₀ : (A ⧸ I)[X])`, with
   `(hg₀ : g₀.Monic) (hh₀ : h₀.Monic)`. PASS: both factors in the actual quotient
   ring, both monic, with no degree constraint.
6. Their product is the reduction: `hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀`.
   PASS: exact ordered product, with no uniqueness assumption.
7. They generate the unit ideal: `hcoprime : IsCoprime g₀ h₀`. PASS: I read
   `Mathlib.RingTheory.Coprime.Basic`, definition `IsCoprime`: there exist polynomial
   coefficients a,b with a*g₀+b*h₀=1. This is precisely the two-generator unit-ideal
   condition, not merely absence of common irreducible divisors.
8. Existence of a commutative ring A' and ring map from A:
   `∃ (A' : Type u) (_ : CommRing A') (φ : A →+* A')`. PASS: the ring and map
   are chosen after the input factors; no injectivity or faithful flatness is added.
9. Spec A' → Spec A is étale:
   `AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))`.
   PASS: Spec reverses the displayed ring map in the required direction. The
   dependency's `AlgebraicGeometry.Etale` class, read in
   `Mathlib.AlgebraicGeometry.Morphisms.Etale`, quantifies over affine opens and
   requires their induced ring maps to be étale. Its `HasRingHomProperty` instance
   and `Etale.iff_flat_and_formallyUnramified` confirm the dependency's notion.
10. Extended ideal IA': `let J : Ideal A' := I.map φ`. PASS: the ideal generated
    by the images of I, not its preimage or an arbitrarily chosen ideal.
11. The induced quotient map α: `let α : A ⧸ I →+* A' ⧸ J :=
    Ideal.quotientMap J φ Ideal.le_comap_map`. PASS: I read `quotientMap` and
    `quotientMap_mk` in `Mathlib.RingTheory.Ideal.Quotient.Operations`; this sends
    [a] to [φ(a)]. The containment proof follows automatically from J=I.map φ
    and adds no hypothesis.
12. That very map is an isomorphism: `Function.Bijective α`. PASS: bijectivity
    of this ring homomorphism is equivalent to its having a ring inverse. No
    unrelated quotient isomorphism is substituted.
13. Existence of monic lifted factors: `∃ g' h' : A'[X], g'.Monic ∧ h'.Monic`.
    PASS: the same chosen A' and φ serve both factors.
14. Factorization upstairs: `f.map φ = g' * h'`. PASS: f is mapped from A to A'
    coefficientwise, and the factors remain in their prescribed order.
15. First prescribed reduction: `g'.map (Ideal.Quotient.mk J) = g₀.map α`.
    PASS: the coefficientwise canonical quotient comparison requested by the node.
16. Second prescribed reduction: `h'.map (Ideal.Quotient.mk J) = h₀.map α`.
    PASS: independent second clause; neither is omitted or weakened.

All hypotheses precede the existential conclusion. The two `let` bindings uniquely
specify J and α and therefore do not add existential choices. The existential
ring structure is in scope for the ring map and all subsequent clauses. Universe
u is explicitly declared, and no variable is auto-implicit or unbound. Choosing
A' in Type u does not exclude a case: the finite-variable universal algebra,
its quotient, and principal localization used in the node's construction all
have carriers in Type u. The source's finite-presentation construction supplies
such a witness, rather than requiring an arbitrary larger test universe.

Edge cases: for I=0, the identity extension and the prescribed factors work after
the canonical quotient identification. For I=⊤, A/I is zero and all reduction
conditions are equalities in a singleton polynomial ring; A'=A, φ=id, g'=f,
h'=1 provide the required witness. This also covers A itself being the zero ring
and its empty spectrum. A degree-zero monic factor is permitted; f=1 and n=0
are permitted. There is no index family or characteristic parameter to restrict,
and no `Nontrivial` or `IsDomain` instance is assumed. PASS in every case.

Independent searches, 2026-10-11, with queries different from the first reader's:

- `msearch.py H1 <item> leanfinder` with "henselian pair arbitrary ideal polynomial
  factors etale neighborhood preserves quotient ring": eight hits, including
  HenselianRing, its root-lifting condition, HenselianLocalRing, and the standard
  étale square-zero lifting lemma. None is the arbitrary-ideal factorization
  statement with a quotient-preserving étale extension.
- `msearch.py H1 <item> loogle` with `Ideal.quotientMap, Polynomial.map`: one hit,
  `Polynomial.isIntegral_isLocalization_polynomial_quotient`, concerning a prime
  ideal and integral localization, not this lemma.
- `msearch.py H1 <item> grep` with
  `0ALH|quotient.*factorization|factorization.*ideal`: 25 hits, mainly ideal
  factorization and power-series Weierstrass factorization; no match.
- `rg` on Mathlib's polynomial and quotient modules, plus direct reading of
  `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`
  in UniversalFactorizationRing.lean: its prime/residue-field input and output
  are different from A/I and the whole quotient comparison, so it cannot serve
  as an existing declaration for this node.
- `rg` on all WeilConjectures, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `0ALH`, the proposed declaration name,
  `monic.*coprime.*etale`, and `étale.*factorization`: no exact match. A broader
  search for `hensel|factorization|quotientMap` in the ring-theory directories
  led to the project's MonicFactorizationOfIdempotent and FactorizationLocallyNilpotent;
  I opened both. Their Jacobson/idempotent and locally nilpotent hypotheses,
  respectively, distinguish them from the present arbitrary-ideal étale lifting.

H4/H12/H13: no duplicate notion or statement found; the sole statement dependency
is usable and directly imported. The sandbox contains exactly one module and one
item node; no new definition node or dependency module is required. There is no
`statement_change` and no correction requiring a citer audit.

H5/H6/H8/H9: no definitions or private copies, one theorem with only `sorry` as
its proof, source tags in both docstrings, and all six node proof steps represented.
I compared each step: universal resultant localization with the zero-quotient degree
case; the surjective map to A/I; quotient étaleness and idempotent splitting; lifting
and principal localization; the canonical quotient isomorphism; and the two factor
reductions. The docstring preserves the node's explicitly recorded replacement of
Stacks' intermediate localization by the universal coprime factorization ring.
Imports serve the displayed notions, lines satisfy the convention, and the recorded
`lean.statement` is verbatim the signature through the conclusion, before `:=`.

No mismatch found. I changed neither the Lean module nor the node: only this
independent review section was appended. Server single-file compilation using
`scompile.py H1 <item> <module>` completed in 1.7 seconds, exit code 0, with no
errors or warnings. The delivery preflight and push results follow from the
required `deliver2.py` runs.
