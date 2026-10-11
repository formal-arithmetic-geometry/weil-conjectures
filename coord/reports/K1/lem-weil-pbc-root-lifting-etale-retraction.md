## Worker report

The module `Sheaf.RingTheory.RootLiftingEtaleRetraction` states
`IsLocalRing.existsUnique_algHom_of_monic_simple_root_lifting_etale`.
Its only proof is `sorry`; no definition or auxiliary theorem is introduced.
The node is unchanged except for its `lean` record. No statement dispute, correction,
new node, or dependency replacement is needed.

### Hypotheses and conclusion

| Node clause | Lean rendering |
| --- | --- |
| Local ring (R, m, κ) | `{R : Type u} [CommRing R] [IsLocalRing R]`; m is `maximalIdeal R` and κ is `ResidueField R`. |
| Every monic polynomial f in R[T] | `hroot : ∀ f : Polynomial R, f.Monic → ...`. |
| Every residue element a₀ | `∀ a₀ : ResidueField R`. |
| f̄(a₀) = 0 | `Polynomial.aeval a₀ f = 0`; the canonical R-algebra structure on the residue field reduces coefficients. |
| f̄'(a₀) ≠ 0 | `Polynomial.aeval a₀ f.derivative ≠ 0`; reducing the derivative equals differentiating the reduction. |
| There is a root lifting a₀ | `∃ a : R, f.IsRoot a ∧ residue R a = a₀`. |
| Ring map R → S | `[CommRing S] [Algebra R S]`, with map `algebraMap R S`. Every commutative ring map determines this algebra structure; no finiteness or injectivity is imposed. |
| Spec S → Spec R is étale | `[Etale (Spec.map (CommRingCat.ofHom (algebraMap R S)))]`, exactly the recorded scheme predicate. |
| Prime q in S | `(q : Ideal S) [q.IsPrime]`. |
| q lies over m | `hq : q.comap (algebraMap R S) = maximalIdeal R`. |
| Induced residue field map is an isomorphism | `hres : Function.Bijective ((Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap (⟨q, inferInstance⟩ : Spec (.of S))).hom`. This is the induced field homomorphism itself, not existence of an unrelated isomorphism. |
| Exactly one R-algebra homomorphism τ : S → R | `∃! τ : S →ₐ[R] R, ...`; its algebra-map compatibility says precisely that it retracts `algebraMap R S`, since the self algebra map of R is the identity. |
| τ⁻¹(m) = q | `(maximalIdeal R).comap τ.toRingHom = q`, the predicate within `∃!`. Uniqueness is among maps with this prime preimage. |

The scheme residue-field map has source κ at the image of q. Mathlib's
`AlgebraicGeometry.Spec.map_apply` identifies that point with the comap prime;
`hq` identifies it with m. The scheme residue fields are those of the respective
local stalks, exactly as `def-weil-residue-field` says. On affine schemes,
`Scheme.Spec.residueFieldIso` identifies them with prime-ideal residue fields;
the residue field at the maximal ideal of a local ring is its usual residue field.
Consequently the displayed bijectivity is exactly the stated κ → κ(q) isomorphism.
A bijective field ring homomorphism is an isomorphism; neither extra surjectivity
of R → S nor maximality of q is assumed.

### Dependency declarations read and used

- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` from
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, used on `Spec.map` in the hypothesis.
  Its full signature/docstring defines affine-locally étale ring maps.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap` from
  `Mathlib.AlgebraicGeometry.ResidueField`, used through the latter's source and
  target and the induced-map hypothesis. Their full signatures/docstrings were read.
- The local-ring residue notation and root-lifting expression are Mathlib's:
  `IsLocalRing.ResidueField`, `IsLocalRing.residue`, `Polynomial.aeval`, and
  `Polynomial.IsRoot`. The explicit `hroot` is exactly the second entry of
  `HenselianLocalRing.TFAE`, whose full signature was read; it is not replaced by
  a new henselian definition or a typeclass assumption.

All imports are used by these expressions. Every variable and the universe `u`
are explicit. Both rings live in a shared universe, as needed for the scheme
morphism category; this is an ambient universe choice, not a smallness condition
on either ring.

### Source and edge cases

The cited local `literature/stacks-project/algebra.tex` is absent on this machine.
Read the primary source at https://stacks.math.columbia.edu/tag/04GG, statement (8)
and proof of (1) ⇒ (8). It agrees with the node. The declaration docstring carries
all six DAG proof steps, including the localization correspondence, extraction
of the simple residue root, existence by `hroot`, and uniqueness by Stacks 06RR.

Checked before writing:

- The zero ring is not a local ring in Mathlib's usual nontrivial local-ring
  convention, agreeing with the source's proper maximal ideal and residue field.
  The zero S algebra has no prime q, so this case has no instances of the hypotheses.
- No prime of S, or no prime over m, makes the pointed assertion vacuous, as intended.
- For R a field, the root hypothesis holds and a residue-rational étale point
  gives exactly the corresponding algebra map S → R; q need not be arbitrary.
- For S = R, the only R-algebra endomorphism of R is the identity; q = m.
- For S = R × R, choosing a prime over m selects one projection. Uniqueness
  is for that q, so it does not incorrectly identify the two different projections.
- Constant monic f = 1 has no residue root; multiple roots are not required to lift.
  No polynomial degree or characteristic restriction is added.
- No Noetherian or henselian typeclass hypothesis is added. The explicit root
  lifting condition includes non-Noetherian local rings and every characteristic.
- In proof step 4, n = 0 still makes h̄(a₀)^n nonzero; nothing requires n positive.

### Searches for an existing statement

All remote searches used `msearch.py K1 lem-weil-pbc-root-lifting-etale-retraction`:

- LeanSearch: “A local ring where simple roots of monic polynomials lift has a
  unique algebra retraction from an etale algebra at a prime with trivial residue
  field extension”. Service unavailable (Internal Server Error), recorded without
  a mathematical verdict.
- LeanFinder: “simple roots of monic polynomials lift in a local ring implies
  unique retraction from etale algebra with trivial residue field extension”.
  Eight hits include `StandardEtalePair.homEquiv`, `StandardEtalePair.lift`,
  `StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot`, and
  `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`.
  These supply ingredients, not the local-ring retraction assertion.
- Loogle: `HenselianLocalRing, AlgHom`. One hit, `HenselianLocalRing.TFAE`,
  characterizes root lifting but does not state the retraction conclusion.
- Remote Mathlib grep (RingTheory):
  `HenselianLocalRing|root.*lifting.*retraction|exists.*algHom.*maximalIdeal`.
  Five hits in `Mathlib/RingTheory/Henselian.lean`: class, field instance, TFAE;
  no retraction statement.
- Local `rg` of the source project and `lean/Sheaf` for root lifting, retractions,
  `HenselianLocalRing`, and the exact node id. The source's
  `HenselianLocalRing.of_exists_algHom_comap_maximalIdeal_eq` and
  `IsLocalRing.exists_isRoot_algebraMap_eq_of_exists_algHom_comap_maximalIdeal_eq`
  are the converse direction, not this node. The project module
  `HenselianEtaleRetraction.lean` states the sibling
  `existsUnique_algHom_of_henselianLocalRing_etale` with a henselian class, rather
  than this node's explicit simple-root lifting assumption. The project module
  `HenselianLocalRootLifting.lean` cites this item in its proof but states an
  equivalence with idempotent lifting. Neither is this node's exact statement.
- Checked the proposed full declaration name in Mathlib, the source project,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

### Validation

`python3 /home/ubuntu/weil-launcher/scompile.py K1
lem-weil-pbc-root-lifting-etale-retraction
<absolute sandbox module path>` compiled the 63-line module on the server in
1.7 seconds, exit code 0, no errors and no warnings. No local compilation was run.
`deliver2.py K1 lem-weil-pbc-root-lifting-etale-retraction --no-push` printed
OK: compilation and preflight passed except for the independent second reading,
which the second reader supplies. Nothing was pushed.

## Second reading by K1

Read the node, its six proof steps, the delivered module, both statement dependency
nodes and their actual Mathlib declarations independently. The local Stacks checkout
is absent. Read the primary source [04GG](https://stacks.math.columbia.edu/tag/04GG),
[04GF](https://stacks.math.columbia.edu/tag/04GF), and the upstream `algebra.tex`
`lemma-characterize-henselian`, especially assertion (8) and the proof of (1) ⇒ (8).
The source assumes a commutative local ring with proper maximal ideal; it assumes
neither Noetherianity nor a characteristic restriction. The node agrees with that
source. No `statement_change` is present, so correction/citer review is inapplicable.

Independent inventory and comparison (each verdict is PASS):

| Object, hypothesis or conclusion of the node | Lean rendering and verdict |
| --- | --- |
| Commutative local ring R | `{R : Type u} [CommRing R] [IsLocalRing R]`: PASS, no domain or Noetherian assumption. |
| Its maximal ideal m and residue field κ | `maximalIdeal R`, `ResidueField R`, `residue R`: PASS, the canonical ideal, quotient and quotient map. |
| Every monic polynomial f | `∀ f : Polynomial R, f.Monic →`: PASS, all degrees. |
| Every residue element a₀ | `∀ a₀ : ResidueField R`: PASS, inside the quantifier on f. |
| Vanishing of the reduced polynomial at a₀ | `Polynomial.aeval a₀ f = 0`: PASS, coefficients use the canonical residue algebra map. |
| Nonvanishing of the reduced derivative | `Polynomial.aeval a₀ f.derivative ≠ 0`: PASS, reduction commutes with differentiation. |
| Existence of a lifting root | `∃ a : R, f.IsRoot a ∧ residue R a = a₀`: PASS, no uniqueness of lifts is assumed. |
| Commutative ring S and ring map R → S | `{S : Type u} [CommRing S] [Algebra R S]`, map `algebraMap R S`: PASS, each commutative unital ring map has this algebra structure. |
| Étale affine scheme morphism | `[Etale (Spec.map (CommRingCat.ofHom (algebraMap R S)))]`: PASS, precisely Spec S → Spec R. |
| Prime ideal q | `(q : Ideal S) [q.IsPrime]`: PASS, no maximality assumption. |
| q lies over m | `hq : q.comap (algebraMap R S) = maximalIdeal R`: PASS, exact inverse image. |
| Induced map κ → κ(q) is an isomorphism | `hres : Function.Bijective ((Spec.map ...).residueFieldMap (⟨q, inferInstance⟩ : Spec (.of S))).hom`: PASS, bijectivity of the actual induced field homomorphism. |
| A retraction τ of R → S | `τ : S →ₐ[R] R`: PASS, `AlgHom.commutes` with the self algebra map of R gives τ ∘ algebraMap = id. |
| τ has prescribed inverse image of m | `(maximalIdeal R).comap τ.toRingHom = q`: PASS, exact equality. |
| Exactly one such τ | `∃! τ : S →ₐ[R] R, ...`: PASS, uniqueness among maps satisfying the inverse-image predicate, for the fixed q. |

For H3/H4, opened `Mathlib.AlgebraicGeometry.Morphisms.Etale`: the class
`AlgebraicGeometry.Etale` tests affine ring maps, and
`Etale.iff_flat_and_formallyUnramified` supplies exactly the dependency node's
finite-presentation, flat and unramified clauses. Opened
`Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField X x` is the
residue field of the stalk; `Scheme.Hom.residueFieldMap f x` is induced by
`f.stalkMap x`, with source at f(x). `Spec.map_apply` identifies f(q) with
the comap prime, which `hq` identifies with m. `Scheme.Spec.residueFieldIso`
identifies affine residue fields with ideal residue fields. Thus `hres` tests
κ → κ(q), not an unrelated abstract isomorphism. Both recorded dependency
notions are used directly and are usable. There are no new definition nodes,
dependency modules, private definitions, or missing notions.

Edge cases independently checked: `IsLocalRing` extends `Nontrivial`, excluding
the zero base ring just as the source's proper maximal ideal does. A zero S or
empty Spec S has no prime q; the assertion has no pointed inputs in that case.
There is no index set or zero object in this statement. For a field R the
hypothesis is the usual trivial lifting property. S = R gives the identity;
S = R × R gives a different projection for each selected q, and the uniqueness
predicate correctly keeps those apart. Constant monic f = 1 has no root;
repeated residue roots are excluded exactly by the derivative hypothesis.
All characteristics and non-Noetherian rings remain covered. The proof's
standard-étale exponent may be n = 0, since the evaluated power is then 1.
The single polymorphic universe is the common ambient universe required by
Mathlib's scheme category: any pair of ring universes can be placed in their
common maximum. No bound on cardinality, test-scheme universe, independent
lower universe, or unbound variable appears.

Independent H4 searches, using different wording from the worker:

- LeanFinder via `msearch.py`: “lifting a rational closed point of an etale affine
  scheme to a unique section over a local base with monic Hensel property”. Eight
  hits: standard-étale square-zero lifting, `StandardEtalePair.homEquiv`, étale
  loci and `SpecToEquivOfLocalRing`; none states this retraction theorem.
- Loogle via `msearch.py`: `IsLocalRing, Etale, AlgHom` could not resolve the
  unqualified `Etale`; this is not a no-match result. Follow-up
  `HenselianLocalRing, _ →ₐ[_] _` gives only `HenselianLocalRing.TFAE`.
  Opened its signature: it contains precisely our root hypothesis, but no
  étale-retraction conclusion.
- LeanSearch via `msearch.py`: “The monic Hensel root property implies unique
  sections of etale ring maps at rational closed points”. Service returned
  Internal Server Error; recorded unavailable, without a mathematical verdict.
- Local `rg` for `retract|existsUnique.*algHom|comap_maximalIdeal|Bijective.*residueFieldMap`
  across source `WeilConjectures`, Mathlib Henselian and project RingTheory.
  Opened the source Henselian converse declarations: they deduce root lifting
  from existence of retractions, rather than supplying our implication. Opened
  `Algebra.Etale.exists_algHom_comap_maximalIdeal_eq` in source QuasiFinite:
  it assumes an integrally closed local domain with separably closed fraction
  field, and asserts existence only; it is not this statement. Opened the
  project's `existsUnique_algHom_of_henselianLocalRing_etale`: it states the
  sibling with a henselian class, not the explicit monic root hypothesis.
  `HenselianLocalRootLifting` states an equivalence, not this conclusion.
  Exact-name search in the source, project and `dag/lean_names_upstream.json`
  found no declaration collision. No existing exact statement was found.

H5/H6/H8/H9: the sole theorem has proof `by sorry`; there are no definitions or
proved auxiliary results. Module and declaration docstrings name 04GG and the
blueprint item. Checked the six docstring steps against the six DAG steps:
residue map, standard presentation, localization bijection, simple residue root,
root lift and universal map, uniqueness via 06RR. Every step and its dependency
is present. Imports supply the scheme étale predicate, induced residue map and
local-ring polynomial/residue expressions. Lines respect 100 columns.

Mismatches found: none. Changes: appended this independent reading only;
kept the Lean and the node record as written. The recorded `lean.statement`
is verbatim the theorem signature up to `:=`, with all binders explicit.

Additional Mathlib `rg` in `RingTheory/Etale` and `RingTheory/Henselian.lean`
for `existsUnique.*algHom|retraction|HenselianLocalRing` found only the
Henselian definitions/TFAE, not the conclusion. A literal comparison of the
node's recorded signature with the module text passed, as did the line-width check.
Independent server `scompile.py` compiled the 63-line module in 1.8 seconds,
exit 0, with no warnings or errors. `deliver2.py --no-push` printed
`OK (dry run)`: preflight and compilation passed; nothing was pushed in that check.
