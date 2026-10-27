## Worker report

The module `Sheaf.RingTheory.OrdinaryPDPolynomialExtension` states
`DividedPowers.ordinary_pd_polynomial_extension`, with `sorry` as its only proof.
Its helper structure `DividedPowers.OrdinaryPDPolynomialExtensionData` packages precisely
the algebra, named monomial basis, ideals, normalized divided powers and universal
property whose existence the node asserts. It is an interface for the same node, not
an independent notion. The theorem constructs no downstream definition by choice from
its existence assertion. Every data field in the interface has its actual mathematical
type; no definition has a `sorry` body.

Source read: `literature/stacks-project/dpa.tex`, section
`section-divided-power-polynomial-ring`, lines 710–799, especially
`lemma-divided-power-polynomial-algebra` (Tag 07H5). The node agrees with that source.
The seven-step proof plan in the declaration docstring reproduces every proof step
of the node and names the applicable DAG prerequisites.

The hypothesis-by-hypothesis and clause-by-clause translation is:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative coefficient ring C | `(C : Type u) [CommRing C]` |
| Ideal I with ordinary divided powers γ | `(I : Ideal C) (γ : DividedPowers I)`; this is the dependency's exact Mathlib match |
| Integer t ≥ 1 | `(t : ℕ) (ht : 1 ≤ t)`; natural numbers with this bound are precisely the stated positive integers |
| Free C-module on α ∈ ℕ^t | `basis : Module.Basis (Fin t →₀ ℕ) C P`; since `Fin t` is finite, these finitely supported multiindices are exactly all t-tuples, and `basis.repr` is the linear equivalence with the required direct sum |
| Commutative unital C-algebra P | Data fields `P : Type u`, `[commRingP : CommRing P]`, `[algebraCP : Algebra C P]` |
| Unit is X^[0] | `basis_zero : basis 0 = 1` |
| Displayed binomial multiplication | `basis_mul`, with the finite product of natural binomial coefficients cast to C, acting by C-scalar multiplication |
| Constants are the coefficient inclusion | `algebraMap C P`; C-linearity of the basis coordinate equivalence and `basis_zero` imply that c maps to coefficient c at multiindex zero |
| P₊ is the span of positive monomials | `positive_eq` identifies `positive` with `Ideal.span` of `basis α`, α ≠ 0; by `basis_mul` that ideal equals their C-linear span, because multiplication of a positive monomial by any monomial still has nonzero multiindex |
| K = IP + P₊ | `K_eq : K = Ideal.map (algebraMap C P) I ⊔ positive`; ideal supremum is ideal sum |
| Existence of ordinary δ on K | Field `δ : DividedPowers K` inside the data whose `Nonempty` is asserted |
| δ restricts to γ on I | `restrict`, equality of total `dpow` operations on the coefficient inclusion for every x ∈ I and every n |
| δ_n(X_j) = X_j^[n] for n ≥ 1 | `generators`, where X_j is `basis (Finsupp.single j 1)` and the output multiindex is `n • Finsupp.single j 1` |
| Uniqueness of δ subject to restriction and normalization | `unique`, quantified over every `δ' : DividedPowers K` with exactly those two properties |
| Arbitrary commutative target D with ideal L and divided powers η | In `universal`: `∀ (D : Type (max u w)) [CommRing D] (L : Ideal D) (η : DividedPowers L)` |
| Unital f : C → D mapping I into L and preserving divided powers | `(f : C →+* D), IsDPMorphism γ η f`; its fields are `I.map f ≤ L` and equality of operations on I |
| Arbitrary prescribed z_j ∈ L | `(z : Fin t → D) → (∀ j : Fin t, z j ∈ L)` |
| Existence of unital F : P → D | `∃ F : P →+* D` in `universal` |
| F extends f | `F.comp (algebraMap C P) = f` |
| F maps K into L and preserves its divided powers | `IsDPMorphism δ η F` |
| F(X_j) = z_j | The generator-value conjunct in `universal` |
| Explicit value on every monomial, including multiindex zero | `∀ α, F (basis α) = ∏ j : Fin t, η.dpow (α j) (z j)` |
| Uniqueness of F with extension, divided-power preservation and generator values | The final `∀ G : P →+* D, ... → G = F`; the competing G is not assumed to satisfy the monomial formula |
| Ordinary axioms and integer factorial quotients | The existing `DividedPowers` structure: `dpow_zero`, `dpow_one`, `dpow_mul`, `dpow_add`, `mul_dpow`, `dpow_comp`, and `dpow_mem`. Its iteration coefficient is `Nat.uniformBell`, the integer coefficient specified by the dependency |

The universal property uses the source's positive/ideal-valued operations through their
Mathlib total extension by zero off the ideal. Requiring restriction at n = 0 adds no
mathematical condition: the coefficient image of I lies in K and unital ring maps
preserve 1. Likewise the degree-zero preservation in `IsDPMorphism` follows from ideal
mapping and unitality. No rational algebra, torsion-free coefficient ring, nontriviality,
flat target map, or characteristic restriction is imposed.

The algebra is packaged with its full named basis rather than chosen by a definition
from an unspecified existence theorem. The basis and multiplication determine it up to
the unique C-linear identification preserving every named monomial. `P : Type u` keeps
the constructed free module in the coefficient universe; it is not required to inhabit
an independent possibly smaller universe. The target universe is `max u w`, in accordance
with the project's convention for tests against arbitrary algebras; w remains arbitrary.
`set_option autoImplicit false` and explicit universe declarations forbid accidental binders.

Dependency declarations read and used:

- `def-sfb-ordinary-divided-power-structure`: exact `mathlib_match` `DividedPowers`,
  `Mathlib.RingTheory.DividedPowers.Basic`, structure and docstring at lines 78–101.
  It is publicly available through `Mathlib.RingTheory.DividedPowers.DPMorphism`.
- `DividedPowers.IsDPMorphism`, `Mathlib.RingTheory.DividedPowers.DPMorphism`,
  structure at lines 65–69, used for the two maps' ideal and operation compatibility.
- `Module.Basis`, `Mathlib.LinearAlgebra.Basis.Defs`, publicly imported by
  `Mathlib.LinearAlgebra.Basis.Basic`, for the exact free-module coordinates.
- Proof import `Sheaf.RingTheory.DividedPowersFactorialCriterion`:
  `DividedPowers.exists_unique_of_factorial_divisibility_on_generators`
  (`lem-sfb-pd-torsionfree-factorial-criterion`).
- Proof import `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`
  (`def-weil-pbc-mv-polynomial-ring`), for the torsion-free polynomial cover.
- Proof import `Mathlib.RingTheory.DividedPowers.SubDPIdeal`:
  `DividedPowers.Quotient.OfSurjective.dividedPowers`, `dpow_apply`,
  `dividedPowers_unique` (`lem-sfb-pd-surjective-descent`).
- Proof import `Mathlib.RingTheory.Flat.Basic`: `Module.Flat.of_projective` and
  `Module.Flat.of_free` (`lem-weil-pbc-projective-module-flat`).
- Proof import `Sheaf.RingTheory.DividedPowersFlatExtension`:
  `DividedPowers.existsUnique_extension_of_flat` (`lem-sfb-pd-flat-extension`).
- Proof import `Sheaf.RingTheory.DividedPowersGlueIdeals`:
  `DividedPowers.coincide_mul_and_existsUnique_sup` (`lem-sfb-pd-glue-ideals`).

Edge cases checked before finalizing:

- t = 1 gives the single-variable construction of the source; t = 0 is excluded only
  by the exact positive-t hypothesis, not by any implicit nonemptiness instance.
- C the zero ring is allowed; a free module and its basis over it are legitimate,
  and every displayed identity specializes correctly. No `Nontrivial` instance is used.
- I = 0 gives the augmentation ideal, and the coefficient restriction is still correct
  at x = 0, including n = 0. I = C is allowed whenever it actually carries γ.
- n = 1 gives each generator back. Normalization is asserted only for n ≥ 1 as stated;
  n = 0 on elements of K is already 1 by the ordinary structure.
- α = 0 in the universal formula yields the product of η_0(z_j) = 1, hence F(1) = 1.
- Zero prescribed elements and the zero target ring are allowed. Positive-characteristic
  coefficients are never divided by factorials: multiplication uses `Nat.choose`, and
  the iteration axiom uses `Nat.uniformBell`.

Searches (no exact existing statement found):

- `msearch.py leanfinder`, query `ordinary divided-power polynomial extension universal property`:
  eight hits, including quotient operations, `DPMorphism.fromGens`,
  `dpow_comp_from_gens`, `IsDPMorphism` and rational-coefficient uniqueness. None states
  the polynomial extension of an arbitrary given divided-power coefficient ideal.
- `msearch.py leansearch`, query `Free divided power polynomial algebra over a commutative ring with divided power coefficient ideal, existence uniqueness universal property`:
  eight hits, including `DividedPowers`, quotient uniqueness and
  `DividedPowers.dpow_eq_from_gens`; none supplies this algebra with its normalized
  extension and universal property.
- `msearch.py loogle`, query `DividedPowers, DividedPowers.dpow_comp, polynomial`:
  no hits, unknown identifier `polynomial`. Follow-up valid quoted-name query
  `"DividedPowerAlgebra", "dividedPowers"`: zero hits.
- `msearch.py grep`, query `divided.*power.*polynomial|polynomial.*divided.*power`,
  subdirectory `RingTheory/DividedPowerAlgebra`: five hits in `Init.lean`. Read that
  file: it defines a quotient algebra for a module and a weak universal property,
  and expressly leaves the canonical divided-power structure as a TODO. It does not
  give the required relative polynomial extension of (C,I,γ).
- `rg` on project `WeilConjectures/` and `Sheaf/`, patterns
  `ordinary.*divided|divided.*polynomial|pd.*polynomial|OrdinaryPDPolynomial`:
  found the graded ordinary-structure bridge and the graded variable-adjunction
  consumer's proof citation, with unrelated polynomial hits. No ordinary polynomial
  extension declaration exists there. The supplied item-id `grep` likewise found only
  `Sheaf/RingTheory/DividedPowerVariableAdjunction.lean`, whose even-variable theorem
  uses this ordinary result in its proof and does not state it.
- `rg` on `dag/lean_names_upstream.json` for `DividedPowers`,
  `OrdinaryPDPolynomialExtensionData`, `ordinary_pd_polynomial_extension`: no hits.

No statement correction, dependency repair, new independent definition node, or
STATEMENT-DISPUTED issue is needed. Only the item's `lean` field changes.

Validation: every delivered module is compiled separately through `scompile.py` in
module mode against the live published library. The statement contains one expected
`sorry` and no other postponed proof. The final delivery dry run is recorded below.

Final dry run: `deliver2.py N6 lem-sfb-ordinary-pd-polynomial-extension --no-push`
returned `OK (dry run): commit ba612cd7641 passes the preflight and compiles; nothing pushed`.
The staged packet contains exactly the module, the item's node, and this report.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
