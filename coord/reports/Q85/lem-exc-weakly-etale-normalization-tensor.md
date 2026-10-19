## Worker report

The module `lean/Sheaf/RingTheory/WeaklyEtaleNormalization.lean` states
`weaklyEtale_normalization_tensor` (blueprint:
`lem-exc-weakly-etale-normalization-tensor`) and leaves its proof as `sorry`.
The source is Greco, *Two theorems on excellent rings*, Lemma 5.5 proof, first two
sentences, printed page 147 (PDF page 9).

The Lean binders render the hypotheses as follows. `C : Type u` with
`[CommRing C]`, `[IsNoetherianRing C]`, `hCuc : IsUniversallyCatenary C`,
`[IsLocalRing C]`, and `[IsDomain C]` is the commutative Noetherian universally
catenary local domain. `Module.Finite C (integralClosure C (FractionRing C))`
renders that its normalization in its fraction ring is finite as a `C`-module.
`D : Type v` with `[CommRing D]`, `[IsNoetherianRing D]`, and `[IsLocalRing D]`
renders the commutative Noetherian local target. `[Algebra C D]` supplies the
map `f`; `[IsLocalHom (algebraMap C D)]` says it is local, and
`[Algebra.WeaklyEtale C D]` is the recorded weakly etale algebra predicate.

The first conclusion is `IsReduced D`, i.e. every nilpotent of `D` is zero.  The
normalization of `C` is the subalgebra
`integralClosure C (FractionRing C)`, and the normalization of `D` is
`integralClosure D (Localization (nonZeroDivisors D))`; the latter localization
is the total ring of fractions.  The second conclusion is a nonempty
`AlgEquiv D` between the tensor product
`TensorProduct C (integralClosure C (FractionRing C)) D` (using
`Algebra.TensorProduct.rightAlgebra`) and this normalization of `D`.

For each `P : Ideal D` in `Ideal.minimalPrimes (⊥ : Ideal D)`, the final clause
uses `E = integralClosure (D ⧸ P) (FractionRing (D ⧸ P))`.  It existentially
chooses a commutative ring `F : CommRingCat.{v}` and a `D`-algebra structure
`A : Algebra D F`, then an explicit `D`-algebra equivalence from `D'` to
`E × F`.  The `D`-algebra structure on `E` is the canonical structure supplied
by `SubalgebraClass.toAlgebra`; its map is composed with `Ideal.Quotient.mk P`.
The product algebra map is the product of that map and `@algebraMap D F _ _ A`.
The final equality says that the first projection of this equivalence sends the
canonical image of each `d : D` to its image in `E`, exactly the restriction
`D → D/P ↪ E`.

Statement dependencies and declarations used:

- `def-weil-pbc-noetherian-ring`: Mathlib `IsNoetherianRing`.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, declaration
  `IsUniversallyCatenary`.
- `def-weil-pbc-integral-closure`: Mathlib `integralClosure` and its
  `SubalgebraClass.toAlgebra` structure.
- `def-weil-finitely-generated-module`: Mathlib `Module.Finite`.
- `def-weil-pbc-ind-etale-algebra`: `Sheaf.RingTheory.IndPrincipalZariski`,
  declaration `Algebra.WeaklyEtale`.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct` and
  `Algebra.TensorProduct.rightAlgebra`.

Edge cases checked: `Localization (nonZeroDivisors D)` permits zero divisors in
`D` (the total quotient ring); minimal primes are quantified by the exact
`Ideal.minimalPrimes ⊥` predicate, including the one-minimal-prime and empty
possibilities; no nonzero or finite-index assumption is imposed on `D`; the
universe of `F` is the target universe `v`; and the tensor product uses the
actual algebra multiplication supplied by Mathlib.  The quotient `D ⧸ P` is
used directly, so the zero quotient and all minimal-prime cases remain in the
statement.

Searches for an existing declaration were made before writing the module:

- `msearch.py Q85 lem-exc-weakly-etale-normalization-tensor leanfinder
  "Normalization of a Noetherian algebra commutes with a weakly etale flat base change"`:
  returned normalization and tensor-product declarations, but no exact weakly
  etale normalization theorem.
- `msearch.py ... loogle "integralClosure, TensorProduct"`: returned only
  smooth/localization/tower comparison theorems, not this statement.
- `msearch.py ... grep "normalization|integralClosure" RingTheory/Etale`: found
  only unrelated Mathlib integral-closure results.
- `msearch.py ... leansearch "Integral closure commutes with normalization base
  change along a weakly etale algebra"`: no exact match.
- `rg` over `WeilConjectures/` and `lean/Sheaf`, plus a search for the node id,
  found no existing declaration of this theorem.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Earlier second reading (a previous round; superseded)

I reread the node and the module together.  The local-domain, Noetherian and
universally-catenary hypotheses appear as the `C` binders; the finite normalization
hypothesis is `Module.Finite`; and the target's Noetherian/local and weakly etale
local algebra hypotheses are all present.  The first conclusion is exactly
reducedness.  The second is an algebra equivalence from the base-changed
normalization to the total-quotient normalization.  For every minimal prime, the
module uses the normalization of `D/P`, an existential commutative `D`-algebra
factor `F`, and an algebra equivalence to their product.  Its final equality
matches the required projection restriction on every `d : D`.  No hypothesis or
component of the node is omitted or strengthened.

## Second reading by Q85

Read independently on 2026-10-17 against the unchanged DAG statement and the actual
Lean declarations. This reading supersedes the short earlier second reading.

Source check: read Greco's published PDF, foreword on printed p. 139, Definition
5.1 and Remark 5.2 on p. 146, and Lemma 5.5 and its first two proof sentences on
p. 147. The foreword assumes all rings commutative and Noetherian; Remark 5.2
identifies AF with flatness over the base and over tensor multiplication in this
setting. Lemma 5.5 assumes a universally catenary local domain with finite
normalization and a local AF map to a local ring. Its proof first establishes
reducedness and the tensor normalization, then selects the normalization of a
minimal-prime quotient as a product factor. The node correctly isolates those
sentences, without the later dimension or weak-etaleness-to-factor conclusion.
PDF read from the publisher:
https://www.cambridge.org/core/services/aop-cambridge-core/content/view/8F98780AD8CD9051866A2716C67833C3/S0027763000017190a.pdf/div-class-title-two-theorems-on-excellent-rings-a-href-fn01-ref-type-fn-span-class-sup-1-span-a-div.pdf
Also read the local Stacks .tex statements and proofs at Tags 092H, 092Q, 092W
(more-algebra.tex) and 035P (morphisms.tex). Tag 035P requires reducedness and
finitely many components on quasi-compact opens, supplied here by reducedness and
Noetherianity; no extra source hypothesis is missing.

Object/hypothesis/conclusion inventory and item-by-item verdict:

1. C is a commutative ring: `(C : Type u) [CommRing C]`. PASS.
2. C is Noetherian: `[IsNoetherianRing C]`, Mathlib's recorded predicate for
   finite generation of ideals. PASS.
3. C is universally catenary: `(hCuc : IsUniversallyCatenary C)` from the
   recorded `Sheaf.RingTheory.ExcellentRing`. Read its definition: Noetherianity
   and catenarity of every finite-type algebra, with the finite-chain bound and
   saturated-chain length equality. Its same-universe finite-type test algebras
   suffice by presentation and transport; the item adds no universe equality. PASS.
4. C is local and a nonzero domain: `[IsLocalRing C] [IsDomain C]`. Read the
   Mathlib definitions, including their `Nontrivial` fields. A commutative local
   ring has exactly one maximal ideal. PASS.
5. K is Frac(C): `FractionRing C`, whose definition is localization at
   `nonZeroDivisors C`, a field since C is a domain. PASS.
6. C' is the integral closure of C in K: `integralClosure C (FractionRing C)`.
   Read the recorded Mathlib definition, the subtype of elements integral over C
   with its inherited ring and canonical C-algebra structure. PASS.
7. C' is finite over C: `[Module.Finite C (integralClosure C (FractionRing C))]`,
   using the recorded finite-generation predicate, with no field extension or
   stronger finite-presentation hypothesis. PASS.
8. D is a commutative Noetherian local ring: `(D : Type v) [CommRing D]
   [IsNoetherianRing D] [IsLocalRing D]`. No domain assumption on D. PASS.
9. f is a ring homomorphism C to D: `[Algebra C D]`, with f = `algebraMap C D`.
   Commutativity makes this equivalent to specifying the homomorphism. PASS.
10. f is local: `[IsLocalHom (algebraMap C D)]`. Read the Mathlib definition:
    it reflects units, equivalently the maximal-ideal inverse-image equality
    for the two local rings. PASS.
11. f is weakly etale: `[Algebra.WeaklyEtale C D]`. Followed the recorded
    `Sheaf.RingTheory.IndPrincipalZariski` public imports to the existing
    Mathlib predicate. Its fields are flatness over C and flatness of tensor
    multiplication, exactly the node's definition; neither IndEtale nor finite
    presentation is assumed. PASS.
12. D is reduced: first conjunct `IsReduced D`, the existing predicate that
    every nilpotent is zero. PASS.
13. Q(D) inverts every nonzerodivisor: `Localization (nonZeroDivisors D)`.
    This is the total fraction ring, not a fraction field assumption on D. PASS.
14. D' is the integral closure of D in Q(D):
    `integralClosure D (Localization (nonZeroDivisors D))`. PASS.
15. Canonical D-algebra comparison C' tensor_C D to D': the first existential
    `e : @AlgEquiv D ...`, with the explicitly supplied
    `Algebra.TensorProduct.rightAlgebra` on the tensor. Read that declaration:
    its structure map is `d ↦ 1 ⊗ d`. Multiplication is Mathlib's standard
    algebra tensor multiplication. PASS after making the characterization
    explicit: for every c in C', every a,s in C with s nonzero and s*c=a in K,
    and every d in D, the statement requires f(s)*e(c tensor d)=f(a)*d in Q(D).
    Every c has such a fraction presentation. Flatness makes f(s) a
    nonzerodivisor, hence a unit in Q(D), so the equation uniquely fixes e on
    pure tensors and therefore everywhere. This renders the canonical map
    without introducing another normalization or an arbitrary auxiliary map.
    The original Nonempty D-algebra equivalence had no explicit normalization
    equation; the birational algebra relations determine the same map, and
    the new formula exposes that determination in the formal interface.
16. Every minimal prime P of D: `∀ (P : Ideal D),
    P ∈ Ideal.minimalPrimes (⊥ : Ideal D) → ...`. Read the predicate: a prime
    minimal over zero, exactly the node's quantification. PASS.
17. E is normalization of D/P in Frac(D/P):
    `integralClosure (D ⧸ P) (FractionRing (D ⧸ P))`. On the minimal-prime
    branch P is prime and this fraction ring is a field. The type itself is
    defined for all ideals, so no extra prime instance is silently assumed. PASS.
18. There exists a commutative D-algebra factor F: `∃ (F : CommRingCat.{v})
    (A : Algebra D F), ...`. The category object supplies the commutative ring,
    with its D-algebra structure explicitly bound. PASS.
19. There is a D-algebra equivalence D' to E times F: the second `∃ e :
    @AlgEquiv D ...`. Its target structure is explicitly `RingHom.toAlgebra`
    of the product of the quotient/integral-closure map and `algebraMap D F`.
    In particular the E structure is the quotient structure, not an unrelated
    algebra instance. PASS.
20. The first projection restricts on D to D to D/P to E: the final `∀ d`,
    applying `.1` to `e (algebraMap D D' d)`, equals the canonical map from
    the quotient of d. This is exactly the node's required compatibility,
    even though it also follows from the specified D-algebra structures. PASS.

Dependency inspection: opened all six statement dependency records. Read the
actual signatures and definitions of `IsUniversallyCatenary`, `integralClosure`,
`Module.Finite`, `IsNoetherianRing`, `Algebra.WeaklyEtale`, `TensorProduct`, and
`Algebra.TensorProduct.rightAlgebra`, and the locality/minimal-prime interfaces.
The recorded definitions suffice. There are no new nodes, dependency repair
modules, hollow definitions, file-local instances, private notions, or extra
hypotheses. The single postponed theorem remains `weaklyEtale_normalization_tensor`.

Edge cases: C and D cannot be the zero ring, since the source's local rings have
one maximal ideal and `IsLocalRing` includes nontriviality. Likewise a quotient
by a minimal prime is nonzero. These correct the earlier report's suggestions
that zero D and a zero prime quotient were cases of this statement. No domain
assumption is placed on D; zero divisors and several minimal primes are covered.
For a single minimal prime the complementary F is the empty product, i.e. the
zero ring, which is permitted by `CommRingCat` and `Algebra D F`. The
Noetherian nonzero target has a nonempty finite set of minimal primes, so an
empty set of minimal primes is outside these hypotheses. No characteristic,
positive dimension, n>0, field base, or chosen number of factors is imposed.
The identity map C to C and the case where C is a field are included.
Universes u and v are independent. The tensor has universe max(u,v); its
AlgEquiv to a normalization in v imposes no equality on universes. F may live
in v because it can be constructed as a finite product of normalizations of
quotients of D, all living in v. No independent smaller universe is used for
test algebras or primes.

Independent searches, using wording different from the worker's:

- `msearch.py ... leanfinder "weakly etale base extension normalization total
  quotient reduced local ring"`: eight etale/localization results, no exact match.
- `msearch.py ... loogle '"WeaklyEtale", "integralClosure"'`: zero hits.
- `msearch.py ... grep 'normaliz.*(base|tensor)|integralClosure.*(etale|Etale)'
  RingTheory`: four smooth/standard-etale integral-closure results, no exact match.
- `msearch.py ... leansearch "Integral closure in the total fraction ring is the
  tensor product with a normalization for a weakly etale algebra"`: integral
  closure definitions and the tensor comparison/injectivity/localization results,
  no exact weakly-etale normalization and component decomposition statement.
- `rg` over Mathlib RingTheory, upstream WeilConjectures, project lean/Sheaf,
  and the DAG with normalization, integralClosure, weak-etale, comparison and
  tensor variants: no exact statement already exists. Opened Mathlib's
  `TensorProduct.toIntegralClosure` and its injectivity, localization and smooth
  bijectivity interfaces: they do not supply this full statement. Also opened
  the existing normal-localization and total-fraction decomposition modules;
  those supply different results or proof ingredients, not a duplicate of this item.

Repairs: made the canonical tensor equivalence's fraction-clearing normalization
explicit; replaced the short statement-only docstring with all ten proof steps,
including every dependency used by those steps; added the missing non-public
imports for all recorded proof dependencies with known modules. Kept every
hypothesis, the minimal-prime product clause, namespace conventions and the
node's mathematical statement. No §1(C) statement correction is needed, hence
no `statement_change` or citer audit applies. The node's `lean.statement` is
verbatim the repaired signature. Checked all binders and universe variables
by eye; all Lean lines are at most 100 characters. Final delivered module
compiled through scompile.py, both sandbox and library paths, without errors
or warnings. The theorem proof remains `sorry`, as stage 2 requires.
