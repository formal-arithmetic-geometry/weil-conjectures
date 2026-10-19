## Worker report

The module `Sheaf.RingTheory.DvrNormValuationSum` states
`IsDiscreteValuationRing.norm_valuation_sum`, with exactly one `sorry` and no new definitions.
The statement is the DVR specialization of Stacks Algebra Tag 02MJ,
`lemma-finite-extension-dim-1` (read in `literature/stacks-project/algebra.tex`,
lines 30037–30083). Its proof is included step by step in the theorem docstring:
reduce a fraction to numerator and denominator, compute the weighted local lengths,
push these lengths down to A, and identify the length with the order of the determinant norm.
Second-reader update: the current node has six proof steps and twelve proof dependencies.
The docstring now follows those six steps, and the available Mathlib proof-dependency
modules are imported. The two currently unstated proof lemmas are identified below.

Hypothesis and clause correspondence:

- A DVR: `(A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]`.
- Its fraction field K: `(K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]`.
  The residue field k is represented canonically, rather than chosen separately:
  `A ⧸ IsLocalRing.maximalIdeal A`.
- B a commutative domain containing A and finite as an A-module:
  `(B : Type w) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]`.
  Injectivity of the inclusion follows from the two compatible towers into L:
  A → K → L is injective, and A → B → L is the same map.
- L the fraction field of B and a finite extension of K through this inclusion:
  `(L : Type z) [Field L] [Algebra B L] [IsFractionRing B L]`,
  `[Algebra K L] [FiniteDimensional K L] [Algebra A L]`,
  `[IsScalarTower A K L] [IsScalarTower A B L]`.
  These scalar towers express compatibility of the given inclusions, not another
  finiteness, separability, or normality condition.
- X the finite set of all maximal ideals: `[Fintype (MaximalSpectrum B)]`.
  Fintype supplies the finite enumeration used by the sum; its order is immaterial.
- Every maximal ideal contracts to the maximal ideal of A:
  `hcontract : ∀ q : MaximalSpectrum B, q.asIdeal.under A = IsLocalRing.maximalIdeal A`.
- Every B_q is a DVR:
  `[∀ q : MaximalSpectrum B, IsDiscreteValuationRing (Localization.AtPrime q.asIdeal)]`.
- Every residue degree is finite:
  `[∀ q : MaximalSpectrum B, Module.Finite (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal)]`.
  Because q is maximal and `hcontract` identifies its contraction with m_A,
  these quotients are fields and this is exactly finite-dimensionality over k.
  Mathlib's quotient algebra is the canonical one induced by A → B.
- Normalized valuation v_R: `WithZero.log (Ring.ordFrac R x)`.
  `Ring.ordFrac_irreducible` sends a uniformizer to `WithZero.exp 1`, and
  `WithZero.log_exp` gives 1; units have value 0 by `Ring.ordFrac_of_isUnit`.
  Multiplication and inverses then give exactly the exponent r in u t^r.
  This also agrees with the existing project convention `-WithZero.log` of the
  maximal-ideal adic valuation, by `Ring.ordFrac_eq_valuation_inv`.
- Norm: `Algebra.norm K (y : L)`, definitionally
  `LinearMap.det (Algebra.lmul K L (y : L))` by `Algebra.norm_apply`.
- Every nonzero y: `(y : Lˣ)`. Units of a field are precisely its nonzero elements.
- The asserted integer equality is the final equality of the two logarithmic orders.
  The coefficient is `(Module.finrank (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal) : ℤ)`,
  precisely f_q through the contraction equality. The sum runs over every maximal ideal.
- Evaluation of y in B_q's fraction field uses the canonical B-algebra equivalence
  `IsLocalization.algEquiv (nonZeroDivisors B) L (FractionRing B)`.
  Mathlib's `Localization.LocalizationLocalization` supplies the canonical
  `Algebra (Localization.AtPrime q.asIdeal) (FractionRing B)` and fraction-ring instance.
  Thus this evaluates the original y under the canonical identification; no arbitrary
  field embedding or extra local-algebra hypothesis is introduced.

Dependency interfaces read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` from
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (publicly imported through
  `Mathlib.RingTheory.OrderOfVanishing.Noetherian`), the local nonfield PID class.
- `def-weil-finitely-generated-module`: `Module.Finite` from
  `Mathlib.RingTheory.Finiteness.Defs` (transitively public); top submodule finitely generated.
- `def-pc-field-extension`: `Algebra` from `Mathlib.Algebra.Algebra.Defs`
  (transitively public), with fields K and L.
- `def-weil-vector-space-dimension`: `Module.finrank` from
  `Mathlib.LinearAlgebra.Dimension.Finrank` (transitively public), used for residue degrees.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic` (transitively public), used for B_q.
  The node's residue/fibre definitions are not privately redefined; maximal residue
  fields are written as the canonically isomorphic quotient fields B/q and A/m_A.
- `def-weil-endomorphism-determinant`: `LinearMap.det` from
  `Mathlib.LinearAlgebra.Determinant` (publicly imported through
  `Mathlib.RingTheory.Norm.Defs`), used by the actual definition of `Algebra.norm`.

Additional existing Mathlib APIs used: `Ring.ordFrac` and its DVR normalization from
`Mathlib.RingTheory.OrderOfVanishing.Noetherian`; `MaximalSpectrum` from
`Mathlib.RingTheory.Spectrum.Maximal.Defs`; `Ideal.under` and canonical quotient
algebras from `Mathlib.RingTheory.Ideal.Over`; `IsLocalization.algEquiv` and the
localized fraction-field instance from
`Mathlib.RingTheory.Localization.LocalizationLocalization`.

Edge cases checked: y=0 is intentionally excluded by Lˣ; y=1 gives 0=0;
units of B give zero local valuations; denominators and negative powers retain
integer signs (no natural-number truncation); B=A yields the single-place identity.
An empty maximal spectrum is impossible for the domain B, and is not artificially
assumed nonempty. Arbitrary residue characteristic and inseparable finite extensions
are covered: there are no characteristic or separability assumptions. All four
underlying type universes are independent and explicitly bound. Norm of y is nonzero
because `Algebra.norm` maps units to units, so `WithZero.log` never masks a zero value.

Existing-statement searches (Q116 msearch wrapper, results also in sandbox searches.jsonl):

- LeanFinder, “The valuation of a field norm equals the sum of local normalized valuations
  weighted by residue field degrees”: 8 hits, mainly number-field finite-place norm
  definitions, the number-field product formula, and `Valued.norm_def`; no general
  semilocal norm-order statement.
- LeanSearch, “The valuation of the norm of an element of a finite fraction field extension
  is the sum of its local valuations weighted by residue field degrees”: 8 hits,
  `NormedField.v_eq_valuation`, `NormedField.valuation_apply`, `Valued.norm`,
  number-field norm definitions, `ValuationRing.valuation`, and completion compatibility;
  no match to this statement.
- Loogle, `Ring.ordFrac, Algebra.norm`: 0 hits.
- Mathlib grep, `ordFrac.*norm|norm.*ordFrac`, RingTheory: 0 hits.
- `rg` of `ordFrac.*norm|norm.*ordFrac` in WeilConjectures and lean/Sheaf: no hits.
- `grep -rn` of the node id in WeilConjectures: no hits.
- `rg` of `norm_valuation_sum` in Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json: no hits, so the declaration name is available.
- Read the actual Mathlib definitions of the dependencies and the normalization lemmas;
  the available norm and order APIs express the notions, but no existing declaration
  gives this weighted sum for arbitrary finite extensions.

Validation: scompile.py compiled the delivered module successfully both as sandbox and
library module, with no errors or warnings. No statement correction, dependency repair,
new node, or STATEMENT-DISPUTED flag was necessary.


## Second reading by Q116

I independently read the sandbox node and module, Stacks `algebra.tex`
`lemma-finite-extension-dim-1` (Tag 02MJ, lines 30037–30083), its signed
lattice-distance input (Tags 02MF/02MG/02MI, lines 29840–30035), and
`lemma-pushdown-module` (Tag 02M0, lines 12602–12645). The source assumes
only a Noetherian local domain of dimension one and a finite extension of domains;
our node explicitly specializes both the base and the localizations to DVRs.
The source has no standing separability, characteristic, Galois, henselian,
completeness, or normal-closure hypothesis. There is no repair note for this item.

Object/hypothesis/conclusion checklist, in the order of the node:

1. **Base ring A is a DVR.** `(A : Type u) [CommRing A] [IsDomain A]
   [IsDiscreteValuationRing A]`. PASS. I opened the recorded dependency
   `def-sc-discrete-valuation-ring` and Mathlib `DiscreteValuationRing/Basic.lean:58`:
   the class extends principal-ideal-ring and local-ring structures and says the
   maximal ideal is nonzero. Thus it is the same nonfield local PID as the node;
   its Noetherian and dimension-one properties need no added hypotheses.
2. **K is A's fraction field.** `(K : Type v) [Field K] [Algebra A K]
   [IsFractionRing A K]`. PASS. The fraction-ring structure gives the intended
   injective map A → K, not an arbitrary extension field.
3. **k is A's residue field.** No independent choice of a field k is required:
   the formula uses `A ⧸ q.asIdeal.under A`, which `hcontract` identifies with
   `A ⧸ IsLocalRing.maximalIdeal A`. PASS. This quotient is a field. It represents
   the same canonical residue field, with no hypothesis on its cardinality.
4. **B is a commutative domain containing A and finite as an A-module.**
   `(B : Type w) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]`.
   PASS. `Module.Finite`, the declaration of `def-weil-finitely-generated-module`
   in `RingTheory/Finiteness/Defs.lean:117`, says the top submodule is finitely
   generated; it does not mean a finite underlying set. Injectivity A → B follows
   from compatibility with A → K → L and the injectivity of A → K and K → L.
5. **L is Frac(B), finite over K through this inclusion.** `(L : Type z)
   [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
   [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L]
   [IsScalarTower A B L]`. PASS. The two towers identify the composites A → L;
   they impose precisely the compatibility specified by “through this inclusion”.
   I opened `def-pc-field-extension` and `Algebra/Algebra/Defs.lean:95`:
   `Algebra K L` is the ring homomorphism of the field extension. FiniteDimensional
   is finite generation over a field. The redundant-looking A-algebra on L is
   canonical data that every such compatible extension supplies, not extra mathematics.
6. **X is the finite set of all maximal ideals of B.**
   `[Fintype (MaximalSpectrum B)]`. PASS. I opened
   `Spectrum/Maximal/Defs.lean`: its elements are ideals with a maximality proof,
   so the sum enumerates every maximal ideal exactly once. Fintype is an
   enumeration of the asserted finite set and makes no ordering assumption.
7. **Every maximal ideal contracts to m_A.**
   `hcontract : ∀ q : MaximalSpectrum B,
   q.asIdeal.under A = IsLocalRing.maximalIdeal A`. PASS.
   `under` is contraction along the given algebra map, not an independently
   supplied prime of A.
8. **Every B_q is a DVR.** `[∀ q : MaximalSpectrum B,
   IsDiscreteValuationRing (Localization.AtPrime q.asIdeal)]`. PASS. I opened
   `def-weil-pbc-localization-at-prime` and `Localization/AtPrime/Basic.lean:57`:
   it is localization at the complement of the prime, as the node requires.
9. **Each residue degree f_q is finite.** `[∀ q : MaximalSpectrum B,
   Module.Finite (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal)]`. PASS. By item 7,
   the base quotient is the residue field k, so module finiteness is precisely
   finite field-extension degree. `Ideal/Over.lean:287` supplies the canonical
   quotient algebra induced by A → B. No arbitrary residue embedding is used.
10. **Normalized valuation on the fraction field of any DVR.**
    `WithZero.log (Ring.ordFrac R x)`. PASS. I read
    `OrderOfVanishing/Basic.lean:324` and
    `OrderOfVanishing/Noetherian.lean:155–190`:
    `ordFrac` is multiplicative on fractions, units have value one, and a
    uniformizer has value `WithZero.exp 1`. Applying log therefore sends
    `u t^r` to r for all integer r, with the positive uniformizer convention.
    This is an existing Mathlib construction, not a private definition.
11. **Norm is the determinant of multiplication by y on L over K.**
    `Algebra.norm K (y : L)`. PASS. I opened the determinant dependency
    `def-weil-endomorphism-determinant` and `Norm/Defs.lean:61–64`:
    `Algebra.norm_apply` is definitionally `LinearMap.det (Algebra.lmul K L y)`.
    The finite-dimensional field-extension assumptions ensure this is the actual
    determinant rather than the fallback used for modules without a finite basis.
12. **Every nonzero y in L, after all ring and field data are fixed.**
    `(y : Lˣ)`. PASS. For a field this is equivalent to quantifying over all
    nonzero elements, with no integral-element or unit-of-B restriction.
13. **The equality, both sides, coefficient, and canonical evaluation.**
    The left side is `WithZero.log (Ring.ordFrac A (Algebra.norm K (y : L)))`.
    The right side sums over `q : MaximalSpectrum B`, with coefficient
    `(Module.finrank (A ⧸ q.asIdeal.under A) (B ⧸ q.asIdeal) : ℤ)` and factor
    `WithZero.log (Ring.ordFrac (Localization.AtPrime q.asIdeal) (... y ...))`.
    PASS. I opened `def-weil-vector-space-dimension` and `Dimension/Finrank.lean:62`:
    finite rank over this field is exactly f_q. The integer cast preserves the
    integer equality without truncation. The argument `... y ...` is
    `IsLocalization.algEquiv (nonZeroDivisors B) L (FractionRing B) (y : L)`;
    I read its definition in `Localization/Basic.lean:172`, which fixes B and
    sends a fraction b/s to the identical fraction. The canonical instance at
    `Localization/LocalizationLocalization.lean:291–294` makes `FractionRing B`
    the fraction field of B_q. Thus it evaluates the original y, not a different
    element or a freely chosen local embedding. All clauses match, with none added.

Edge cases: B and A cannot be zero rings since they are domains; they cannot
have an empty maximal spectrum, so no valid empty-index case is lost. An arbitrary
Fintype enumeration changes no sum. A field B would force the nonfield DVR A to
be a field under the finite integral inclusion, so that case is already impossible
mathematically. The formula includes y = 1, all units of B, fractions with
negative valuations, and the identity extension B = A. The local length calculation
in the docstring explicitly includes n = 0 and r < 0. y = 0 is excluded by the
node itself; norm of a nonzero field element is nonzero, so log at zero never
creates a spurious equality. Arbitrary residue characteristic, including positive
characteristic and inseparable finite extensions, is allowed. Universes u, v, w,
z are independent and explicitly bound; quotient/localization types impose no
universe equality. There are no scheme objects to which an empty-scheme case applies.

Independent searches, using different phrases from the worker (recorded by
`msearch.py` in `searches.jsonl`):

- LeanFinder: “The order of vanishing of the determinant of multiplication is a
  sum of residue degrees times local orders in a finite algebra over a discrete
  valuation ring”. Eight hits: ramification-index/degree theorems, elliptic-curve
  discriminant valuations, Kummer–Dedekind, and number-field zeta residue. None is
  this norm formula for every nonzero element of an arbitrary finite extension.
- LeanSearch: “For a semilocal finite extension of a DVR the additive order of a
  field norm is the sum of local orders weighted by residue field degrees”.
  Eight hits: finite-field norm powers, the sum of ramification times inertia
  degrees, analytic invariant extensions, and finite-place absolute norms.
  None has this statement; the ramification-degree identity concerns base
  uniformizers rather than arbitrary y in L.
- Loogle: `"norm", "ord"`. Twelve hits concerning tactic normalization and
  order-theoretic normal functions; no field norm/order formula.
- Direct `rg` throughout pinned Mathlib for
  `ordFrac.*(norm|det)|(norm|det).*ordFrac|valuation.*intNorm|intNorm.*valuation`:
  no hits. Searches of upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the proposed declaration name and node id
  found no existing declaration. Broader norm/order and norm/valuation searches
  in the ring/field portions found only analytic p-adic norm material and
  unrelated normalization/valuation discussions, not this weighted identity.

No new definition nodes, dependency repair modules, statement correction, or
hollow definition are present. The only theorem is
`IsDiscreteValuationRing.norm_valuation_sum`, whose proof remains exactly `sorry`.
The lean.statement record is checked byte-for-byte against its unchanged signature.
Every binder and universe is explicit. All lines of the module are at most 100 columns.

Mismatches repaired: the worker report's assertion that proof/proof_deps were empty
was stale against the current six-step node. The earlier docstring described the
shorter numerator/denominator proof from Stacks, omitting the node's lattice-spanning,
signed-distance, localization-intersection, and negative-exponent steps. Replaced
only that proof paragraph with the six-step route, naming its DAG inputs and sources.
Added ordinary proof imports for the stated Mathlib dependencies: finite-dimensional
spaces, module length, localized modules and exactness, PID Noetherianity and DVR
power factorization. The two proof-only nodes `lem-exc-dvr-lattice-distance-determinant`
and `lem-exc-semilocal-restriction-length` currently have no recorded declaration;
they are cited in the docstring and need no import yet. They are not needed to type
this stage-2 statement. No mathematical statement or node field was changed.

Second-reader validation: `scompile.py Q116 lem-exc-dvr-norm-valuation-sum`
compiled the sole delivered file as both sandbox and library module (1.5 s and
1.6 s), with no errors or warnings.
