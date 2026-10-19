## Worker report

`lean/Sheaf/FieldTheory/FiniteTameCharacterTower.lean` states
`IsDiscreteValuationRing.finite_tame_character_tower`. Its only theorem proof is `sorry`.
No definitions, additional nodes, dependency repairs, or changes to the mathematical
statement are needed. The node copy differs from the shared node only in `lean`.
I read Stacks `more-algebra.tex`, Lemma `lemma-compare-inertia` (0BU7) and Remark
`remark-canonical-inertia-character` (0BU8), together with the full declaration and
proof docstring of the recorded finite-DVR tame-inertia dependency.

The earlier sandbox version compiled but omitted the formula identifying its existential
raw characters as the actual uniformizer characters. I added the formula for every local
uniformizer, using precisely the interface of the recorded dependency. I also made the
canonical-kernel equalities explicit, removed the unnecessary `FiniteDimensional L M` and
`IsGalois L M` assumptions, replaced all local `let` aliases by explicit Mathlib terms,
completed the ten-step proof docstring, and filled in the required `branch` and `existing`
fields. The former placeholder second-reading section was removed: the independent second
reader must write that section, not the statement worker.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A is a DVR | `A : Type u`, `[CommRing A] [IsDomain A] [IsDiscreteValuationRing A]`. This is Mathlib's local PID which is not a field. |
| K is its fraction field | `K : Type v`, `[Field K] [Algebra A K] [IsFractionRing A K]`. |
| M/L/K is a tower | The field and algebra instances on `L : Type w`, `M : Type z`, with `IsScalarTower A K L`, `A K M`, `A L M`, and `K L M`, specify compatible inclusions. No equality between the four universes is imposed. |
| L/K and M/K are finite Galois | `[FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]`; no separate M/L finiteness or Galois hypothesis. |
| Positive residue characteristic p | `p : ℕ`, `[Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]`. Positive field characteristic is necessarily prime. |
| B_X is the integral closure | The actual Mathlib subalgebras `integralClosure A L`, `integralClosure A M`, with their induced integral-closure Galois actions. |
| Choose a maximal ideal upstairs | `𝔫M : Ideal (integralClosure A M)` and `[𝔫M.IsMaximal]`, universally quantified. |
| Put n_L = n_M cap B_L | The initial conclusion proves maximality of `Ideal.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom 𝔫M`. The rest is for every maximal `𝔫L` with `hcomp` equating it to this contraction. Thus maximality downstairs is supplied, not an extra restriction. |
| The normalized local valuations and e_X | The witnesses `hCL`, `hCM` are the local DVR structures; `eL`, `eM` satisfy `@addVal ... hCX (algebraMap A ... πA) = (eX : ℕ∞)` for every irreducible base uniformizer. `addVal` assigns 1 to a local uniformizer. |
| Canonical inclusions of the local rings into the fields | `jL`, `jM` extend the actual integral-closure inclusions on every `b`. This characterizes the localization embeddings uniquely and supplies the evaluation used in the raw character formula. These are the `j` maps of the dependency, not arbitrary replacements. |
| D_X stabilizes the chosen ideal | `MulAction.stabilizer Gal(L/K) 𝔫L` and its upper analogue. |
| I_X acts trivially on the residue field | `𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L)` and its upper analogue, the same Mathlib groups as in the dependency. |
| χ_X is the uniformizer character with codomain μ_eX | `χL`, `χM` are monoid homomorphisms to `rootsOfUnity eX 𝔫X.ResidueField`. For every irreducible local `t` and every inertia element `σ`, a unit `a` satisfies `jX a = σ.1.1 (jX t) / jX t`, and the residue of `a` is the underlying field value of `χX σ`. This is exactly the dependency's formula, including independence of the uniformizer. |
| P_X is ker χ_X | `χL.ker`, `χM.ker`, not unrelated subgroups or unconstrained groups. |
| Write e_X = q_X n_X with q_X a p-power and n_X prime to p | Witnesses `qL nL qM nM : ℕ`, the clauses `∃ aX, qX = p ^ aX`, `Nat.Coprime nX p`, and `eX = qX * nX`. These characterize the same prime-to-p factors uniquely. |
| Restriction surjects on D | `rD` is a surjective group homomorphism whose underlying automorphism is `AlgEquiv.restrictNormalHom L σ.1` for every element. |
| Restriction surjects on I | `rI` is surjective and its underlying Galois automorphism equals `AlgEquiv.restrictNormalHom L σ.1.1`. |
| Restriction surjects on P | `rP : χM.ker →* χL.ker` is surjective and `(rP σ).1 = rI σ.1`, so it is exactly restriction on the wild kernels. |
| n_L divides n_M | `nL ∣ nM`. |
| Set χ_X,can = χ_X ^ q_X with codomain μ_nX | The witnesses `χLcan`, `χMcan` have codomains `rootsOfUnity nX 𝔫X.ResidueField`, and their values as units are the `qX`-th powers of `χX`. |
| Each canonical character is surjective | `Function.Surjective χLcan ∧ Function.Surjective χMcan`. |
| Each canonical character has kernel P_X | `χLcan.ker = χL.ker ∧ χMcan.ker = χM.ker`. |
| Natural residue-field embedding | `Ideal.ResidueField.map 𝔫L 𝔫M (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom hcomp`, mapped on units by `Units.map`. It is the canonical embedding induced by contraction, rather than an existential field map. |
| Displayed identity for every σ in I_M | The final universal equality maps `χLcan (rI σ)` by that residue embedding and equates it to `(χMcan σ : 𝔫M.ResidueFieldˣ) ^ (nM / nL)`. |
| The displayed power map is the transition on tame quotients | The restriction identities, canonical-character surjectivity, kernel equalities, and final equality together identify both quotients with the stated roots of unity and determine their transition on every representative. Surjectivity of `rI` and of the lower character also implies surjectivity of that transition. |

Dependencies used, read from their recorded declarations:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, including
  `irreducible_iff_uniformizer` and the normalized `addVal` interface.
- `def-weil-pbc-integral-closure`: `integralClosure` in
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, with carrier `IsIntegral A x`.
- `lem-exc-finite-dvr-tame-inertia`:
  `IsDiscreteValuationRing.finite_normalization_tame_inertia` in
  `Sheaf.FieldTheory.FiniteDVRTameInertia`. Its existential local embeddings, normalized
  indices, and uniformizer-character formula give exactly the objects used here.

The finite-inertia statement is a theorem, not a separately defined character object;
there is no dependency definition to apply as a term. This module imports that theorem's
module and uses its identical character characterization, so its characters are the same
unique objects. It introduces no duplicate notion. Mathlib supplies `Ideal.inertia`,
`MulAction.stabilizer`, `rootsOfUnity`, `AlgEquiv.restrictNormalHom`, the canonical
integral-closure inclusion map, and `Ideal.ResidueField.map`. Proof-only imports provide
`integralClosure.isFractionRing_of_algebraic`, normality of the integral closure,
`AlgEquiv.restrictNormalHom_surjective`, `Algebra.isInvariant_of_isGalois`,
`Algebra.IsInvariant.exists_smul_of_under_eq`, and
`IsFractionRing.stabilizerHom_surjective`, matching the recorded Mathlib proof dependencies.

Edge cases checked mathematically before the repair:

- `M = L`: the contracted prime, restriction maps, indices and uniquely characterized
  characters coincide; `nM / nL = 1`.
- `L = K`: the lower inertia and tame quotient are trivial, `eL = nL = 1`; the final
  formula says that an nM-th root raised to nM is 1.
- Unramified extensions: `eX = 1`, so `qX = nX = 1` and the tame characters are trivial.
- Purely wild extensions: `nX = 1` is allowed, and canonical kernels are all inertia.
- Trivial wild inertia: the kernel has the identity element and restriction still has
  its usual meaning; no nontriviality hypothesis was introduced.
- `p = 2` and odd primes: q-powers act bijectively on prime-to-p roots in both cases.
- No perfectness or separability assumption on residue extensions is made. Inseparable
  residue extensions remain covered; no claim `|I| = e` was introduced.
- There is no e=0 valuation case for a base uniformizer in a finite local extension.
  The characterizations force positive e. In particular `Nat.Coprime nX p` with p prime
  excludes `nX = 0`, so the division exponent is the genuine integer ratio.

Searches repeated in this attempt (through `msearch.py NC
lem-exc-finite-tame-character-tower`):

- LeanFinder, query `Restriction maps wild inertia surjectively in a finite Galois tower
  and canonical tame uniformizer characters are compatible with the ramification index
  prime to p power map`: 8 hits, including `Ideal.ramificationIdxIn_mul_ramificationIdxIn`,
  `Ideal.inertiaDegIn_mul_inertiaDegIn`, and `Ideal.card_inertia_eq_ramificationIdxIn`;
  none states the raw or scaled uniformizer-character compatibility and wild surjectivity.
- Loogle, query `AlgEquiv.restrictNormalHom, Ideal.inertia, rootsOfUnity`: 0 hits.
- Mathlib grep, query `wild.*inertia|tame.*character|ramificationIdx.*mul` under `RingTheory`:
  6 hits on ramification-index infrastructure and relative norms; no target match.
- LeanSearch, query `Restriction in a finite Galois tower of discretely valued fields
  surjects on wild inertia and scaled tame uniformizer characters commute with power maps`:
  8 hits, including `AlgEquiv.restrictNormalHom_surjective`, restriction-composition lemmas,
  and inertia degrees; no theorem about these canonical characters.
- Direct `rg -n` for `finite_tame_character_tower|tame.*character|wild.*inertia|canonical.*inertia`
  in `WeilConjectures` and `lean/Sheaf`: no upstream match; the side project has only
  the finite-DVR dependency and a reference to this node in the henselian sequence proof
  docstring. Direct Mathlib search for the same phrases found no matching statement.
- `grep -rn 'lem-exc-finite-tame-character-tower' WeilConjectures`: no upstream declaration
  attached to this node. The earlier attempt's search log is retained in the sandbox.

No mathematical node fault or `STATEMENT-DISPUTED` issue was found. No statement correction
was made. Every variable and universe is explicitly bound and auto-implicits are disabled.
The repaired sole module compiled cleanly through `scompile.py`, with no errors or warnings.
The required `deliver2.py ... --no-push` is the final validation; the second reader alone
writes the independent reading and pushes the delivery.

## Second reading by NC

I read the current shared node, the sandbox node and sole module independently of
the worker's correspondence table. I read Stacks `more-algebra.tex`, lines
33620–33726: Lemma `lemma-compare-inertia` (0BU7) and Remark
`remark-canonical-inertia-character` (0BU8); the tag table confirms both labels.
Their hypotheses are a DVR and a finite Galois tower, with the chosen upper maximal
ideal and its contraction. They impose neither completeness nor henselianity nor
perfect residue fields. The node explicitly restricts to positive residue
characteristic. The Lean says precisely this specialization of the source.

My object/hypothesis/conclusion inventory and independent correspondence check:

| Node item | Lean rendering and verdict |
| --- | --- |
| DVR A, fraction field K | `A : Type u`, `CommRing`, `IsDomain`, `IsDiscreteValuationRing`; `K : Type v`, `Field`, `Algebra A K`, `IsFractionRing A K`. Exact. I opened Mathlib's DVR class: local principal ideal domain with nonzero maximal ideal. |
| Positive residue characteristic p | `p : ℕ`, `Fact p.Prime`, `CharP (IsLocalRing.ResidueField A) p`. Exact: a field's positive characteristic is prime, so primality adds no restriction. |
| Compatible tower M/L/K | The algebras and four `IsScalarTower` instances specify the compatible inclusions, including the induced A-algebras. Exact; these are tower coherence, not extra mathematical hypotheses. |
| Finite Galois L/K and M/K | `FiniteDimensional K L`, `FiniteDimensional K M`, `IsGalois K L`, `IsGalois K M`. Exact; no additional M/L hypothesis. |
| B_L and B_M | Actual `integralClosure A L` and `integralClosure A M`. Exact; Mathlib's carrier is `IsIntegral A x`. |
| Chosen upper maximal ideal | `(𝔫M : Ideal (integralClosure A M)) [𝔫M.IsMaximal]`. Exact, universally quantified. |
| Lower ideal is the contraction | The first conjunct proves maximality of `Ideal.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom 𝔫M`. The following `∀ 𝔫L [𝔫L.IsMaximal] (hcomp : 𝔫L = ...)` uses exactly this contraction. Exact: the preceding maximality clause supplies the instance, so this does not assume maximality instead of proving it. |
| Local DVRs and normalized indices | `hCL`, `hCM` are DVR structures on the actual `Localization.AtPrime` rings; the formulas for every irreducible `πA` use `@addVal ... hCL` and `@addVal ... hCM` and `(eX : ℕ∞)`. Exact: Mathlib's `irreducible_iff_uniformizer` and `addVal_uniformizer` give precisely normalization one. |
| View local rings inside L and M | `jL`, `jM` are ring maps whose values on every integral-closure element are its actual field inclusion. Exact: localization's universal property determines these maps uniquely; denominators map to nonzero field elements. These are not arbitrary embeddings. |
| Decomposition groups D_X | `MulAction.stabilizer Gal(X/K) 𝔫X`, with the integral-closure Galois action from the dependency. Exact. |
| Inertia groups I_X | `𝔫X.inertia (MulAction.stabilizer Gal(X/K) 𝔫X)`. Exact: inertia fixes every element modulo the ideal, hence fixes the fraction field of the quotient, which is `𝔫X.ResidueField`. |
| Raw uniformizer characters | `χX : I_X →* rootsOfUnity eX 𝔫X.ResidueField`; for every local irreducible `t` and inertia element `σ`, a unit `a` satisfies `jX a = σ.1.1 (jX t) / jX t` and `χX σ` reduces to the residue of `a`. Exact, including independence of t; I compared the full formula with `finite_normalization_tame_inertia`, not merely its name. |
| Wild groups P_X | `χX.ker`. Exact, with no unrelated subgroup variable. |
| e_X = q_X n_X, q_X a p-power, n_X prime to p | Existential natural numbers, `(∃ aX, qX = p ^ aX)`, `Nat.Coprime nX p`, `eX = qX * nX`. Exact; these conditions uniquely specify the two factors. |
| Restriction surjects on D | `rD : D_M →* D_L`, `Function.Surjective rD`, and equality of its underlying automorphism with `AlgEquiv.restrictNormalHom L σ.1`. Exact; the equality fixes the homomorphism to restriction. |
| Restriction surjects on I | `rI : I_M →* I_L`, surjectivity and the corresponding equality on underlying automorphisms. Exact; also agrees with rD on inertia by subtype extensionality. |
| Restriction surjects on P | `rP : χM.ker →* χL.ker`, surjectivity, and `(rP σ).1 = rI σ.1`. Exact, including compatibility with the already fixed restriction. |
| n_L divides n_M | `nL ∣ nM`. Exact. |
| Scaled canonical characters | `χXcan : I_X →* rootsOfUnity nX 𝔫X.ResidueField`, with their values as units equal to `(χX σ : 𝔫X.ResidueFieldˣ) ^ qX`. Exact, fixing the scaling and its codomain. |
| Surjectivity and wild kernels | `Function.Surjective χLcan`, `Function.Surjective χMcan`, `χLcan.ker = χL.ker`, `χMcan.ker = χM.ker`. Every clause is present. |
| Natural residue embedding | `Ideal.ResidueField.map 𝔫L 𝔫M (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom hcomp`, applied to units by `Units.map`. Exact; I opened this API: it is the map on residues induced by the canonical localization map. |
| Displayed identity for every upper inertia element | Final `∀ σ : I_M`, equality of the embedded `χLcan (rI σ)` with `(χMcan σ : 𝔫M.ResidueFieldˣ) ^ (nM / nL)`. Exact exponent, direction, codomain and quantifier. |
| This power map is the transition on tame quotients | Surjective characters with these kernels identify I_X/P_X with the root groups; the equality on every representative gives the induced transition, and surjective rI gives its surjectivity. Thus the final prose clause is fully expressed by these clauses, with no missing quotient choice. |

Quantifier review: the ring, fraction field, tower, characteristic and upper maximal
ideal are arbitrary. The contracted lower ideal is fixed by `hcomp`. The local DVR
structures, indices and characters are existential presentations of uniquely
characterized objects, rather than extra assumptions or selectable substitute
characters. Restriction and the canonical characters are fixed by their formulas.
No hypothesis is hollow, no extra separability of residue extensions is assumed,
and no existential witness can make a character formula vacuous: every local DVR
has an irreducible uniformizer.

Dependency review (H4/H12/H13): I opened the three statement dependency records.
`def-sc-discrete-valuation-ring` matches Mathlib's class and uniformizer convention;
`def-weil-pbc-integral-closure` records Mathlib's actual `integralClosure`.
I read all of `Sheaf.FieldTheory.FiniteDVRTameInertia`, including its full signature
and proof docstring. Its local embeddings, valuation indices and raw-character
formula are exactly the ones used here, in independent universes. It states a
theorem characterizing characters, not a separate character definition to reuse as
data. Repeating that characterization in this theorem introduces no second
definition. Its quotient equivalence also justifies the raw-character surjectivity
used in proof steps 8 and 10. There are no new nodes or dependency repair modules
in this delivery. No repair note exists for this item. The sandbox node differs
from the shared node only in `lean`; there is no statement correction to audit.

Edge cases: M=L gives identity restrictions and nM/nL=1; L=K gives lower index
and tame group of order one. Unramified extensions allow e=q=n=1. Purely wild
extensions allow n=1 and all inertia in the character kernel. Trivial wild groups
are allowed. Both p=2 and odd primes are included, and p=0 and p=1 are correctly
excluded by the node's positive residue characteristic. Since p is prime,
`Nat.Coprime nX p` excludes nX=0; qX is positive and the valuation indices are
positive, so the natural-number division has the intended nonzero divisor. No
empty index family or scheme occurs here; the zero ring cannot be a DVR domain.
No perfectness or finite residue field is required. `u v w z` are all explicitly
bound and independent; no equality or size bound restricts the four ring/field
types.

Independent searches, using different wording from the first worker:

- LeanFinder via `msearch.py`: “In a finite normal tower of discretely valued
  fields the restriction on wild ramification groups is onto and normalized
  inertia characters respect the prime-to-characteristic ramification ratio”.
  Eight hits, including `Ideal.ramificationIdxIn_mul_ramificationIdxIn`,
  `Ideal.card_inertia_eq_ramificationIdxIn` and `ValuationSubring.inertiaSubgroup`;
  none states this character identity or the whole restriction result.
- Loogle via `msearch.py`: `rootsOfUnity, AlgEquiv.restrictNormalHom`: zero hits.
- LeanSearch via `msearch.py`: “Compatibility of ramification characters under
  restriction to a normal subfield and surjection of wild ramification groups”.
  Eight hits, headed by `AlgEquiv.restrictNormalHom` and ordinary Galois
  restriction results; no wild-character tower theorem.
- Direct `rg` in all upstream `WeilConjectures`, project `lean/Sheaf`, and Mathlib
  for `ramification character|wild.?inertia|tame.?character|scaled.?character|uniformizer.?character`,
  and separate broader inertia/ramification searches in the FieldTheory folders.
  Mathlib supplies valuation-subring inertia and ramification-index arithmetic;
  upstream supplies no match. The project's finite-DVR character and inertia-order
  theorems are inputs, not duplicate tower statements; the henselian sequence
  mentions this node only as a proof dependency. No existing declaration replaces
  this module. The search wrapper retained the search records in `searches.jsonl`.

H5/H6/H8/H9: the module defines no data and contains exactly one theorem with
`by sorry`. The source/blueprint docstrings are present, and proof steps 1–10
match the node's ten steps, including maximal contraction, restriction lifting,
uniformizer comparison, coprime-power wild lifting, and scaled-character kernels.
The imports supply the recorded statement/proof interfaces. No local notation,
private definition, file-local instance, unbound variable, hidden `let` statement
binder or line over 100 characters occurs. The stored `lean.statement` is verbatim
the theorem signature, excluding `:= by sorry`.

Mismatches found in the version supplied to this second reader: none. I made no
Lean or mathematical-node change, preserving the correct worker repair. I added
this independent reading and its search evidence. The sole delivered module was
compiled with the prescribed `scompile.py` wrapper: both sandbox and library
checks passed (2.8 and 3.7 seconds), with no errors or warnings.
