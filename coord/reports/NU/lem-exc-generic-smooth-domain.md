## Worker report

The module `Sheaf.RingTheory.GenericSmoothDomain` states
`Algebra.exists_smooth_localization_of_separable_fractionRing`. It gives the affine
form of generic smoothness: an injective finite type map of integral domains whose
canonical fraction-field extension is separable has a nonzero principal localization
of the target that is smooth over the source. The proof is `sorry`, with the complete
source-based proof route in the declaration docstring.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| commutative rings R and S | `(R : Type u) (S : Type v) [CommRing R] [CommRing S]` |
| R and S integral domains | `[IsDomain R] [IsDomain S]`; these typeclasses include the nonzero and no-zero-divisor conditions |
| R-algebra structure / ring map | `[Algebra R S]`, with the map rendered by `algebraMap R S` |
| finite type | `[Algebra.FiniteType R S]` |
| injectivity | `(hinj : Function.Injective (algebraMap R S))` |
| fraction fields and induced embedding | `FractionRing R`, `FractionRing S`, and `IsFractionRing.map ... hinj` |
| separability of the fraction-field extension | `hsep : @IsSeparableExtension ... (IsFractionRing.map ... hinj).toAlgebra` |
| nonzero principal localization | `∃ g : S, g ≠ 0 ∧ ...` |
| smooth map R → S_g | `Algebra.Smooth R (Localization.Away g)` |

The universes of R and S are independent, so the statement includes arbitrary-size
integral domains. The canonical `IsFractionRing.map` preserves the given embedding;
there is no arbitrary field map or extra compatibility hypothesis. The zero element is
excluded exactly by `g ≠ 0`; the localization at a nonzero element is therefore the
required nonempty principal open. No Noetherian, finite-presentation, or characteristic
hypothesis is added.

Dependencies inspected and used:

- `def-weil-pbc-finite-type-algebra`: Mathlib `Mathlib.RingTheory.FiniteType`,
  `Algebra.FiniteType` (`class ... where out : (⊤ : Subalgebra R A).FG`).
- `def-weil-pbc-separable-field-extension`: `Sheaf.FieldTheory.SeparableExtension`,
  `Algebra.IsSeparableExtension`; its definition quantifies over finitely generated
  intermediate fields and `Algebra.IsSeparablyGenerated`.
- `def-weil-pbc-smooth-ring-map`: Mathlib `Mathlib.RingTheory.Smooth.Basic`,
  `Algebra.Smooth`, whose fields are formal smoothness and finite presentation;
  its recorded `H1Cotangent` correspondence matches the node's smooth ring map.

Edge cases checked: R and S may have different universes; the finite type generating
set may be empty; `g` is required nonzero even when `g = 1` is the available
localization; all domains and all characteristics are allowed. The statement has no
Noetherian assumption and does not require the fraction-field extension to be finite.

Searches made on 2026-10-16 with `msearch.py NU lem-exc-generic-smooth-domain`:

- `leanfinder`, “injective finite type homomorphism of domains with separable fraction
  fields exists nonzero element target localization smooth”: eight hits, but only
  localization-preservation and finite-type tools, no generic-smoothness theorem.
- `loogle`, “Algebra.Smooth, RingHom.Smooth, FractionRing”: zero hits.
- `grep`, “IsSeparableExtension|Smooth|FractionRing” under `RingTheory/Smooth`: hits
  for smooth localization and separably generated field ingredients, no exact statement.
- `rg` over `lean/Sheaf` and the source `WeilConjectures` tree for generic smoothness,
  separable fraction-field localization, and the node id: no existing declaration
  matching this theorem. The nearby `Algebra.smoothAtPrime_bot_of_isSeparable_fractionRing`
  is the field-base ingredient and has a different conclusion.

The required `scompile.py` check compiled the module cleanly; the expected `sorry`
warning is suppressed by the project options. No statement correction or dispute was
found.

## Earlier second reading (a previous round; superseded)

I independently reread the node statement, all three dependency records and the
published source declarations. The theorem signature above preserves every hypothesis
and conclusion, uses the canonical induced fraction-field map, and compiles with the
required `scompile.py` wrapper. The recorded node Lean object now has `existing: false`
and its `statement` is the exact declaration header through the conclusion (without the
proof keyword), as required by stage 2. No correction, dependency repair, or additional
node is needed.


## Earlier second reading (a previous round; superseded)

I reread the source at Stacks Project, Algebra, Tag 07ND, Lemma 10.140.9. The
source states that for an injective finite-type map of domains, separability of
the induced fraction-field extension implies smoothness at the zero prime;
unpacking smoothness there gives a nonzero principal localization which is
smooth. The Lean statement matches this implication.

Object and hypothesis checklist:

* The source's commutative rings `R` and `S` are `(R : Type u) (S : Type v)` with
  `[CommRing R] [CommRing S]`.
* Integral-domain hypotheses are `[IsDomain R] [IsDomain S]`, including the
  required nontrivial and no-zero-divisor conditions.
* The algebra structure and map are `[Algebra R S]` and `algebraMap R S`, with
  injectivity exactly `hinj : Function.Injective (algebraMap R S)`.
* Finite type is `[Algebra.FiniteType R S]`, the recorded Mathlib
  `def-weil-pbc-finite-type-algebra` declaration.
* Fraction fields are `FractionRing R` and `FractionRing S`; the induced map is
  the canonical `IsFractionRing.map (K := FractionRing R) (L := FractionRing S)
  hinj`.
* Separability is the recorded `Algebra.IsSeparableExtension`, applied to the
  algebra structure of that canonical map in `hsep`.
* The conclusion `∃ g : S, g ≠ 0 ∧ Algebra.Smooth R
  (Localization.Away g)` renders an element outside the zero prime, its
  principal localization, and the composite ring map through the canonical
  `Algebra R` structure.

No extra Noetherian, finite-presentation, characteristic, finite-extension, or
universe-equality hypothesis occurs. Quantifier order and all conclusion clauses
agree with the node. The independent universes `u` and `v` preserve arbitrary
size rings.

Edge cases checked: the finite-type generating family may be empty; both domains
are nonzero; `g = 1` is allowed while `g = 0` is excluded; every characteristic,
including positive characteristic, is allowed; and no empty scheme or index-set
parameter is introduced.

I inspected the three dependency declarations: Mathlib `Algebra.FiniteType`,
project `Algebra.IsSeparableExtension`, and Mathlib `Algebra.Smooth`. Each gives
exactly the notion used here. Searches on 2026-10-16 used LeanFinder, Loogle,
LeanSearch, grep, and `rg` through Mathlib, the project source, and `lean/Sheaf`;
they found only localization/smoothness and field-separability ingredients, not
this theorem. The required `scompile.py` check passed cleanly with the expected
postponed proof. No mismatch, statement correction, dependency repair, or citer
break was found, and the node's `lean.statement` remains verbatim equal to the
theorem signature.

## Repair applied

The return concerns the reviewer-fix bundle layout: a repository-style
`coord/reports/NU/lem-exc-generic-smooth-domain.md` path is not accepted by
`--apply-fixes`. The repair bundle is now `scratchpad/apply-fixes/` and contains
only the three allowed root-level artifacts:

- `GenericSmoothDomain.lean`: the existing delivered module, copied verbatim.
- `lem-exc-generic-smooth-domain.lean-record.json`: the item's Lean record.
- `lem-exc-generic-smooth-domain.report.md`: this report, including the repair.

The reviewer should pass that dedicated directory to `--apply-fixes`, rather
than a directory with the repository's `coord/reports/` layout. The normal worker
delivery remains under `lean/Sheaf/`, `dag/nodes/`, and root `report.md`, as
required by `deliver2.py`. No statement correction or new node is needed.

## Second reading by NU

I read the item node, its source place (Stacks Project Algebra, Tag 07ND,
Lemma 10.140.9), the Lean module, and all three statement dependencies. Tag 07ND
assumes an injective finite type map of commutative domains and says that smoothness
at the zero prime is equivalent to separability of the induced fraction-field
extension. The node records the converse implication (separability implies
smoothness) in its principal-open form.
The following list matches every node object, hypothesis, and conclusion clause to
the Lean declaration:

* The two commutative rings are `(R : Type u)` and `(S : Type v)` with
  `[CommRing R] [CommRing S]`; `u` and `v` are independent.
* The domain assumptions are `[IsDomain R] [IsDomain S]`, which include the
  nontrivial and no-zero-divisor conditions required by the source.
* The algebra structure and ring map are `[Algebra R S]` and
  `algebraMap R S`; injectivity is exactly
  `hinj : Function.Injective (algebraMap R S)`.
* The finite-type assumption is `[Algebra.FiniteType R S]`, the exact Mathlib
  declaration recorded by `def-weil-pbc-finite-type-algebra`.
* The fraction fields are `FractionRing R` and `FractionRing S`. The displayed
  map `IsFractionRing.map (K := FractionRing R) (L := FractionRing S) hinj`
  is the canonical map induced by the given injective ring map, rather than an
  arbitrary field embedding.
* The hypothesis `hsep` applies the recorded
  `Algebra.IsSeparableExtension` to the algebra structure of that canonical
  fraction-field map, exactly the node's separability notion (including its
  finitely generated subextension quantifier).
* The conclusion is the existential `∃ g : S, g ≠ 0 ∧ ...`; its first clause
  selects a nonzero element, and its second clause is
  `Algebra.Smooth R (Localization.Away g)`, the composite map
  `R → S → S_g` expressed with Mathlib's canonical localization algebra.
  Thus no conclusion clause is omitted, strengthened, or weakened.

The edge cases are covered: `u` and `v` are not identified; finite type allows an
empty generating family; `g = 1` is allowed while `g = 0` is excluded; all
characteristics are allowed; and there is no hidden Noetherian, finite
presentation, finite-extension, or nonempty-index hypothesis. The statement has
no scheme or empty-scheme parameter, so those cases are irrelevant here.

For the one-definition-per-notion check, I searched the pinned Mathlib, the
slopmaster2 `WeilConjectures` tree, and this project's `lean/Sheaf` tree by exact
name and by `generic smooth`, `fraction ring`, `separable extension`, and
`smooth localization`. I also ran the required LeanFinder, Loogle, and grep
searches. The hits concern smoothness already known at a prime, localization of
an already smooth map, or the field case; none states this domain-base generic
smoothness theorem. The dependency declarations were opened: Mathlib
`Algebra.FiniteType`, project `Algebra.IsSeparableExtension`, and Mathlib
`Algebra.Smooth`; each is the notion used by the node and no dependency repair is
needed.

No mismatch was found, so no Lean or node repair was necessary. The module was
compiled with `scompile.py` and produced no errors or warnings beyond the
postponed proof. The node's `lean.statement` remains verbatim equal to the
declaration signature.
