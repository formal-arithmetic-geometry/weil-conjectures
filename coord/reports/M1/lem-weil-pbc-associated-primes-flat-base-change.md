## Worker report

The item is stated by `Module.annihilatorAssociatedPrimes_flat_base_change` in
`Sheaf.RingTheory.AnnihilatorAssociatedPrimesFlatBaseChange`. Its only proof is `sorry`.
The definition in the sibling module has full data and contains no `sorry`.
The node's statement, proof and proof dependencies are unchanged; its `stmt_deps` gains
`def-weil-pbc-annihilator-associated-primes` for the exact-annihilator convention it explicitly uses.
No dependency module or statement correction is needed. No statement is disputed.

Read the item's nine proof steps and both statement-dependency nodes. Read the full signatures
and documentation of `Module.Flat`, `RingHom.Flat`, the tensor-injectivity characterization,
and `IsNoetherianRing` in the pinned Mathlib source. The local literature checkout is absent;
read the source statement and whole proof at [Stacks Tag 0312](https://stacks.math.columbia.edu/tag/0312)
and the associated-prime definition at [Tag 00LA](https://stacks.math.columbia.edu/tag/00LA).
The source agrees with the item's statement.

Clause-by-clause rendering:

- The commutative rings are `{R : Type r} {S : Type s} [CommRing R] [CommRing S]`.
  `[Algebra R S]` supplies exactly the ring map `algebraMap R S`; every homomorphism of
  commutative rings gives this structure by `RingHom.toAlgebra`. It imposes neither
  injectivity, finite type nor flatness on the map.
- The `R`-module is `(M : Type m) [AddCommGroup M] [Module R M]`.
- The `S`-module is `(N : Type n) [AddCommGroup N] [Module S N]`.
  `[Module R N] [IsScalarTower R S N]` expresses restriction through the given ring map:
  `r • n = (algebraMap R S r) • n`, obtained by applying the tower law to `r`, `1`, `n`.
  Every restricted module supplies these instances. These are compatibility data, not an
  additional mathematical hypothesis on `N`.
- Flatness of `N` over `R` is `[Flat R N]`, the dependency's `Module.Flat` declaration.
  `S` itself need not be flat and `N` need not be faithfully flat.
- Association is `Module.annihilatorAssociatedPrimes`, with membership
  `p.IsPrime ∧ ∃ z, p = (⊥ : Submodule R M).colon {z}`.
  Mathlib's `Submodule.mem_colon_singleton` identifies the latter ideal with `{a | a • z = 0}`.
  This expresses every part of the node's definition of associated prime, including primality.
- The tensor is literally `M ⊗[R] N`. The local module instance is
  `(TensorProduct.comm R M N).toAddEquiv.module S` from Mathlib's transfer operation.
  It transports the standard action on the left factor of `N ⊗[R] M`. On a pure tensor,
  `m ⊗ n` is sent to `n ⊗ m`, scaled to `(s • n) ⊗ m`, and sent back to
  `m ⊗ (s • n)`. Thus it is exactly the required action through `N`, with no action of `S`
  assumed on `M` and no change to the underlying additive group of the tensor.
- `pN` is `((p : Set R) • (⊤ : Submodule S N))`, using Mathlib's scoped pointwise set
  scalar action on submodules. Its definition is the smallest `S`-submodule containing all
  `r • n` with `r ∈ p` and `n ∈ N`. Finite sums of these products are already closed under
  `S` multiplication: `s • (r • n) = r • (s • n)` by scalar compatibility and commutativity.
  Consequently this is exactly `pN`, not a larger closure. The quotient is the actual
  `S`-module `N ⧸ pN`.
- `rhs` is `⋃ p ∈ annihilatorAssociatedPrimes R M, annihilatorAssociatedPrimes S (N ⧸ pN)`.
  This is the union over precisely the associated primes of `M`, without an extra parameter.
- `rhs ⊆ annihilatorAssociatedPrimes S (M ⊗[R] N)` gives the unconditional inclusion.
- The conjunction's second clause is
  `IsNoetherianRing R → annihilatorAssociatedPrimes S (M ⊗[R] N) = rhs`.
  This gives equality exactly when the extra Noetherian hypothesis on `R` is available;
  the first clause still applies when `R` is not Noetherian. No Noetherian assumption on `S`
  or finite-generation hypothesis on either module appears.

Dependency declarations and imports:

- `def-weil-pbc-flat-ring-map`: `Module.Flat`, `Mathlib.RingTheory.Flat.Basic`.
  Read also its `iff_lTensor_preserves_injective_linearMap`; the recorded `RingHom.Flat`
  is not used because the hypothesis concerns `N`, not flatness of the ring map.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, `Mathlib.RingTheory.Noetherian.Defs`,
  available transitively through `Mathlib.RingTheory.Flat.Basic`.
- New dependency: `Module.annihilatorAssociatedPrimes`,
  `Sheaf.RingTheory.AnnihilatorAssociatedPrimes`.
- Other building blocks: `Submodule.colon` (Mathlib.RingTheory.Ideal.Colon),
  `TensorProduct.comm` and `TensorProduct.leftModule` (tensor-product imports of Flat.Basic),
  `Submodule.pointwiseSetSMul` (Mathlib.Algebra.Module.Submodule.Pointwise), and
  `AddEquiv.module` (Mathlib.Algebra.Module.TransferInstance). Each explicit import is used.

Edge cases checked before writing: if `M = 0`, its associated-prime set and the tensor's set
are empty; the annihilator of zero is the top ideal, which is not prime. If `N = 0`, all
quotients and the tensor are zero, so both sides are empty. The zero ring is permitted by
`CommRing`; it has no prime ideals and only zero unital modules. A zero quotient `N/pN`
contributes an empty set. An empty indexing set gives the empty union, without introducing
an artificial nonemptiness hypothesis. Arbitrary, non-finite modules and arbitrary
characteristics are admitted. Independent universes `r s m n` admit rings and modules of
different sizes. For non-Noetherian `R` only inclusion is asserted; even for Noetherian `R`,
`S` may be non-Noetherian, so exact annihilators must be used on both sides.

Searches performed with `msearch.py M1 lem-weil-pbc-associated-primes-flat-base-change`:

- LeanFinder: "associated primes of M tensor N for flat N over R are union of associated
  primes of N/pN" returned eight flatness/tensor results including `Module.Flat.ker_lTensor_eq`,
  but no associated-prime base-change formula.
- Loogle: `associatedPrimes, TensorProduct` returned zero results.
- Grep: `associatedPrimes|IsAssociatedPrime` under `RingTheory/Ideal/AssociatedPrime` returned
  fifteen hits, covering definitions, localization and finiteness, no general flat base change.
- LeanSearch: "prime ideal equal to annihilator of an element of a module without radical"
  was unavailable (Internal Server Error); recorded as unavailable, not negative evidence.
- LeanFinder: "associated prime defined as exactly the annihilator of an element in a module
  over any commutative ring" returned eight hits including `associatedPrimes` and
  `IsAssociatedPrime`. Their search descriptions suggest exact annihilators, but reading
  this pinned checkout's actual definitions shows a radical. No exact general-ring set.
- Loogle: `Submodule.colon` returned twelve hits, providing the annihilator building block.
- `rg` over `WeilConjectures` for `associatedPrimes|IsAssociatedPrime|0312` and the item's id:
  only unrelated `ProjectiveDimension.lean` uses, no matching declaration or tagged item.
- `rg` over `lean/Sheaf/RingTheory` found existing exact-annihilator lemma signatures,
  including `AssociatedLocalizationFg` and `AnnihilatorEqIffMinimalPrimeOfFG`, but no set
  definition or base-change theorem. `dag/lean_names_upstream.json` has no matching names.
- DAG definition search `annihilator.*associated|associated.*annihilator` found only
  `def-sc-weakly-associated-primes`, which concerns minimal primes over annihilators.
  `tools/blueprint_refs.py search 'associated primes'` found zero blueprint nodes.
- New full declaration names were checked by `rg` in Mathlib, WeilConjectures and Sheaf:
  no existing declarations with either name.

Validation: both modules compiled together on the server through `scompile.py`, exit 0,
with no warnings. Their universe names are distinct to accommodate the tool's concatenated
check file. No Lean compilation ran locally.

## New nodes

`def-weil-pbc-annihilator-associated-primes` defines the exact associated-prime set over an
arbitrary commutative ring, as in Stacks Definition 10.63.1 (Tag 00LA), used in Tag 0312.
Its module is `Sheaf.RingTheory.AnnihilatorAssociatedPrimes` and declaration is
`Module.annihilatorAssociatedPrimes`. The existing Mathlib set takes radicals and agrees
with this set only under additional assumptions; `S` is arbitrary in this item. Existing
Sheaf statements use inline colon ideals but provide no reusable set declaration. The DAG
weak-association node is a different notion. The searches above, also recorded in the new
node's `mathlib_searches`, establish the need for this new definition. It has no theorem,
no postponed data, and no additional mathematical assumptions. Its blueprint ancestry was
obtained with `tools/blueprint_refs.py ancestor` and its `via` prepends the item to the
item's existing path. The item directly cites it in `stmt_deps`.

## Second reading by M1

Independently read the item, its nine proof steps, both original statement-dependency
nodes and their Mathlib declarations, the new definition node, and both delivered modules.
The local Stacks checkout is absent. Read the actual Stacks `algebra.tex` downloaded into
this item's scratchpad from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex:
Conventions (rings are commutative with 1, including the zero ring),
`definition-associated` at lines 15108–15115, and `lemma-bourbaki` with its entire proof
at lines 15774–15851. Also checked https://stacks.math.columbia.edu/tag/0312 and
https://stacks.math.columbia.edu/tag/00LA. The surrounding relative-assassin discussion
imposes no additional standing hypothesis on this lemma.

Object/hypothesis/conclusion inventory and its Lean rendering:

1. Commutative rings `R`, `S` and a ring map `R → S`: `{R : Type r} {S : Type s}`,
   `[CommRing R] [CommRing S] [Algebra R S]`. Verdict: exact. Every unital ring map
   gives the algebra structure; no injectivity, finite type, or flatness of the ring map
   is required.
2. An arbitrary `R`-module `M`: `(M : Type m) [AddCommGroup M] [Module R M]`.
   Verdict: exact; no finite generation is assumed in the statement.
3. An arbitrary `S`-module `N`, regarded over `R` through the map:
   `(N : Type n) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]`.
   Verdict: exact. Setting the middle scalar to 1 in the tower law gives
   `r • n = (algebraMap R S r) • n`; this is compatibility, not extra flatness.
4. `N` flat over `R`: `[Flat R N]`. Verdict: exact. Opened `Module.Flat` and its
   arbitrary-module tensor-injectivity characterization in `Flat/Basic.lean`;
   it is the module clause of `def-weil-pbc-flat-ring-map`, not `RingHom.Flat`.
5. For every commutative ring `T` and module `P`, association means a prime ideal
   exactly equal to an element's annihilator: `annihilatorAssociatedPrimes T P`
   unfolds to `p.IsPrime ∧ ∃ z, p = (⊥ : Submodule T P).colon {z}`.
   Verdict: exact. Opened `Submodule.mem_colon_singleton`: membership means
   `a • z ∈ ⊥`, hence `a • z = 0`. No radical or Noetherianity is inserted.
6. The `S`-module `M ⊗[R] N` with action through `N`: the statement's local
   `letI` transports the left-factor action on `N ⊗[R] M` along
   `(TensorProduct.comm R M N).toAddEquiv.module S`. Verdict: exact.
   Read `TensorProduct.comm`, `comm_tmul`, `leftModule`, `smul_tmul'`, and
   `AddEquiv.module`; the resulting action sends `m ⊗ n` to `m ⊗ (s • n)`.
   The original tensor's additive group is retained; no `S`-module on `M` is assumed.
7. Each quotient `N/pN`: `N ⧸ ((p : Set R) • (⊤ : Submodule S N))`.
   Verdict: exact. Read `Submodule.pointwiseSetSMul`, whose value is the smallest
   `S`-submodule containing all `r • n` for `r ∈ p`. Finite sums of these are
   already stable under `S` by the compatible commuting actions, so this is `pN`.
8. Union over all associated primes of `M`:
   `let rhs := ⋃ p ∈ annihilatorAssociatedPrimes R M, ...`.
   Verdict: exact; the prime is bound before its membership condition and quotient.
9. Unconditional inclusion: `rhs ⊆ annihilatorAssociatedPrimes S (M ⊗[R] N)`.
   Verdict: exact direction and full union, with no Noetherian hypothesis.
10. Equality if `R` is Noetherian: the conjunction's second clause is
    `IsNoetherianRing R → annihilatorAssociatedPrimes S (M ⊗[R] N) = rhs`.
    Verdict: exact. Opened `IsNoetherianRing` and `IsNoetherian`: every ideal is
    finitely generated as in `def-weil-pbc-noetherian-ring`. There is no assumption
    that `S` is Noetherian, and no finiteness assumption on either module.

Edge cases: independent universes `r s m n` are explicitly bound and impose no size
identification. Zero rings and zero modules are allowed. The zero element's annihilator
is top, which is not prime; thus zero modules, zero tensors and zero quotients contribute
empty sets. An empty associated-prime indexing set yields an empty union. No
nonemptiness or characteristic hypothesis appears. The equality clause is conditional
only on `R`; non-Noetherian `S` is allowed even there. Scheme and integer-index edge
cases are not objects in this statement.

Independent searches used different wording: LeanFinder query "Bourbaki assassin tensor
flat module associated prime base change" gave eight results about flatness, going down
and base change, none this formula. Loogle query `associatedPrimes` returned twelve
results (definition, product, localization-related and exact-sequence tools), no flat
base-change formula. LeanSearch query "prime ideals that are annihilators of elements
of modules" again failed with Internal Server Error; this is unavailability, not a
negative mathematical result. Grep for `assassin|bourbaki|annihilatorAssociatedPrimes|0312|00LA`
in Mathlib's associated-prime directory, all `WeilConjectures`, and `lean/Sheaf` found
no declaration for either new name. Broader `annihilator|associated` searches in both
project RingTheory trees found existing annihilator and associated-prime lemmas, not
an exact general-ring set. Searching DAG definition files by `annihilator|associated prime`
found only `def-sc-weakly-associated-primes`, which was opened: minimality over an
annihilator is a different notion. Opened pinned Mathlib's
`Submodule.IsAssociatedPrime`, `IsAssociatedPrime`, and `associatedPrimes` in
`AssociatedPrime/Basic.lean`: all use radicals; `isAssociatedPrime_iff` requires
Noetherianity of the coefficient ring to recover exact annihilators. Consequently the
new definition cannot be replaced by that existing set on arbitrary `S`.

New-node review (H12): `def-weil-pbc-annihilator-associated-primes` agrees exactly with
Stacks `definition-associated`/00LA for arbitrary commutative rings and modules.
No existing DAG node carries this notion. Its definition uses Mathlib's colon rather
than duplicating the annihilator ideal; it has explicit data and no `sorry`.
Its fields, empty proof lists and statement dependencies, three search kinds,
creation record, blueprint ancestry/via, chapter/unit, audit and Lean record meet
brief §5. The item directly cites it. There are no dependency modules (H13) and
no statement correction or correction-citer verdicts to review (4c).

No mathematical or Lean mismatch was found; no module or node was rewritten.
The only change in this second reading is this independent review record.
Both source docstrings and all nine proof steps were checked; only the main theorem
has a `sorry`. Imports are used, names have no `Sheaf` prefix, lines satisfy the
project conventions, and all variables/universes are bound. Both modules compiled
together through `scompile.py` on the server, exit 0, clean with no warnings (1.4 s).

## Reviewer fix (R-apf1412, stage 2)

K1 landed `def-weil-pbc-annihilator-associated-primes` first (merge e0c34bc1a) as
`RingTheory.annihilatorAssociatedPrimes` in the same file path, the same notion (prime ideal
equal to `(⊥ : Submodule R M).colon {z}`, no radical, no Noetherian hypothesis). M1's duplicate
node and module `Module.annihilatorAssociatedPrimes` were dropped (H4/H12: one definition per
notion). The item's theorem now lives in namespace `RingTheory`
(`RingTheory.annihilatorAssociatedPrimes_flat_base_change`) and uses the landed definition;
`[Flat R N]` is spelled `[Module.Flat R N]`, and `Mathlib.RingTheory.Noetherian.Defs` is
imported explicitly for `IsNoetherianRing`. Statement otherwise unchanged. Checked in Lean: no
ambient `Module S (M ⊗[R] N)` instance exists, the transported action satisfies
`s • (m ⊗ₜ n) = m ⊗ₜ (s • n)` by `rfl`, and `p • ⊤ ≤ ((p : Set R) • ⊤).restrictScalars R`.
