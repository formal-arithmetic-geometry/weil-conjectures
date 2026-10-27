## Worker report

The module `Sheaf.RingTheory.TransitiveDomainProductInvariants` states
`RingTheory.transitive_domain_product_invariants`, with its only theorem proof `sorry`.
Two real-data helper definitions spell out the fixed subrings using Mathlib's existing
`RingHom.eqLocus` and complete lattice of subrings. They are listed in `lean.declarations`.
There is no second general fixed-ring construction, no arbitrary map, and no choice of data
from an unproved existence theorem.

The inherited BLOCKED ending concerned an accepted stage-1 split, not a stage-2 declaration.
The current node has no Lean record and is explicitly queued at stage 2. The stage handoff in
`coord/brief-stage2.md` §0 authorizes recording this statement while preserving the split.
No repair note exists. This delivery changes only the item's `lean` field.

Clause-by-clause correspondence:

- The finite group is `H : Type u` with `[Group H] [Finite H]`. The finite nonempty set is
  `I : Type v` with `[Finite I] [Nonempty I]`, with its specified `[MulAction H I]`.
  `htrans : ∀ i j, ∃ h, h • i = j` is exactly transitivity.
- The varying commutative domains are `B : I → Type w`, with the two pointwise instances
  `[∀ i, CommRing (B i)]` and `[∀ i, IsDomain (B i)]`. In particular the zero ring is excluded
  in every factor, while no domain instance is asserted for the product.
- `ρ : ∀ h i, B i ≃+* B (h • i)` gives the stated unital ring isomorphisms.
  `hρone` is the identity law; `hρmul` is the composition law. `RingEquiv.cast` uses only
  `one_smul` or `mul_smul` to identify the dependent codomains, preserving their ring structures.
- The helper `transitiveProductFixedSubring B ρ` is the intersection of equalizers of
  evaluation at `h • i` and `ρ h i` after evaluation at `i`. Membership is precisely
  `∀ h i, b (h • i) = ρ h i (b i)`. This is the statement's `B^H`: the specified induced
  action satisfies `(h b) (h i) = ρ h i (b i)`, and every index is `h i` for a unique `i`.
  Thus being fixed under that action is exactly this coordinate equation. No extra action
  instance or compatibility hypothesis is imposed on the product.
- The chosen point is `i : I`. The stabilizer is written without introducing another group
  structure: quantify `h : H` with `hi : h • i = i`. The helper
  `transitiveStabilizerFixedSubring B ρ i` intersects equalizers of the endomorphism
  `(ρ h i).trans (RingEquiv.cast hi)` and the identity. This is exactly `B_i^D` with the
  inherited ring structure, and does not require that `D` be normal.
- The first conjunct provides `e : B^H ≃+* B_i^D`. Its equation for every `b` says
  `(e b : B i) = b.val i`, so this is the restriction of the projection itself, rather than
  an unspecified abstract ring isomorphism.
- The second conjunct quantifies every `A : Type a` with `[CommRing A]` and unital ring
  homomorphism `f : A →+* (∀ j, B j)`. Its two assumptions are exactly injectivity and
  `f.range = B^H`. The notation `f` renders the node's map `u`.
- The conclusions are `IsDomain A`, injectivity of `(Pi.evalRingHom B i).comp f`, and equality
  of the range of that projected map with `B_i^D`. No domain hypothesis on `A` was added.
- Arbitrary fraction fields `K : Type k` and `L : Type l` carry `[Field]`, `[Algebra]`, and
  `[IsFractionRing]`, hence their designated canonical maps are `algebraMap A K` and
  `algebraMap (B i) L`. These maps are the injective quotient embeddings since the rings
  are domains (for `A`, this is a conclusion above). Each element is a quotient by the
  `IsFractionRing` property. Quantifying arbitrary realizations avoids restricting the
  statement to one implementation of fraction fields and includes the usual `FractionRing`.
- `∃ v : K →+* L` with the displayed equality of composites asserts the extension.
  The following quantifier over `v'` asserts uniqueness among ALL extending ring maps,
  independently of the range condition. A homomorphism out of the field `K` is injective.
  By the recorded `def-pc-field-extension`, a unital ring map between fields is precisely
  a field extension, equivalently the `Algebra` structure it induces via `RingHom.toAlgebra`.
- The last equality is `Set.range v = {x : L | ...}`. The predicate quantifies all
  stabilizer elements and uses Mathlib's canonical
  `IsFractionRing.ringEquivOfRingEquiv` on `L`. Its defining localization map sends
  `b/c` to `ρ(h)(b)/ρ(h)(c)`. This is exactly `Frac(B_i)^D` with the action specified in
  the node, not invariants for a freely supplied action.
- There is no faithfulness, characteristic, stabilizer-normality, or group-order-unit
  assumption. Universes of the group, indices, rings, source ring, and both fraction
  fields are separately explicit. `set_option autoImplicit false` forbids auto-bound names.

Dependencies read and used:

- `def-pc-field-extension` records `Algebra`, module `Mathlib.Algebra.Algebra.Defs`.
  Its full class signature and docstring were read. Its documented equivalent ring-map
  encoding is used for `v : K →+* L`; the algebra definitions are public through
  `Mathlib.RingTheory.Localization.FractionRing`.
- `lem-weil-pbc-fraction-field-lift` is the Mathlib match `IsFractionRing.lift`,
  `IsFractionRing.lift_algebraMap`, `IsFractionRing.lift_unique`, `RingHom.injective`.
  The localization source and docstrings were read, including `IsFractionRing.map` and
  `IsFractionRing.ringEquivOfRingEquiv`. The latter supplies the actual canonical action
  maps, without adding a new helper theorem or choosing unspecified automorphisms.
- `lem-sfb-finite-invariant-fraction-field-lifting` matches `IsFractionRing.isInvariant`
  in `Mathlib.RingTheory.Invariant.Basic`, imported as a proof dependency. Its entire
  section context and `Algebra.IsInvariant` definition were read: finite group,
  compatible towers and fixed base ring imply the fixed fraction field assertion.
- `lem-sfb-domain-product-action-fixed-ring` has no usable Lean record or Mathlib match
  at present. It is a proof dependency only, and not used to define any object in this
  statement; accordingly there is no import of a nonexistent module. The module docstring
  retains its exact two-step use from the accepted split. Its future proof import is
  maintainer bookkeeping under stages/2-statements.md §3.7.

Edge cases checked before writing: empty `I` is excluded exactly as in the node; the fixed
choice `i` exists because `I` is nonempty. Singleton `I` gives the ordinary invariant-ring
and fraction-field theorem; trivial `H` and singleton `I` give evaluation of one factor.
A kernel in the group action is harmless. Non-normal point stabilizers (e.g. a point in the
three-letter symmetric-group action) are allowed by quantifying the stabilizer equality.
Characteristic dividing the group order is allowed: no averaging or invertibility appears.
The zero ring for `A` cannot satisfy injectivity into this nonzero product with invariant
image; `IsDomain A` is correctly concluded, not presupposed. The same fraction field or
identity maps are permitted. Independent universes place no finiteness or size restriction
on any ring. No statement fault or STATEMENT-DISPUTED issue was found.

Searches actually run using `msearch.py`:

- LeanFinder: “Evaluation of invariants of a transitively permuted dependent product of
  integral domains identifies them with the stabilizer fixed ring”. Eight hits, principally
  `DomMulAct.stabilizerMulEquiv` and related fiberwise-permutation statements; also
  `IsFractionRing.stabilizerHom` and `Algebra.IsInvariant.isIntegral`. None is this theorem.
- Loogle: `Algebra.IsInvariant, IsFractionRing`. Nine hits, including
  `IsFractionRing.isInvariant`, which supplies the fraction-field step but no product
  evaluation isomorphism.
- Mathlib grep: `fixedSubring|fixedPoints|isInvariant` in `RingTheory/Invariant`.
  Eighteen hits; invariant-ring definitions and fraction invariance, no full product theorem.
- LeanSearch: “The invariant subring of a transitive product of rings is isomorphic to
  the fixed ring of the stabilizer of a factor”. Eight hits, including
  `FixedPoints.subring`, `FixedPoints.subalgebra`, `IsInvariantSubring`, and
  `Algebra.isInvariant_iff`; no dependent product theorem.
- Project `rg` across both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `transitive.*[Ii]nvariant|[Ii]nvariant.*[Tt]ransitive|fixedSubring`: only two unrelated
  narrative occurrences. Searching all three proposed declaration names across Mathlib,
  upstream, and Sheaf returned no hits. The required upstream search for the item id had
  no hits. No existing declaration matches the full node.

Validation: `scompile.py Q31 lem-sfb-transitive-domain-product-invariants` compiled the
module against the live published server library in both sandbox and library mode, without
errors or unexpected warnings. The theorem remains postponed; no proof was supplied.

## Second reading by Q31

No independent worker was started, as the dispatcher explicitly forbids starting agents.
The maintainer's independent review is the delivery review. A final in-thread re-reading
checked the coordinate direction, dependent casts, projection equation, all three ring
conclusions, uniqueness among arbitrary extensions, and the canonical fraction fixed set.
The accepted node statement and proof split are unchanged.
