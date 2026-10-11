## Worker report

The module `Sheaf.FieldTheory.PthRootsExtensionDegree` states
`IntermediateField.finiteDimensional_finrank_adjoin_pth_roots`, with `sorry` and no proofs.
It states precisely the degree assertion of Stacks Project, Algebra, Lemma 10.158.3,
[Tag 07DZ](https://stacks.math.columbia.edu/tag/07DZ). The local literature checkout
contains only indexes, so the source statement and induction proof were read on that page.
The declaration docstring records all five proof steps of the DAG, including the spanning
monomials, the differential contradiction, the degree-p simple extension, and multiplicativity.

Hypotheses and clauses:

- A field `k` of characteristic `p > 0`: `(p : ℕ) [Fact p.Prime] (k : Type u)
  [Field k] [CharP k p]`. The characteristic of a field, when positive, is prime;
  `Fact p.Prime` records this, and excludes characteristic zero and one.
- The `n` elements are `(n : ℕ) (a : Fin n → k)`, including `n = 0`.
- Their differentials in Ω over F_p are `KaehlerDifferential.D (ZMod p) k (a i)`.
  `attribute [local instance] ZMod.algebra` supplies Mathlib's canonical prime-field
  algebra from `[CharP k p]`, without an extra algebra hypothesis or a new definition.
  `hind : LinearIndependent k (fun i : Fin n ↦ ...)` expresses independence over k,
  not over F_p.
- An arbitrary chosen algebraic closure is `(Ω : Type v) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]`. Separate explicit universes admit any size of algebraic closure.
- The chosen roots are `(α : Fin n → Ω)` and
  `hα : ∀ i : Fin n, α i ^ p = algebraMap k Ω (a i)`.
  This universally quantifies over choices of the roots named in the node, rather than
  constructing a second root notion. Such roots exist by algebraic closedness and are
  unique by injectivity of Frobenius in a field. The root equations therefore place no
  additional restriction on a or on the algebraic closure.
- The smallest subfield containing the base field and the roots is
  `adjoin k (Set.range α)`. Its existing Mathlib definition is the subfield closure of
  `Set.range (algebraMap k Ω) ∪ Set.range α`, so this is exactly the specified field.
- Finiteness of the extension is the first conjunct
  `FiniteDimensional k (adjoin k (Set.range α))`.
- Its degree as a k-vector space is the second conjunct
  `Module.finrank k (adjoin k (Set.range α)) = p ^ n`.
  Finiteness is asserted separately, so the zero convention for finrank of an infinite
  module cannot hide the finite-extension clause.

Dependency declarations read and used:

- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential` and `KaehlerDifferential.D`; the signature and docstring of
  `KaehlerDifferential.linearMapEquivDerivation` were also read to verify universality.
- `def-weil-algebraic-closure`: its Mathlib match includes `IsAlgClosure`, from
  `Mathlib.FieldTheory.IsAlgClosed.Basic`. This records both algebraic closedness and
  algebraicity, exactly the arbitrary closure in the node. No dependency module is needed.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs` (imported transitively);
  the base embedding is `algebraMap k Ω`, and the generated intermediate field inherits
  the algebra structure. The statement concerns the field-extension clause of that node;
  its associated Spec morphism is not part of this item's statement.
- Additional existing Mathlib infrastructure: `IntermediateField.adjoin` from
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`, `Module.finrank` from
  `Mathlib.LinearAlgebra.Dimension.Finrank`, and `ZMod.algebra` from
  `Mathlib.Algebra.Algebra.ZMod`. No missing mathematical notion requires a new node.

Edge cases checked before writing:

- `n = 0`: independence and root equations are vacuous, the range is empty, and
  `adjoin_empty` identifies the extension with the bottom intermediate field, of degree
  one, agreeing with `p ^ 0`.
- `n = 1`: the independence hypothesis says the differential is nonzero; a p-th power
  has zero differential, so the degree-p assertion agrees with the source's base case.
- A zero element, a p-th power, or repeated elements cannot occur in a nonempty independent
  family (zero or repeated differentials); there is no hidden nonzero/distinct hypothesis.
- Perfect base fields admit no nonempty such family; the theorem remains meaningful at
  `n = 0`. Characteristic two is allowed. No finite-dimensionality of k over F_p is imposed.
- k and Ω may lie in independent universes; no equality-of-universes restriction is imposed.

Searches performed with `msearch.py E1 lem-weil-pbc-pth-roots-extension-degree`
(the exact queries and digests are in the sandbox's `searches.jsonl`):

- LeanFinder: "adjoining p-th roots of elements with linearly independent Kahler
  differentials over F_p gives degree p^n". Eight hits, principally
  `IsPurelyInseparable.finrank_eq_pow` and inseparable-degree results. These only assert
  that a finite purely inseparable degree is some power; none computes the exponent n
  from independent differentials.
- LeanSearch: "degree adjoining pth roots independent Kahler differentials".
  Service unavailable (Internal Server Error); recorded as unavailable.
- Loogle: "KaehlerDifferential.D, LinearIndependent". One hit,
  `Algebra.Generators.disjoint_ker_toKaehler_of_linearIndependent`, about the kernel of a
  cotangent map, not the degree of an extension.
- Mathlib grep: "pthRoot|pBasis|07DZ|finrank.*adjoin", subdirectory FieldTheory.
  Hits include `AdjoinPthRoots`, adjoining all roots, and `finrank_adjoin_eq_one_iff`;
  none gives this independent-differentials statement.
- Direct rg in `WeilConjectures/` and `lean/Sheaf/`: patterns
  `pthRoot|pBasis|07DZ|pth-roots-extension-degree|KaehlerDifferential`.
  The source has no matching statement; project hits include p-basis statements and
  the citer `GeometricallyRegularH1Injective`, none asserting this degree.
- Direct rg in `dag/lean_names_upstream.json` and Mathlib for
  `pth.*roots|finrank_adjoin.*differential|finrank_adjoin_pth_roots`: no collision with
  the chosen declaration. The item's blueprint id was included in the source search;
  it does not name a source declaration.

No statement correction, disputed statement, new node, or dependency replacement was needed.

## Second reading by E1

I independently compared the node JSON with
`lean/Sheaf/FieldTheory/PthRootsExtensionDegree.lean` and found the statement faithful.
The objects and hypotheses match item by item:

- The node's positive characteristic prime `p` and field `k` are rendered by
  `(p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]`; no finiteness,
  perfectness, or extra characteristic hypothesis is added.
- The finite family of elements is `(n : ℕ) (a : Fin n → k)`, so the empty family
  and all finite cardinalities are included.
- The differential family is exactly
  `KaehlerDifferential.D (ZMod p) k (a i)`, with
  `hind : LinearIndependent k ...`; the local `ZMod.algebra` instance supplies the
  canonical prime-field algebra and does not add a user hypothesis.
- The arbitrary algebraic closure is `(Ω : Type v) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]`, with an independent universe allowed.
- The selected roots are `(α : Fin n → Ω)` with
  `hα : ∀ i, α i ^ p = algebraMap k Ω (a i)`. This is the node's unique-root
  choice and introduces no stronger condition.

The conclusion has both clauses from the node, in the same order: finiteness
`FiniteDimensional k (adjoin k (Set.range α))`, followed by the exact degree
`Module.finrank k (adjoin k (Set.range α)) = p ^ n`. `IntermediateField.adjoin`
is Mathlib's smallest intermediate field containing the base image and root range,
so it represents the stated subfield; no alternate extension notion is introduced.
The source's induction proof is preserved in the theorem docstring step by step.

Edge cases checked: `n = 0` gives the bottom/base field and degree `p ^ 0 = 1`;
characteristic two is allowed; zero or repeated elements are excluded only when
independence genuinely excludes them; arbitrary algebraic-closure size and all
universes are retained. No empty-scheme or zero-object condition is relevant.

Searches were rechecked in Mathlib, `WeilConjectures/`, `lean/Sheaf/`, and
`dag/lean_names_upstream.json` for p-th-root, p-basis, Kähler-differential degree,
and Tag 07DZ names. Independent LeanFinder query: "dimension extension adjoining radical roots from
independent universal derivation values" returned smooth-cotangent ranks,
characteristic-zero differential extension structures, and a power-basis bound,
none asserting this degree. Independent Loogle query: "KaehlerDifferential,
Module.finrank" returned zero hits. Independent LeanSearch query: "finite field
extension degree from independent differentials and adjoining characteristic
roots" was unavailable (Internal Server Error); no conclusion is drawn from it.
Direct rg used "radical|independent.*differential|07DZ|finrank_adjoin_pth_roots"
over Mathlib FieldTheory, WeilConjectures, and lean/Sheaf; its relevant project hit
is the different p-independence/differentials statement, not this extension degree.
No exact existing statement was found.

I read the source statement and proof at https://stacks.math.columbia.edu/tag/07DZ:
its characteristic and independence assumptions agree with the node. I opened
Mathlib Kaehler.Basic (KaehlerDifferential, D, linearMapEquivDerivation),
IsAlgClosed.Basic (IsAlgClosure), Algebra.Defs (Algebra), ZMod (algebra), and
IntermediateField.Adjoin.Defs (adjoin). These signatures supply exactly the three
dependency nodes and the generated field, with no unusable dependency record.
There are no new nodes, dependency modules, or statement corrections to review.

No mismatch was found, so no source, node statement, dependency, or module repair
was needed. The module compiles cleanly with the required `sorry`-only proof.
