## Worker report

The module `Sheaf.TraceFormula.LciFieldChangeLocal` states
`Algebra.isCompleteIntersectionLocal_fieldChange`, with a single `sorry` proof.
The additional module defines the missing local-ring predicate by real existential data;
it contains no postponed theorem and no `sorry`.

I read the full node, every statement dependency and its recorded declaration/docstring,
the recorded proof interfaces, Stacks algebra.tex lines 36013–36028 (00SD) and
36199–36259 (00SI), and the example CompactObject module and record.
The statement is unchanged, apart from adding the definition dependency.

Hypothesis/clause correspondence:

- The field extension is `(k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]`.
  A homomorphism between fields is injective; no extra separability or algebraicity is used.
- The commutative finite type algebra is `(C : Type w) [CommRing C] [Algebra k C]
  [FiniteType k C]`. This is the algebra form of the dependency's `RingHom.FiniteType`;
  the recorded Mathlib match explicitly supplies `Algebra.FiniteType` for this form.
- `C_K` is exactly `K ⊗[k] C`, with the canonical left-factor `K` action.
- The arbitrary prime above is `(qK : Ideal (K ⊗[k] C)) [qK.IsPrime]`.
- Its contracted prime is `qK.comap
  (Algebra.TensorProduct.includeRight (R := k) (A := K)).toRingHom`.
  This map is exactly `c ↦ 1 ⊗ c`; its primality instance follows from comap.
- The two local rings are precisely `Localization.AtPrime` of these ideals.
  Their field-algebra and essential-finite-type structures are inferred canonically.
- The conclusion is the full `↔` between `IsCompleteIntersectionLocal k` of the first
  local ring and `IsCompleteIntersectionLocal K` of the second.
- The definition uses `[IsLocalRing A] [EssFiniteType k A]`; the existential presentation
  has `[CommRing R] [Algebra k R] [IsRegularLocalRing R] [EssFiniteType k R]`, a finite
  list `xs`, `RingTheory.Sequence.IsRegular R xs`, membership in the maximal ideal for
  every list element, and `Nonempty ((R ⧸ Ideal.ofList xs) ≃ₐ[k] A)`.
  Thus the quotient isomorphism is of field algebras, not just rings.

Dependency declarations used:

- Mathlib.RingTheory.FiniteType: `Algebra.FiniteType` / `RingHom.FiniteType`.
- Mathlib.RingTheory.Localization.AtPrime.Basic: `Localization.AtPrime`.
- Mathlib.RingTheory.RegularLocalRing.Defs: `IsRegularLocalRing`, the ring clause of
  def-weil-regular-scheme's retained Mathlib match. Its scheme predicate is irrelevant here.
- Mathlib.RingTheory.EssentialFiniteness: `Algebra.EssFiniteType`.
- Mathlib.RingTheory.Regular.RegularSequence: `RingTheory.Sequence.IsRegular`.
- Mathlib.RingTheory.TensorProduct.Basic: `Algebra.TensorProduct.includeRight`.
- The new `Sheaf.RingTheory.CompleteIntersectionLocal`:
  `Algebra.IsCompleteIntersectionLocal`.

Stated proof dependencies are imported non-publicly: the Q49 kernel-invariance module,
DimensionAtPointFieldExtension, LciConormalFreeRankCodimension,
ConormalGeneratorsGlobalCompleteIntersection and LCIRegularSequenceGlobalCompleteIntersection.
The Mathlib leaves for polynomial rings, Noetherianity, Nakayama and presentation base change
are imported too (`MvPolynomial`, `IsNoetherianRing`, `IsLocalRing.map_mkQ_eq_top`,
`MvPolynomial.isRegularRing_of_isRegularRing`, `Algebra.Presentation.baseChange`).
The conormal-fibre and pointwise-criterion nodes presently have neither a Lean record nor a
Mathlib match. They are proof-only dependencies, so no import exists yet and their statements
are not needed to type this item. Their role remains in the complete seven-step proof docstring.
No declaration from either node is silently assumed in the Lean statement.

Edge cases checked: an empty regular sequence is allowed by `List R` (including the
regular-local and field cases); the zero algebra has no prime, so it produces no false
local-ring assertion; primes need not be maximal; the identity extension, purely inseparable
extensions, transcendental extensions and either field characteristic remain allowed.
The independent universes `u v w` are explicit. The presentation witness is in
`Type (max u v)` for a base field in `Type u` and algebra in `Type v`: any essentially
finite type presentation is a localization of a finite type algebra and has a model of
this size, so this imposes no mathematical size restriction. All variables are bound,
and no local notation, instance, let-binder or arbitrary comparison map occurs.

Searches: msearch LeanFinder queried invariance at corresponding primes and returned
quasi-finiteness, smoothness and Zariski-main-property results, none matching. Loogle
`"CompleteIntersection"` returned zero hits. Mathlib grep
`CompleteIntersection|complete.intersection` in RingTheory returned only the presentation
`dimension` docstring at Extension/Presentation/Basic.lean:103, which was inspected.
LeanSearch queried a regular-local quotient by a finite regular sequence: eight hits,
including `Algebra.EssFiniteType.mk` and quasi-finiteness; none gives the predicate.
LeanFinder's definition query likewise returned only smoothness/quasi-finiteness results.
Direct rg searches in WeilConjectures and lean/Sheaf found the affine-cover predicate
`IsLocalCompleteIntersection` but no local-ring predicate and no theorem for individual
corresponding primes. Searching for the item id in WeilConjectures had no hits.
The upstream name index had no conflicting declaration. DAG definition searches and
`blueprint_refs.py search 'complete intersection local'` found no node for this definition.

Both delivered files compiled cleanly with scompile.py, each separately in dependency
order against the private overlay. Nothing is proved at stage 2. No statement dispute or
source correction was necessary.

## New nodes

`def-trf-complete-intersection-local` records precisely Stacks 00SD's local-ring quotient
notion, using the existing essential-finite-type, regular-local and regular-sequence
interfaces. Its source and three kinds of search are in the node. The existing
`def-weil-pbc-complete-intersection-over-field` defines a principal-open-cover predicate
for a finite type algebra, and the scheme definition likewise concerns affine covers;
neither is the local-ring notion. This new definition is cited directly in the item's
stmt_deps and has its own module. There are no dependency repairs or corrected statements.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
