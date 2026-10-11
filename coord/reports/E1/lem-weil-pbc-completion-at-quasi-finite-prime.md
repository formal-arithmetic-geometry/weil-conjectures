## Worker report

The module `Sheaf.RingTheory.CompletionAtQuasiFinitePrime` states the splitting theorem from
Stacks Algebra Tag 07NC. It introduces a commutative Noetherian base ring `R`, a finite-type
`R`-algebra `S`, a prime `q`, and the quasi-finiteness hypothesis. It defines `p` as the
contraction of `q`, the localizations `Rp` and `Sq`, the extended maximal ideals `Ip` and
`Iq`, their adic completions `Rph` and `Sqh`, and the tensor product `U`. The conclusion
quantifies a ring `B`, maps `β : U →+* B` and `φ : U →+* Sqh`, and a ring equivalence
`e : U ≃+* Sqh × B` whose underlying map is `RingHom.prod φ β`. The proof is `sorry` as
required at stage 2.

The hypotheses render as `[CommRing R]`, `[CommRing S]`, `[Algebra R S]`,
`[Algebra.FiniteType R S]`, `[IsNoetherianRing R]`, and
`hq : IsQuasiFiniteAtPrime R S q`. The localization and completion clauses render through
`Localization.AtPrime`, `Ideal.map`, and `AdicCompletion`; the product decomposition clause
is the displayed ring equivalence and equality with `RingHom.prod`.

Dependency declarations used are `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing`,
`Algebra.IsQuasiFiniteAtPrime` from `Sheaf.RingTheory.QuasiFiniteAtPrime`,
`Localization.AtPrime` and `Ideal.ResidueField`/`Ideal.Fiber` from Mathlib localization files,
and `AdicCompletion` from `Mathlib.RingTheory.AdicCompletion.Basic`.

Edge cases checked include `q` arbitrary (including maximal and non-maximal primes), zero
rings where permitted by the typeclass assumptions, and arbitrary universe levels `u` and `v`.
The completion ideals are the images of the contracted primes in the corresponding localizations.

Searches recorded in the node were reviewed: LeanSearch, LeanFinder, Loogle, and grep found no
existing theorem giving this product decomposition. Grep of the project source also found no
existing declaration for Tag 07NC.

The formal `φ` is existentially quantified as a ring map and the equivalence explicitly
identifies the pair map with `RingHom.prod φ β`; this is the Lean rendering of the natural
projection map used in the source.

## Earlier second reading (a previous round; superseded)

The theorem was reread against the node statement and Tag 07NC. All hypotheses and the
conclusion's product decomposition are present. The localization and completion objects use
the same contracted prime and prime `q`; no extra mathematical hypotheses were introduced.

## Second reading by E1

I independently opened the node and module, all four statement dependency nodes, and their
recorded declarations. I read Stacks algebra.tex in the local read-only Stacks checkout
`/home/ubuntu/c1-stacks-review`: the conventions, 00PK/00PL, and 07NC with its proof and
final sanity check. The conventions require commutative unital rings, allowing the zero
ring; they add no hidden Noetherian, field, characteristic, or injectivity assumption.
There are no new nodes, dependency modules, or statement corrections in this delivery.

Object/hypothesis/conclusion inventory and matching verdicts:

- Ring map R → S: `(R : Type u) (S : Type v) [CommRing R] [CommRing S]
  [Algebra R S]`, with map `algebraMap R S`. This covers every commutative ring map,
  including noninjective ones. Exact.
- R Noetherian: `[IsNoetherianRing R]`. I read Noetherian/Defs.lean:196 and its
  ideal-finite-generation equivalence. Exact, using the dependency's recorded notion.
- S finitely generated as an R-algebra: `[Algebra.FiniteType R S]`. Exact; neither
  finite as a module nor globally quasi-finite is assumed.
- Prime q of S: `(q : PrimeSpectrum S)`. Prime ideals are bundled, with no maximality
  assumption. Exact.
- p = inverse image of q: `let p : Ideal R := q.comap (algebraMap R S)`. Exact.
- Quasi-finite at q: `(hq : IsQuasiFiniteAtPrime R S q)`. I opened
  Sheaf.RingTheory.QuasiFiniteAtPrime: its definition is openness of the singleton of
  the canonical fibre prime via `preimageHomeomorphFiber`. This is exactly 00PL/00PK(1),
  with tensor-factor symmetry, and is the recorded dependency declaration. Exact.
- Local rings Rp and Sq: `Localization.AtPrime p` and `Localization.AtPrime q.asIdeal`.
  AtPrime/Basic.lean:57 constructs localization at the prime complement. Exact.
- Extended maximal ideals: `Ip := Ideal.map (algebraMap R Rp) p` and the analogous
  `Iq`. These are pRp and qSq, the dependency's maximal ideals. Exact.
- Completions Rph and Sqh: `AdicCompletion Ip Rp`, `AdicCompletion Iq Sq`.
  Basic.lean's compatible-family submodule and Algebra.lean's ring operations and
  `evalₐ` are the inverse limits of Rp/Ip^n and Sq/Iq^n. Exact.
- Completed local map: existential `f : Rp →+* Sq` satisfies the equality on every
  `r : R`, uniquely specifying the localization-induced map. Existential
  `ψ : Rph →+* Sqh` satisfies, for every n, x and quotient representative a,
  `evalₐ Ip n x = mk (Ip ^ n) a → evalₐ Iq n (ψ x) = mk (Iq ^ n) (f a)`.
  Quotient representatives always exist; hence this specifies every coordinate and
  uniquely specifies the induced completed map, including p-adic to q-adic change.
  Exact; these are conclusion witnesses specifying canonical objects, not additional
  input hypotheses. No separate definition is introduced.
- Tensor product U: `TensorProduct R Rph S`. Its R action is the canonical action
  through localization and completion. Exact, with no same-universe restriction.
- Natural φ: existential `φ : U →+* Sqh` now constrained by
  `φ (TensorProduct.tmul R x y) = ψ x * algebraMap Sq Sqh (algebraMap S Sq y)`.
  Pure tensors generate additively, so this uniquely specifies precisely the node's
  natural map. Exact after repair.
- Ring B and β: existential `(B : Type (max u v)) (_ : CommRing B) (β : U →+* B)`.
  Exact: B can be the complementary idempotent factor of U, in this universe; no
  nontriviality condition is imposed.
- Product isomorphism: `∃ e : U ≃+* Sqh × B, e.toRingHom = RingHom.prod φ β`.
  Exact; the first component is now forced to be the natural projection.
- S- and Rph-algebra clauses: the pure-tensor equation at x = 1 or y = 1 and the
  displayed equality of ring maps imply e respects the product structure maps
  `y ↦ (ι(y), β(1 ⊗ y))` and `x ↦ (ψ(x), β(x ⊗ 1))`. These define the two actions
  on B via β, and make e an algebra isomorphism for both bases. Thus the clauses are
  encoded by their defining commuting equations, with no arbitrary algebra instances.

Mismatches and repairs: the earlier unrestricted existential φ allowed a splitting
through an arbitrary ring homomorphism and did not establish either required canonical
algebra compatibility. Added f and ψ with their canonical coordinate specifications,
and the pure-tensor formula for φ. The earlier worker report's claim that an unrestricted
φ rendered the natural projection is superseded by this repair. Replaced the unnecessarily
broad LinearDisjoint import with TensorProduct.Basic. Expanded the vague proof docstring
into the node's eight steps, naming the nodes used and explaining the final compatibility.
The node's mathematical statement remains unchanged; `lean.statement` was updated verbatim.
No data definition contains sorry; the only theorem proof is sorry. All binders/universes
are explicit, names have no Sheaf prefix, and lines have at most 100 characters.

Edge cases: a zero S (or zero R with a unital map) has no prime q, so the theorem is
vacuous exactly as in the source; B may be the zero ring, including a single-factor
splitting. Nonmaximal q is permitted. No characteristic is selected. Quotient-coordinate
conditions include n = 0, where I^0 = top and the quotient is zero. No index-set or scheme
objects are introduced, so empty-index and empty-scheme restrictions do not arise.
Independent universes u and v cover arbitrary rings; the complementary factor fits max u v.

Independent searches (2026-10-11):
- msearch LeanSearch: `completed local ring is a direct summand of tensor base change at
  isolated fiber point`; service unavailable (Internal Server Error), recorded as such,
  not treated as a negative mathematical result.
- msearch LeanFinder: `canonical projection from tensor product onto completed local ring
  splits at quasi finite prime`; eight hits, including SurjectiveOnStalks and
  AdicCompletion.ofTensorProductEquivOfFiniteNoetherian. None states 07NC: finite-module
  completion comparison does not give this factor with its canonical projection.
- msearch grep: `completion.*(quasi|factor)|quasi.*completion` in Mathlib/RingTheory:
  three Basic.lean hits, no splitting theorem. Independently searched the project's
  lean/Sheaf, upstream WeilConjectures, and dag/lean_names_upstream.json for 07NC,
  the proposed declaration name, and completion/quasi-finite combinations: no duplicate.
  CompletionFiniteQuotient is a different finite polynomial-quotient statement; it also
  uses quotient-coordinate specifications, but is not this node or this splitting.

Validation: server scompile of CompletionAtQuasiFinitePrime.lean succeeded in 2.4 seconds
without errors or warnings. No other delivered module needs compilation.
