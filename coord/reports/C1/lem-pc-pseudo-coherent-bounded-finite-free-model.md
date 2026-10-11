## Worker report

The module `Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel` states
`DerivedCategory.exists_finiteFree_model_isStrictlyLE`. Its only proof is `sorry`.
No definitions or dependency modules are introduced.

Hypotheses and clauses, matched individually:

- R is a ring: `{R : Type u} [CommRing R]`. Stacks uses commutative unital rings,
  including the zero ring (Tag 00AQ); no nontriviality or Noetherianity is assumed.
- b is an integer: `(b : ℤ)`, without a sign restriction.
- C belongs to D(R): `(C : DerivedCategory (ModuleCat.{v} R))`, with the explicit
  `[HasDerivedCategory.{w} (ModuleCat.{v} R)]` localization-size/model binder.
- C is pseudo-coherent: `(hC : IsPseudoCoherent C)` uses the landed ring definition.
  Its bounded-above finite-free representative is equivalent to the node's finite
  projective representative by Tag 064U, clauses (1) and (3).
- H^i(C) vanishes for every i > b: `hvan` quantifies `i : ℤ`, assumes `b < i`, and
  asserts `IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj C)`.
- There exists a complex P of R-modules: `∃ P : CochainComplex (ModuleCat.{v} R) ℤ`.
- Every P^i is finitely generated free: `∀ i : ℤ, Module.Free R (P.X i) ∧
  Module.Finite R (P.X i)`; both conditions are stated in every degree.
- Every P^i above b is zero: `P.IsStrictlyLE b`. The Mathlib lemma
  `CochainComplex.isStrictlyLE_iff` says exactly `∀ i, b < i → IsZero (P.X i)`.
- P maps quasi-isomorphically to C: `Nonempty (Q.obj P ≅ C)`. C is an object of
  the localization, not a chosen cochain complex, so this is the well-typed form of
  a quasi-isomorphism from a representative. A bounded-above free complex is
  K-projective, so this also recovers actual quasi-isomorphisms to chosen
  representatives; no representative or map is additionally assumed.

Dependency declarations used:

- `def-weil-abstract-derived-category`: Mathlib's `DerivedCategory`, `HasDerivedCategory`
  and `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`, and
  `DerivedCategory.homologyFunctor` in `.HomologySequence`. Their full signatures and
  docstrings were read in the source checkout; Q localizes at quasi-isomorphisms.
- `def-pc-ring-pseudo-coherent-complex`: `DerivedCategory.IsPseudoCoherent` in
  `Sheaf.RingTheory.RingPseudoCoherent`, whose complete signature and definition were
  read in the project library. Imported directly; no private copy.
- The original `def-pc-derived-category` record and its scheme-specialization signature
  were read; it cannot supply D(R). This is handled as a statement correction below,
  rather than altering that valid scheme definition or introducing a duplicate notion.

Edge cases checked: the zero ring is allowed, as are the zero derived object and zero
complex; no Nonempty or Nontrivial condition appears. Integers b and degrees i can be
negative or zero. The conclusion is bounded above only, with no lower bound added.
There is no finite-rank positivity condition and no restriction on characteristic.
The independent object/module/localization universes u, v, w are explicit, matching the
landed ring definition; no test-module quantifier can become vacuous. Nothing restricts
rank-zero terms, and the proof docstring covers a complex already zero above b.

Searches for an existing declaration:

- `msearch.py ... leanfinder "pseudo coherent complex finite free representative
  vanishing above cohomology bound"`: 8 generic results (projective resolutions,
  cohomological IsLE/IsGE and maps from single complexes), none giving this theorem.
- `msearch.py ... loogle "DerivedCategory.Q, Module.Free, CochainComplex.IsStrictlyLE"`:
  0 hits.
- `msearch.py ... leansearch "pseudo coherent complex bounded above finite free model"`:
  unavailable, Internal Server Error; not treated as a negative result.
- `msearch.py ... grep "pseudo.?coherent|finite.?free.*model" Algebra/Homology`:
  0 Mathlib hits.
- `rg` of `PseudoCoherent|pseudo_coherent|<item>` in the upstream WeilConjectures
  source: 0 hits. Search of upstream names for this item and the proposed declaration:
  0 hits.
- `rg` of `exists.*finiteFree|finiteFree.*model|pseudoCoherent.*bound` in Mathlib and
  `lean/Sheaf`: only `exists_finiteFreeResidueModel` and `exists_boundedAbove_finiteFree_lift`,
  concerning residue models and affine lifts; no exact theorem.
- Read landed `RingPseudoCoherent`, `FiniteHomologyOfMPseudoCoherent`, and
  `RingPseudoCoherentFiniteTorPerfect`; the first supplies the notion, and the latter
  uses this result but does not state it.

Source checked directly at https://stacks.math.columbia.edu/tag/064U (local literature
checkout is absent); its final assertion is precisely the claimed model and upper bound.
Tag 00AQ was also opened to verify the ring convention.

Validation: remote `scompile.py` compiled the 48-line module in 1.9 seconds, exit 0,
without warnings. Every binder and universe is explicit. No STATEMENT-DISPUTED issue.

## Statement corrected

Old statement (verbatim):

Let $R$ be a ring, let $b$ be an integer and let $C$ be an object of the derived category $D(R)$ [def-pc-derived-category]. If $C$ is pseudo-coherent, meaning that it admits a quasi-isomorphism from a bounded-above complex of finitely generated projective $R$-modules, and $H^i(C)=0$ for every $i>b$, then there is a quasi-isomorphism $P^\bullet\to C$ from a complex $P^\bullet$ of finitely generated free $R$-modules with $P^i=0$ for every $i>b$.

The cited def-pc-derived-category defines D(O_X) for a scheme, not D(R), so it cannot type the stated ring-derived object. Replace it by the abstract derived category specialized to ModuleCat R and cite the landed ring pseudo-coherence definition. Explicit commutativity is the source convention (Tag 00AQ), including the zero ring; the finite projective characterization is equivalent by Tag 064U, not an extra hypothesis.

The corrected statement follows More on Algebra, Lemma 15.66.5 (Tag 064U), final assertion; ring convention Tag 00AQ. The ring pseudo-coherence definition is cited explicitly; Tag 064U proves the two characterizations equivalent. This changes neither the mathematical hypothesis nor the conclusion, and this supporting node is not the blueprint unit itself. Proof and proof_deps are unchanged.

- `lem-pc-ring-pseudo-coherent-finite-tor-perfect`: holds = true. Step 1 still obtains a finite free model vanishing above b from pseudo-coherence and cohomological vanishing; Tag 064U equates the finite projective and finite free definitions.

Citers were found by searching the item ID over dag/nodes and checking stmt_deps and proof_deps. The sole citer and its proof were read; it is not edited.

## Second reading by C1

The corrected node introduces: a commutative ring `R`; an integer `b`; an object `C` of
the abstract derived category of `R`-modules; pseudo-coherence of `C`; vanishing of
`H^i(C)` for every `i > b`; and the conclusion that there is a complex `P` of
finitely generated free `R`-modules, a quasi-isomorphism `P → C`, and `P^i = 0` for
every `i > b`.  The Lean renders these as `{R : Type u} [CommRing R]`,
`[HasDerivedCategory.{w} (ModuleCat.{v} R)]`, `C : DerivedCategory (ModuleCat.{v} R)`,
`b : ℤ`, `hC : IsPseudoCoherent C`, and
`hvan : ∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj C)`;
the conclusion is `∃ P : CochainComplex (ModuleCat.{v} R) ℤ` with
`P.IsStrictlyLE b`, degreewise `Module.Free R (P.X i) ∧ Module.Finite R (P.X i)`,
and `Nonempty (Q.obj P ≅ C)`.  Each object, hypothesis, quantifier, and conclusion
clause matches the corrected statement.

The original dependency was wrong: `def-pc-derived-category` is the scheme
`D(O_X)` definition and cannot provide `D(R)`.  I retained the worker's correction,
which cites `def-weil-abstract-derived-category` and
`def-pc-ring-pseudo-coherent-complex`; the node copy already records
`statement_change`, and its sole citer `lem-pc-ring-pseudo-coherent-finite-tor-perfect`
still holds.  No other mismatch was found.  The source is More on Algebra,
Lemma 15.66.5 (Tag 064U), with commutative-ring convention Tag 00AQ.

Edge cases checked: zero rings, zero complexes and zero derived objects are allowed;
`b` and degree indices may be negative or zero; empty/rank-zero terms are allowed;
no characteristic, nontriviality, positivity, or lower-bound hypothesis is added;
the explicit universes prevent vacuous module quantification.  The empty index/rank
case is covered by `Module.Free` and `Module.Finite`.

Searches (`msearch.py` LeanFinder/Loogle/LeanSearch and `rg` in Mathlib,
`WeilConjectures`, and `lean/Sheaf`) found no existing theorem for a bounded finite-free
pseudo-coherent model; only unrelated residue-model and affine-lift results occurred.
The landed `DerivedCategory.IsPseudoCoherent` definition was read and used directly;
no duplicate or hollow definition was introduced.  The module compiles cleanly with
`scompile.py`; only the theorem proof is `sorry`.
