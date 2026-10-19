## Worker report

The delivery states `RingTheory.Sequence.isRegular_localizationAtPrime_tensorProduct_of_flat_quotient`
in `Sheaf.RingTheory.RelativeRegularEquationsBaseChange`, with `sorry` as its whole proof.
It defines no new notion. The current item node, including Q12's reviewed stage-1 split,
is preserved verbatim apart from adding `lean`. The previous worker's unchanged-item
preflight failure is addressed by supplying the missing Lean module and record.
No statement correction, dependency module or new node is needed.

Statement correspondence, hypothesis by hypothesis and clause by clause:

| Node | Lean |
| --- | --- |
| Commutative rings R, A and R' | `{R : Type u} {A : Type v} {R' : Type w}` and their three `CommRing` instances |
| Maps R → A and arbitrary R → R' | `[Algebra R A] [Algebra R R']`, whose structure maps are the given ring maps; every commutative ring homomorphism supplies its `toAlgebra` structure |
| R → A flat | `[Module.Flat R A]`; `RingHom.flat_algebraMap_iff` identifies this with the recorded `RingHom.Flat (algebraMap R A)` |
| A finitely presented over R | `[Algebra.FinitePresentation R A]` |
| b ≥ 0 and ordered f_1, ..., f_b | `{b : ℕ} (f : Fin b → A)` and `List.ofFn f`, preserving order |
| The sequence is A-regular | `(hreg : IsRegular A (List.ofFn f))`; this includes all prefix multiplication injections and nonzero final quotient |
| A/(f_1, ..., f_b) flat over R | `[Module.Flat R (A ⧸ Ideal.span (Set.range f))]`, with the canonical quotient algebra and scalar tower |
| A' = A ⊗_R R' | `A ⊗[R] R'`, the recorded module tensor product with Mathlib's canonical algebra tensor-product commutative ring instance |
| Multiplication and unit in A' | The standard instance has `(a ⊗ r) * (a₁ ⊗ r₁) = (a*a₁) ⊗ (r*r₁)` by `Algebra.TensorProduct.tmul_mul_tmul` and `1 = 1 ⊗ 1` by `Algebra.TensorProduct.one_def`; these specify the object, rather than adding conclusions |
| f'_j = f_j ⊗ 1 | `f j ⊗ₜ[R] (1 : R')` in both the membership hypothesis and conclusion |
| Every prime q' of A' containing every f'_j | `(q : Ideal (A ⊗[R] R')) [q.IsPrime] (hmem : ∀ j : Fin b, f j ⊗ₜ[R] (1 : R') ∈ q)` |
| Local ring A'_{q'} and each specified f'_j/1 | `Localization.AtPrime q` and `algebraMap (A ⊗[R] R') (Localization.AtPrime q) (f j ⊗ₜ[R] (1 : R'))` |
| Ordered images form a regular sequence in that local ring | `IsRegular (Localization.AtPrime q) (List.ofFn fun j : Fin b ↦ ...)`, including its nonzero final quotient clause |

All universes and variables are explicit; `set_option autoImplicit false` is enabled.
The three ring universes are independent, so the statement excludes no ring-size case.
There is no flatness, finite-presentation, Noetherian or nontriviality assumption on R'.

The recorded statement dependencies were read in full with their source declarations:

- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`,
  `RingHom.flat_algebraMap_iff`; module flatness is `Module.Flat` from
  `Mathlib.RingTheory.Flat.Basic`. The algebra-map equivalence justifies using the class.
- `def-weil-pbc-finitely-presented-algebra`: `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation`, which is a finite polynomial presentation with FG kernel.
- `def-weil-pbc-regular-sequence`: `Mathlib.RingTheory.Regular.RegularSequence`,
  `RingTheory.Sequence.IsRegular`; its inherited `IsWeaklyRegular` specifies injectivity
  on each preceding quotient, and `top_ne_smul` specifies the nonzero final quotient.
- `def-weil-pbc-module-tensor-product`: its Mathlib match `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, used through
  `Mathlib.RingTheory.TensorProduct.Basic` for the required ring structure.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`, localization at the complement of the prime.

Proof-plan imports include the two currently recorded Sheaf proof dependencies:
`Sheaf.RingTheory.RegularSequenceGradedPolynomial` (`Ideal.regularSequence_gradedPolynomial`)
and `Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood`
(`RingTheory.exists_isRegular_localizationAway_of_isRegular_localizationAtPrime`).
Their full statements and docstrings were read. The module also imports the recorded
Mathlib/upstream proof leaves for Noetherian spectra, exact localization, flat-quotient
tensor injection, weak regularity after localization, and
`Algebra.exists_notMem_isRegularPrincipal_and_flat_of_fiber` in
`WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.
The two new stage-1 quasi-regularity proof nodes have no Lean record or Mathlib match
and introduce no object needed for this statement; their proof steps remain in the
DAG and in the theorem docstring. The theorem docstring follows all six node steps,
including the prefix-flatness induction and tensor/quotient/localization maps.

Source reading: `literature/stacks-project/divisors.tex`,
`remark-relative-regular-immersion-elements` (0FUD) and
`lemma-relative-regular-immersion-flat-in-neighbourhood` (063U), including its proof;
`literature/stacks-project/more-algebra.tex`,
`lemma-relative-regular-immersion-algebra` (0CEP), including its proof.
The source remark's unqualified phrase "every prime" needs the containing-equations
restriction when regularity includes a proper final quotient. The reviewed node already
has exactly that restriction, and the delivery preserves it. For example f=t in k[t]
at (t-1) becomes a unit, so cannot be a regular sequence under the node's definition.
This is a source wording fault already documented in Q12's review, not a new node fault.
No `STATEMENT-DISPUTED` flag is needed for the node as stated.

Edge cases checked mathematically before drafting:

- b=0 is included by `Fin 0` and `List.ofFn`; the conclusion is the empty regular
  sequence in a nonzero prime localization. Prime existence supplies nontriviality.
- If the tensor-product ring is zero (including R' the zero ring), there is no prime q,
  and the universally quantified assertion has no prime instance.
- A zero ambient A admits no A-regular sequence, including the empty sequence, because
  its final quotient is zero. A unit among the f_j is likewise excluded by regularity.
- For nonflat base change, take R=A=ℤ[t], f=t and R'=R/(2). The final quotient ℤ is
  flat as an R-module only if t acts injectively, which fails, so this is not an
  admissible example. A valid test is R=ℤ, A=ℤ[t], f=t and R'=ℤ/2: A and A/(t)=ℤ
  are flat over ℤ, R' is not, and t stays regular in the local ring at (t).
- The containing-equations hypothesis ensures the final quotient is nonzero: it maps
  onto the residue field at q. There is no unsupported extension to primes off V(f).
- Nothing assumes R or A Noetherian: the proof plan asserts Noetherianity only for
  the finite-type fibre over a residue field.

Searches for an existing declaration (2026-10-17):

- `msearch.py leanfinder`: "A regular sequence in a flat finitely presented algebra with
  flat quotient remains regular locally at primes containing the equations after
  arbitrary base change". Eight hits: flat base-change and faithfully flat base-change
  results, weak regularity under tensoring with a flat module, and prime-localization
  regularity. None supplies this arbitrary-base-change conclusion from ambient and
  final-quotient flatness.
- `msearch.py loogle`: `RingTheory.Sequence.IsRegular, Localization.AtPrime`.
  Service succeeded, zero hits.
- `msearch.py grep`, Mathlib `RingTheory`:
  `IsRegular.*(Tensor|baseChange)|IsWeaklyRegular.*(Tensor|baseChange)`.
  Seven hits in Regular/Flat and Regular/RegularSequence; none is the item.
  The full raw query records are in this sandbox's `searches.jsonl`.
- `rg` in `WeilConjectures` and `lean/Sheaf` for relative regularity, regular base change,
  `isRegular.*[Bb]ase|regular.*flat.*quotient|flat.*[Rr]egular.*[Ss]equence`, and
  `grep -rn` for the exact node id in `WeilConjectures`: no exact declaration.
  Existing relative-complete-intersection and fibre-Cartier statements are different
  interfaces; the source regular-sequence flat-map lemmas assume a flat changing map.

Validation: `scompile.py NY lem-pur-relative-regular-equations-base-change` compiled the
module cleanly, both sandbox and library-path probes, with no errors or warnings.
The overlay also compiled the graded-polynomial dependency successfully. The node copy
was programmatically checked to differ from the shared node only in `lean`. Every
Lean line has at most 100 characters. The independent second reading is left to the
second worker as required. Delivery is dry-run only; nothing is pushed.

## Second reading by NY

I independently opened the item JSON, its Lean module, each of its five statement-dependency
nodes, and the actual Mathlib declarations those nodes record. I read Stacks
`divisors.tex`, Section Relative regular immersions, the statement and proof of
`lemma-relative-regular-immersion-flat-in-neighbourhood` (063U), and
`remark-relative-regular-immersion-elements` (0FUD), together with
`more-algebra.tex`, `lemma-relative-regular-immersion-algebra` (0CEP), statement and
proof. There is no surrounding Noetherian, field, characteristic, or nontrivial-base
assumption. The node already restricts to primes containing the equations, as points of
Z in the 063U proof require. The unqualified "every prime" in 0FUD cannot include primes
off V(f) with the node's 00LF convention. This inherited restriction needs no new
statement correction. There is no `statement_change`, no new definition node, and no
dependency module in this packet. No repair note for this item is present.

My object/hypothesis/conclusion inventory and correspondence is as follows. Every row
passes; no hypothesis or conclusion clause is added, removed, weakened, or strengthened.

| Node inventory | Exact Lean rendering and verdict |
| --- | --- |
| Arbitrary commutative R and A, and map R to A | `{R : Type u} {A : Type v}`, `[CommRing R] [CommRing A]`, `[Algebra R A]`. PASS: the map is `algebraMap R A`; any ring map supplies its `toAlgebra` structure, so the algebra encoding does not restrict it. |
| This map is flat | `[Module.Flat R A]`. PASS: `RingHom.Flat` is the target module's flatness with the map's algebra structure, and `RingHom.flat_algebraMap_iff` identifies it with this exact instance. |
| A is finitely presented over R | `[Algebra.FinitePresentation R A]`. PASS: its `out` field is a surjection from `MvPolynomial (Fin n) R` with finitely generated kernel, exactly the recorded definition node. |
| Nonnegative finite length b, and the specified ordered f_1,...,f_b in A | `{b : ℕ} (f : Fin b → A)` and `List.ofFn f`. PASS: indices 0,...,b-1 encode indices 1,...,b without permuting the list. |
| That sequence is A-regular | `(hreg : IsRegular A (List.ofFn f))`. PASS: I read `IsWeaklyRegular.regular_mod_prev` and `IsRegular.top_ne_smul`, giving exactly injection on each ordered prefix quotient and a nonzero final quotient. |
| Final quotient A/(f_1,...,f_b) is flat over R | `[Module.Flat R (A ⧸ Ideal.span (Set.range f))]`. PASS: the ideal is the same as `Ideal.ofList (List.ofFn f)`; the quotient has the canonical R-action induced by R to A to the quotient, with no extra chosen action. |
| Any commutative R' and homomorphism R to R' | `{R' : Type w} [CommRing R'] [Algebra R R']`. PASS: no flatness, finiteness, or faithful-flatness condition on this map. |
| A' is A tensor_R R', with the stated product and unit | `A ⊗[R] R'`. PASS: I read the recorded `TensorProduct` quotient construction and `Algebra.TensorProduct.instCommRing`; `tmul_mul_tmul` gives the stated product and `one_def` gives `1 ⊗ 1`. These are the canonical ring structure, not omitted additional conclusions. |
| Each specified f'_j is f_j tensor 1 | `f j ⊗ₜ[R] (1 : R')`. PASS: used unchanged both in `hmem` and in the localized list. |
| For every prime q' of A' containing all f'_j | `(q : Ideal (A ⊗[R] R')) [q.IsPrime] (hmem : ∀ j : Fin b, f j ⊗ₜ[R] (1 : R') ∈ q)`. PASS: the prime is quantified after the arbitrary base change and the sequence. |
| The local ring A' at q', and each specified image f'_j/1 | `Localization.AtPrime q` and `algebraMap (A ⊗[R] R') (Localization.AtPrime q) (f j ⊗ₜ[R] (1 : R'))`. PASS: `Localization.AtPrime` is localization at `q.primeCompl`, with the fraction map sending a to a/1. |
| Those images, in the original order, form a regular sequence | `IsRegular (Localization.AtPrime q) (List.ofFn fun j : Fin b ↦ ...)`. PASS: this has both prefix injectivity and the nonzero final-quotient clause, with no existential replacement of the equations. |

The dependency signatures were checked in their actual source files:
`RingHom/Flat.lean:27,31`, `Flat/Basic.lean:113,316`,
`FinitePresentation.lean:44`, `Regular/RegularSequence.lean:135,140,146`,
`LinearAlgebra/TensorProduct/Defs.lean:81,107`,
`RingTheory/TensorProduct/Basic.lean:113,155,478`, and
`Localization/AtPrime/Basic.lean:53,57` in the pinned Mathlib. These are the recorded
notions, not similar names. In particular the module uses regular *sequences*, not
regular rings or regular ring homomorphisms. I also read the two Sheaf proof imports
`Ideal.regularSequence_gradedPolynomial` and
`RingTheory.exists_isRegular_localizationAway_of_isRegular_localizationAtPrime`, and the
upstream fibre-Cartier declaration
`Algebra.exists_notMem_isRegularPrincipal_and_flat_of_fiber` at `Fiber.lean:981`.
Their actual hypotheses support the planned uses: the Noetherian condition in the
neighbourhood lemma is on the fibre, and the fibre-Cartier criterion allows an arbitrary
base and supplies flatness of the next quotient. They are existing prerequisites, not
extra declarations delivered here.

The statement docstring carries all six node proof steps: empty length and regular to
polynomial graded algebra; arbitrary residue-field base change and Noetherian fibre;
exact localization and local quasi-regular to regular; spreading and lifting the fibre
denominator; the prefix-flatness induction using the all-primes fibre-Cartier criterion;
and tensoring each short exact sequence with arbitrary R', flipping factors, and
localizing the specified equations. The containing-prime hypothesis supplies the final
nonzero quotient through its residue field. The public imports serve the statement,
and the private imports are the recorded proof plan as required by stage 2. Both source
and blueprint tags are present. The only declaration is the named theorem with `sorry`
as its whole proof; there is no definition, private copy, hidden axiom, or proved helper.

Edge cases checked independently:

- b=0 is included: `Fin 0` yields the empty list and the containment hypothesis is
  vacuous. `q.IsPrime` guarantees that `Localization.AtPrime q` is nonzero, so its empty
  sequence is regular. No positive-length restriction occurs in Lean.
- A=0 gives no regular sequence, including the empty one, because the final quotient
  would be zero. This is exactly the node's convention, not an extra Lean hypothesis.
- R'=0, or any zero tensor ring A', has no prime q and the conclusion is vacuous.
  Equivalently the corresponding empty spectrum has no local ring to test.
- A unit among the equations is excluded by the original regularity, and after base
  change by containment in q. The example k[t], f=t, q=(t-1) is correctly outside the
  conclusion's quantified primes; dropping `hmem` would be wrong.
- R=Z, A=Z[t], f=t, R'=Z/2 is an allowed nonflat change with flat ambient and quotient
  and the expected regular t at the prime (t). Conversely R=A=Z, f=2, R'=Z/2 fails
  quotient flatness and therefore supplies no counterexample.
- Repeated or zero equations in positive length fail prefix injectivity in the
  relevant nonzero quotient. The hypotheses detect them without a separate assumption.
- All characteristics are covered. Universes u, v, w are explicitly declared and
  independent. No test-algebra quantifier, universe equality, field instance,
  Noetherian instance, or Nontrivial instance silently narrows the statement.

Independent duplicate searches (2026-10-17), with queries different from the first
worker's main query:

- `msearch.py ... leanfinder "regular sequence flat finitely presented algebra arbitrary
  tensor base change localization prime"` returned eight candidates. I inspected the
  actual types and `Regular/Flat.lean`: `IsWeaklyRegular.of_flat` and
  `of_flat_of_isBaseChange` assume the *changing* algebra flat; the faithfully-flat
  regularity lemmas and flat-module tensor lemmas likewise do not assert this node.
- `msearch.py ... loogle "RingTheory.Sequence.IsRegular, Localization.AtPrime"`
  succeeded with zero hits.
- `msearch.py ... grep "IsRegular.*quotient|IsRegular.*base|IsWeaklyRegular.*flat"`
  returned fourteen hits, chiefly the same flat-change lemmas and unrelated language
  regularity. No exact statement was found. Raw searches are in `searches.jsonl`.
- I ran `rg` independently over Mathlib, `WeilConjectures/`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, using regular-sequence, tensorProduct, baseChange,
  relative regularity, flat quotient, and the exact proposed declaration name.
  The project complete-intersection localization lemmas start from polynomial
  presentations and have different hypotheses; regular-fibre base change concerns
  regular *rings*. The smooth-coordinate module cites this node in its proof and
  does not state it. No duplicate of this theorem or notion was found.

No mathematical mismatch was found and no Lean or node content needed rewriting.
I appended only this independent second-reading record and the fresh search logs.
I checked that the sandbox node differs from the shared node only by its `lean` record,
that `lean.statement` is verbatim the module's signature, that every Lean line is at
most 100 characters, and that `autoImplicit false` leaves no unbound variable or universe.
The prescribed `scompile.py NY lem-pur-relative-regular-equations-base-change` invocation
compiled the sole delivered module cleanly in both the sandbox and library-path probes
(1.7 s and 2.1 s respectively), with no error or warning. The required final dry run and
push follow this reading.
