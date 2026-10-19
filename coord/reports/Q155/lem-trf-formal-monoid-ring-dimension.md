## Worker report

The module `Sheaf.RingTheory.FormalMonoidRingDimension` states
`AddMonoidAlgebra.formalMonoidRing_dimension`; its only proof is `sorry`.
No definition is introduced, and the node changes only in `lean`.

Hypotheses and constructions, clause by clause:

- The coefficient ring is `(D : Type u) [CommRing D] [IsRegularLocalRing D]`.
  The last class extends both `IsNoetherianRing D` and `IsLocalRing D`;
  the latter extends `Nontrivial D`. Thus nonzero, regular, Noetherian and
  local are all retained, without redundant instance binders.
- Complete and separated for the maximal ideal is
  `[IsAdicComplete (IsLocalRing.maximalIdeal D) D]`.
- The additive commutative monoid is `(T : Type v) [AddCommMonoid T]`.
  `hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative T)` uses
  the existing canonical-group-completion definition: finite generation,
  injectivity into its group completion, and saturation for all positive powers.
  `hsharp` says that an invertible element of its multiplicative type tag is
  additively zero. This is precisely sharpness, including the trivial monoid.
- Mathlib `AddMonoidAlgebra D T` is the finitely supported `D`-basis on `T`
  with convolution multiplication; `single t 1` is the node's `[t]`.
- `a` is a name for the precise ideal, fixed by `ha` to the supremum of the
  extended maximal ideal and the span of nonzero basis monomials. It is not
  an arbitrary adic ideal. `AdicCompletion a (AddMonoidAlgebra D T)` is `H`,
  the inverse limit of its power quotients with its canonical ring structure.
- `L` is likewise fixed by `hL` to the span in `H` of the canonical images
  of all the nonzero basis monomials. `AdicCompletion.of` is the canonical
  completion map. These ideal equations merely name the node's objects.

Conclusions, clause by clause:

- The first three conjuncts are `IsNoetherianRing H`, `IsLocalRing H`, and
  `IsDomain H`.
- The fourth conjunct is `ringKrullDim H = ringKrullDim D + r`, where `r` is
  `Cardinal.toENat (Module.rank ℚ (TensorProduct ℤ ℚ
  (Additive (Algebra.GrothendieckGroup (Multiplicative T)))))`, coerced to
  `WithBot ℕ∞`. This is the rational dimension of the actual group completion,
  exactly the definition of group rank in the recorded fs-log dependency.
  Fs sharpness ensures this rank is finite; no freeness hypothesis is added.
- The existential `e : (H ⧸ L) ≃ₐ[D] D` is the stratum identification.
  Its being a `D`-algebra equivalence means its inverse is the constant
  inclusion into `H/L`, so it is canonical, rather than a freely chosen
  unrelated ring isomorphism. Explicitly, the algebra equivalence from `D`
  to `H/L` is determined on every `d` by `commutes`; its inverse is unique.
  Therefore `e (Ideal.Quotient.mk L η)` is exactly the node's reduction.
- For every `η : H`, the two implications impose respectively membership of
  this reduction in the maximal ideal and nonmembership in its square.
- `Function.Injective (fun x : H => η * x)` states injective multiplication.
- `IsRegularLocalRing (D ⧸ Ideal.span {e (Ideal.Quotient.mk L η)})` is precisely
  the regular-local coefficient hypersurface conclusion.
- `ringKrullDim (H ⧸ Ideal.span {η}) + 1 = ringKrullDim D + r` and
  `ringKrullDim (D ⧸ Ideal.span {e (Ideal.Quotient.mk L η)}) + 1 = ringKrullDim D`
  are the two dimension drops. The additive form avoids subtraction in
  extended natural dimensions. Local Noetherian dimensions are finite; under
  the parameter hypothesis the coefficient dimension is positive. Hence these
  are exactly the displayed minus-one formulas, including all edge cases.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` is the self-module
  Noetherian predicate, equivalent to finite generation of every ideal.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing` extends
  Noetherianity and locality, with maximal-ideal span finrank equal to Krull
  dimension. This is the regular-local part of `def-weil-regular-scheme`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `IsAdicComplete`,
  `AdicCompletion`, its commutative-ring and scalar-algebra instances, and
  `AdicCompletion.of`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: imports the existing
  `AlgebraicGeometry.IsFineSaturatedMonoid` from
  `Sheaf.AlgebraicGeometry.LogRegularPair`, and uses the same rational-rank
  encoding in `EtaleLogStructure.characteristicRank`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, with values in
  `WithBot ℕ∞`.

All already stated proof dependencies are imported non-publicly:
`Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType.isNoetherianRing`),
`WeilConjectures.RingTheory.AdicCompletionNoetherian`
(`AdicCompletion.isNoetherianRing`, read from the live source using
`scompile.py --source`), `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
(`IsRegularLocalRing.isDomain` and `.quotient_span_singleton`),
`Mathlib.RingTheory.Length` (`Module.length_eq_add_of_exact`),
`Sheaf.RingTheory.HilbertSamuelGrowthDimension`
(`IsLocalRing.exists_hilbertSamuel_polynomial`), and
`Mathlib.RingTheory.KrullDimension.Regular`
(`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`).
The proof dependencies `lem-trf-fs-face-sharpening`,
`lem-trf-sharp-monoid-positive-grading` and
`lem-trf-monoid-completion-coefficients` have no recorded Lean declaration
in the shared DAG and are therefore not imported. They are proof inputs, not
missing statement notions. Their steps are retained in the theorem docstring.

Edge checks: when `T = {0}`, the monomial spanning sets are empty, `L = 0`,
`a` is just the extended coefficient maximal ideal, and completeness identifies
`H` with `D`; rank is zero, giving exactly the coefficient-ring assertions.
If `dim D = 0`, regular local `D` is a field, its maximal ideal is zero and
there is no reduction in `m` outside `m²`; the universal parameter clause is
vacuous. No zero ring enters via `D`, since locality is nontrivial. No free
monoid hypothesis is imposed: arbitrary singular sharp fs monoids are covered.
The universes `u v` are independent and explicitly bound. There is no `let`,
private notation, chosen algebra structure, hollow data or hidden hypothesis.

Searches for an exact existing declaration (all via `msearch.py Q155
lem-trf-formal-monoid-ring-dimension`, plus read-only source searches):

- LeanFinder: "The completion of the monoid ring of a sharp fine saturated
  monoid over a complete regular local ring is a Noetherian local domain of
  dimension coefficient dimension plus group completion rank". Eight hits,
  principally Dedekind-domain valuation completions and finite local Krull
  dimension; no formal-monoid dimension theorem.
- Loogle: `AddMonoidAlgebra, ringKrullDim`. Zero hits.
- Mathlib grep: `ringKrullDim.*(AddMonoidAlgebra|MonoidAlgebra)|
  (AddMonoidAlgebra|MonoidAlgebra).*ringKrullDim`. Zero hits, also checked
  directly against the pinned Mathlib source.
- LeanSearch: "The completed monoid algebra of a fine saturated sharp monoid
  over a complete regular local ring has Krull dimension the coefficient
  dimension plus the rank of the group completion". Eight hits, including
  `MvPolynomial.ringKrullDim_of_isNoetherianRing`, power-series dimension
  inequalities, and a finite-generation result for monoid algebras. None says
  the node's statement for arbitrary sharp fs monoids.
- `rg` against `WeilConjectures` for `formalMonoid|FormalMonoid|monoid.*Dimension|
  IsFineSaturatedMonoid`, and the required node-id grep: no match.
- `rg` against `lean/Sheaf` for `formalMonoid|FormalMonoid|
  IsFineSaturatedMonoid|completedMonoid` finds the fs predicate above and
  `CompletedMonoidSupportProjection`. The latter concerns a supported-series
  projection for lattice monoids, not this dimension or hypersurface statement.
- The proposed full declaration name was searched in `dag/lean_names_upstream.json`,
  upstream `WeilConjectures`, and `lean/Sheaf`; it is new.

Source checked: the ILO PDF at https://arxiv.org/pdf/1207.3648, printed p. 70
(PDF page index 75), VI 1.6(i)--(ii), gives the complete sharp-fs formal monoid
models and the parameter quotient in mixed characteristic. The DAG explicitly
identifies this theorem as the agent-supplied commutative-algebra refinement.
The full eight-step proof plan from the node is rendered in the docstring.
No statement fault or disputed claim was found; no correction is requested.

Validation: compilation and the prescribed delivery preflight are recorded below.

`scompile.py Q155 lem-trf-formal-monoid-ring-dimension
lean/Sheaf/RingTheory/FormalMonoidRingDimension.lean` passed on the server:
sandbox check 30.9 seconds, actual module check 21.5 seconds; no diagnostics.

## Second reading by Q155

Independent maintainer second reading, 2026-10-18, of immutable delivery
3b3d5f541bf407b71ac428a85d22c0f775963808. The reviewer did not write or
previously second-read this delivery. The original placeholder under this heading
has been replaced by the present actual reading; the Worker report above is retained.

The node and delivered module were read together, along with all six statement
dependency records and the exact underlying definitions. No mathematical mismatch
or statement correction was found:

- `D : Type u`, `CommRing D`, and `IsRegularLocalRing D` give exactly a nonzero
  regular Noetherian local commutative ring. Mathlib RegularLocalRing/Defs.lean:51
  extends IsLocalRing and IsNoetherianRing; LocalRing/Defs.lean:30 includes
  Nontrivial. No field, excellence, characteristic, or extra finiteness assumption
  is imposed. `IsAdicComplete (maximalIdeal D) D` includes separatedness.
- `T : Type v` and AddCommMonoid give the additive monoid. The predicate read in
  Sheaf/AlgebraicGeometry/LogRegularPair.lean:141 asserts finite generation,
  injectivity of the canonical Grothendieck-group map, and saturation for every
  positive power. `hsharp` identifies every unit with zero. It is the exact fs
  notion exposed through FineSaturatedLogBlowup, not an unrelated ambient group.
- AddMonoidAlgebra is the finitely supported coefficient algebra; `single t 1`
  gives the basis monomial and its convolution product is the required sum of
  exponents. `ha` fixes a to the extended coefficient maximal ideal plus the
  nonzero-monomial ideal. AdicCompletion is the compatible power-quotient limit,
  with componentwise ring operations. `hL` fixes L to the ideal generated by the
  canonical completion images. Neither ideal is arbitrary.
- The three initial conjuncts assert precisely Noetherianity, locality and the
  integral-domain property of H. The dimension conjunct uses ringKrullDim and
  the rational rank of the actual group completion. Fine saturated sharp monoids
  have finite free group completion, so Cardinal.toENat loses no rank information.
- The existential D-algebra equivalence `(H / L) ≃ₐ[D] D` gives the canonical
  quotient identification. Its inverse on every d must be the canonical scalar
  inclusion, by the algebra-equivalence commuting law, so there is no arbitrary
  identification affecting the parameter condition.
- The universal eta binder, membership in m, and nonmembership in m squared
  impose exactly the parameter condition on that canonical reduction. The
  subsequent clauses give injective multiplication, regular locality of the
  coefficient quotient, and both required dimension drops. Writing each drop
  as dimension plus one is equivalent to subtraction here: the dimensions are
  finite and the parameter forces positive coefficient dimension.

Source places read: ILO arXiv:1207.3648, PDF page 76 (index 75), printed p.70,
VI 1.6(i)--(ii), including its sharp fs monoid, equal-characteristic model and
mixed-characteristic parameter relation. The broader algebra assertion is
explicitly an agent-supplied refinement, rather than a verbatim ILO theorem.
Also read Stacks algebra.tex section-Noetherian (00FM), definition-Krull (00KE),
definition-regular-local (00KU), section-completion (00M9), definition-complete
(0317), proposition-dimension (00KQ), and more-algebra.tex
lemma-completion-dimension (07NV). These agree with the notions used here.

Read the eight node proof steps and their corresponding declaration docstring
steps. The zero-face sharpening and positive weight establish the lattice input;
finite-type and completion Noetherianity precede the coefficient-family argument;
constant coefficient and the convergent geometric series give the stratum and
locality; least exponents give the domain assertion; the monomial filtration
and upper/lower lattice counts give Hilbert--Samuel growth; the final parameter
step applies the nonzerodivisor dimension drop and regular hypersurface result.
Read the statements of all ten proof dependencies in the read-only group clone.
The imported exact declarations for finite type, length, Hilbert--Samuel growth,
regular-local domains, regular hypersurfaces, and quotient dimension supply the
claims taken from them. The completion-Noetherian source was additionally read
through `scompile.py --source WeilConjectures.RingTheory.AdicCompletionNoetherian`.
The three not-yet-stated proof lemmas are not missing objects in this statement;
they do not require a new helper or a statement-dependency repair.

Edge cases checked: for the trivial monoid both nonzero-monomial spanning sets
are empty, L is zero and H is D by completeness; rank is zero. For coefficient
dimension zero, m is zero and no element satisfies the parameter hypothesis, so
that clause is vacuous. Singular sharp fs monoids remain allowed. The zero ring
is excluded as required. Independent explicit universes u and v cover all sizes;
there is no silent universe equality, unbound object, or test-object restriction.

The report records LeanSearch, LeanFinder, Loogle and grep searches. Independent
read-only rg searches of pinned Mathlib, upstream WeilConjectures and group
lean/Sheaf found no existing formal-monoid dimension theorem or declaration-name
collision. LogRegularPair's fs predicate and FineSaturatedLogBlowup's rational-rank
encoding are reused; no second definition is introduced. CompletedMonoidSupportProjection
is about support projection, not this theorem. The module has no definitions,
one theorem proved only by sorry, source/blueprint docstrings and the complete
eight-step proof plan. All lines are at most 100 characters. Its nonpublic proof
imports are explicitly required by brief-stage2 section 3 even with a sorry body.

The node's lean.statement was compared programmatically with the exact theorem
signature up to `:= by` and is verbatim equal. The commit changes only the module,
the report, and the item's lean record; no statement or dependency delta occurs.
No new definition or dependency module needs review. The current shared route-pivot
dropped list has no intersection with this item's statement or proof dependencies;
there is no route-pivot repair note for this item and no dropped machinery or
pro-etale substitute is introduced.

Reproduction: ran the prescribed wrapper on the immutable module:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q155
lem-trf-formal-monoid-ring-dimension
snapshot/lean/Sheaf/RingTheory/FormalMonoidRingDimension.lean`.
Exit status 0; no diagnostics. The installed wrapper currently requests the server
side-overlay check and reported private artifacts under
`/dev/shm/nt-tmp/nt-local-compile-zqyff8fj/.lbuild`: sandbox check 39.2 seconds,
library check 7.6 seconds. This independently reproduces the worker's recorded
clean per-file compilation (30.9 and 21.5 seconds respectively).
No global build, live Lean write, direct SSH command, Git mutation, merge or
delivery was performed. Only the permitted reviewer files were written.

Finding H1/H11: the delivered Second reading section contained only a disclaimer,
not an actual independent reading. This complete replacement report repairs that
mechanical documentation defect. The Lean module and node record need no changes.
