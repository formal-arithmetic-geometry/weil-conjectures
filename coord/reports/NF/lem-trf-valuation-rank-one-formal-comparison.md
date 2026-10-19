## Worker report

The delivery states `ValuationRing.valuation_rank_one_formal_comparison` in
`Sheaf.TraceFormula.ValuationRankOneFormalComparison`. Its conclusion uses the transparent
predicate `ValuationRing.HasRankOneFormalComparison` to bind normed realizations of the actual
localized adic completions. This is a packaging of the conclusion, not an additional hypothesis.
All original statement text, proof steps, and proof dependencies are unchanged. The two new
statement dependencies supply the missing analytic predicates and canonical completed ring map.

Source checked: Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
Theorem 3.5.5, Step 3, printed pp. 22–23, and the analytic input in Step 2.
The Huji PDF URL timed out in the web reader; the same primary paper was read at
https://arxiv.org/pdf/0707.3953, particularly the text beginning “Step 3. Decompletion”.
No source-file or target-statement correction is proposed.

Hypotheses and object identifications, with the node and final file read together:

- The separably closed field is `(K : Type u) [Field K] [IsSepClosed K]`.
- The valuation ring is `(V : Type v) [CommRing V] [IsDomain V] [ValuationRing V]`,
  with `[Algebra V K] [IsFractionRing V K]`. These express the specified inclusion in
  its fraction field; Mathlib's fraction-ring map is injective for a domain. There is
  no independently chosen fraction field or a discrete-valuation hypothesis.
- Height one is `hheight : ∀ p : Ideal V, p.IsPrime → p = ⊥ ∨ p =
  IsLocalRing.maximalIdeal V`. The nontriviality condition follows from the specified
  `π ≠ 0` and `π ∈ IsLocalRing.maximalIdeal V`: a field could not satisfy these.
- The chosen element is `(π : V) (hπ : π ≠ 0) (hπm : π ∈ ...maximalIdeal V)`.
- The algebra is `(A : Type w) [CommRing A] [Algebra V A]
  [Module.Flat V A] [Algebra.FinitePresentation V A]`.
- Geometric reducedness is `hgeom : @Algebra.IsGeometricallyReduced K (A ⊗[V] K)
  ... Algebra.TensorProduct.rightAlgebra`. The explicit final argument supplies the
  correct K-action on the right tensor factor. Mathlib's algebraic-closure test is
  equivalent to reducedness after every field extension; it is not merely reducedness
  of `A_K`, separable geometric reducedness, or a finite-extension-only test.
- `Vh`, `Ah`, `Eh` in the predicate are actual `AdicCompletion` objects for the indicated
  principal ideals. `Kh` and `C` are actual `Localization.Away` objects. The lets are
  only aliases in the body of a transparent definition; the theorem signature has none.
  In the finite-intermediate clause, `πE := algebraMap A E (algebraMap V A π)` agrees
  with `algebraMap V E π` by the scalar-tower identity. This form makes the domain of
  the actual completed inclusion `jA` definitionally equal to its stated codomain.

Every conclusion clause is present:

- `∃ F nf hu B nb, HasRankOneFormalComparison ...` binds the normed structures instead
  of assuming a norm, completeness, algebraic closedness, or an analytic comparison.
- `eF : Localization.Away πh ≃+* F` identifies the exact `Vh[1/π]` with the normed
  field. `CompleteSpace F ∧ IsAlgClosed F` gives both field conclusions.
- `IsUltrametricDist F` gives the nonarchimedean inequality for its real-valued norm.
  `0 < ‖(eV πh : F)‖ ∧ ‖(eV πh : F)‖ < 1` makes it nontrivial. No rank/discreteness
  convention is implicit: a nontrivial real norm is exactly the node's rank-one convention.
- `W : Subring F`, `eV : Vh ≃+* W`, the equality
  `↑(eV x) = eF (algebraMap Vh Kh x)`, and
  `∀ x, x ∈ W ↔ ‖x‖ ≤ 1` identify the actual completed valuation ring with the unit ball
  under the same localization map. `iK` extends V's original map to K. These are
  structural identifications, not a substitute abstract valuation ring.
- `jV := AdicCompletion.principalRingMap (algebraMap V A) π` is the coordinatewise
  canonical completed scalar map. `RingHom.Flat jV` states flatness over `Vh`.
- `RestrictedSeries.IsTopologicallyFinitelyPresented W Ah (jV.comp eV.symm.toRingHom)
  (eV πh)` states finite restricted-series presentation, a finitely generated relation
  ideal, scalar compatibility, and the adic quotient topology.
- `eC : C ≃+* B` transports the norm of the realization B to the actual localized
  completion. The commutation equation for `scalar : F →+* B` makes this the canonical
  `Kh`-algebra structure, not an arbitrary field action.
- `IsReduced B` transports to precisely `IsReduced C` through `eC`.
  `RestrictedSeries.IsAffinoidQuotient F B scalar` gives a finite Tate restricted-series
  quotient, its actual quotient Gauss norm, and completeness. The topology is the norm
  topology, not coefficientwise convergence of formal series.
- `HasBoundedTopologicallyGeneratedImage W Ah B ...` says the image of `Ah` in C is
  uniformly norm-bounded and admits a finite tuple whose polynomial W-algebra is dense
  in that image, using the topology induced from C. It does not assert that polynomials
  over W are dense in all of C.
- The scalar-saturation clause quantifies over every flat finitely presented V-algebra
  E in the common enlarged universe, every `s : V` with `s ≠ 0`, and every `x : E`.
  The iff compares membership of its completion image in the principal ideal generated
  by s with membership of x in `Ideal.span {algebraMap V E s}`. Thus it expresses the
  inverse-image equality, without treating E as a subring of its completion.
- The last clause quantifies over `E : Subalgebra A (A ⊗[V] K)`, with
  `[Module.Finite A E] [Module.FinitePresentation A E] [Module.Flat V E]
  [Algebra.FinitePresentation V E]`. The subalgebra gives the actual intermediate
  inclusion and A-structure, rather than an arbitrary auxiliary map.
- `tensorIso : (Ah ⊗[A] E) ≃+* Eh` has the pure-tensor characterization
  `tensorIso (a ⊗ₜ e) = jA a * algebraMap E Eh e`. Hence it is the canonical tensor
  comparison, not a bare assertion that two unrelated rings are isomorphic.
- `t : A ⊗[V] K →+* B` is fixed on every pure tensor by the completed A-map and `iK`.
  The map `g : Eh →+* B` is injective, continuous for the principal adic topology, agrees
  with `t` on every original element of E, and agrees with the C-localization map on
  the completed A-subring. Since E is dense in its adic completion and B is Hausdorff,
  this characterizes the induced completed inclusion uniquely.
- `localizedIso : Localization.Away (algebraMap E Eh πE) ≃+* B`, agreeing with `g` on
  every completed element, gives the canonical `Eh[1/π] ≅ C`, through `eC.symm`.
- No hypothesis or clause states injectivity of `A → Ah` or `E → Eh`.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (and the recorded companion
  `IsSepClosure`, which is not needed in this statement).
- `Mathlib.RingTheory.Valuation.ValuationRing`: `ValuationRing`, its induced local-ring
  structure, and `ValuationRing.TFAE`, identifying the node's fraction-field condition.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its commutative-ring and algebra structures, `AdicCompletion.evalₐ`,
  `AdicCompletion.liftRingHom`. No second inverse-limit type is defined.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`; its underlying module notion is
  `Module.Flat` from `Mathlib.RingTheory.Flat.Basic`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- The two new modules: `RestrictedSeries.constants`,
  `RestrictedSeries.IsTopologicallyFinitelyPresented`, `RestrictedSeries.IsAffinoidQuotient`,
  `RestrictedSeries.HasBoundedTopologicallyGeneratedImage`, and
  `AdicCompletion.principalRingMap`.
- Existing Mathlib notions also used directly: `Algebra.IsGeometricallyReduced`,
  `Localization.Away`, `IsAlgClosed`, `CompleteSpace`, `NormedField`, `NormedCommRing`,
  `IsUltrametricDist`, `Subalgebra`, and the algebra tensor product. These are not redefined.

Available proof dependencies are imported non-publicly: tower-limit exactness, fields
excellent, finite-type/localization excellent, regular-map reduced target, completion
Noetherianity, valuation torsion-free flatness, localization reducedness/Noetherianity,
Krull intersection, and the completion-mod-power results. The excellent-ring/G-ring
interfaces are supplied by those imports. The height-one absolute-value lemma,
separable-monic approximation, and affinoid/algebraic local-completion comparison have
no Lean records on the read base, so there is no proof-only module to import for them.
Separable polynomial factorization is available through `Mathlib.FieldTheory.IsSepClosed`.
No missing proof theorem is used to define data.

Edge cases checked mathematically against the final signatures:

- `A = 0`: `Ah`, C and B may all be zero. `NormedCommRing B` permits this (Mathlib even
  has `PUnit.normedCommRing`); only F is required to be a field. The quotient norm of
  the zero quotient is zero, and no `Nontrivial A/B/E` assumption appears.
- `π` invertible in A, e.g. `A = V[1/π]`: completion is zero even for nonzero A.
  Saturation still holds because every nonzero s divides a power of π in V, so s is
  already invertible in A. The completion maps have no injectivity requirement.
- `E = A` and `E = 0` when A is zero: tensor and localization characterizations give
  the expected identity comparisons, not excluded cases.
- Nondiscrete height-one valuations are included; only the two-prime condition occurs.
- Imperfect separably closed fields in positive characteristic are included: no
  `PerfectRing K`, characteristic-zero, or algebraic-closedness hypothesis on K is added.
- Empty variable tuples (`n = 0`), zero relation ideals and the unit relation ideal are
  allowed by `n : ℕ` and `ker.FG`.
- A unit s is allowed in scalar saturation; s = 0 is excluded exactly as in the node.
- K, V and A have separately bound universes u, v and w. Test E has universe
  `max u v w`, avoiding a test universe below the base; the intermediate subalgebra
  has its natural tensor-product universe. All variables and universes are explicit.

Searches made before writing:

- `msearch.py ... leanfinder`: “Completion of a height one valuation ring and flat
  finitely presented algebra gives reduced affinoid algebra and finite module completion
  comparison”: 8 hits, principally Dedekind-domain completions, not the theorem.
- `msearch.py ... loogle`: `AdicCompletion, Algebra.FinitePresentation, ValuationSubring`:
  0 hits.
- `msearch.py ... grep`: `TateAlgebra|RestrictedPowerSeries|restricted.series|
  IsGeometricallyReduced|Completion.*map`: general completion maps and geometric
  reducedness, no exact formal-comparison statement.
- Direct `rg` in Mathlib, WeilConjectures and `lean/Sheaf` found Mathlib's
  `MvPowerSeries.IsRestricted.subring`, `isRestricted_C`, and `gaussNorm`, all reused.
  No public affinoid/presentation predicate or exact target theorem was found.
- `rg` for this item id in upstream WeilConjectures and for the proposed declaration
  names in the upstream declaration index/source and Mathlib found no existing match.
- DAG and `blueprint_refs.py` searches found statements using affinoids and restricted
  series, but no definition node carrying the missing analytic predicates or principal
  completed ring map. Exact further queries and their returned hits are in the new nodes'
  `mathlib_searches` records. Private project completion maps were inspected; none gives
  an importable public interface. The new map reuses Mathlib's generic inverse-limit lift.

Validation: all three modules compiled separately, in dependency order, with the prescribed
`scompile.py NF lem-trf-valuation-rank-one-formal-comparison ...` wrapper, with no errors or
warnings. The only postponed theorems are the main comparison and the two named
well-definedness/compatibility obligations of the new coordinatewise map. Each has a source,
blueprint tag, and natural-language proof. Every definition contains real data or an explicit
predicate; there is no choice from an undetermined existence theorem.

## New nodes

`def-trf-restricted-series-presentation` defines the scalar constants, topological finite
presentation by restricted series with finitely generated relations, the Banach affinoid
quotient-norm predicate, and bounded finite topological generation of a model's image.
Source: Temkin, Theorem 3.5.5, Steps 2–3. The underlying series subring and Gauss norm are
existing Mathlib constructions and are reused exactly. The searches found no DAG or public
project declaration giving these presentation/model predicates. This node adds those
predicates rather than a new implementation of power series.

`def-trf-adic-ring-completion-map` defines the canonical ring map between principal adic
completions coordinatewise through `AdicCompletion.liftRingHom`. Its two postponed
obligations are exactly the ideal-power containment and residue compatibility explicitly
included in the node's statement. Source: the functorial completion maps in Temkin's
Theorem 3.5.5, Step 3. Mathlib's same-base `AdicCompletion.map` is linear and does not provide
this varying-base ring map. The generic lift is reused, and private local constructions
elsewhere in the project cannot be imported. No completion object is redefined.

## Second reading by NF

This is the author's second pass, not a claim of an independent sub-agent review; the
dispatcher explicitly prohibits starting other agents and the maintainer supplies the
independent review. I reopened the item, every statement dependency's record, the Mathlib
signatures/docstrings they designate, both new nodes, and the three final source files.
The hypothesis/clause correspondence above is the result of that reading.

The first main-file compile exposed a type mismatch between the two syntactic expressions
for π in the intermediate algebra. I changed its local alias to the image via A, so the
canonical completed inclusion has precisely the displayed codomain. This uses the existing
scalar-tower equality and changes no hypothesis or object mathematically. The supporting
modules needed `noncomputable` for Mathlib's actual ring structures, the qualified name
`Topology.IsQuotientMap`, and the explicit polynomial-evaluation import; these are repaired.
The second pass specifically checked that B can be zero, K is only separably closed,
the quotient topology/norm is present, topological density is only claimed in the model's
image, both finite and finite-presentation hypotheses remain, the completed inclusions are
characterized rather than arbitrary, and neither original completion map is assumed injective.
No remaining mismatch or disputed statement was found.
