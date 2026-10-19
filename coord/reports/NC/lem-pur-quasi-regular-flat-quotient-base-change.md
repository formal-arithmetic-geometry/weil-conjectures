## Worker report

Recovery note: the retained sandbox contained only dispatcher markers, with no node,
Lean source or report. The second reader reconstructed the missing delivery in this
session; there was no earlier worker report or review section to preserve. This
section records the reconstruction rather than attributing it to an absent worker.

Module: `Sheaf.RingTheory.QuasiRegularFlatQuotientBaseChange`.
Declaration: `Ideal.quasiRegular_flatQuotient_baseChange`, with its sole proof `sorry`.
No new definition, dependency repair, or natural-language statement correction.

The statement is Stacks 0CEP (1), using R,A,R' for the source's A,B,A'. Its canonical
map is the landed `Ideal.regularSequenceGradedPolynomialMap` from
`Sheaf.RingTheory.RegularSequenceGradedPolynomial`. Despite its name, this definition
has no regularity hypothesis: it is polynomial evaluation at the degree-one classes
of any finite family. The existing node `lem-pur-regular-sequence-graded-polynomial`
was added to stmt_deps solely to cite this canonical construction, without using or
assuming that node's regular-sequence theorem.

The rings are independent-universe `CommRing` types, the two structure maps are
`Algebra R A` and `Algebra R R'`, and `f : Fin b → A` is the finite sequence. The
ideal and quotient are `Ideal.span (Set.range f)` and `A ⧸ Ideal.span (Set.range f)`.
Quotient flatness is the corresponding `Module.Flat R` instance; input quasi-regularity
is `Function.Bijective (regularSequenceGradedPolynomialMap f)`. The conclusion is
bijectivity of that same map for `fun j ↦ f j ⊗ₜ[R] (1 : R')` in `A ⊗[R] R'`.

Dependency signatures read: Mathlib's `MvPolynomial`, `MvPolynomial.aeval` and
`MvPolynomial.algHom_ext`; `Ideal.Quotient.algebra` and `Ideal.Quotient.mkₐ`;
`Module.Flat` and its injectivity characterization; `TensorProduct` and its algebra
multiplication; the recorded `Ideal.associatedGraded`, `associatedGradedPiece`,
`associatedGradedAlgebra`, and product/scalar formulas. The published associated-graded
module was also read with `scompile.py --source WeilConjectures.RingTheory.AssociatedGradedRing`.
The canonical map's current source was read with `scompile.py --source
Sheaf.RingTheory.RegularSequenceGradedPolynomial` and agrees with the local definition.

The proof docstring carries all eight DAG proof steps. Proof-leaf interfaces were
checked: `Module.Flat.directSum`, `Module.Flat.of_linearEquiv`,
`DirectSum.linearEquivFunOnFintype`, `LinearMap.lTensor_injective_of_exact_of_flat`,
`LinearMap.lTensor_exact` and `LinearMap.rTensor_exact`. The necessary flatness and
right-exactness modules are imported; no proof dependency requires a new module.

Edge cases: `b = 0` is permitted; `CommRing` allows the zero ring, and no `Nontrivial`
instance appears. Thus zero quotients and a zero tensor-product ring are included.
All characteristics are allowed. There is no base-flatness, ambient-flatness,
Noetherian, finite-presentation, field, locality or nonempty-sequence assumption.

Searches (2026-10-17):
- LeanSearch via msearch: "A finite quasi regular sequence remains quasi regular under
  scalar extension if its quotient is flat". Hits were ordinary/weak regular-sequence
  preservation under flat or faithfully flat scalar extension, not this statement.
- LeanFinder via msearch: "Bijectivity of polynomial map to associated graded ring
  after base change with flat quotient". Hits included base change of bijective ring
  homomorphisms, integral closure and unrelated geometric maps; none supplies the
  associated-graded base-change comparison with only quotient flatness.
- Grep via msearch: `quasiregular|quasiRegular|quasi_regular|gradedPolynomialMap`.
  Hits were quasiregular elements of nonunital rings, a different notion.
- Direct rg over pinned Mathlib, upstream WeilConjectures, and project lean/Sheaf,
  using `associatedGraded`, `AssociatedGraded`, quasi-regular spellings and the proposed
  theorem name. The project canonical map was found and reused. No existing theorem
  states this quotient-flat arbitrary-base-change result. Mathlib regular sequences
  explicitly list quasi-regular sequences as TODO.

## Second reading by NC

I read the node and Stacks more-algebra.tex, lemma-relative-regular-immersion-algebra
(Tag 0CEP), part (1), together with algebra.tex, definition-quasi-regular-sequence
(Tag 061P), its preceding displayed map, and the global ring conventions. The source
assumes only commutative unital rings (including the zero ring), quotient flatness and
quasi-regularity; there is no implicit finiteness or Noetherian condition to restore.
The node already says precisely this. No `statement_change` or citer audit is needed.

Object/hypothesis/conclusion checklist, established before reconstructing the module
and rechecked against its final text:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| R,A,R' commutative rings | `R : Type u`, `A : Type v`, `R' : Type w`, three `CommRing` instances | Exact; independent universes |
| Ring maps R → A and R → R' | `[Algebra R A] [Algebra R R']` | Exact; commutative algebras encode arbitrary unital ring maps |
| Integer b ≥ 0 and the b elements | `{b : ℕ} (f : Fin b → A)` | Exact, including b = 0 |
| J generated by this family | `Ideal.span (Set.range f)` inside the canonical map and quotient | Exact; no unrelated ideal parameter |
| C = A/J and C flat over R | `[Module.Flat R (A ⧸ Ideal.span (Set.range f))]` | Exact quotient action via the given structure map |
| Canonical C-polynomial-to-gr_J map is an isomorphism | `hf : Function.Bijective (regularSequenceGradedPolynomialMap f)` | Exact fixed algebra map, not an arbitrary isomorphism |
| A' = A tensor_R R', with stated multiplication and unit | Inferred ambient type of `f j ⊗ₜ[R] (1 : R')` with `Mathlib.RingTheory.TensorProduct.Basic` | Exact multiplication on pure tensors; unit 1 tensor 1 |
| f'_j = f_j tensor 1, J' generated by f', C' = A'/J' | Input `fun j ↦ f j ⊗ₜ[R] (1 : R')` to the same canonical map | Exact; its signature forms this generated ideal and quotient |
| The canonical graded C'-algebra map is an isomorphism | Conclusion `Function.Bijective (regularSequenceGradedPolynomialMap ...)` | Exact; bijective canonical graded algebra map |
| No flatness of R', flatness of A, Noetherian or finite-presentation hypotheses | Full binder list contains none of these | Exact |

For the two isomorphism clauses, I opened the map definition: its domain is
`MvPolynomial (Fin b) (A ⧸ Ideal.span (Set.range f))` and its codomain is precisely
`Ideal.associatedGraded (Ideal.span (Set.range f))`, as an algebra over that quotient.
`MvPolynomial.aeval` sends X_j to `DirectSum.of ... 1 (Submodule.Quotient.mk ⟨f j, ...⟩)`.
Thus constants have degree zero and each generator has degree one. Products and sums
show that this fixed map preserves homogeneous degree for every family, with no
regularity premise. Bijectivity therefore gives an algebra inverse, and the direct-sum
decomposition makes that inverse preserve degree as well. No extra homogeneity
hypothesis is being silently required or conclusion clause lost. In particular the
regular-sequence hypothesis of `Ideal.regularSequence_gradedPolynomial` is neither
assumed nor used; only its unconditional map definition is reused.

I read the actual associated-graded dependency definitions: its nth piece is the
quotient of J^n by the comap of J^(n+1), its carrier is the direct sum, its product is
the product of representatives, and its quotient-algebra structure is the degree-zero
inclusion. This is the node's notion, including degree zero, not an abstract graded
ring with similar notation. The canonical-map dependency's statement and signature
were opened as well; adding its node as a dependency introduces no new hypothesis.
No new nodes or dependency modules are delivered, so H12/H13 add no further work.

Edge-case rereading: `Fin 0` requires no element, there is no `Nonempty` instance, and
the generated empty ideal is zero. In degree zero the canonical map is the coefficient
inclusion; positive degrees for an empty family vanish. Zero rings/zero quotients are
allowed and no characteristic is restricted. `u`, `v`, `w` are explicitly bound and
independent; tensor products and the canonical map admit their maximum universe.
There is no geometric object or scheme-size condition in this algebraic statement.

Independent search queries and results are recorded above. I inspected the close
Mathlib matches: weak/ordinary regular-sequence base-change results impose flatness
of the extension, so cannot replace this theorem. The project's canonical map is the
same map needed here and was reused instead of defining a second copy.

Mismatches found and repaired: the entire delivery packet was missing, not merely
uncompiled. I reconstructed the node copy, theorem module and report; reused the
landed canonical map and cited its owning node; supplied the complete eight-step
proof docstring and all ring universes explicitly. No mathematical defect was found
in the natural-language node, and no definition or theorem was duplicated. The only
new theorem proof is `sorry`; there is no definition with postponed data.

Validation: `scompile.py NC lem-pur-quasi-regular-flat-quotient-base-change` compiled
the delivered module as both sandbox and library source cleanly under the default
60-second per-file limit. The final signature was copied verbatim into `lean.statement`.
