## Worker report

This delivery states `AlgebraicGeometry.algebraic_relativeDualizing_isomorphic` in
`lean/Sheaf/RingTheory/AlgebraicRelativeDualizingIsomorphism.lean`. Its sole theorem has
proof `by sorry`; no definitions or subsidiary theorems are introduced. The source is
Stacks `dualizing.tex`, Definition 0E2C and Lemma 0E2D, in the node's Noetherian special
case. I opened both source passages and the native derived closed construction.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| A homomorphism R → A of commutative rings | `R A : Type u`, `[CommRing R]`, `[CommRing A]`, `[Algebra R A]`, with map `algebraMap R A` |
| R and A Noetherian | `[IsNoetherianRing R] [IsNoetherianRing A]` |
| Flat | `hflat : RingHom.Flat (algebraMap R A)` |
| Finitely presented | `[Algebra.FinitePresentation R A]` |
| B = A tensor_R A | The actual ring `A ⊗[R] A`, used in the third derived-localization binder and the shared helpers |
| First coprojection p1(a) = a tensor 1 | `relativeDualizingModuleFirstPullback R A` unfolds to `relativeDualizingDerivedExtension (Algebra.TensorProduct.includeLeft ...).toRingHom` |
| A as B-module through multiplication | `relativeDualizingModuleDiagonal R A` is `A[0]`, formed by `ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' R).toRingHom` |
| M,N in D(A) | `M N : DerivedCategory (ModuleCat.{u} A)` |
| Each pseudo-coherent over A | `hM : DerivedCategory.IsPseudoCoherent M` and `hN : DerivedCategory.IsPseudoCoherent N` |
| Separate finite intervals a_T ≤ b_T over R | `hMTor` and `hNTor` each bind their own `∃ a b : ℤ, a ≤ b ∧ ...` |
| Every R-module Q, every i outside the interval | `∀ (Q : ModuleCat.{u} R) (i : ℤ), i < a ∨ b < i → ...` |
| H^i(T tensor-derived_R Q) = 0 | `IsZero ((DerivedCategory.homologyFunctor ... i).obj (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj T) ⊗ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj Q)))` |
| Flat resolution tensor and injective resolution Hom | Shared `relativeDualizingDerivedExtension` is the K-flat left-derived extension; the native derived tensor is the K-flat total tensor, and its `ihom` is the total right-derived internal Hom using K-injective resolutions |
| RHom_B(A, M tensor-derived_{A,p1} B) isomorphic to A in D(B) | `hMHom : Nonempty (relativeDualizingModuleHom R A M ≅ relativeDualizingModuleDiagonal R A)` |
| Same condition for N | `hNHom` with N |
| There exists M isomorphic to N in D(A) | `Nonempty (M ≅ N)` |
| No generator chosen or compatibility required | No generator, class map, counit normalization condition, or equality between generators occurs in the signature |

`[Algebra R A]` is the usual encoding of the node's ring map, not a restriction to
another kind of map: every ring map induces this algebra structure. There is one
common arbitrary universe `u` for rings and tested modules, so the tests are not
in a smaller independent universe. The three `HasDerivedCategory.{u}` binders
record localization choices for module Grothendieck abelian categories, available
by the existing Grothendieck derived-category API. They are size infrastructure,
not additional ring or complex hypotheses. These are exactly the same native
module sizes as the landed affine-comparison declarations used by consumers.

The dependency declarations used, with their full definitions/signatures and
docstrings read in source:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`; its definition is flatness of
  the target via the ring map, equivalently `Module.Flat`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`; its
  finite polynomial presentation and finitely generated kernel give the node's
  finite presentation notion.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; the localization of cochain complexes.
- `Sheaf.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`,
  precisely an isomorphism to a bounded-above finite-free complex.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, the recorded site Hom. The module
  is publicly imported. The already landed affine comparison supplies its
  ordinary-module presentation by the native derived closed structure. In
  `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`,
  `DerivedCategory.internalHomQhObj` right-derives homotopy internal Hom using
  K-injective resolutions, and `DerivedCategory.monoidalClosed` transports it
  along the localization's representative isomorphism. Thus `ihom` here computes
  RHom in D(B), not Hom sets or an underived Hom object. No second Hom definition
  has been written. Since the hypothesis asks only for an isomorphism, the
  representative and sign-conjugate Hom-complex presentations do not add any
  choice or normalization to the assertion.
- `Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison`:
  `AlgebraicGeometry.relativeDualizingModuleHom`,
  `AlgebraicGeometry.relativeDualizingModuleDiagonal`,
  `AlgebraicGeometry.relativeDualizingModuleFirstPullback`, and
  `AlgebraicGeometry.relativeDualizingDerivedExtension`. This already landed
  node was added to `stmt_deps` under the explicit permission to cite landed
  notions. Its theorem is not assumed or applied; these are its existing helpers.
  The addition introduces no dependency on pair rigidity, the downstream consumer.

Proof-dependency modules imported without `public`:
`Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel` and
`Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`. Their theorem
signatures/docstrings were read. The other three named proof dependencies have
no recorded Lean module in the shared DAG at the time of this delivery, so there
is no import path for them yet. They remain named in the proof docstring, matching
all five proof steps of the unchanged node.

Edge cases checked against the definitions and source:

- Zero rings are allowed: there is no `Nontrivial`/domain/field hypothesis. For
  A = 0 the diagonal and both module-derived objects lie in the zero category.
- Identity R = A is allowed; the diagonal is A[0] and the two Hom hypotheses reduce
  to M and N each being isomorphic to A[0].
- Intervals may have length zero, and M and N may have different intervals.
  Negative degrees are admitted (`ℤ`). Every R-module is tested, without finite
  generation or flatness imposed on Q.
- The zero complex is not excluded; for nonzero A it fails the diagonal Hom
  hypothesis rather than being silently removed by a separate condition.
- No finite Tor dimension over A or B is imposed. Restriction to R appears only
  in the two Tor hypotheses; the diagonal Hom remains an object of D(B).
- Flat finitely presented maps of any characteristic and non-smooth/singular
  algebras are included. No lci, properness, or regularity is imposed.
- Shifted objects are covered; there is no degree-zero or selected-generator
  normalization beyond the two source isomorphism hypotheses.

Searches made on this item:

- `msearch.py ... leanfinder "Any two algebraic relative dualizing complexes of a flat finitely presented Noetherian algebra are isomorphic"`:
  8 results on smoothness/flatness and Kahler differentials, no uniqueness theorem.
- `msearch.py ... loogle "DerivedCategory, CategoryTheory.Iso"`:
  12 results on general localization/derived-category comparison isomorphisms,
  no relative-dualizing theorem.
- `msearch.py ... leansearch "Any two relative dualizing complexes for a flat finitely presented algebra are isomorphic"`:
  8 results on algebra equivalences, flat maps and base change of ordinary duals;
  no match for this node.
- `msearch.py ... grep "relative.dualizing|semidualizing"`: no Mathlib match.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for
  `relative.dualiz|semidualiz|algebraic_relative_dualizing` found only etale
  smooth-duality terminology, not this ordinary-module theorem.
- `grep -rn "lem-trf-algebraic-relative-dualizing-isomorphism"` in that upstream
  tree found no declaration.
- `rg` over the shared `lean/Sheaf` found the affine-comparison constructions
  above and pair-rigidity proof prose, but no theorem identifying two affine
  relative-dualizing objects. Those shared constructions are reused here.
- `rg` for the proposed full declaration name in Mathlib, upstream,
  `dag/lean_names_upstream.json`, and shared `lean/Sheaf` found no collision.

No statement correction, disputed statement, dependency repair, or new node.
Only `lean` and the addition of the landed helper-owning node to `stmt_deps`
change in the item's JSON.

## Second reading by Q103

This is the author's self-check, under the dispatcher's no-subagents instruction;
the maintainer supplies the independent reading. I reopened the node and the
written signature and checked the correspondence table above against both.
The two possible orientation errors were checked by opening the helper bodies:
`includeLeft` is used, and `lmul'` gives the B-action on both appearances of A.
`relativeDualizingModuleHom` is native derived internal Hom on D(B), with
`relativeDualizingModuleFirstPullback` as its target. The Tor test instead
restricts M or N to D(R), without assuming finite Tor amplitude over A/B.
Both isomorphism hypotheses are `Nonempty`, and the conclusion is exactly
`Nonempty (M ≅ N)` with no chosen comparison data. No extra geometric hypothesis
enters by importing the affine module: none of its theorem's scheme hypotheses
are binders of the helpers used here. No mismatch or statement change was needed.
