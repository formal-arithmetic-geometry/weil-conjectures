## Worker report

The module `Sheaf.RingTheory.PolynomialSimplicialTensorModel` states
`Algebra.CotangentResolution.polynomial_simplicial_tensor_model`, with one `sorry`.
It also constructs the precise augmented simplicial algebra/module and tensor
functor used in the statement. All helper definitions have real data and use
existing categorical constructions; none selects a witness of an existence theorem.
No new DAG notion or dependency repair is needed, and no node statement is changed.

Read source: `literature/stacks-project/cotangent.tex`, remark-resolution
(Tag 08QI), lines 666–704, and lemma-flat-base-change (Tag 08QP), lines 957–981.
The latter proof explicitly uses the monomial-free terms and equality of the
scalar-extended alternating complex with the alternating complex of the extended
simplicial algebra. Our node isolates that construction and does not claim that
an arbitrary augmentation is a resolution.

Hypotheses and clauses, in order:

- The ring map A→B is `f : Arrow CommRingCat.{u}`; the other ring map is the
  algebra structure of `A' : CommAlgCat.{u} f.left`. These introduce arbitrary
  commutative rings and arbitrary homomorphisms, including zero rings.
- The supplied augmented simplicial algebra is exactly the dependency's
  `P : Augmentation f`, not a new resolution structure. `hε` states surjectivity
  of every `P.augmentation.app (op ⦋n⦌)`. There is no `QuasiIso` hypothesis.
- The arbitrary variable sets are `I : ℕ → Type v`, with `v` independent of `u`.
  The chosen algebra identifications are `e n : MvPolynomial (I n) f.left ≃ₐ[f.left]
  (tensorModelAlgebra P).obj (op ⦋n⦌)`. This uses the inverse orientation of
  P_n≅A[I_n] and keeps exactly its scalar action.
- `tensorModelAlgebra P` is `Under.lift P.algebra P.base` followed by the existing
  equivalence `commAlgCatEquivUnder`. Its terms and ring operators are the
  supplied ones, now carrying their specified A-algebra structures.
  `tensorModelCocone P` uses `Under.liftCocone` with the actual augmentation and
  `P.triangle`, so its vertex is B with the specified A-action.
- `tensorModelModule` forgets multiplication, retaining this diagram and cocone.
  `negativeComplex` from the dependency is the alternating-face chain complex
  followed by extension along `ComplexShape.embeddingDownNat`; hence C^(-n)=P_n,
  the differential is the alternating sum of faces, and positive terms are zero.
  `tensorModelAugmentation` is the existing alternating augmentation extended by
  zero, so it is exactly q:C→B[0]. `tensorModelTarget` constructs that same target.
- The first conjunct gives a `Module.Basis (I n →₀ ℕ)` whose α-th vector is
  `e n (MvPolynomial.monomial α 1)`, and explicitly asserts `Module.Free` and
  `Module.Flat` for P_n. The next conjunct states preservation of `Function.Exact`
  sequences by both `LinearMap.lTensor` and `LinearMap.rTensor`.
- The following conjunct supplies the coefficient `LinearEquiv` F for every
  A-module `M : ModuleCat.{w} f.left`. Its formula on every p⊗m and coordinate α
  is `MvPolynomial.coeff α ((e n).symm p) • m`. Its inverse is the exact finite
  `Finsupp.sum` of monomial tensors from the node. `(I n →₀ ℕ) →₀ M` is the
  direct sum of the identical copies of M (finite-support-function realization).
  The last F clause is naturality for every module morphism g, using `lTensor`
  and `Finsupp.mapRange.linearMap`.
- `tensorModelExtension A'` constructs the scalar-extension functor on algebras,
  with terms `A' ⊗[A] S` and maps `Algebra.TensorProduct.map (AlgHom.id A' A') h.hom`.
  Its action is definitionally a'⊗p↦a'⊗h(p), so it extends all faces, degeneracies
  and augmentations. Applying `mapCocone` to `tensorModelCocone P` gives the
  augmented simplicial A'-algebra with vertex B'=A'⊗_A B. A simplicial diagram
  and its cocone are the standard augmented simplicial object encoding; no
  unprescribed replacement is existentially chosen.
- The next conjunct asserts surjectivity of every new augmentation. The e'
  conjunct is an A'-algebra equivalence from the actual tensor term to
  `MvPolynomial (I n) A'`, with formula e'(a'⊗X^α)=monomial α a'. This is precisely
  X^α⊗a'↦a'X^α in the node's tensor order.
- The last conjunct supplies a chain isomorphism ψ:TC≅s(P'), where T is
  `(ModuleCat.extendScalars (algebraMap f.left A')).mapHomologicalComplex`.
  `tensorModelTermIso` identifies cohomological degree -n with simplicial degree n;
  the equation says the ψ components are the identity on every a'⊗p under these
  identifications. All other terms are zero by extension by zero.
- The target isomorphism τ:T(B[0])≅B'[0] has the same identity normalization in
  degree zero via `tensorModelTargetIso`; away from zero both targets vanish.
  This is the canonical identification denoted T(B[0])=B'[0] in the node.
- There is explicitly an isomorphism φ **in DerivedCategory**, identified by
  `φ = DerivedCategory.Q.mapIso ψ`, and the concluding equation is
  `φ.hom ≫ Q.map q' = Q.map (T.map q) ≫ Q.map τ.hom`. Under τ it is exactly
  Q(q')∘φ=Q(Tq). Thus both the representative and the derived map are prescribed.

The tensor convention `A' ⊗_A P_n` is the recorded base-change dependency's
convention, related to the displayed P_n⊗_A A' by `TensorProduct.comm`. It changes
neither the scalar action nor any normalization. The coefficient tensor P_n⊗_A M
uses exactly the order in the node. The ring universe u, variable universe v,
test-module universe w and derived morphism universe z are separately bound.

Dependency declarations read and used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Augmentation`, `negativeComplex`. Read the full
  declarations and the `additiveAugmentation` construction; the latter is
  AddCommGrp-valued, so the helper here applies the same Mathlib augmentation to
  the supplied A-module action rather than redefining a resolution notion.
- `Mathlib.Algebra.MvPolynomial.Basic` / `.Eval`: `MvPolynomial`, `aeval`,
  `algHom_ext`; the statement uses `MvPolynomial`, `monomial`, `coeff` and the
  existing algebra equivalence type. Polynomial data are not copied.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` / `.Basic` / `.Map`:
  `TensorProduct`, `TensorProduct.mk`, `lift`, `ext'`, `LinearMap.rTensor` and
  `lTensor`, as specified by the tensor dependency's `mathlib_match`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower` and
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: `LinearMap.baseChange`,
  `ModuleCat.extendScalars`; the latter's object is A'⊗M and map is the standard
  baseChange of the module map. The recorded bilinear extension interface
  `TensorProduct.AlgebraTensorModule.distribBaseChange` is compatible with the
  algebra tensor multiplication used by `Algebra.TensorProduct.map`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; arbitrary chosen localization universe z.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, `Module.Basis`.
- `Mathlib.RingTheory.Flat.Basic`: `Module.Flat`, `Module.Flat.lTensor_exact`,
  `Module.Flat.rTensor_exact`; the latter two are the proof dependency
  `lem-weil-pbc-flat-tensor-exact`'s actual recorded Mathlib declarations.
  The flat-ring-map node explicitly records this same module-flatness predicate.

Edge cases checked: no finite or nonempty constraint on I_n; the empty variable
set has its constant monomial; the empty support gives a zero inverse sum; n=0
uses the original augmentation, n>0 has zero target; positive cochain degrees
are zero. No nontriviality or flatness of A' is assumed. Non-resolving original
augmentations are allowed. Naturality is for all module morphisms. The variable
universe was made independent during the second pass, including the degenerate
zero-ring case where a large polynomial-variable set can have a small carrier.

Searches for an existing full result (all with the prescribed msearch.py wrapper):

- LeanFinder: “Base change of augmented simplicial polynomial algebras commutes
  with the alternating face complex and preserves surjectivity”: eight hits,
  including `Algebra.FiniteType.baseChangeAux_surj` and
  `AlgebraicTopology.AlternatingFaceMapComplex.ε`; no complete statement.
- LeanSearch: “The alternating face complex commutes with base change of simplicial
  polynomial algebras”: eight hits, including `alternatingFaceMapComplex` and
  `LinearMap.toMvPolynomial_baseChange`; no complete statement.
- Loogle: `MvPolynomial, tensor` reported unknown identifier `tensor`; repeated as
  `"MvPolynomial", "tensor"`, giving twelve hits including
  `MvPolynomial.algebraTensorAlgEquiv`, `scalarRTensorAlgEquiv`, and their formulas.
  Read `Mathlib/RingTheory/TensorProduct/MvPolynomial.lean`; these supply polynomial
  scalar extension, not the full augmented result.
- Mathlib grep: `simplicial.*(tensor|baseChange)|alternating.*(tensor|baseChange)`:
  two unrelated hits in ExteriorPower.Pairing and SimplicialCategory.Basic.
  Read `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean` directly:
  `map_alternatingFaceMapComplex` and ε give the additive comparison and
  augmentation separately.
- Project `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `polynomialSimplicialTensor`, and monomial/tensor combinations found no full
  result. Related cotangent modules use the recorded augmentation interface.
  A second `rg` checked all delivered full declaration names against Mathlib,
  WeilConjectures and Sheaf; only unrelated names in other namespaces appeared.
  `dag/lean_names_upstream.json` has no match for this item's id.

No STATEMENT-DISPUTED or source fault was found. No new nodes or dependency
modules are included. Every theorem proof is `sorry`; definition data are complete.

## Second reading by Q19

A separate pass by the dispatcher worker reopened the node and module together;
no second agent was started, as the assignment prohibits starting agents. The
maintainer's independent mathematical review follows delivery.

The pass matched the ring maps to f and the CommAlgCat structure, polynomial
identifications to e, degreewise surjectivity to hε, monomial basis/free/flat to
the first conjunct, exactness to the next, and both coefficient formulas and
naturality to F. It checked that mapCocone keeps the actual augmentation and
vertex, that e' fixes every monomial tensor, and that ψ and τ have identity
components on pure tensors. It checked that φ is a derived isomorphism with
the prescribed representative and that the final square has the correct
composition order and target identification. No quasi-isomorphism assumption
was introduced. The pass added the explicit exactness and derived-isomorphism
clauses and removed the shared-universe restriction on variable sets. The
only tensor-order difference is the recorded Mathlib base-change convention,
with the specified symmetry and its normalization explained above.
