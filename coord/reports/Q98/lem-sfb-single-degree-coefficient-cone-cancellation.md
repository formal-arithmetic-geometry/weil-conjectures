## Worker report

The module `Sheaf.Algebra.Homology.SingleDegreeCoefficientConeCancellation` states
`ModuleCat.singleDegreeCoefficientConeCancellation`, with its proof `sorry`.
Its only helper, `ModuleCat.coefficientConeRestrictionSquareIso`, constructs the
canonical comparison of two successive scalar restrictions around a commuting
ring square using the existing identity-on-elements comparisons. Its data are
fully written. There are no new DAG notions, postponed helper theorems, statement
corrections, or dependency repairs.

The inherited BLOCKED ending concerned stage 1. The current node is split and
reviewed by O2 (2026-10-24), has no Lean record, and appears with stage 2 in the
queue. The explicit stage-handoff paragraph of brief-stage2 section 0 permits
this statement delivery without reopening the accepted split. Its statement,
proof, statement dependencies, and proof dependencies are preserved verbatim.
There is no released repair note for the item.

The source is the agent-formulated algebra prerequisite specified in the node.
I read perfect.tex, lemma-flat-proper-pseudo-coherent-direct-image-general,
including the following paragraph: it states the more general relative
pseudo-coherence result and says See Kiehl. It does not supply this cancellation
lemma. The theorem docstring accurately retains the agent origin and the
primary proof WANTED status and gives all ten steps of the accepted node proof.

Clause-by-clause rendering:

* The commutative rings D, A and S are explicit `Type u` binders with `CommRing`.
  `IsNoetherianRing D` is the node's Noetherian hypothesis.
* `Algebra D A` specifies the given ring homomorphism D -> A; `Algebra D S` and
  `Algebra.FiniteType D S` give the finite type coefficient algebra. Algebra
  structures encode arbitrary unital maps here, with no injectivity or flatness.
* `s : ℕ`, `q : MvPolynomial (Fin s) D →ₐ[D] S`, and `hq : Function.Surjective q`
  are the chosen polynomial presentation, including s=0.
* `S ⊗[D] A` is S_A. For Q_A the statement uses
  `MvPolynomial (Fin s) D ⊗[D] A`. Tensor symmetry identifies it with
  `A ⊗[D] MvPolynomial (Fin s) D`; the existing
  `MvPolynomial.algebraTensorAlgEquiv D A` then identifies this algebra with
  `MvPolynomial (Fin s) A`. Under this identification the left inclusion is the
  coefficient map Q_D -> Q_A and `Algebra.TensorProduct.map q (AlgHom.id D A)`
  is precisely the presented map Q_A -> S_A. This is a canonical ring
  presentation of the same polynomial algebra, not an arbitrary coefficient ring.
* K is an unrestricted object of `DerivedCategory (ModuleCat (S ⊗[D] A))`.
  L is an object of `DerivedCategory (ModuleCat S)`. The library's canonical
  small-Hom derived category of ordinary modules is used, with the existing
  Grothendieck-category instance, rather than choosing a second localization.
* `hL` supplies a finite interval [a,b] and says its cohomology is zero outside
  that interval; `hLfinite` is `Module.Finite S` for every cohomology module.
  Both bounds are existential, so a=b, a>b (the zero case) and every integer
  endpoint remain permitted.
* `γ` has exactly type L -> Res_S K, using the canonical tensor inclusion S -> S_A.
* `η_Q` is the unit arrow from Res_QD L to Res_QD T_Q. The existing predicate
  `IsDerivedBaseChange η_Q` in `hη_Q` says this arrow is universal among maps
  into restrictions of Q_A-module derived objects. This characterizes
  T_Q = Q_A tensor^L_QD Res_QD L, including its unit, up to the unique unit-compatible
  isomorphism. It is the existing universal-arrow description of derived tensor,
  which is computed by the recorded K-flat resolution machinery; no extra
  flatness or boundedness is introduced by this presentation.
* `θ_Q` is Q_A-linear. The equation `hθ_Q` says its adjoint transpose is the
  restriction of γ, with only the canonical restriction-square transport inserted.
  By the extension/restriction adjunction it is exactly extension of γ followed
  by the scalar-action counit. This rules out a freely chosen arrow and fixes the
  map even when scalar extension is not exact.
* `C_Q`, `ι_Q`, `δ_Q`, `hC_Q` specify a distinguished cone triangle with θ_Q as
  first arrow. The node asks for a cone, not a functorial cone choice; any such
  triangle gives the same bounds and finiteness, invariant under cone isomorphism.
* `n : ℤ`, `hupper`, and `hfinite` say exactly that H^i(C_Q)=0 for i>n and that
  H^n(C_Q) is finite over Q_A (in its canonical tensor presentation).
* The conclusion quantifies a commutative ring D', a D-algebra structure, and a
  D'-algebra structure on the given A. `IsScalarTower D D' A` says their composite
  is the original D -> A. `Algebra.FiniteType D D'` is the required finite type
  factorization. It does not require D' -> A to be injective or surjective.
* `L' : DerivedCategory (ModuleCat (S ⊗[D] D'))` is the required S'-complex.
  The two next clauses give its bounded cohomology and finiteness over S'.
* `γ'` has target the restriction of K along the actual induced map
  `S ⊗[D] D' -> S ⊗[D] A`, namely tensor map of the identity of S and the tower
  homomorphism D' -> A.
* `T'`, `η'`, `IsDerivedBaseChange η'` specify the derived tensor
  A tensor^L_D' Res_D' L', in D(A), with its canonical unit. In particular the
  tensor is over D', not over S'. Replacing it by extension along S' -> S_A
  would discard negative Tor in nonflat cases and is not done here.
* The equation for `θ'` specifies its adjoint transpose as Res_D' γ', followed
  by the identity-on-elements restriction comparison in the coefficient square.
  This is precisely the displayed map 1 tensor γ' followed by the given
  A-action counit, after forgetting the retained S'-action to A-modules.
  Scalar restriction of K is along the fixed A -> S_A tensor inclusion.
* `C'`, `ι'`, `δ'` and `Triangle.mk θ' ι' δ' ∈ distTriang _` specify its cone.
  The final `∀ i : ℤ, n ≤ i → IsZero (...)` is exactly vanishing in every
  degree >= n. This is tested on the A-module cone. The canonical tensor
  retaining S'-action in the node lives over S' with a commuting A-action;
  forgetting it either to S'-modules or to A-modules gives the same underlying
  cochain groups, and both forgetful functors are exact and faithful. They
  detect zero cohomology. Consequently this test is exactly the node's bound
  on its S'-linear cone; no conclusion about only some of its cohomology or
  some arbitrary map has been substituted.
* No map L -> L', pseudo-coherence of K, or lower cohomological bound on a cone
  occurs in the signature.

Dependency declarations read and used:

* def-weil-pbc-noetherian-ring: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; its definition is IsNoetherian R R.
* def-weil-pbc-mv-polynomial-ring: `MvPolynomial`,
  `Mathlib.Algebra.MvPolynomial.Basic`; the finite-support monoid algebra.
* def-weil-abstract-derived-category: `DerivedCategory`, `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; and `homologyFunctor` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
* def-weil-finitely-generated-module: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`, top submodule finitely generated.
* def-pc-module-kflat-complex: `CategoryTheory.MorphismProperty.kFlat`,
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`, the two-sided
  tensor quasi-isomorphism predicate. This import is retained; computation of
  the universal derived base change uses this existing predicate and machinery.
* def-weil-triangulated-category: `CategoryTheory.Pretriangulated` and
  `CategoryTheory.IsTriangulated` from their recorded Mathlib modules,
  `Triangle.mk` and `distTriang` on the ordinary derived module categories.
* The existing derived-tensor universal-arrow interface and scalar restrictions:
  `ModuleCat.IsDerivedBaseChange`, `derivedRestrictScalars`,
  `derivedRestrictScalarsCompIso`, in
  `WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange`.
  I read the full defining signatures/docstrings. In particular the universal
  property is a bijection on all derived Hom sets, not only cohomology groups.
  `Functor.mapDerivedCategoryNatIso` and `ModuleCat.restrictScalarsCongr` give
  the helper's canonical comparison. They neither select an arbitrary map nor
  assume an isomorphism of tensor-comparison maps in the nonflat case.

Every proof dependency with a recorded module is imported privately, and the
Mathlib finite-type Noetherian and long-exact-sequence results are already
available from the public imports. The three currently unstated proof nodes
`def-sfb-dg-coefficient-realization`,
`lem-sfb-dg-coefficient-realization-comparison`, and
`lem-sfb-perfect-coefficient-arrow-finite-realization` have no recorded Lean
module to import; they are only part of the proof plan, not missing notions in
this statement. They are named in the proof docstring; no dependency theorem
has been silently assumed as a hypothesis.

Edge cases checked before writing: zero rings (no Nontrivial instances), s=0
(empty variable set), K=0, L=0, L'=0, no generators of H^n, all negative n,
and the case n above all cohomology of the finite-free tail. The universal
properties and cone conditions exclude none of these. The nonflat example
D=k[t], S=A=k is also allowed: tensor over the coefficient ring retains its
negative Tor, while an S -> S_A extension would incorrectly erase it. The final
factorization may be the identity. A finite coefficient enlargement can live in
the same arbitrary universe u; rings and modules of any size are covered by
instantiating u large enough, with no finite or countable size restriction.

Searches for an existing statement (none found):

* msearch leanfinder: "Finite top cone cohomology can be killed after enlarging a
  finite type coefficient algebra for a derived scalar action map" returned
  eight hits on finite cotangent homology, K-injective factorizations, and finite
  cyclic cochains. None states the coefficient enlargement/cancellation result.
* msearch loogle: "ModuleCat.extendScalars, ModuleCat.restrictScalars,
  DerivedCategory" returned zero hits.
* msearch grep: "cone.*cancellation|coefficient.*obstruction|derivedExtendScalars"
  returned zero Mathlib hits.
* msearch leansearch: "Kill finitely generated top cohomology of the cone of
  derived scalar extension after a finite type coefficient factorization"
  returned eight hits: Module.Finite constructors/projections, localization
  and profinite cones; no match.
* rg of both lean/WeilConjectures and lean/Sheaf for single-degree coefficient
  cancellation, coefficient obstruction, and this blueprint id found no exact
  statement. Broader scalar/derived searches found the existing universal-arrow
  derived base-change interface, which is used directly. The flat derived
  extension modules were rejected for this purpose because they assume flatness.
  OrdinaryDerivedChangeOfRings was read as well: its universal K-flat pair confirms
  the same mathematical object, but it has unnecessary monoidal data for this
  statement. No second tensor, K-flatness or finiteness definition is introduced.

The server initially hit deterministic elaboration limits inferring implicit
ring types in a restriction map. Adding explicit polynomial ring types and
using the standard transparency settings fixed it. The final file uses the
original heartbeat limit and compiles twice cleanly (sandbox and module, about
three seconds each) using scompile.py. No local or global build was run.

No STATEMENT-DISPUTED flag or source-based correction is needed.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
