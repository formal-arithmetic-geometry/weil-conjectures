## Worker report

The module `Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed` states
`AlgebraicGeometry.completeLinearSystem_isClosedImmersion`, with `sorry` and no new
definitions. The node is unchanged except for `lean`.

Hypotheses and conclusions, clause by clause:

- The field is `(k : Type u) [Field k]`. The scheme over it is
  `(X : Scheme.{u}) [X.Over (Spec (.of k))]`, and properness is
  `[IsProper (X ↘ Spec (.of k))]`.
- The invertible module is `(M : X.Modules) [M.IsInvertible]`, using the recorded
  `Scheme.Modules.IsInvertible` rather than a different sheaf predicate.
- The k-action on actual global sections `Γ(M, ⊤)` is precisely restriction of scalars
  by `Module.compHom` along `Scheme.globalSectionsRingHom k (X := X)`. The `letI` is
  only an explicit instance, not an auxiliary mathematical object or an assumption.
- The finite-dimensional subspace is `V : Submodule k Γ(M, ⊤)` together with a
  finite basis `bV : Module.Basis I k V`, `[Finite I]`. Quantification over such
  bases is the coordinate presentation of any finite-dimensional V, including zero.
- `j : X ⟶ ℙ(I; Spec (.of k))` is the associated map to P(V-dual) after this basis
  identification. Its structure-map equality states it is over k;
  `IsClosedImmersion j` is exactly the closed-immersion hypothesis.
- The existential isomorphism `e : (tensorPullback j).obj (twist I (Spec k) 1) ≅ M`
  is the specified pullback of O(1). The equalities for every `i : I` identify the
  pulled-back coordinate with `(bV i : Γ(M, ⊤))`. This renders the word
  "associated": an arbitrary j with merely an abstract pullback isomorphism would
  not suffice. `pb` is local notation for the unit of the canonical adjunction
  chosen by `exists_tensorPullbackAdjunction`, exactly as in the dependency module.
- The conclusion supplies a finite basis `b : Module.Basis J k Γ(M, ⊤)` and a map
  `φ : X ⟶ ℙ(J; Spec (.of k))` over k. Thus the target is P(Γ(M)-dual), rather than
  the projective space of an unspecified generating subsystem; existence of this
  finite basis also states the finiteness needed to construct this projective space.
- `IsClosedImmersion φ` renders the first conclusion. The final isomorphism renders
  `φ*O(1) ≅ M`, and the coordinate equalities `... = b i` specify the complete-system
  morphism. Existence of a coordinate realization is the basis-independent assertion:
  the functor-of-points uniqueness identifies any other realization for the same
  basis, and change of basis changes the target by its projective isomorphism.

Dependency declarations read and used:

- Mathlib `Algebra.Field.Defs`: `Field` (extends `CommRing` and `DivisionRing`).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, local triviality of the module.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `AlgebraicGeometry.ProjectiveSpace.twist` and `twistOneSection`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints`:
  `AlgebraicGeometry.projectiveSpace_functor_of_points`. Its recorded universal-pair
  signature and full docstring were read. The present statement uses its exact
  coordinate-compatible-pullback formulation, extending coordinates from Fin(n+1)
  to a finite type so the empty case remains expressible. This imported theorem is
  a stage-3 construction/uniqueness input; it is not a new definition of a notion.
- Through that module: `Sheaf.AlgebraicGeometry.TensorPullback` and
  `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, declarations
  `Scheme.Modules.tensorPullback` and `exists_tensorPullbackAdjunction`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `Scheme.globalSectionsRingHom`, the actual map induced by the structure morphism.
- Mathlib `LinearAlgebra.Basis.Defs`: `Module.Basis`.

Edge cases checked before writing: X empty has Γ(M)=0, with I and J empty; no
Nonempty hypothesis is imposed. If V=0 on nonempty X, an associated morphism to
empty projective space cannot exist, so the hypotheses correctly fail. Projective
space of a one-dimensional space has one coordinate (I singleton), and permits
zero-dimensional schemes. No smoothness, geometric connectedness, algebraic closure,
reducedness, or characteristic assumption is added. P¹ with O(1) and V equal to
all sections gives the usual embedding; P¹ with O(2) and V spanned by x²,y² has an
associated map but fails the closed-immersion hypothesis. Empty bases, disconnected
proper schemes and fields of every characteristic are retained. Every universe and
variable is explicit; finite-dimensional spaces have small finite bases in Type u.

Searches for existing declarations (2026-10-11):

- `msearch.py ... leanfinder "complete linear system containing a subspace defining
  a closed immersion is a closed immersion"`: eight hits, all generic closed-
  immersion lemmas (subschemes, Spec quotients, coborder); no linear-system theorem.
- `msearch.py ... loogle "ProjectiveSpace, IsClosedImmersion"`: no hits, unknown
  identifier ProjectiveSpace in the search service.
- `msearch.py ... grep "linear.system|complete.linear|twistOneSection"
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "A complete linear system containing a subsystem
  defining a closed immersion defines a closed immersion"`: unavailable, Internal
  Server Error; no mathematical verdict drawn from this unavailable service.
- `rg` of the upstream-name index, Mathlib, the source WeilConjectures library and
  this project's `lean/Sheaf` for `completeLinearSystem_isClosedImmersion`,
  `CompleteLinearSystem`, and `complete.linear.system`: no matching declaration;
  only prose references in RiemannRoch and the two already-landed ampleness modules.
- Source search for the item id found no declaration. The existing twist and its
  coordinate sections, canonical k scalar map and canonical pullback unit were read
  in full at their defining declarations and reused.

Source checked directly: Stacks https://stacks.math.columbia.edu/tag/01NE gives
classification by generating invertible pairs with section-preserving isomorphisms;
https://stacks.math.columbia.edu/tag/07RK part (3) is closed-immersion cancellation
along a separated map. The local literature TeX files are absent on this machine,
so those source pages were read instead. The four proof steps in the node are
included in the theorem docstring; no proof step is executed at stage 2.

No new nodes, dependency replacements, statement corrections, or disputed assertions.

## Second reading by H1

I independently compared the node's objects and clauses with
`AlgebraicGeometry.completeLinearSystem_isClosedImmersion` in
`Sheaf/AlgebraicGeometry/CompleteLinearSystemClosed.lean`.

- The field, scheme over `Spec k`, proper structure morphism, invertible module, and
  restriction-of-scalars action on `Γ(M, ⊤)` are rendered by the initial binders and
  `letI`; these match the node without extra hypotheses.
- The finite-dimensional subsystem is rendered by `V`, `[Finite I]`, and
  `bV : Module.Basis I k V`. The map `j` has the required structure-map equality and
  `IsClosedImmersion j`; the existential `e` and coordinate equalities express that
  `j` is the associated morphism and that its pullback of `O(1)` is `M`.
- The conclusion quantifies a finite basis `b` of all global sections and `φ` over
  `k`, asserts `IsClosedImmersion φ`, and supplies the pullback isomorphism and all
  coordinate equalities. This is the coordinate-explicit form of the node's complete
  linear-system conclusion and does not add mathematical assumptions.

Edge cases remain covered: empty schemes and empty finite index types, zero sections,
singleton bases, disconnected proper schemes, arbitrary characteristic, and all
allowed universes. No `Nonempty`, smoothness, reducedness, or algebraic-closure
hypothesis appears. The finite basis in the conclusion is existential, so it does not
exclude the zero global-section case.

I repeated the existing-declaration searches with LeanFinder, Loogle, `msearch.py`,
and `rg` over Mathlib, the source repository, and `lean/Sheaf`; all found only generic
projective or closed-immersion declarations and no complete-linear-system theorem.
The module compiled with `scompile.py`; no mismatch was found and no Lean source
change was needed. The only delivery repair was adding the node's `lean` record and
this second-reading report section.
