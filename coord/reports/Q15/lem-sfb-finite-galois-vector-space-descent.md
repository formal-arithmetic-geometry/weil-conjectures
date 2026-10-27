## Worker report

Delivered module: `Sheaf.FieldTheory.FiniteGaloisVectorSpaceDescent`.
Main declaration: `Field.finiteGaloisVectorSpaceDescent`. This is one theorem,
with proof `sorry`; there are no new definitions, helper axioms, or additional
postponed theorems. The node statement is unchanged, as are its dependency lists.

I read the entire item (including its five proof steps), every statement
dependency and its recorded Mathlib interface, and Milne, Algebraic Groups
(2017), Proposition 3.36 (printed pp. 76–77) and Appendix A.64 (printed
pp. 580–581). Milne explicitly defines the action as a k-linear action with
the semilinearity identity and states the equivalence for all vector spaces.
The finite-Galois setting requires no topology or extra continuity hypothesis.
The declaration docstring records all five proof steps, including the
finite tensor coefficients, the trace-one inverse, naturality, and Hom descent.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fields are `k : Type u`, `L : Type v`, `[Field k]`, `[Field L]`.
  The extension is `[Algebra k L]`, with embedding `algebraMap k L`.
- Finiteness is `[FiniteDimensional k L]`. The hypothesis `[IsGalois k L]`
  comprises precisely `Algebra.IsSeparable k L` and `Normal k L`.
  The former says every minimal polynomial is separable and implies
  algebraicity; `Normal` says each minimal polynomial mapped into `L[T]`
  splits. I read these class declarations and their docstrings in the
  pinned Mathlib sources, rather than imposing an extra splitting hypothesis.
- The group Π is `L ≃ₐ[k] L`, throughout. A space V has `[AddCommGroup V]`
  and `[Module L V]`. Its restricted k-module is exposed through
  `[Module k V] [IsScalarTower k L V]`. This is the usual restriction of
  scalars, not additional mathematical data: compatibility forces
  `c • v = (algebraMap k L c) • v`, by applying the tower identity to
  `c • (1 • v)`. Every L-vector space has this restricted structure.
- The underlying action is `ρ : Representation k (L ≃ₐ[k] L) V`.
  Mathlib defines this as a monoid homomorphism to `Module.End k V`.
  It therefore encodes additivity, the identity action and composition.
  Because Π is a group, the inverse group element gives the inverse map,
  so these endomorphisms are bijections. Conversely the node's additive
  semilinear action is k-linear, since every σ fixes `algebraMap k L c`.
  Thus using a k-linear representation neither strengthens nor weakens
  the input. `hρ` is exactly `ρ σ (a • z) = σ a • ρ σ z` for every σ,a,z.
- The invariant space is the existing `ρ.invariants : Submodule k V`.
  Its source defines membership by `∀ σ, ρ σ z = z`, exactly the node's
  set V^Π and its k-vector-space structure.
- Scalar extension is the recorded `L ⊗[k] U`, with Mathlib's left
  L-module structure. Its action is
  `Representation.tprod (AlgEquiv.toLinearMapHom k L)
    (Representation.trivial k (L ≃ₐ[k] L) U)`.
  Reading `tprod` shows this applies `TensorProduct.map σ.toLinearMap id`.
  The pure-tensor formula is therefore exactly
  `σ(a ⊗ u) = σ(a) ⊗ u`; all action laws come from the existing construction.
- The existential `θ` is a family of L-linear equivalences
  `(L ⊗[k] ρ.invariants) ≃ₗ[L] V`, for every semilinear space.
  Its first conjunct specifies `θ V ρ hρ (a ⊗ z) = a • (z : V)`.
  This fixes the canonical map uniquely, since pure tensors generate.
  Its second conjunct states equivariance on every tensor, not just on
  generators, with the canonical action on the source and ρ on V.
- The next conjunct gives θ-naturality on every tensor `z`, for every
  equivariant `f : V →ₗ[L] V'`. The map on invariants is literally
  `((f.restrictScalars k).comp ρ.invariants.subtype).codRestrict ρ'.invariants`.
  Its membership evidence is the equality from `hf` followed by fixedness
  of the input. `LinearMap.baseChange L` gives the scalar extension of
  this restriction. Thus the equation is exactly
  `f ∘ θ_V = θ_V' ∘ (1 ⊗ f|invariants)`.
- The existential `η` is a family of k-linear equivalences from each U
  to the invariants of its canonical tensor action. The following
  conjunct specifies the inclusion of `η U z` as `1 ⊗ z` in `L ⊗[k] U`.
  Consequently this is the canonical η, not an unspecified isomorphism.
  The next conjunct is its naturality for every k-linear map f,
  expressed after the injective inclusion of the invariant submodule.
- These two natural families are the isomorphisms from scalar extension
  followed by invariants to the identity (θ), and from the identity to
  invariants followed by scalar extension (η). They express the stated
  mutually inverse functors without introducing a second bundled category
  of semilinear spaces. Morphisms are exactly L-linear maps with the
  displayed equivariance identity; identities and compositions are the
  ordinary linear ones. The canonical formulas also give both triangle
  identities on pure tensors and invariant vectors, as in proof step 4.
- The last conjunct covers U and W with independent universes `x` and `y`.
  First it states that every `LinearMap.baseChange L f` is equivariant
  on every tensor. Then for every equivariant
  `g : L ⊗[k] U →ₗ[L] L ⊗[k] W` it states
  `∃! f : U →ₗ[k] W, LinearMap.baseChange L f = g`.
  Together these are precisely bijectivity onto the equivariant maps:
  the first part establishes that the proposed map lands there, and
  existence and uniqueness establish surjectivity and injectivity.
- Only L is finite-dimensional over k. No `FiniteDimensional` or finite
  generation hypothesis is imposed on U,V,V',W. All universes u,v,w,x,y
  are explicit. The naturality families use a fixed arbitrary universe
  for each category, while Hom descent permits different universes.
  Tensor products retain Mathlib's maximum universe automatically;
  no equality between the field and vector-space universes is assumed.

Dependency declarations used, with sources read:

- `def-weil-field`: `Field`,
  `Mathlib.Algebra.Field.Defs` (the node is a Mathlib leaf).
- `def-pc-field-extension`: `Algebra`,
  `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`; used through the exact `IsGalois`
  class in `Mathlib.FieldTheory.Galois.Basic`.
- `def-weil-module-base-change`: `LinearMap.baseChange`,
  `Mathlib.LinearAlgebra.TensorProduct.Tower`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and its canonical
  pure tensors, `Mathlib.LinearAlgebra.TensorProduct.Defs`.
- Additional existing constructions, read in source:
  `Representation` and `Representation.tprod` / `Representation.trivial`
  in `Mathlib.RepresentationTheory.Basic`, `Representation.invariants`
  in `Mathlib.RepresentationTheory.Invariants`, and
  `AlgEquiv.toLinearMapHom` in `Mathlib.Algebra.Algebra.Equiv`.
  These are existing primitives used directly; none is redefined.
- The available proof dependency
  `WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorDecomposition`
  is imported without `public`. The other proof dependency is already
  supplied by the imported Mathlib Galois module
  (`IsGalois.mem_range_algebraMap_iff_fixed`). No proof-dependency interface
  is needed in the theorem's statement.

Searches (all performed for this item through the prescribed wrapper where
specified):

- `msearch.py ... leanfinder "Finite Galois descent for arbitrary semilinear
  vector spaces: scalar extension of invariants is isomorphic to the original
  vector space"`; repeated with "Semilinear Galois descent: a vector space is
  the scalar extension of its invariant vectors". The completed repeated
  search returned eight hits concerning fixed fields / invariant rings,
  including `IsGaloisGroup.isInvariant`, `Algebra.isInvariant_of_isGalois`,
  and `FixedPoints.toAlgHom_bijective`. None gives the equivalence here.
- `msearch.py ... loogle "IsGalois, TensorProduct"`: zero hits.
- `msearch.py ... leansearch "Galois descent for vector spaces with semilinear
  action via tensor product and fixed vectors"`: eight hits, including
  `FixedPoints.linearIndependent_smul_of_linearIndependent`,
  `Representation.tprod_apply`, and fixed-field results. No match for the
  full statement. The tensor-representation hit supplies the canonical
  action that the delivered statement uses directly.
- `msearch.py ... grep "Semilinear|semilinear|Galois.*descent" "FieldTheory/"`:
  five hits, all about Frobenius semilinear maps in purely inseparable
  extensions, with no descent equivalence.
- `rg` for semilinearity, Galois descent and invariants in the project's
  `lean/WeilConjectures` and `lean/Sheaf`, and in Mathlib's FieldTheory,
  RepresentationTheory and LinearAlgebra: project matrix-cocycle descent
  is specialized to finite matrix spaces; it does not state this theorem.
  Mathlib representation/invariant/tensor primitives are used as above.
- `rg -n` for the prospective declaration name and
  `Semilinear.*(Action|Representation)|semilinear.*descent` across Mathlib
  and both project roots found no declaration matching this statement.
- `grep -rn "lem-sfb-finite-galois-vector-space-descent"
  lean/WeilConjectures`: no hits. DAG searches also located the distinct
  `lem-sfb-galois-stable-subspace-descent` and
  `lem-sfb-tensor-field-extension-galois-invariants`: those respectively
  treat stable subspaces of a specified scalar extension and only the
  canonical tensor invariant calculation, not arbitrary semilinear spaces
  and the two natural inverse isomorphisms with the Hom bijection.

Edge cases checked before writing: L=k (trivial Π, ordinary scalar unit),
V=0, U=0 or W=0 (zero invariant spaces and the singleton linear Hom sets),
V=L with its field action (fixed field k), and infinite-dimensional free
spaces. Positive characteristic dividing the extension degree is allowed:
there is no invertible-group-order assumption, averaging operator or
characteristic-zero assumption anywhere in the signature. The trace-one
argument in the proof docstring uses separability, not division by |Π|.
The zero ring is correctly excluded because k,L are fields, but the zero
vector space is included. Nontrivial twists are allowed; ρ is not assumed
trivial or induced from an already supplied k-form.

Validation: the prescribed `scompile.py` checked the delivered module both
as a sandbox file and under its final library module name, with no errors
or warnings. The only initial failure was Lean resolving `.tprod` through
`MonoidHom` rather than `Representation`; replacing this with fully qualified
`Representation.tprod` repaired it. No statement correction, disputed
statement, missing dependency, or new node is needed.

## Second reading by Q15

I reopened the node, Milne's two source passages and the final Lean file
for a separate clause-by-clause reading after compilation. This is the same
worker's second reading: the dispatcher explicitly prohibits starting other
agents; the maintainer's independent review remains the delivery review.

I checked the quantifiers in the existential families against their use in
the following conjuncts; the semilinearity hypothesis is applied to every
σ,a,z. `IsGalois` carries both the recorded separability notion and the exact
minimal-polynomial splitting condition. The k-module tower is restriction
of the supplied L-module and imposes no extra vector-space constraint.
The underlying group representation supplies bijections without requiring
an extra assumption. `ρ.invariants` has the correct fixed-vector predicate.

I checked the tensor action in Mathlib's `tprod` definition: the first
factor is the automorphism's k-linear map, and the second is the identity.
I checked both formulas specify the intended canonical maps, so neither
existential permits a different map. θ-equivariance and θ-naturality
quantify over all tensors. The naturality restriction uses the actual f,
with fixedness proved in the correct direction. η-naturality is equality
in the ambient tensor space, which is equivalent to equality in its
invariant submodule because the inclusion is injective.

I checked that the last clause first establishes equivariance for every
base-changed f and then gives a unique preimage for every equivariant g;
no extra finite-dimensionality enters. Every hypothesis and clause of
the unchanged node is accounted for above, and the two natural isomorphism
families give exactly its explicit equivalence criterion. No mismatch
was found in this reading. No new node or dependency module needs a
separate reading. The final signature has no implicit universe or
undeclared variable, no private abbreviation and no local notation.
