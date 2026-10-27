## Worker report

The delivery states `AlgebraicGeometry.RationalHighestWeight.simple_module_dual_highest_weight`
in `Sheaf.AlgebraicGeometry.GroupScheme.SimpleModuleDualHighestWeight`.
It adds the missing coaction subspace, highest-line and contragredient terminology in
`Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`, owned by the new definition
node `def-sfb-rational-highest-weight-data`. No existing node statement is corrected.
All theorem proofs are `sorry`; all definition data is explicit.

### Hypotheses and objects, clause by clause

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`. `Field` is
  Mathlib's field class; `IsAlgClosed` says that every polynomial splits, equivalently
  every nonconstant polynomial has a root. No characteristic restriction is imposed.
- The group scheme is `G : Grp (Over (Spec (.of F)))`. Its multiplication, inverse and
  identity are exactly its recorded `GrpObj`, not an abstract group of rational points.
- Semisimplicity is `hG : IsSemisimpleGroupScheme G.X`, from the landed definition node
  `def-sfb-semisimple-group-scheme`, now explicitly cited. This includes smoothness,
  connectedness, affineness, finite type and absence of nontrivial smooth connected
  solvable normal closed subgroup schemes. Its solvability predicate is termination of
  the scheme-theoretic derived series, not solvability only of the F-points.
- `T`, `B`, `iT`, `iB`, `j`, `hT`, `hsplit`, `hB`, and `hj` are the split maximal torus,
  Borel and inclusion data of the existing Borel-pair theorem: `hT` is its
  `IsMaximalTorus`; `hsplit` is an isomorphism with some rank-r split torus; `hB` is
  `IsBorelGroupScheme`; and `hj : j ≫ iB = iT` identifies the same torus inclusion.
- `U`, `iU`, `hUclosed`, `hUnormal`, `hUsmooth`, `hUconnected`, `hUunipotent`, `hUmax`
  say exactly that U is the largest smooth connected normal unipotent closed subgroup
  of B, using the same predicates and factorization order as the Borel-pair theorem.
  Its inclusion in G is `iU ≫ iB`. A projection or a chosen semidirect-product inverse
  is unnecessary for this statement; they are consequences of the same Borel pair.
- The affine instances on G, T and U expose properties already forced by these
  hypotheses: G is affine by semisimplicity; T is a torus (and closed in G); and U is
  closed in B, which is closed in the affine G. They supply coordinate-ring scalar
  structures and impose no additional restriction on the mathematical cases.
- The actual character lattice X is written multiplicatively as the group-scheme
  Hom group `T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)`. The commutativity
  instance on G_m is the same commutativity witness exposed by the Borel-pair theorem.
  Character multiplication is additive lattice addition and inverse is lattice negation.
- `[ModObj T.X B.X]` together with `hconj` fixes the action on B to actual conjugation
  by `j`, as morphisms of schemes. `Φplus` is a set of these actual characters and
  `hΦplus` identifies it with exactly the nontrivial character weights of Lie(B), using
  the Borel-pair dependency's `TorusCharacterTangent.weightSpace`. These are precisely
  its positive roots. They are characters, including in positive characteristic;
  differentials of characters are never substituted. The root datum itself is not
  otherwise needed to write the conclusions.
- A longest Weyl element is represented by `n` and `e : T ≅ T`. The morphism equality
  `he` says that e is conjugation by n inverse on the given T subgroup, so n is in
  its normalizer. Consequently composition `e.hom ≫ χ` is exactly
  `(w₀χ)(t) = χ(n⁻¹tn)`. `hlongest` states that its image of Φplus is the inverse
  character set, i.e. w₀(Φplus) = -Φplus. This is an actual normalizer representative
  and its torus automorphism, not an arbitrary lattice automorphism or arbitrary map.
- V is an arbitrary finite-dimensional F-vector space in its own universe v, expressed
  by `AddCommGroup`, `Module F`, `FiniteDimensional F`. The map
  `c : V →ₗ[F] V ⊗[F] coordinateAlgebra G` and the existing
  `HopfAction.Coassociative`/`HopfAction.Counital` hypotheses are exactly the rational
  coaction in the node. `coordinateAlgebra G` is literally Γ(G,O_G), with the canonical
  Hopf structure; it is not an independently supplied algebra or Hopf structure.
- A rational submodule is `IsStable c N`: the image of c on N lies in the range of
  the tensor of `N.subtype`. Tensoring over a field is injective on this inclusion,
  so this is exactly c(N) contained in N tensor F[G]. `hsimple : IsSimple c` says
  nonzero and that every such N is bottom or top. It does not silently use simplicity
  of an abstract group representation, which could have a different notion of submodule.

### Conclusions, clause by clause

- The theorem supplies `lam`, an actual character of T. `HasHighestWeight c iT
  (iU ≫ iB) lam` says `Module.finrank F (invariants c (iU ≫ iB)) = 1` and that T acts
  on every vector of that line by lam. The invariants are the actual equalizer
  `(1 tensor iU*) c(v) = v tensor 1`. The scalar character function is lam's pullback
  of the Laurent coordinate t, rather than an arbitrary associated scalar function.
  This renders both the asserted one-dimensionality and the T-character clause.
- The supplied `d` has underlying vector space `Module.Dual F V = V →ₗ[F] F`.
  Its coassociativity and counit laws are conclusions. `IsContragredient c d` asserts
  the inverse-transpose formula by contraction with EVERY v: the contraction of d(f)
  is S applied to the contraction of c(v) with f. Evaluating this coordinate identity
  at any algebra-valued point gives `(g f)(v) = f(g⁻¹v)`. Conversely these contraction
  identities determine d uniquely, since V is finite-dimensional. Thus the existential
  coaction is the canonical contragredient; this neither chooses arbitrary data nor
  assumes existence of a suitable dual action as an extra hypothesis.
- `IsSimple d` is the dual simplicity conclusion. Its `HasHighestWeight` character
  is `(e.hom ≫ lam)⁻¹`, precisely `-w₀(lam)` in multiplicative character notation.
  `HasHighestWeight` also gives the dual's invariant line, as the node applied to the
  simple dual requires.
- For every finite-dimensional W in an independent universe w, with its own coaction
  identities, `IsSimple cW`, and the same highest weight lam, the final clause supplies
  `f : V ≃ₗ[F] W` and the exact coaction square
  `(f tensor 1) ∘ c = cW ∘ f`. This is an equivariant linear isomorphism. No prescribed
  basis, dimension equality, characteristic-zero condition or extra duality assumption
  is imposed on W. Universes u, v, w are explicitly declared; `autoImplicit` is false.

### Dependencies read and used

- `def-weil-field`: Mathlib `Field`, full declaration in Algebra/Field/Defs.lean.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`,
  FieldTheory/IsAlgClosed/Basic.lean; the node's recorded `mathlib_match` explicitly
  includes this predicate. The theorem does not need to choose an algebraic closure.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`/`Grp`,
  Mathlib.CategoryTheory.Monoidal.Grp; the specialization and subgroup/homomorphism
  conventions are in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, which was read.
- `lem-sfb-reductive-borel-pair-structure`:
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`,
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`; the full signatures and
  proof-plan docstrings were read. Its actual torus, Borel, maximal radical and positive
  tangent-character data are used without redefining their predicates.
- `def-sfb-semisimple-group-scheme`:
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`,
  `AlgebraicGeometry.IsSemisimpleGroupScheme`, with its full derived-series definition.
- Existing real coordinate Hopf structure:
  `HopfAction.coordinateHopfAlgebra` from Sheaf.AlgebraicGeometry.HopfCoactionLinearization;
  it exposes Mathlib.AlgebraicGeometry.Group.Affine's canonical Hopf algebra. The group
  structure exposed on `asOver` is exactly `G.grp`.
- Existing coaction identities:
  `HopfAction.Coassociative` and `HopfAction.Counital` from
  Sheaf.RingTheory.HopfActionModuleData. Their signatures and the algebra/module
  coaction structures were read. No duplicate rational-coaction structure is defined.
- Existing G_m: `StandardGroupSchemes.multiplicative` and its affine Laurent model from
  Sheaf.AlgebraicGeometry.StandardGroupSchemes. Existing tangent character weights:
  `TorusCharacterTangent.weightSpace` from Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights.
- The already stated proof dependency `GmRepresentation.weightDecomposition_and_basis`
  is imported, without public, from Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis.
  Its full signature and docstring were read. The other three proof-dependency nodes
  (unipotent-rational-representation-fixed-vector, geometric-unipotence-invariant-descent,
  primitive-cyclic-weight-bound) have no recorded module, match or upstream declaration
  in this snapshot; they are named in the proof plan and have no import to add yet.
  None supplies missing data needed to type this statement.

### Edge cases and mathematical checks

Read Milne Theorems 22.18--22.19, printed pp.467--468, and the complete contragredient
paragraph on p.471 directly from the local PDF. Also checked the preceding cyclic-vector
bound and its sign convention. For G trivial, T, B and U are trivial, Φplus is empty,
and a simple module is a line of trivial highest weight; the conclusions remain correct.
The empty root system does not require a root or a positive rank. The zero vector space
is excluded only by the node's nonzero simplicity condition. A one-dimensional trivial
module is included for any semisimple group. In characteristic p, characters and the
coaction tests retain Frobenius twists; no differential or rational-point-only
representation is used. Tensoring the identities includes nonreduced test algebras and
the zero algebra. Invariants include zero vectors, but their dimension-one clause forces
a nonzero invariant line. Scalar extension of dual evaluation is valid because V is
finite-dimensional. Independent V and W universes do not alter the mathematical cases.

### Searches

Searches were made through the prescribed msearch wrapper and logged in searches.jsonl.

- LeanFinder: “Simple rational representations of a semisimple algebraic group have
  highest weight lines and contragredient highest weight minus longest Weyl element”:
  8 hits, on abstract Weyl-group representations and Lie-module weight chains; no match.
- LeanFinder: “Simple rational modules for algebraic groups highest weight and
  contragredient”: 8 hits, including FDRep.simple_iff_end_is_rank_one and abstract
  group/Lie irreducibility; no rational group-scheme highest-weight theorem.
- Loogle: `Representation.dual, RootPairing.weylGroup`: 0 hits.
- LeanSearch: “Rational representation affine group scheme comodule dual highest weight”:
  8 hits, including Representation.dual and Weyl-group root/coroot representations;
  none states the item or the coaction terminology.
- LeanSearch: “Rational algebraic group coaction invariant submodule simple representation
  contragredient dual coaction”: 8 abstract-group hits, including Representation.invariants,
  Representation.dual and Subrepresentation.ofSubmodule'; no coaction version.
- msearch grep: `highestWeight|highest_weight|contragredient|Comodule|comodule` under
  Mathlib/RepresentationTheory: 0 hits. The related grep under RingTheory also returned
  0 hits. Direct reads of Representation.dual show it is for an abstract group, so it
  cannot supply the rational coaction definition in arbitrary characteristic.
- Project rg of rational representation/module, highestWeight, highest_weight and
  contragredient: no existing module states this theorem. The hits in curve cohomology
  and WeilConjectures.RepresentationTheory.Dual concern abstract-group dual filtrations.
  A direct search of the item id in WeilConjectures returned no declaration.
- Searched DAG definition nodes by rational representation/module, coaction and highest
  weight, and blueprint_refs search “rational coaction”, “highest weight” (both 0 blueprint
  nodes). The existing def-wf-algebraic-representations has a matrix-group RationalHom
  interface; the representation/comodule dictionary is a separate unstated theorem.
  Neither defines coaction-stable subspaces, invariant highest lines or the canonical
  dual coaction predicate. The existing IsInvariantRationalSubspace is for basis-indexed
  matrix representations; this module does not redefine it or any rational-representation
  object, and uses unbundled coactions exactly as the assigned node permits.

### Validation

Both modules compiled separately in dependency order with scompile.py against the live
published build. Only the expected sorry warnings are permitted. Every declaration has
its source and blueprint tag; the two postponed theorem proofs have natural-language
proof plans. All new definitions have explicit data and no inline sorry.

## New nodes

`def-sfb-rational-highest-weight-data` defines the genuinely missing coaction subspace,
simplicity, invariant highest-line and dual contraction predicates, with the canonical
coordinate pullback and character function they require. Its source is Milne Sections
3a, 4a--4b, 12b, Theorem 22.18 and the p.471 contragredient paragraph. It reuses the
landed canonical Hopf and tensor APIs, rather than introducing a second group scheme,
rational representation or Hopf algebra. The searches above found abstract-group or
matrix-specialized notions, but no these coaction predicates. Its helper theorem
coordinateMap_commutes is solely the scalar-compatibility proof required to bundle
the actual appTop map as an algebra homomorphism; its data is not postponed.
The new node is cited directly by the item. No dependency module is needed.

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
