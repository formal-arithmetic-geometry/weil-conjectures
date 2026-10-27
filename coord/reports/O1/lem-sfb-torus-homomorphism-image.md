## Worker report

The module `Sheaf.AlgebraicGeometry.TorusHomomorphismImage` states
`AlgebraicGeometry.torus_homomorphism_image`, with one `sorry` and no new definitions.
I read the item, all eight original statement-dependency records and their relevant
source signatures/docstrings, and the additional landed torus definition. I checked
Milne, Algebraic Groups (2017), Theorem 12.9(b),(c), printed pp.233--234,
Definition 12.14 and the paragraph following it, printed p.236. In particular the
source explicitly says a quotient of a split torus is again a split torus.

Hypotheses and conclusion, clause by clause:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  The universe is explicit and unrestricted; autoImplicit is disabled.
- T, H and I are F-group schemes: `T H I : Grp (Over (Spec (.of F)))`.
  This is the bundled version of the dependency's `GrpObj` encoding. Its
  morphisms and isomorphisms preserve the actual group laws.
- All three groups are affine: the three `IsAffine ...X.left` instances.
- All three groups are of finite type over F: for each group G, the pair
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`. These are exactly the
  two parts recorded by def-weil-finite-type-morphism, including quasi-compactness.
- T is a torus in the precise sense supplied by the item over F:
  `hT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)`.
  The reused splitTorus is built recursively from the recorded G_m, with the
  tensor unit in rank zero. The isomorphism is in group schemes over F.
- The homomorphism h and factor maps are `h : T ⟶ H`, `j : I ⟶ H`,
  `u : T ⟶ I` in the bundled group category. The original factorization is a
  factorization of group homomorphisms. Even read as only a scheme factor u,
  its group compatibility follows from that of h and j and monicity of j.
- j is the closed subgroup embedding: `hj : IsClosedSubgroupScheme j.hom.hom`.
  This is the recorded dependency class; it includes the closed immersion on
  underlying schemes and the injectivity on all algebra points. For a closed
  immersion group homomorphism that injectivity is automatic, so the class
  imposes no stronger mathematical requirement.
- The factorization h = j ∘ u is `hfactor : u ≫ j = h`.
- Faithful flatness, with exactly the coordinate-ring direction F[I] → F[T], is
  `hu : u.hom.hom.left.appTop.hom.FaithfullyFlat`. `RingHom.FaithfullyFlat` uses
  the algebra structure from this very map. Mathlib's `Module.FaithfullyFlat`
  extends flatness and is equivalent to flatness plus tensor detecting zero
  modules (`iff_flat_and_lTensor_faithful` / `iff_flat_and_rTensor_faithful`).
  Thus it renders extension of scalars being exact and detecting zero modules.
- I is a torus: `∃ d : ℕ, Nonempty (I ≅ MultiplicativeType.splitTorus F d)`.
- There are no smoothness or connectedness hypotheses on H, and no smoothness,
  reducedness, or finiteness hypotheses on the kernel. The dependency records
  for Smooth and ConnectedSpace were read; these notions occur in the node
  only to explain absent assumptions and therefore need no binder or import.

Dependency declarations used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic (available through the torus module).
  The algebraic-closure node explicitly records IsAlgClosed as its relevant clause.
- `CategoryTheory.Grp`, `GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp, and the
  bundled homomorphisms built from `CategoryTheory.IsMonHom`.
- `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, imported directly.
- `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and its canonical
  multiplicativeGroup, Sheaf.AlgebraicGeometry.StandardGroupSchemes, as used by
  `AlgebraicGeometry.MultiplicativeType.splitTorus`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType. Added the already landed node
  def-sfb-tori-multiplicative-type to stmt_deps, as §5 permits. We use its finite
  product construction, not the different general-field algebraic-closure predicate.
- `RingHom.FaithfullyFlat`, Mathlib.RingTheory.RingHom.FaithfullyFlat, supplies
  the inline faithfully flat condition without any private duplicate definition.

The stated proof dependencies are imported without `public`: the faithfully flat
ideal contraction in Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra; the coordinate
Hopf algebra and hopfSpec in Mathlib.AlgebraicGeometry.Group.Affine; TensorProduct
in Mathlib.LinearAlgebra.TensorProduct.Basic; the finite integral basis theorem
in Mathlib.LinearAlgebra.FreeModule.PID; and
`AlgebraicGeometry.affine_finiteType_algebra_of_field` in
Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra. The geometric-criteria node has
no recorded Lean declaration or mathlib_match and is not needed to state this
item; its proof import must be added when it is stated. The theorem docstring
contains every step of the seven-step DAG proof, with all cited node ids.

Edge cases checked mathematically before writing: rank zero gives the trivial
source and trivial image; constant maps have trivial image even in disconnected
or nonsmooth H; the identity and projections of split tori have the asserted
image. In characteristic p, Frobenius of G_m has nonreduced kernel μ_p and has
image G_m, which is allowed. Positive-dimensional kernels such as the kernel
of G_m² → G_m are allowed. No characteristic assumption occurs. An empty I
cannot receive a morphism from a group scheme (which has an identity section),
so there is no missing empty-scheme branch. Ranks r and d range over all naturals.

Searches actually run using msearch.py for O1 and this item:

- LeanFinder: `The faithfully flat image of a homomorphism from a split algebraic
  torus is a split torus`: 8 results, all general faithfully flat ring/module
  facts (including base change, injectivity/descent); no torus-image theorem.
- Loogle: `IsTorus, IsMonHom, FaithfullyFlat`: 0 results, unknown identifier IsTorus.
- Mathlib grep: `IsTorus|SplitTorus|torus.*image|image.*torus`: one unrelated
  UnitAddTorus integration-preimage theorem in Analysis/Fourier/AddCircleMulti.
- LeanSearch: `A faithfully flat homomorphic image of a split torus group scheme
  is a split torus`: 8 results including RingHom.FaithfullyFlat and its injectivity
  and flat/surjective-spectrum characterizations, no algebraic-torus image theorem.
- Direct rg of `lean/WeilConjectures/AlgebraicGeometry` for torus/splitTorus and
  direct grep of `lean/WeilConjectures` for this item's id: no matching theorem.
- Direct rg of `lean/Sheaf` and `lean/WeilConjectures` for torus/image/homomorphism:
  only consumers mention this theorem; no existing declaration states it.
- Direct rg for torus definitions found ToriMultiplicativeType.lean, whose full
  declarations were read. The DAG record confirms its existing definition node.
  Searching dag/lean_names_upstream.json for the node/desired theorem name
  found no existing upstream match.

No new nodes or dependency repairs were needed. There is no statement fault or
STATEMENT-DISPUTED flag. No statement text, proof, or proof_deps was changed.

Validation: scompile.py compiled the sandbox and the library-named module
successfully on the server (10.9 s and 1.9 s), with no errors or unexpected warnings.

## Second reading by O1

I separately reopened the node and completed Lean file for a clause-by-clause
self-review; no second agent was started, as the dispatcher brief prohibits it.
The maintainer supplies the independent review. The three groups retain their
own affine and finite-type assumptions. h, j and u are homomorphisms, hj is the
actual closed-subgroup class, and the order u ≫ j matches h = j ∘ u. appTop
reverses direction correctly, so faithful flatness is on F[I] → F[T]. Both
isomorphisms are in Grp (Over (Spec F)), preventing a mere scheme isomorphism
from replacing a group-scheme isomorphism. The rank-zero clauses match the
recursive definition. The result imposes no condition on H or ker h absent
from the node. The only dependency addition reuses the existing splitTorus
construction. All seven proof steps are present in the docstring; all existing
proof-dependency modules are imported. No mismatch or further edit was found.
