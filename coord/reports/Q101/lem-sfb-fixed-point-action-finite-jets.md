## Worker report

The module `Sheaf.AlgebraicGeometry.FixedPointActionFiniteJets` states
`AlgebraicGeometry.FixedPointAction.fixed_point_action_finite_jets` with one
`sorry`. Its three helpers abbreviate the actual stalk quotient, construct its
canonical scalar algebra, and construct its canonical morphism into X. No data
are postponed and no independent mathematical notion is introduced. All four
names are recorded in `lean.declarations`.

I read the assigned node (including all eight proof steps), every statement
dependency and its Lean record/mathlib_match, the recorded source declarations,
and Milne, *Algebraic Groups* (2017), printed pp.138--139 and 150 (PDF pp.150--151
and 162). The source's fixed-subscheme quantifiers include arbitrary algebra
extensions, and the statement preserves them. The proof docstring includes all
eight steps, including the integral-domain repair of the reducedness issue.
There is no statement correction and no STATEMENT-DISPUTED issue.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- H and X are k-schemes: `H X : Over (Spec (.of k))`.
- H is a group scheme: `[GrpObj H]`. Its structural morphism has
  `[IsSeparated H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`.
  The last two conditions are exactly finite type. No affineness, smoothness,
  connectedness, commutativity, reducedness, or faithfulness is imposed on H.
- X is smooth, connected, separated, finite type:
  `[Smooth X.hom] [ConnectedSpace X.left] [IsSeparated X.hom]`, together with
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
  `IsSeparated` is defined by its closed diagonal, as requested.
- The action and its unit/associativity identities after every base change are
  `[ModObj H X]` in the cartesian monoidal category of schemes over k. Its
  `smul` is the morphism H times X to X, and the induced action on every Hom
  type is Mathlib's `CategoryTheory.Hom.mulAction`.
- The rational point is `x : 𝟙_ (Over (Spec (.of k))) ⟶ X`. The unit's underlying
  scheme is Spec k and its structural morphism is the identity, so this is a
  section, including its required structural equality. `hfixed` says that
  `h • (toUnit T ≫ x) = toUnit T ≫ x` for every k-scheme T and T-point h.
  Taking T=H and the universal h gives exactly the morphism equality in the
  node, and that equality gives this universally quantified form.
- R is the actual structure-sheaf stalk at `x.left (closedPoint k)`.
  `Jet X x n` is its quotient by `IsLocalRing.maximalIdeal R ^ (n+1)`.
  A rational section induces a local map R to k; its kernel is the unique
  maximal ideal, so this is precisely the node's m, with no auxiliary ideal.
  `jetAlgebra` composes the structure map on stalks with `StructureSheaf.toStalk`
  and the quotient map; hence its k-vector-space structure is canonical.
- For every n>=1, the conclusion asserts `Nontrivial (Jet X x n)` and
  `FiniteDimensional k (Jet X x n)`. No conclusion is required at n=0.
- `c`, `1 ≤ c`, and `b : Module.Basis (LinearGroupSchemes.Index c) k (Jet X x n)`
  choose an ordinary finite basis. `Index c = ULift (Fin c)` has exactly c
  elements and accommodates the common universe of the existing GL scheme.
- `jₙ` is a k-morphism from Spec V_n to X, with `jₙ.left = jetInclusion X x n`
  and `IsClosedImmersion jₙ.left`. The helper is literally Spec of the quotient
  map followed by `X.left.fromSpecStalk`; jₙ is not an arbitrary embedding.
- `ρ : H ⟶ GeneralLinearGroup (Index c) k` and `_hρ : IsMonHom ρ` are the required
  morphism and homomorphism of group schemes. For every k-algebra B and h in
  H(B), the conclusion gives a B-algebra automorphism T of `B ⊗[k] Jet X x n`.
  Its equation after applying Spec is exactly inverse-action pullback: its
  composite to X is the inverse of the base-changed h acting on the canonical
  point of the infinitesimal neighbourhood. The maps `includeLeft` and
  `includeRight` specify the two scalar-extension projections. The subsequent
  equation identifies every matrix coefficient of T in `b.baseChange B`
  with `GeneralLinearGroup.homMulEquiv ... (h ≫ ρ)`. This specifies the actual
  representation induced by the inverse action, rather than some representation
  with the same kernel. Since the thickening embeds in X, this specification
  determines T and hence ρ uniquely in the chosen basis.
- The kernel is the existing `CategoryTheory.GrpObj.ker ρ`, defined as the fibre
  product with the identity section; its inclusion is `GrpObj.kerι ρ`.
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, `LocallyOfFiniteType`,
  and `QuasiCompact` state all four requested properties, schematically.
- The single outer `∃ n₀, 1 ≤ n₀` precedes the universal n. The representation
  exists for every n>=1; `n₀ ≤ n → ...` gives the eventual assertion.
  Kernel membership is `∃ q : Spec B ⟶ ker ρ, q ≫ kerι ρ = h`, not merely a
  set of geometric points. On the right, every commutative k-algebra B', every
  `f : B →ₐ[k] B'`, and every `z : Spec B' ⟶ X` is quantified, and the equality
  is `(StandardGroupSchemes.map k f ≫ h) • z = z`. This quantifies precisely
  all commutative B-algebras: the k-structure on any such B' is induced from B,
  and conversely a k-algebra map from B gives that B-algebra structure. There
  are no reduction, nonzero, local, finite-generation, or field assumptions
  on B or B'. The empty Spec of the zero algebra is allowed.

Dependency declarations used (full signatures and docstrings read in source):

- `Field`, `Mathlib.Algebra.Field.Defs`; `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (the closure node explicitly records
  this component of its Mathlib match).
- `CategoryTheory.GrpObj`, `IsMonHom`, and the point group in
  `Mathlib.CategoryTheory.Monoidal.Grp` and `.Cartesian.Grp`.
- `Scheme` and its Hom, `Mathlib.AlgebraicGeometry.Scheme`; `Over` bundles the
  structure morphism without adding any mathematical condition.
- `LocallyOfFiniteType`, `QuasiCompact`, `Smooth`, `IsSeparated`, and
  `IsClosedImmersion` in the corresponding
  `Mathlib.AlgebraicGeometry.Morphisms` modules; `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`.
- `CategoryTheory.Limits.pullback` and its projections in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, used by the
  cartesian structure of Over and by `GrpObj.ker`.
- `Ideal.Quotient`, `Ideal.Quotient.mk`, and the usual ideal powers in
  `Mathlib.RingTheory.Ideal.Quotient.Operations` and `.Ideal.Operations`;
  `FiniteDimensional` in `Mathlib.LinearAlgebra.FiniteDimensional.Defs`;
  `TensorProduct` in `Mathlib.LinearAlgebra.TensorProduct.Defs`.
- The recorded `Sheaf.AlgebraicGeometry.LinearGroupSchemes` re-exports the
  upstream `AlgebraicGeometry.GeneralLinearGroup` and `homMulEquiv`, defined
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`. I use that
  existing GL, and the recorded `LinearGroupSchemes.Index`, not a new GL.
- `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`; the already implemented
  kernel and its inclusion in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
- Existing construction helpers `StandardGroupSchemes.affine` and `.map` in
  `Sheaf.AlgebraicGeometry.StandardGroupSchemes`; `ModObj` and Hom actions in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`; `Module.Basis.baseChange`
  in `Mathlib.LinearAlgebra.TensorProduct.Basis`; `Scheme.fromSpecStalk` and
  `StructureSheaf.toStalk` in the Mathlib stalk/structure-sheaf API.

Already stated proof-dependency modules are imported, including Regular,
NoetherianQuasicoherentSubmodules, the kernel construction and subgroup
properties, ideal sheaves, Yoneda, the affine adjunction, and Filtration.
The two new stage-1 proof dependencies
`lem-sfb-rational-point-thickenings-base-change` and
`lem-sfb-universal-fixed-subscheme` currently have no Lean record, so their
modules are not imported; no statement notion is being assumed from them.
Their full mathematical content needed for this proof remains in the docstring.

Edge cases checked before and after writing:

- X=Spec k: all jets are k of dimension one; the action is trivial and the
  kernel is all of H. The positive basis dimension admits c=1.
- Trivial action on any allowed X: the representation is trivial, and the
  universal kernel equivalence asserts all of H on both sides.
- Characteristic p and the nonreduced group mu_p scaling A^1 at 0: the first
  jet detects mu_p on nonreduced algebras; no use of k-points alone appears.
- Nonaffine H (e.g. an abelian variety acting trivially) is allowed.
- X empty is already excluded by connectedness and also cannot carry x;
  this matches the source, rather than an added nonemptiness hypothesis.
- n=0 is outside the asserted range; n=1 is retained. B and B' may be zero
  rings or nonreduced rings. The index and test algebras use the existing
  common scheme universe, not an independent smaller test universe.

Searches for an exact existing statement, all made before writing:

1. `msearch.py Q101 lem-sfb-fixed-point-action-finite-jets leansearch
   "The scheme theoretic kernel of an algebraic group action is detected on a
   finite jet at a fixed rational point"`: 8 hits, including Scheme.Hom.ker,
   ker_comp and specTargetImageIdeal; none is the finite-jet action theorem.
2. `msearch.py ... leanfinder "An algebraic group action fixing a rational
   point has its scheme theoretic kernel detected by a finite jet of the local
   ring"`: 8 hits, including Ideal.Quotient.ker_stabilizerHom, Scheme.ker_toSpecΓ,
   FormallyUnramified and germ injectivity; no matching theorem.
3. `msearch.py ... loogle '"GrpObj", "Action"'`: zero hits.
4. `msearch.py ... grep 'fixed.point|finite.jet|jetRepresentation'
   AlgebraicGeometry`: zero Mathlib hits.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
   `finite.jet|FiniteJet`, action structures, and group-scheme/GL terminology:
   no declaration for this item. Existing torus fixed-local jets use an affine
   coordinate torus action and cannot cover a general nonaffine H or X.
   Existing finite-jet generic-fibre results concern deformation smoothness.
   Existing GL, ModObj, subgroup, quotient, and tensor APIs are used directly.

Compilation is exclusively by the prescribed `scompile.py` wrapper. Initial
elaboration repairs were a binder colliding with scoped inverse notation, explicit
tensor-inclusion types, and using the actual cartesian unit for the section's
domain (Spec k with identity structure). None changes the mathematics.

## Second reading by Q101

A separate second pass reread the node alongside the final file. The dispatch
brief prohibits starting another agent, so this is explicitly a same-worker
second reading, not a claim of an independent agent review. The maintainer's
independent review remains required.

Checked k and its closure; all H hypotheses and absence of affineness; all X
hypotheses; the ModObj action diagrams and the universal fixed section; the
actual stalk, its unique maximal ideal, powers n+1, and canonical quotient
scalars; positive n, nonzero finite dimension and positive basis size; the
canonical closed jet embedding; the group homomorphism; the inverse-action
Spec equation for every B; each coefficient in the scalar-extended basis;
the actual fibre-product kernel, closedness, normality and both finite-type
conditions; one common positive stabilization index; both directions of the
universal equivalence with every B-algebra and X-point. The displayed matrix
coefficient convention is column j, row i, exactly the usual matrix of T.

The second pass made explicit `IsClosedImmersion jₙ.left` so that the hook
notation for Spec V_n into X is asserted, and confirmed that using the
cartesian unit for x incorporates exactly the section equality. It found no
remaining mathematical mismatch, correction, hidden arbitrary map, hollow
definition, or additional theorem. All declaration variables and the one
universe are explicitly bound, and the file sets `autoImplicit false`.

Final compile: `scompile.py Q101 lem-sfb-fixed-point-action-finite-jets` passed
for both sandbox and final library module on 2026-10-24 (3.5 s and 4.4 s).
There are no compiler errors or unexpected warnings.
