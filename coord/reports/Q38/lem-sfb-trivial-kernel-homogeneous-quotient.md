## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TrivialKernelHomogeneousQuotient`
states `AlgebraicGeometry.exists_homogeneousQuotient_of_trivialKernel` with one
`sorry`. No definitions, auxiliary theorems, node corrections or dependency repairs
are needed. The node is unchanged except for `lean`.

Source read: Milne, *Algebraic Groups* (2017), Definition 5.20(a) and Theorem 5.28,
printed pp.104--105; Appendix B, Theorem B.37 and Remark B.38, printed pp.605--606.
Theorem 5.28 explicitly allows a homomorphism with trivial kernel. Definition 5.20(a)
gives right-coset fibres. The kernel-pair interpretation extends this equality from
algebras to arbitrary scheme tests by gluing the unique H-valued lifts. The node
retains only the action, distinguished point, finite type and fibre equivalence;
it does not request the full local-lifting conclusion of Milne's quotient theorem.

Hypothesis and conclusion correspondence:

- `k : Type u` and `[Field k]` render an arbitrary field, in arbitrary universe u.
- `H G : Over (Spec (.of k))` are the two k-schemes; `[GrpObj H] [GrpObj G]`
  supply multiplication, inverse and identity with the group diagrams.
- `[IsSeparated H.hom]` and `[IsSeparated G.hom]` render separatedness over k.
- For each of H and G, `[LocallyOfFiniteType _.hom] [QuasiCompact _.hom]`
  render finite type. Neither affineness nor smoothness nor reducedness is imposed.
- `i : H ⟶ G` and `[IsMonHom i]` render a group-scheme homomorphism over k.
- `hker : IsIso (toUnit (GrpObj.ker i))` says that the canonical map from the
  scheme-theoretic kernel to the terminal k-scheme is an isomorphism. The upstream
  definition is `GrpObj.ker i = pullback i η[G]` in the slice. Its underlying
  scheme is the stated fibre product. The slice tensor unit is `Over.mk (𝟙 (Spec k))`,
  so the underlying terminal scheme is precisely Spec k. Its group structure is
  the unique terminal group structure; any isomorphism to it is a group isomorphism.
  This hypothesis does not assume i is a closed immersion or use injectivity only
  on field-valued points.
- `∃ X : Over (Spec (.of k))` supplies the k-scheme X.
- `LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom` gives exactly its finite type.
- `act : ModObj G X` supplies the scheme morphism `act.smul : G ⊗ X ⟶ X`.
  Tensor in this slice is the scheme fibre product over k. `ModObj.one_smul`
  gives μ(e,x)=x; `ModObj.mul_smul` gives μ(g,μ(g',x))=μ(gg',x). In the cartesian
  category these are equivalent to their pointwise forms on every scheme test.
  No new action predicate or copy of ModObj is defined.
- `o : 𝟙_ (Over (Spec (.of k))) ⟶ X` is the distinguished k-point.
  `toUnit T ≫ o` is its base change o_T, since `toUnit T` is T's structure map.
- The quantifier `∀ (T : Over (Spec (.of k))) (a b : T ⟶ G)` ranges over every
  k-scheme in the working universe and both of its G-valued points, not just affines.
- `lift a (toUnit T ≫ o) ≫ act.smul` is q_T(a)=μ(a,o_T), and the same expression
  with b is q_T(b). Thus the left side is exactly the orbit-map equality.
- `a⁻¹ * b ∈ Set.range (fun h : T ⟶ H ↦ h ≫ i)` is exactly
  a⁻¹b ∈ i_T(H(T)), with inverse and multiplication from `Hom.group`.
  The `↔` gives both directions and no extra quotient conclusion is added.

Dependency declarations used, with their defining modules read:

- def-weil-field: `Field`, `Mathlib.Algebra.Field.Defs`.
- def-sc-group-scheme: `CategoryTheory.GrpObj`, `CategoryTheory.IsMonHom`,
  `Mathlib.CategoryTheory.Monoidal.Grp` / `.Mon`; the functor-of-points group is
  `CategoryTheory.Hom.group`, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
  `CategoryTheory.GrpObj.ker`, `.kerι`, `.isPullback_kerι` are in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` and publicly
  available via `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, whose full
  group-scheme terminology and kernel section were read. No private kernel is used.
- def-weil-proper-morphism: `AlgebraicGeometry.IsSeparated`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`, publicly imported through the
  dependency's recorded `.Proper` module. Only separatedness is used.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, in `.Morphisms.FiniteType` and `.QuasiCompact`.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; it underlies the
  kernel construction and the slice cartesian tensor structure.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- Existing action API: `CategoryTheory.ModObj`, `Mathlib.CategoryTheory.Monoidal.Mod`,
  and `CategoryTheory.Hom.mulAction`, `.Monoidal.Cartesian.Mod`. The instance
  `CategoryTheory.Over.cartesianMonoidalCategory`, `.Monoidal.Cartesian.Over`,
  identifies the tensor unit with Spec k and tensor with fibre product.

Every currently recorded proof-dependency module is imported without `public`:
`Mathlib.AlgebraicGeometry.Sites.Fpqc`,
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`,
`Sheaf.AlgebraicGeometry.ClosedPointField`,
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient`,
`Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseSchemeOpen`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal`,
`Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`,
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
`Mathlib.RingTheory.Jacobson.Ring`, `Mathlib.AlgebraicGeometry.Noetherian`.
The group-scheme dependency is already a public import. The still-unstated proof
nodes finite-extension-open-exhaustion, representable-lft-fppf-source-descent,
space-closed-immersion-fppf-descent, space-largest-schematic-open and
space-qcqs-permanence have no recorded module to import. They are named explicitly
in the eleven-step proof docstring and are not statement prerequisites.

Edge cases checked mathematically before writing:

- H=1: take X=G, its left regular action, and o=e. The relation becomes a=b iff
  a⁻¹b=e, so the right-coset orientation is correct.
- i=id_G (H=G): take X=Spec k with its trivial action. Every pair has equal
  orbit image and a⁻¹b always belongs to the full image. The kernel is terminal.
- Empty T: all morphisms from T into a scheme are unique. Both sides hold, since
  there is the unique empty-test H-point. No nonempty-test hypothesis is introduced.
- Empty H or G is not a hidden exclusion: neither can be a group scheme over a
  field, since its identity section has nonempty source Spec k.
- Nonreduced tests and group schemes remain allowed. For example Frobenius on G_a
  in characteristic p has nontrivial infinitesimal kernel α_p, so it does not satisfy
  hker despite injectivity on field-valued points. The use of GrpObj.ker detects this.
- T may be non-affine and disconnected. All slice schemes in universe u are tested;
  u is arbitrary, as in the existing group-scheme and homogeneous-quotient APIs.
- No normality, characteristic restriction, perfection, algebraic closedness,
  connectedness or closedness of i is assumed. The conclusion does not require
  separatedness of X, local lifts, or a specified quotient map beyond its orbit map.

Searches made:

- `msearch.py ... leanfinder`: "A finite type group scheme over a field modulo a
  homomorphism with trivial scheme theoretic kernel has a homogeneous scheme quotient
  with right coset fibres". Eight hits concerned Galois-category quotients, abstract
  action quotients and abstract groups; none is the group-scheme theorem.
- `msearch.py ... loogle`: `"GrpObj", "ker"`. Eight hits were unrelated
  commutator/unit identities and supplied no homogeneous scheme quotient.
- `msearch.py ... grep`: `homogeneous|quotient|trivialKernel`, in
  `AlgebraicGeometry/Group`. Zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `trivial.kernel|TrivialKernel|homogeneous.quotient|HomogeneousQuotient` found the
  existing closed-subgroup quotient and its consumers, plus unrelated ring/linear
  algebra quotients. `exists_homogeneousQuotient` requires
  `[IsClosedSubgroupScheme j]` and does not supply an action in its conclusion;
  it is a proof dependency, not an exact existing statement of this node.
  `HomogeneousOrbitQuotientGeometry` has stronger closed, affine, smooth and
  algebraically-closed hypotheses. `MonomorphismClosedImmersion` is a downstream
  theorem with a different conclusion, not used to assume closedness here.
- Search for the exact blueprint id in `lean/WeilConjectures` found no declaration.
- Exact new declaration name was searched in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`: no clash.
- `msearch.py ... leansearch`: "A homomorphism of finite type group schemes with
  trivial scheme theoretic kernel has a homogeneous scheme quotient with an action
  and right coset fibres". Eight hits concerned finite-set actions, abstract group
  extension quotients, quotient representations and abstract coset maps; none
  supplied the scheme quotient or its existence theorem.
- The existing ModObj and kernel APIs were read directly, so neither needs an extra
  definition node.

Validation: prescribed `scompile.py Q38 lem-sfb-trivial-kernel-homogeneous-quotient`
compiled the delivered file as sandbox and as library module, cleanly (10.9s and 4.4s).
No errors or unexpected warnings. Every universe and variable is bound explicitly,
and `set_option autoImplicit false` enforces that condition. The module has exactly
one theorem with proof `by sorry`, no data definitions and no auxiliary proof holes.

No STATEMENT-DISPUTED flag: the source and all clauses agree. No statement correction.
The sample `Sheaf.CategoryTheory.CompactObject` was read; it is now withdrawn. Its
node points to the upstream `WeilConjectures.CategoryTheory.CompactObject`, so the
new file follows the live public-module conventions shown in the group-scheme files.

## Second reading by Q38

Reread the exact node and the complete delivered signature after compilation. This
is a same-worker check; the dispatcher's brief prohibits starting another agent,
and assigns independent review to the maintainer. The check finds both H and G
separated and finite type, the homomorphism condition explicit, and hker attached
to the actual kernel pullback. The terminal map is canonical, so no arbitrary map
or merely pointwise reduced-kernel condition is substituted. The existential action
is the existing ModObj construction, including precisely the two action laws.
The point is a genuine Spec k morphism. The fibre formula uses a⁻¹b (right cosets),
not ba⁻¹, and quantifies over all schemes. X is only required finite type, as in
the node. No mismatch was found and no clause was changed. The proof docstring
retains all eleven node steps; the existing proof modules are imported privately.
