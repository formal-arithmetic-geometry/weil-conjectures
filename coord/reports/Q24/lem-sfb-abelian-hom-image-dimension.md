## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.HomImageDimension` states
`AlgebraicGeometry.isAbelianVariety_image_and_dimension`, with one `sorry` proof.
No definitions, auxiliary theorems, new nodes, dependency repairs or statement changes
are needed. The node copy changes only `lean`, preserving the reviewed stage-1 split.
The previous worker's stage-1 stale-assignment ending does not apply: brief-stage2 §0
explicitly permits this stage-2 handoff, and the live item has no Lean attachment.

Hypotheses and clauses, matched against the live node:

- The field is `{k : Type u} [Field k]`, with the universe explicitly declared.
- The two schemes over this field are `{A B : Over (Spec (.of k))}`. Their group
  structures are `[GrpObj A] [GrpObj B]`, and their properness, smoothness and
  connectedness are exactly `[IsAbelianVariety A] [IsAbelianVariety B]`.
- The group-scheme homomorphism is `(f : A ⟶ B) [IsMonHom f]`. Being a morphism
  in the over category already includes compatibility with the maps to `Spec k`.
- The specified scheme-theoretic image is `f.left.image`, definitionally the
  closed subscheme `f.left.ker.subscheme`, rather than a reduced or set-theoretic
  image. Its inclusion is `f.left.imageι`, and its structure map is
  `f.left.imageι ≫ B.hom`.
- The first conclusion is
  `IsAbelianVariety (Over.mk (f.left.imageι ≫ B.hom))`. The established declaration
  `exists_isMonHom_imageι f` supplies the group structure induced from `B` on this
  exact over object, and makes its inclusion a homomorphism. Thus the first
  conjunct supplies precisely the proper, smooth and connected properties that
  remain to make this already constructed group scheme an abelian variety.
  `IsAbelianVariety` deliberately has no group-structure parameter, as its defining
  module explains; no arbitrary group structure or extra hypothesis is introduced.
- The kernel is `(GrpObj.ker f).left`. Reading its definition shows that it is
  the pullback of `f` along the actual identity section in the over category.
  It retains scheme structure, including nilpotents.
- The second conclusion is literally
  `topologicalKrullDim A.left = topologicalKrullDim f.left.image +
  topologicalKrullDim (GrpObj.ker f).left`. These are the underlying schemes'
  Krull dimensions, in `WithBot ℕ∞`, with the summands in the node's order.
- The finite-type qualification follows from the hypotheses and these actual
  constructions: `A` is proper, the image is a closed subscheme of proper `B`,
  and the kernel is a closed subscheme of proper `A`. No additional finite-type
  assumptions, dimension truncation, smoothness of the kernel, perfectness of
  `k`, separability of `f`, algebraic closure or characteristic restriction occurs.

Statement dependencies and the declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-sc-abelian-variety`:
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`,
  `AlgebraicGeometry.IsAbelianVariety`. Its docstring and full class signature
  specify exactly proper, smooth and connected, independently of `GrpObj`.
- `def-sc-group-scheme`: Mathlib.CategoryTheory.Monoidal.Grp,
  `CategoryTheory.GrpObj`; Mathlib.CategoryTheory.Monoidal.Mon,
  `CategoryTheory.IsMonHom`; and the upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` and
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`,
  `CategoryTheory.GrpObj.ker`. These are available through the public image import.
- `lem-sc-image-subgroup`:
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Image`,
  `AlgebraicGeometry.exists_isMonHom_imageι`. Its complete statement and proof
  use exactly `Over.mk (f.left.imageι ≫ B.hom)` and give its induced group structure,
  surjectivity and finite type. The companion
  `exists_isClosedSubgroupScheme_imageι` also records quasi-compactness explicitly.
- `def-kun-dimension`:
  `WeilConjectures.Mathlib.Topology.KrullDimension`, `topologicalKrullDimAt`,
  together with Mathlib.Topology.KrullDimension, `topologicalKrullDim`.
  The latter is used directly; its definition is the supremum of irreducible
  closed chains. Both defining docstrings and signatures were read.

All stated proof dependencies are imported (plain imports when only needed for
the future proof). The image and kernel constructors, properness, and geometric
reducedness notions also arrive through the public statement imports. The proof
docstring follows every step and names every input of the accepted node proof.
The proof-only node `lem-sfb-algebraic-group-homomorphism-factorization` currently
has neither a Lean record nor a Mathlib match; its import is omitted because no
module is recorded. Its mathematical use remains in proof step 3, unchanged.
It is not needed to type this statement.

Source read: `literature/milne-algebraic-groups_iAG2017.pdf`, actual PDF pages
40–41 (printed pp.28–29), Proposition 1.70 and Theorem 1.72, and PDF pages
120–121 (printed pp.108–109), Theorem 5.39 and Remark 5.42. The latter gives the
stated dimension formula for the scheme-theoretic kernel; the former gives
geometric reducedness of the image of a smooth algebraic group. Properness and
connectedness of the image are supplied by the accepted node's argument.

Edge cases checked before writing:

- The zero homomorphism: image is the identity copy of `Spec k`, kernel is `A`,
  and the formula reads `dim A = 0 + dim A`.
- The identity: image is `A`, kernel is `Spec k`, giving `dim A = dim A + 0`.
- A projection from a product: image is its target factor, kernel is the other
  factor, giving the usual sum of dimensions.
- Frobenius or multiplication by the characteristic: the kernel may be
  nonreduced but is the full scheme-theoretic kernel; no smoothness is required.
- Dimension-zero abelian varieties and maps involving them are included.
- Imperfect fields and inseparable homomorphisms are included. Empty schemes
  cannot be group schemes over a field, since the identity section supplies a point.

Searches for an existing statement (2026-10-23):

- `msearch.py ... leanfinder` with query "The scheme theoretic image of a
  homomorphism of abelian varieties is an abelian variety and the dimension of
  its source is the dimension of the image plus the dimension of its scheme
  theoretic kernel": eight hits, led by `Scheme.Hom.toImage_app`, `Scheme.Hom.image`,
  `Scheme.Hom.range_subset_ker_support`, `Scheme.Hom.le_ker_comp`, and
  `Scheme.Hom.toImage`. None states the item.
- `msearch.py ... leansearch` with query "The scheme theoretic image of a
  homomorphism of abelian varieties is an abelian variety and the source
  dimension equals image dimension plus kernel dimension": eight hits, including
  `Scheme.Hom.image`, `imageι`, `toImage`, and kernel ideal-sheaf operations.
  None supplies abelian images or this dimension formula.
- `msearch.py ... loogle 'AlgebraicGeometry.IsAbelianVariety'`: zero hits;
  this is an upstream project notion, unknown to the Mathlib search service.
- `msearch.py ... grep 'IsAbelianVariety|topologicalKrullDim.*ker|ker.*topologicalKrullDim'
  AlgebraicGeometry`: zero hits.
- Local `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `IsAbelianVariety.*image|image.*IsAbelianVariety|topologicalKrullDim.*ker|ker.*topologicalKrullDim|lem-sfb-abelian-hom-image-dimension`
  found no existing statement of the item. The hits in Hilbert polynomials,
  support dimension and a polynomial kernel lemma concern different notions.
- Local `rg -n 'image|ker|dimension'` in the upstream abelian-variety directory
  found the special multiplication/isogeny results and their uses of the existing
  image theorem, but no general image-and-kernel-dimension statement.
- `grep -rn 'lem-sfb-abelian-hom-image-dimension' lean/WeilConjectures` found no hit.
- The proposed declaration name was searched in Mathlib and both project roots:
  no collision.

Validation: `scompile.py Q24 lem-sfb-abelian-hom-image-dimension` compiled this
file both as a sandbox module (6.1 s) and at its library module path (5.2 s),
with no errors or warnings. Every theorem proof is `sorry`; no proofs were added.
No statement dispute or node fault was found.

## Second reading by Q24

A separate second pass by the same worker reopened the node, its recorded
dependencies and the complete generated module. No other agent was started,
as this assignment explicitly prohibits delegation; the maintainer's independent
delivery review remains independent of this self-check.

The field, both abelian varieties and their group structures, and the
homomorphism are bound explicitly. The first conjunct uses the actual schematic
image with its induced structure map, and the existing image theorem supplies
the compatible group structure without a new choice or definition. The second
conjunct uses the full pullback kernel and the untruncated Krull dimensions in
the stated order. No extra hypothesis or clause, perfect-field restriction or
reduced-kernel substitution was found. The named source and proof agree with the
accepted split. No mismatch was found and no change was needed on this pass.
