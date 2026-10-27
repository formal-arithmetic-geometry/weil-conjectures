## Worker report

The module `Sheaf.AlgebraicGeometry.SemiabelianAbelianQuotientAmpleReflection`
states `AlgebraicGeometry.semiabelian_abelian_quotient_ample_reflection`, with its
single proof `sorry`. It adds no definition, dependency module or node. The accepted
stage-1 split is preserved verbatim. The inherited BLOCKED ending concerned a duplicate
stage-1 split, whereas the current node has no Lean record and is in the stage-2 queue;
coord/brief-stage2.md section 0 explicitly authorizes this handoff.

Hypothesis and conclusion correspondence:

- The arbitrary field k is `{k : Type u} [Field k]`, for explicitly bound universe u.
- The given k-group schemes C, T and G are `C T G : Grp (Over (Spec (.of k)))`.
  Their group laws are the bundled laws, and i and q are bundled group homomorphisms.
- C is an abelian variety: `[IsAbelianVariety C.X]`. This is precisely proper,
  smooth and connected, in the presence of C's given group structure.
- T is a torus: `hT : MultiplicativeType.IsTorus T`. This allows arbitrary finite
  rank and only asks for splitting after algebraic closure, not over k itself.
- G is commutative: `[IsCommMonObj G.X]`; smooth: `[Smooth G.X.hom]`;
  separated: `[IsSeparated G.X.hom]`; finite type:
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- The supplied maps T -> G -> C are `(i : T ⟶ G) (q : G ⟶ C)`.
- Exactness at T and G is `hkernel : IsPullback i.hom.hom (toUnit T.X)
  q.hom.hom η[C.X]`, in schemes over Spec k. Thus i identifies T with the
  whole scheme-theoretic kernel, rather than just an arbitrary subgroup in it.
  Since representable fppf sheaves preserve limits, this is also the sheaf kernel.
- Exactness at C is `hepi : Presheaf.IsLocallySurjective
  (Scheme.fppfTopology.over (Spec (.of k))) (yoneda.map q.hom.hom)`.
  This says every section of C lifts fppf locally, i.e. q is an epimorphism
  of the represented fppf sheaves. It uses the same q as the torsor condition.
- q is faithfully flat: `[Flat q.hom.hom.left] [Surjective q.hom.hom.left]`.
  q is of finite presentation: `[LocallyOfFinitePresentation q.hom.hom.left]`,
  `[QuasiCompact q.hom.hom.left]`, `[QuasiSeparated q.hom.hom.left]`.
- The specific torsor isomorphism `(g,t) ↦ (g,gt)` is expressed without choosing
  an arbitrary comparison: `htorsor : IsPullback (fst G.X T.X)
  (lift (fst G.X T.X) (snd G.X T.X ≫ i.hom.hom) ≫ μ[G.X])
  q.hom.hom q.hom.hom`. This square says the comparison from the actual
  product G ×_k T to G ×_C G is an isomorphism; its two components are exactly
  g and g times i(t). The multiplication is G's given multiplication.
- The arbitrary invertible module is `(D : C.X.left.Modules) [D.IsInvertible]`.
- The ample tensor pullback is `hample : @Scheme.Modules.IsAmple G.X.left
  ((Scheme.Modules.tensorPullback q.hom.hom.left).obj D)
  (((Scheme.Modules.invertible_pullback_tensor q.hom.hom.left).1 D).2)`.
  The last argument is the existing proof that pullback preserves invertibility,
  not an additional hypothesis or a new definition. The module is the actual
  inverse-image/change-of-rings tensor construction, not the older arbitrary
  choice of a left adjoint. Its normalized recorded interface is publicly imported.
- The conclusion is exactly `Scheme.Modules.IsAmple C.X.left D`.
- There is no splitting, perfect-field, characteristic, symmetric-line or positive-rank
  hypothesis. The field and all schemes have the library's common universe u.

Dependency declarations used:

- `def-weil-field`: `Field` (Mathlib.Algebra.Field.Defs).
- `def-sc-abelian-variety`: `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`, `AlgebraicGeometry.IsAbelianVariety`.
- `def-sfb-tori-multiplicative-type`: `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`, `AlgebraicGeometry.MultiplicativeType.IsTorus`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-sc-group-scheme`: `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj`.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`, `AlgebraicGeometry.Scheme.fppfTopology`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`.
- `def-weil-pbc-ample-invertible-module`: `WeilConjectures.AlgebraicGeometry.Ample`, `AlgebraicGeometry.Scheme.Modules.IsAmple`.

The invertibility argument of IsAmple additionally uses
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`,
`AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor` (an already listed
proof dependency), so that module is public. Products and kernel/torsor squares use
Mathlib's CartesianMonoidalCategory and IsPullback, as in the landed geometric
semiabelian quotient and geometric-fibre interfaces. The existing Field, Scheme,
Smooth, LocallyOfFiniteType, QuasiCompact, GrpObj, fppfTopology, pullback,
IsAbelianVariety, IsTorus, IsInvertible, tensorPullbackObj/tensorPullback and IsAmple
source declarations and docstrings were read.

Every currently recorded proof-dependency module is imported. Mathlib leaf proof
inputs add Proper, Separated, QuasiCompact, QuasiSeparated, Sites.Precoverage,
Flat.FaithfullyFlat.Basic and LinearAlgebra.Basis.VectorSpace. The following proof
nodes have neither a Lean record nor a Mathlib match and supply no module to import:
lem-sfb-abelian-field-extension, lem-sfb-space-relative-ampleness-fpqc-descent,
lem-sfb-split-torus-torsor-section-extraction,
lem-sfb-semiabelian-picard-pullback-kernel,
lem-sfb-semiabelian-effective-square-generation,
lem-sfb-semiabelian-algebraic-equivalence-norm. These are proof inputs only and are
not needed to state this theorem; their accepted proof plan is in the docstring.

Edge cases checked before writing:

- Rank-zero T is included. The extension then identifies G with C and the result
  reduces to invariance of ampleness under that isomorphism; no rank bound is added.
- C can be the zero-dimensional trivial abelian variety. The theorem includes
  arbitrary tori over a point, with invertible modules on Spec k.
- A split product extension G = T × C uses the actual right-translation map.
  Its identity section makes reflection consistent with restriction to C.
- Non-split tori and imperfect fields in every characteristic are admitted by IsTorus;
  neither the statement nor its IsPullback formulations introduce a splitting choice.
- Empty schemes cannot be groups over Spec k, since their identity sections would
  have nonempty source. No separate nonemptiness assumption is added.
- Replacing i by the zero homomorphism in a nontrivial torus does not satisfy the
  kernel and torsor squares. Replacing q by the constant map to a positive-dimensional
  C fails local surjectivity and scheme surjectivity. Thus these conditions do not
  silently allow arbitrary maps. A non-ample D is excluded only by the ample-pullback
  hypothesis, whose substantive content is the theorem's asserted implication.

Searches for reuse (results in searches.jsonl in the sandbox):

- msearch.py leanfinder: `Ampleness of an invertible sheaf on an abelian variety is reflected by pullback to an extension by a torus`; 8 hits: `AmpleSet.preimage_iff`, `AmpleSet.image_iff`, `AmpleSet.preimage`, `AmpleSet.image`, `AlgebraicGeometry.AffineSpace.isPullback_map`, `AlgebraicGeometry.Scheme.isPullback_toSpecΓ_toSpecΓ`, `AlgebraicGeometry.AffineSpace.homOfVector`, `AlgebraicGeometry.Scheme.Modules.instAdditivePullback`.
- msearch.py grep: `semiabelian|semiAbelian|IsAmple`; 0 hits: .
- msearch.py loogle: `"IsAmple", "IsAbelianVariety"`; 0 hits: .

The LeanFinder results concern convex AmpleSet, affine-space pullbacks and an
additive module-pullback instance, not ampleness of invertible sheaves under a
semiabelian quotient. Loogle and Mathlib grep have no matches. Direct rg searches
of lean/WeilConjectures and lean/Sheaf for the item id return no existing theorem;
searches for ampleness with quotient/abelian/reflection find only other statements
(e.g. finite-surjective reflection and polarization calculus). The source-name
index dag/lean_names_upstream.json has ample predicates and ample tensor-power
results, with no theorem for this semiabelian quotient implication. No duplicate
notion is introduced.

Source status: Raynaud XI 1.11 is WANTED as the accepted node already records.
The statement was taken verbatim from that accepted node; its assembled proof uses
Milne and Stacks as recorded there. No source-based statement correction was needed.
There are no STATEMENT-DISPUTED flags and no node faults.

Validation: scompile.py compiled both the sandbox and final library module cleanly
against the live published build (2.7 seconds each). The delivery dry run follows.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
