## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.HomDimensionKernelImage` states
`AlgebraicGeometry.algebraicGroup_hom_dimension_kernel_image`, with one `sorry` and no
new definitions. The original node is changed only in `lean`. No statement correction,
new node, or dependency repair is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| G,H affine k-group schemes | `G H : Grp (Over (Spec (.of k)))`, `[IsAffine G.X.left]`, `[IsAffine H.X.left]` |
| G,H of finite type over k | `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]` and the same two instances for H |
| Homomorphism f:G→H | `f : G ⟶ H` in the category of bundled group objects; the underlying Over morphism is `f.hom.hom` |
| L is the scheme-theoretic kernel, not a kernel on rational points | `(GrpObj.ker f.hom.hom).left`; the existing definition is the pullback along the unit in the Over category, whose underlying scheme is the indicated scheme fibre product |
| Homomorphism factorization through the closed image group I | `I : Grp (Over (Spec (.of k)))`, `q : G ⟶ I`, `j : I ⟶ H`, and `hfactor : q ≫ j = f` |
| q faithfully flat | `[Flat q.hom.hom.left] [Surjective q.hom.hom.left]` |
| q finitely presented | `[LocallyOfFinitePresentation q.hom.hom.left] [QuasiCompact q.hom.hom.left] [QuasiSeparated q.hom.hom.left]`, exactly the full finite-presentation convention of the recorded factorization |
| j a closed immersion | `[IsClosedImmersion j.hom.hom.left]` |
| All dimensions finite nonnegative integers | First conjunct: `∃ dG dH dI dL : ℕ`, with the four respective topological dimensions equal to their casts into `WithBot ℕ∞` |
| dim G = dim I + dim L | Second conjunct, using `topologicalKrullDim` on the underlying schemes, with the image dimension first in the sum |
| If H smooth and connected | `Smooth H.X.hom → ConnectedSpace H.X.left → ...` in the third conjunct; these conditions do not restrict the first two conjuncts |
| Faithful flatness iff dim G = dim H + dim L | `(Flat f.hom.hom.left ∧ Surjective f.hom.hom.left) ↔` the stated equality in the third conjunct |
| Flat and surjective on spaces is the meaning of faithfully flat | Existing `Flat` is equivalent to flatness of every stalk map; existing `Surjective` is literally surjectivity of the underlying function |
| No smoothness/connectedness for G or L, no separability hypothesis | There are no such hypotheses; the kernel is the full scheme-theoretic kernel |

The factorization is an input with exactly the properties specified in the node. This
allows any representative of the essentially unique homomorphism factorization, rather
than making an arbitrary choice from an existence theorem. There is no extra affineness,
separatedness, finite-type, or quotient-presentation hypothesis on I. Its necessary
properties follow from its closed immersion into H and the stated factorization theorem.
Every universe and variable is explicit, and `autoImplicit` is disabled.

Dependency interfaces read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the closure node's match explicitly
  identifies this as its algebraically closed clause. No choice of an algebraic closure is needed.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, bundled `Grp`, and its category of
  homomorphisms; `Mathlib.CategoryTheory.Monoidal.Mon`: `IsMonHom` underlying those morphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` and
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: the recorded
  group-scheme interface and `CategoryTheory.GrpObj.ker`, defined as a pullback.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization`:
  `AlgebraicGeometry.algebraicGroup_homomorphism_factorization`, whose complete signature
  supplies q flat, surjective and finitely presented and j a closed immersion.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, used by the
  existing kernel, with `pullback.fst` and `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim : ... → WithBot ℕ∞`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- Full finite-presentation properties use `LocallyOfFinitePresentation` and
  `QuasiSeparated` from their Mathlib morphism modules, exposed by the factorization module.

All modules of recorded proof dependencies are imported as proof imports when not already
publicly available through a statement dependency: separatedness, finite-dimensionality,
point dimensions, the flat composite fibre formula, rational-point stalk dimension,
identity stalk dimension, geometrically reduced smooth fibres, regular local smooth rings,
regular closed-point components, the domain assertion, and the spectrum/ring dimension
comparison. The natural-language proof in the theorem docstring follows all six DAG steps.
The `lem-wf-affine-dimension-drop` record currently exposes its domain assertion only;
the full strict-drop argument remains part of the node's stage-3 proof plan, not an extra
assumption of this statement. No new postponed theorem is introduced for it.

Sources checked locally: Milne iAG2017 PDF, printed p.104 (PDF p.116), Proposition 5.23;
printed pp.108–109 (PDF pp.120–121), Theorem 5.39 and Remark 5.42; printed p.17 (PDF p.29),
Corollary 1.35. These give the quotient dimension formula, factorization, image formula,
and irreducibility input. No change to the source meaning is required.

Edge cases checked mathematically:

- All groups, including the kernel and image, have an identity point. An empty scheme
  cannot carry the stated group structure, so no `Nonempty` assumption is added. The
  existential natural-number dimensions exclude both bottom and infinity as required.
- For the trivial groups all four dimensions are 0 and both assertions hold.
- For a trivial homomorphism to a positive-dimensional smooth connected H, I is the
  identity subgroup and L=G. The formula holds, and the criterion correctly fails.
- For Frobenius on the additive group in characteristic p, G and H have dimension 1,
  I=H and L=alpha_p has dimension 0. Faithful flatness holds despite inseparability
  and the nonreduced kernel. This case is retained without any characteristic condition.
- Inclusion of mu_n into the multiplicative group has zero-dimensional image and kernel;
  it is not faithfully flat onto its dimension-1 target.
- Inclusion of the identity into alpha_p shows why the smooth-target hypothesis cannot
  be omitted. The 0=0+0 dimension equality alone would not force flatness.
- Inclusion of the identity component into a disconnected smooth group shows why
  connectedness is needed: equal dimensions alone do not imply surjectivity.

Searches before writing, using the prescribed msearch wrapper with Q66 and this item:

- LeanFinder, query “For an affine algebraic group homomorphism the dimension equals
  dimension of closed image plus dimension of scheme theoretic kernel, with faithful
  flatness criterion”; repeated more briefly as “Dimension of affine group scheme equals
  dimension of closed image plus kernel”. Eight hits included presentation dimension,
  affine-monoid rank, ideal-sheaf kernels, and linear rank-nullity, not this theorem.
- Loogle, query `"topologicalKrullDim", "ker"`: 0 hits.
- Mathlib grep, query `(ker|image).*(topologicalKrullDim|dimension)|(topologicalKrullDim|dimension).*(ker|image)`
  in `AlgebraicGeometry/Group`: 0 hits.
- LeanSearch, query “The Krull dimension of an algebraic group equals dimension of image
  plus dimension of kernel of a homomorphism”: eight hits on linear rank-nullity, quotient
  ring dimension, dimension comparisons, and module support, not the group-scheme formula.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` with the dimension/kernel/image
  pattern found related geometry and linear results, not the formula. The specific node-id
  search in `lean/WeilConjectures` found nothing. The upstream group `Basic.lean` describes
  a same-dimensional closed-subgroup criterion, but does not state this formula and has
  different hypotheses. It was read rather than treated as a match from its module summary.
- Exact proposed-name search in Mathlib, both project Lean roots, and
  `dag/lean_names_upstream.json`: no existing declaration.

Validation: scompile.py compiled the delivered module in both sandbox and library modes
against the live server build (7.7 s and 7.9 s respectively), with no errors or warnings.
The only postponed proof is `AlgebraicGeometry.algebraicGroup_hom_dimension_kernel_image`.
No STATEMENT-DISPUTED flag or statement fault was found.

## Second reading by Q66

This is a second pass by the same worker; the dispatcher brief forbids starting other
agents and assigns the independent review to the maintainer. I reopened the node and
the actual Lean signature and checked each row above. In particular the original uses
scheme-theoretic kernels, affine finite-type G,H, a finitely presented faithfully flat q,
a closed-immersion j, addition in the image-then-kernel order, finite natural dimensions,
and a conditional criterion requiring both smoothness and connectedness of H. All are
present. Smoothness and connectedness appear inside the last implication only. There is
no surjectivity assumption on f and no replacement of L by a reduced or rational-point
kernel. The four natural witnesses certify finiteness without changing the dimension
definition or silently truncating it to a natural number. No mismatch or correction was
found on this pass.
