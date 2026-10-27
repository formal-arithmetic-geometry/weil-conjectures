## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.KernelAbelianPart` states
`AlgebraicGeometry.IsAbelianVariety.exists_closed_subgroup_ker_same_dimension`.
It has one theorem, with proof `sorry`, and no new definition. The item node changes
only in `lean`; its statement and all dependencies are preserved.

Source read: Milne, Abelian Varieties, Chapter I, printed pp.42–43 (PDF pp.48–49),
Proposition 10.1, footnote 10, and the discussion after Remark 10.2, footnote 11.
These explicitly flag the geometric-reducedness issue over imperfect fields.
The accepted node's six-step proof addresses that issue by geometric reduction,
finite separable definition and Galois descent. The Lean asserts existence over k,
never equality with the reduction over k. Its declaration docstring reproduces
all six proof steps with the corresponding node references.

Hypothesis and clause correspondence:

- Any field k: `{k : Type u} [Field k]`, with the universe u explicitly bound.
  There is no perfectness, characteristic or algebraic-closedness restriction.
- Abelian varieties A and B over k: `{A B : Over (Spec (.of k))}` and
  `[GrpObj A] [GrpObj B] [IsAbelianVariety A] [IsAbelianVariety B]`.
  `IsAbelianVariety` means proper, smooth and connected, exactly as in the
  dependency. Group structures are separate parameters, as that API requires.
- A k-group-scheme homomorphism f: `(f : A ⟶ B) [IsMonHom f]`.
  The over-category morphism is over k and `IsMonHom` gives group compatibility.
- Scheme-theoretic kernel K: every occurrence is the recorded canonical
  `GrpObj.ker f`, the pullback of f along the unit of B. No abstract kernel,
  reduction, chosen map, or auxiliary substitute is introduced.
- Existence of a closed k-subgroup D contained in K: the first conjunct binds
  `(D : Over (Spec (.of k))) (_ : GrpObj D)` and `(i : D ⟶ GrpObj.ker f)`,
  and asserts `IsClosedSubgroupScheme i`. This includes homomorphism compatibility,
  injectivity on points over every k-algebra and closed immersion of schemes.
  The second displayed inclusion K into A is the canonical `GrpObj.kerι f`;
  it is a closed subgroup inclusion by the existing kernel instance. Composing
  these inclusions gives exactly the inclusion D into A in the node.
- D is abelian over k: the existential binder `(_ : IsAbelianVariety D)`.
- The dimensions agree: `topologicalKrullDim D.left =
  topologicalKrullDim (GrpObj.ker f).left`. Both use the recorded topological
  Krull dimension, not a natural-number truncation or local dimension.
- If dim K = 0, K is finite over k: the second conjunct is
  `topologicalKrullDim (GrpObj.ker f).left = 0 → IsFinite (GrpObj.ker f).hom`.
  This refers to the whole kernel scheme, including its nilpotents. There is
  no reducedness assumption on K. Finiteness is the scheme morphism predicate,
  not merely finiteness of its points.
- The final explanatory sentence about imperfect-field reduction is respected:
  the theorem does not identify D with a reduction, nor demand that K be smooth.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, the match of def-weil-field.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety`, the recorded def-sc-abelian-variety.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, and
  `Mathlib.CategoryTheory.Monoidal.Mon`: `CategoryTheory.IsMonHom`, the
  recorded group-scheme terminology. Both are publicly available through the
  imported upstream group-scheme module.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`:
  `CategoryTheory.GrpObj.ker`, `CategoryTheory.GrpObj.kerι`, whose definitions
  explicitly use the pullback along the unit.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `AlgebraicGeometry.IsClosedSubgroupScheme`,
  `AlgebraicGeometry.isClosedSubgroupScheme_kerι`, and the existing finite
  structure-morphism convention. Read full definitions and docstrings.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, whose range is
  `WithBot ℕ∞` and whose definition is `Order.krullDim (IrreducibleCloseds T)`.

The already stated proof dependencies are imported privately: BaseChangeConventions,
Dimension, EffectiveDescent, the group-object kernel module,
SubvarietySeparableDefinition, DimensionExtension, ProperDimZeroFiniteOverField,
ClosedImmersion, Proper, ZariskisMainTheorem, AlgebraicClosure, and Normal.Basic.
The proof-only nodes lem-sfb-abelian-closed-subgroup-reduced-component,
lem-sfb-abelian-field-extension, and lem-sfb-galois-closed-subscheme-descent have
no recorded declaration in the read base; they are not needed to type this
statement. Their future proof imports belong to maintainer bookkeeping.

Edge cases checked before writing:

- The zero-dimensional abelian variety (the trivial group) is allowed for A,
  B and D. No positive dimension, nonzero morphism or nontriviality is assumed.
- For the identity map, K is the trivial subgroup and D can be trivial; the
  finite-kernel implication has its ordinary zero-dimensional meaning.
- For the zero homomorphism, K is A and D can be A. The conclusion does not
  accidentally assert every kernel finite.
- In positive characteristic, an inseparable isogeny (for example [p] on an
  abelian variety with nonreduced p-torsion) has a zero-dimensional, potentially
  nonreduced kernel. The implication concludes finiteness of that full scheme.
- An arbitrary imperfect field remains allowed; the statement does not demand
  the reduction of K be a subgroup or an abelian variety.
- An empty kernel cannot arise because the identity factors through K. We add
  no nonemptiness hypothesis, and the dimension convention retains bottom for
  empty spaces rather than silently coercing all dimensions to naturals.
- All universes and variables are explicitly bound, with autoImplicit disabled.

Searches actually run (logged by msearch.py for this item):

- LeanFinder: "The scheme theoretic kernel of a homomorphism of abelian varieties
  contains an abelian subvariety of equal dimension". Eight results, all about
  scheme ideal kernels (`Scheme.Hom.ker`, `le_ker_comp`, `ker_comp`,
  `range_subset_ker_support`, `Scheme.kerFunctor_obj`, `kerFunctor_map`,
  `Scheme.IdealSheafData.map_ker`, `Hom.ker_toNormalization`); none is this result.
- Loogle: `"IsAbelianVariety", "ker"`. Zero results.
- Mathlib grep: `IsAbelianVariety|abelian.*kernel|kernel.*abelian` in
  AlgebraicGeometry. Zero results.
- LeanSearch: "The kernel of a homomorphism of abelian varieties over a field
  contains an abelian subvariety of the same dimension". Eight results:
  MonoidHom.mker, AddMonoidHom.ker, AddMonoidHom.mker,
  AddMonoidHom.decidableMemKer, MonoidHom.ker, AddCon.ker, Abelianization.ker_of,
  AddMonoidHom.mem_ker. None concerns the required closed abelian subgroup scheme.
- rg of both project source roots for abelian/kernel terminology and the exact
  node id, then focused reads of their AbelianVariety directories. No exact
  statement. HomImageDimension states the distinct image/kernel dimension formula;
  PolarizationCalculus uses a geometric reduced-component argument but does not
  declare this arbitrary-field result.

No new nodes, dependency repair, statement correction, or mathematical dispute
was needed. The example CompactObject module was read; it is now withdrawn and
contains no declarations, so the current required module/public-import conventions
and a recent AbelianVariety statement module were used for the header structure.

Validation: scompile.py compiled the sole delivered file in both sandbox and
library-module modes on the server, exit code 0, with no errors or warnings.

## Second reading by Q125

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
