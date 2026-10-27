## Worker report

Item: lem-sfb-stack-etale-local-qcqs-homeomorphism. The delivery states two theorems
in `Sheaf.AlgebraicGeometry.StackEtaleLocalQcqsHomeomorphism`, both with whole-proof
`sorry`. The first gives the three separate target-etale locality equivalences;
the second gives the three separate arbitrary-base-change implications. No theorem
is proved. The additional definition module contains real predicate data and no sorry.
The item's natural-language statement and proof are unchanged.

Hypothesis-by-hypothesis reading:

- Base scheme and sizes: `{S : Scheme.{u}}`; independent endpoint hom/object levels
  `v₁,w₁,v₂,w₂`, base-change levels `v₃,w₃`, and independent further test bounds.
  The quasi-compactness predicate is the recorded one, with explicit final test
  universe arguments. The new universal-homeomorphism predicate uses the same
  `max u ...` and `max (u+1) ...` size convention. No equality of universes is assumed.
- Arbitrary algebraic stacks A and B: the two `BasedCategory` binders, with
  `hA : IsAlgebraicModuliStack A` and `hB : IsAlgebraicModuliStack B`.
- Their morphism: `f : BasedFunctor A B`. There is no representability, DM,
  finite-inertia, finite-type, or separation hypothesis on f.
- Small family of algebraic spaces: `(I : Type z) (W : I → AlgebraicSpace S)`.
  No `Nonempty I`, finiteness, quasi-compactness or separatedness is required.
- The actual cover maps: `a i : BasedFunctor (discreteModuli (W i).obj.obj) B`.
  This uses the existing discrete fibred groupoid of each algebraic space.
- Representable etale: `ha : ∀ i, IsEtaleModuliMap (a i)`. Its recorded definition
  says that EVERY scheme 2-base change has an algebraic-space presentation whose
  actual projection satisfies `SpaceMapIsEtale`. The latter tests all etale scheme
  charts. It neither requires scheme representability nor chooses an atlas.
- Joint surjectivity: `hsurj` quantifies over every field K, structural map b and
  field-valued object y. It supplies an index i, extension field L and unital field
  map j, and a field-valued x in W i. `ModuliTwoIso` identifies `x.comp (a i)` with
  the pullback of y along the actual `Spec.map j`. This is extension-local lifting,
  not lifting over K itself or requiring each individual a i to be surjective.

Clause-by-clause reading:

- The local projection f_i is `moduliTwoFiberFst (a i) f`, whose source is the
  existing category of triples W_i ×_B A and whose target is W_i. Interchanging
  the written order A ×_B W_i uses the canonical symmetry; it does not change
  the projection or add data to the statement.
- First equivalence: `IsQuasiCompactAlgebraicModuliMap f ↔ ∀ i, ... f_i`.
  This is exactly the stack-test/smooth quasi-compact atlas convention of the
  dependency, not the narrower etale-atlas DM quasi-compactness predicate.
- Second equivalence: `IsQuasiSeparatedAlgebraicModuliMap f ↔ ∀ i, ... f_i`.
  This predicate tests the actual relative diagonal and demands representability,
  quasi-compactness AND quasi-separatedness of every space-valued scheme test.
- Third equivalence: `IsUniversalHomeomorphismAlgebraicModuliMap f ↔ ∀ i, ... f_i`.
  The new definition quantifies over arbitrary algebraic-stack base changes and
  requires `IsHomeomorph` of the actual induced point map. It is not an arbitrary
  existence of a homeomorphism, nor just bijectivity or scheme-only tests.
- Topologies: the existing global `moduliPointTopologicalSpace` instance is the
  smooth-atlas topology; `StackPointTopology` establishes independence and continuity.
- The second theorem takes any algebraic C and any `g : BasedFunctor C B` and
  states, separately, `QC f → QC (moduliTwoFiberFst g f)`, the corresponding QS
  implication, and the corresponding universal-homeomorphism implication.
  It has NO cover-family hypothesis. This matters because arbitrary algebraic
  stacks need not admit a representable etale cover by algebraic spaces.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
  The size-convention node is metatheoretic and has no declaration to import.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack` and its
  smooth-surjective-atlas formulation.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale` and the
  actual underlying fppf sheaf of each space.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `BasedFunctor`, `discreteModuli`, `discreteModuliMap`,
  `ModuliTwoIso`, `HasSpaceBaseChange`, `SpaceMapIsEtale`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `IsQuasiCompactAlgebraicModuliMap`, `IsQuasiSeparatedAlgebraicModuliMap`.
- `Sheaf.AlgebraicGeometry.StackPointTopology`: `stack_point_topology` and the
  exported `ModuliPoints`, `moduliPointMap`, `moduliPointTopologicalSpace` interface
  from `DmStackMorphismProperties` and `StackPointTopologyFlatLfpOpen`.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `IsEtaleModuliMap`.
  Its owner, the already landed `def-sfb-moduli-chart-normalization`, is added to
  stmt_deps under the rule permitting additional landed statement dependencies.
  Only its representable-etale helper is used; no normalization assumption is added.
- New `Sheaf.AlgebraicGeometry.StackUniversalHomeomorphism`:
  `CategoryTheory.IsUniversalHomeomorphismAlgebraicModuliMap`.

Public imports supply the signature; plain imports supply the recorded proof plan:
`AlgebraicStackFibreProducts`, `AlgebraicStackQuasicompactSurjection`,
`AlgebraicSpaceAffineEtaleCover`, `StackChartwiseSmoothEtaleCalculus`,
`StackPointTopologyFlatLfpOpen`, `AlgebraicSpaceQuasiCompactFppfLocal`,
`AlgebraicSpaceFibreProductsEtaleCovers`, `RelativeInertiaSecondDiagonalGeometry`;
Mathlib `AffineScheme`, `Limits`, `Morphisms.QuasiSeparated` for the two Mathlib
proof leaves. The groupoid-diagonal-two-pullback-identities proof node has no
recorded Lean declaration/module; there is consequently no import to add for it.
Its role is retained explicitly in both proof docstrings. No import cycle is added.

Edge cases checked before writing:

- Empty index: no nonempty binder; hsurj then says there are no target field objects.
  The conclusion gives the expected vacuous local tests for an empty target.
- Empty scheme/test stack: permitted; the empty finite atlas refinement is used in
  the proof plan, with the empty affine coproduct Spec of the zero ring.
- Identity family and identity base change: these recover the original property;
  none of the three conclusions is replaced by a condition on an identity map.
- Non-quasi-compact W_i and infinite families: no compactness assumption on them;
  finite selection occurs only over the affine test atlas.
- Non-DM algebraic stacks: the base-change theorem remains applicable, independently
  of whether such a target admits the special cover in the locality theorem.
- Nonrepresentable f: allowed by both the signature and Stacks' definition 0CI7.
  In particular universal homeomorphism is not encoded as representability.
- Non-quasi-separated f: the QS clause is an equivalence, not an unconditional
  assertion; the whole diagonal qcqs test is preserved.
- Field lifts require arbitrary extension fields, not algebraic closure or an
  algebraic extension. Common extensions and the comparison isomorphisms are retained.

Searches (all remote search results are in searches.jsonl):

1. LeanFinder: “Quasi compact quasi separated and universal homeomorphism of algebraic
   stacks descend along a surjective etale algebraic space cover” — eight scheme
   descent hits; none concerns morphisms of arbitrary algebraic stacks.
2. Loogle: `AlgebraicGeometry.QuasiCompact, AlgebraicGeometry.QuasiSeparated` — twelve
   scheme morphism/diagonal hits, no stack locality result.
3. msearch grep: `stack.*(quasi.?compact|quasi.?separated|homeomorphism)|` followed by
   `(quasi.?compact|quasi.?separated|homeomorphism).*stack`, in Mathlib AlgebraicGeometry
   — zero hits.
4. LeanSearch: “Properties of a morphism of algebraic stacks can be checked after an
   etale surjective base change” — eight scheme/ring base-change hits, no exact match.
5. For the new notion, LeanSearch: “A morphism of algebraic stacks is a universal
   homeomorphism if every algebraic stack base change is a homeomorphism on points” —
   eight scheme injectivity/closedness/isomorphism hits, no stack predicate.
6. For the new notion, LeanFinder: “Universal homeomorphism for general algebraic
   stacks on the topology defined by smooth atlases” — eight scheme/manifold hits;
   none is this predicate. Mathlib CategoryTheory grep
   `UniversalHomeomorph|universal.homeomorph` — zero hits.
7. Local rg of WeilConjectures and Sheaf for the item id and for universal-homeomorphism
   stack predicates found no exact declaration. Existing Sheaf coarse-space modules
   have inline base-change homeomorphism clauses, which use the same point map and
   topology; they do not define the general predicate. WeilConjectures has scheme
   universal-homeomorphism results. No duplicate definition was introduced.
8. DAG search of definition statements found only the SCHEME definition
   `def-weil-universal-homeomorphism`. Blueprint search “stack homeomorphism” returned
   four unrelated scheme/site results; “universal homeomorphism stack” three such
   results. The theorem nodes with that phrase give consequences, not the definition.
   `blueprint_refs.py ancestor` reports the inherited ancestor as None; the new
   definition preserves the item's existing via chain with the item prepended.

Sources opened: stacks-morphisms.tex, definition-universal-homeomorphism (0CI7),
lemma-check-separated-covering (06TZ), lemma-check-quasi-compact-covering (0DTL),
lemma-check-universal-homeomorphism-covering (0DTQ), and the three base-change lemmas
050F, 050V and 0CI8. Their single-cover statements give the stated small-family
version by the disjoint union and the finite-chart refinement recorded in the DAG.
No statement dispute or source correction was needed.

Validation: both delivered modules compiled individually through scompile.py,
against the live server library, with no errors or warnings. The module header,
public visibility, explicit universes and 100-character line bound were checked.

## New nodes

`def-sfb-stack-universal-homeomorphism` records Stacks Tag 0CI7 exactly: all
algebraic-stack base changes induce homeomorphisms on the existing atlas point
spaces. Its module is `Sheaf.AlgebraicGeometry.StackUniversalHomeomorphism` and its
sole declaration is `CategoryTheory.IsUniversalHomeomorphismAlgebraicModuliMap`.
The predicate has real data: a dependent universal quantification and `IsHomeomorph`
of the canonical projection map, with no chosen map or chosen homeomorphism.
The searches above and verbatim msearch records in the node establish that neither
Mathlib nor the project already defines this stack predicate. The existing scheme
universal-homeomorphism node has different objects and cannot be applied to stacks.
The item cites the new definition directly. No dependency module was needed.

## Second reading by Q47

I reread the node, the two complete modules, and the expanded signatures after the
clean compile. This is a worker self-check: the dispatcher explicitly prohibits
starting another agent; the maintainer's independent delivery review remains pending.
The three `↔ ∀ i` clauses render three SEPARATE properties, not only their conjunction.
The QS clause uses the diagonal's qc AND qs definition. The third property applies
`IsHomeomorph` to the actual `moduliPointMap`, using the smooth-atlas topology, after
all algebraic-stack tests in the explicit universe bound. The original and local
maps use the same extra test bounds. Every cover map retains the representable-etale
scheme-test definition; hsurj retains the field extension, choice of index, actual
lift and 2-isomorphism. No assumption that each cover member is surjective was added.
The independent base-change theorem has only algebraicity of its three endpoints
and the displayed morphisms, so that assertion does not silently depend on a DM
cover hypothesis. No finite-type, finite-inertia, nonempty-index or representability
hypothesis on f appears. The new definition has no proof/data hole. I found no
mismatch requiring a change to the node's statement.
