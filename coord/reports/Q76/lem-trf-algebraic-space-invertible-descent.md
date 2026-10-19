## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent` states
`AlgebraicGeometry.AlgebraicSpace.exists_lineModule_of_etale_descent`. Its only theorem
has proof `by sorry`; no mathematical result is proved in this stage-2 delivery.
All helper definitions have explicit data. The statement of the item is unchanged.

The hypotheses and conclusions correspond to the node as follows:

- The base scheme is `{S : Scheme.{u}}`; the algebraic space is `F : AlgebraicSpace S`.
  This is the recorded fppf-sheaf definition with representable diagonal and an étale
  surjective atlas, not a scheme standing in for the algebraic space.
- The family is `V : I → F.EtaleSite`, with `I : Type u`. An object of this recorded
  small étale site includes its scheme over S and its representable étale map to F.
  In particular, being étale is already present in `V`, rather than omitted.
- `hjoint` says that for every scheme test `T`, every map `h_T → F`, and every point
  x of T, some represented base change of a family member has a point above x.
  The `IsPullback` square makes that scheme precisely `T ×_F V_i`; thus this is
  joint surjectivity after arbitrary scheme base change. The base changes exist
  from the already bundled representable étaleness. Individual q_i are not
  required to be surjective.
- `R`, `p₁`, `p₂`, and `hR` specify schemes over S and their representing pullback
  squares of presheaves. They encode the displayed `R_ij = V_i ×_F V_j` and its
  projections. They are choices of representations of that canonical fibre
  product, not arbitrary overlaps or an additional geometric condition.
- `M i` is an ordinary `Scheme.Modules` object on the underlying scheme of V_i.
  `hM i : Scheme.Modules.IsInvertible (M i)` is exactly the recorded invertibility
  predicate. The given ordinary modules are retained as inputs.
- `D.transition i j` is the specified ordinary isomorphism
  `(tensorPullback p₂).obj (M j) ≅ (tensorPullback p₁).obj (M i)` on R_ij.
  Here `tensorPullback` is the recorded tensor-formula pullback, not Mathlib's
  abstract scheme module pullback.
- `D.diagonal` restricts the self-overlap transition along every diagonal lift
  `d : V_i → R_ii`, with both projection composites equal to identity. Its
  resulting endomorphism of the identity pullback of M_i is identity. This
  imposes no identity on all of R_ii. The displayed diagonal lifts exist and
  are unique from `hR` and Yoneda full faithfulness.
- `D.cocycle` is `α_ik = α_jk ≪≫ α_ij` after pullback. It is evaluated on every
  scheme T over S mapping to the three pair overlaps, with the six projection
  equations specifying common maps to V_i, V_j, and V_k. These are precisely
  scheme-valued tests of the triple product. Equality there is equivalent to
  this test-scheme form: one direction pulls back the triple-product equality;
  the converse tests at the representing triple-product scheme itself.
  `atlasTransitionOn` and `atlasTransitionOver` use the canonical
  `tensorSectionsComp`, its inverse, functorial pullback of the given transition,
  and equality transport along the supplied leg equations. They retain the
  composition identifications instead of assuming strict tensor-pullback equality.
- The first conclusion supplies `N : F.Modules` with `F.IsLineModule N` and
  `e i : OrdinaryEtaleIdentification F (V i) N (M i)`. The latter is the full
  local isomorphism, in the direction from the ordinary associated module to
  the restriction of N. For each object `p : T → V_i` of the localized site,
  its `app` is a `Γ(T, O_T)`-linear equivalence
  `Γ(T, p^* M_i) ≃ₗ N(T)`. Its `naturality` is compatibility with the existing
  canonical tensor-pullback restrictions. This is the sectionwise form of the
  ordinary/small-étale interpretation named in the statement; it is not an
  arbitrary map or a choice of a global extension of each M_i.
- Every map between objects étale over F is étale on schemes, and every scheme
  étale over V_i gives an object étale over F by composition. Consequently the
  slice objects used in `OrdinaryEtaleIdentification` are exactly the tests
  of the small étale site of V_i. Its tensor-section formula is the one in the
  recorded `def-sc-etale-qcoherent-module` and its restriction formula is the
  one in `lem-sc-etale-qcoherent-presheaf-functorial`. Linearity and naturality
  therefore encode an isomorphism of module sheaves, including its scalar action.
- The equation following `e` tests any overlap against a small-étale test object T
  with maps a and b to V_i and V_j and a map r to the represented R_ij. It says
  `e_i(α_ij(s)) = e_j(s)`, using canonical ordinary pullback transports. This is
  exactly the requirement that the identifications induce the specified α_ij.
  It applies also when i=j and when the two maps into V_i differ.
- The second conjunct quantifies over **any** line modules P,Q on F. A local map
  `g i` is a module-sheaf morphism between their restrictions by the recorded
  `F.etalePullback (V i)`. The compatibility premise equates its linear components
  on every test object with maps to both V_i and V_j. By representability this is
  precisely agreement on R_ij, with no chosen comparison between iterated slice
  sites. Under the ordinary/small-étale interpretation these are the ordinary
  module maps in the node. `∃! f`, with the equations
  `(F.etalePullback (V i)).map f = g i`, expresses surjectivity and injectivity of
  the canonical restriction map to compatible families.

Dependencies and source declarations read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `IsEtale`, `IsRepresentableWith`, `Modules`, `etalePullback`,
  and `IsLineModule`; their full definitions and docstrings were read.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, with its Zariski local-structure-sheaf predicate.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `Scheme.Modules.tensorPullback`. Its current source was read with
  `scompile.py --source`; it constructs inverse image followed by change of rings.
- `Sheaf.AlgebraicGeometry.EtaleTensorSections`:
  `tensorSectionsComp` and `tensorSectionsUnit`, including their canonical
  adjunction normalization and the existing restriction/presheaf signatures.
  The item's statement dependencies gain the two already recorded nodes
  `def-pc-module-pullback` and `lem-sc-etale-qcoherent-presheaf-functorial` for these
  public interfaces. No existing dependency node is edited.
- Proof imports include `Mathlib.CategoryTheory.Sites.Limits`
  (`Sheaf.createsLimitsOfShape`, the recorded Mathlib leaf),
  `Sheaf.CategoryTheory.SiteCoveringAxioms` (`Precoverage.IsSiteForCoverings`) and
  `Sheaf.CategoryTheory.RingedSiteModules` (`ringedSiteModules`). The size
  convention has no Lean module. The proof dependency
  `lem-trf-scheme-etale-invertible-comparison` currently has no recorded Lean
  declaration, so there is no module for it to import. The present statement
  requires no inverse comparison functor: the intended local isomorphisms are
  expressed directly by their given tensor-section formula and naturality.

The source was opened locally at Spaces Descent, proposition-fpqc-descent-quasi-coherent
(Tag 04W8), lemma-finite-locally-free-descends (Tag 060X); Descent,
lemma-equivalence-quasi-coherent-properties (Tag 05VG); and Sites,
lemma-glue-sheaves and lemma-glue-maps (Tags 04TR and 04TQ). The eight proof steps
of the DAG are included in the theorem docstring.

Edge cases checked: I may be empty; no `Nonempty I` or chosen index is imposed.
In that case `hjoint` forces all scheme base changes of F to have no points,
so the empty-space case and its unique module maps are retained. Empty schemes
and zero global-section rings cause no restriction on the linear equivalences.
Repeated indices are included in the triple cocycle. In particular, R_ii is not
identified with V_i, nor is its entire transition required to be identity.
Disconnected schemes, non-quasi-compact atlases, infinite covers, arbitrary
characteristic and arbitrary base schemes are all allowed. Scheme tests and
local module coefficients live in the same explicit universe u, rather than in
an unrelated potentially smaller universe. All variables and universes are bound.

Searches actually run:

- `msearch.py leanfinder`, query "Invertible modules on algebraic spaces descend
  along jointly surjective etale scheme maps with cocycles and morphisms":
  8 results, including morphism-property descent and scheme étale definitions;
  none states algebraic-space invertible-module descent.
- `msearch.py loogle`, query `"descent", "Module"`: 0 results.
- `msearch.py grep`, query `invertible.*descent|descent.*invertible`, subdirectory
  `AlgebraicGeometry`: 0 results.
- `msearch.py leansearch`, query "A natural sectionwise linear isomorphism
  identifies a line module on an algebraic space with the etale tensor sections
  of an ordinary invertible scheme module": 8 results, including generic linear
  equivalences and scheme-module evaluation; no exact algebraic-space interface.
- `rg` in Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the descent concepts and all six introduced
  declaration names found no exact match or collision. Searching the item id
  upstream found no declaration. Upstream Picard/TwistedDescent's `DescentCocycle`
  was read: it is a scalar-function cocycle over a scheme target, not these
  ordinary-module transition isomorphisms over an algebraic space.
- `tools/blueprint_refs.py search 'invertible descent'`: 0 blueprint-node matches.
  The existing DAG item and scheme-comparison node were read and reused as the
  mathematical statement and proof input, respectively. No duplicate node was added.

No statement correction, disputed statement, missing-definition data, arbitrary
canonical map, stronger geometric assumption or new axiom is introduced. The helpers
only spell out the node's local identifications and its given descent datum, as
permitted by the launcher's authorization for helpers in the owning node's module.

Validation: `scompile.py Q76 lem-trf-algebraic-space-invertible-descent <module>`
compiled the full statement without errors or warnings. The final path and direct
proof-import list are checked again by the required delivery dry run.

## Second reading by Q76

Author's explicit self-check, under the dispatcher instruction not to start other
agents; this is not claimed as an independent review. The maintainer's independent
reader remains the independent review specified by this task. I reread the node,
its source places, and the completed file and matched each hypothesis and conclusion
above. During drafting I corrected the order of the cocycle composite, kept the
ordinary modules instead of assumed global extensions, added actual represented
scheme overlaps and base-change joint surjectivity, and replaced a vacuous identity
map claim by unique gluing of compatible local morphisms. I checked that the
identifications preserve scalars and commute with every localized restriction;
that the transition compatibility retains the supplied α_ij; and that diagonal
normalization only concerns the diagonal. The finalized theorem matches the node;
all six helper/main declarations are listed in the lean record and every postponed
proof is the one named theorem carrying this item's blueprint id.
