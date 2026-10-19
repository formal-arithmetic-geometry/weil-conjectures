## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedPointSupportDetection` states
`AlgebraicGeometry.Etale.isZero_iff_cohomology_of_support_closedPoints`, with its entire proof
left as `sorry`. There are no new definitions, dependency repairs, or statement corrections.
Its declaration docstring gives all seven steps of the node's general, unbounded proof.

The source was checked at https://stacks.math.columbia.edu/tag/0F1G (Lemma 59.97.4).
It agrees with the node, including its unbounded scope and abelian coefficients. The local
blueprint and Stacks TeX files named by the node are absent from this checkout, so the source
was read on the Stacks website. No mathematical fault or disputed statement was found.

Hypotheses and conclusion, clause by clause:

- A separably closed field `K` is `{K : Type u} [Field K] [IsSepClosed K]`. The last class
  is Mathlib's existing separably closed field notion; it does not require perfectness or
  algebraic closedness.
- A scheme `X` over `K` is `(X : Scheme.{u}) [X.Over (Spec (.of K))]`. Its structure morphism
  is the canonical `X ↘ Spec (.of K)` supplied by this `Over` structure.
- Finite type of that structure morphism is expressed by the two standard classes
  `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and
  `[QuasiCompact (X ↘ Spec (.of K))]`. There is no separatedness assumption.
- The arbitrary object of `D(X_Et)` is
  `(Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))`.
  This is the unbounded derived category of abelian sheaves, as specified by
  `def-weil-pbc-derived-categories`. It is not a bounded-below or module coefficient variant.
- The stalk-support condition is
  `(hQ : X.etaleComplexSupport Q ⊆ closedPoints X)`. The recorded support definition is the
  union over all integer degrees of the supports of the cohomology sheaves; membership in a
  sheaf's support means that some geometric stalk over the point is nonzero. Geometric
  stalks are exact, so their complexes have cohomology equal to the stalks of the cohomology
  sheaves. A derived stalk is zero exactly when all those cohomology groups are zero.
  Consequently the inclusion is exactly the assertion that a nonzero derived stalk lies
  over a closed point. It neither asks for finite support nor a closed support subset.
  The point notion is the existing `closedPoints X`, meaning `IsClosed ({x} : Set X)`.
- `Q = 0` is categorical vanishing, `IsZero Q`, rather than equality to a particular choice
  of zero object.
- The equivalence is `↔`, including both directions. The second side is
  `∀ i : ℤ, IsZero ((cohomology AddCommGrpCat.{u + 1} X i).obj Q)`.
  Here the existing `cohomology` is explicitly the composite of unbounded
  `rightDerivedGlobalSections` and `DerivedCategory.homologyFunctor` in degree `i`.
  Thus this is vanishing of global hypercohomology in every integer degree.

Dependency declarations read and reused:

- `def-kun-separably-closed`: `Mathlib.FieldTheory.IsSepClosed`, `IsSepClosed`.
- `def-kun-support`: `Sheaf.AlgebraicGeometry.EtaleSupport`,
  `AlgebraicGeometry.Scheme.etaleComplexSupport` and `etaleSheafSupport`; the published
  current source was also retrieved with `scompile.py --source` and agrees with the local
  file. The support's geometric stalk is `Scheme.pointSmallEtale` followed by
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber`.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, the
  recorded `DerivedCategory` and `DerivedCategory.homologyFunctor` encoding for abelian
  sheaves. The node's separate torsion predicate is not imposed.
- `def-weil-pbc-geometric-stalks`: `Mathlib.CategoryTheory.Sites.Point.Basic`,
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber`, with
  `AlgebraicGeometry.Scheme.pointSmallEtale` in `Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
  Their full definitions identify the stalk as the colimit over pointed etale neighborhoods.
- `def-kun-rgamma-unbounded`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` and `AlgebraicGeometry.Etale.cohomology`.
  Read the full signatures and docstrings; they apply directly to `AddCommGrpCat.{u + 1}`.

The modules of the currently stated proof dependencies are ordinary, non-public imports.
These include `GeometricStalkCohomology`, `EtaleLfpAndFiniteType`, `GeometricStalkAsPullback`,
`ClosedPointField`, `EtaleGloballyGenerated`, the upstream inverse-image/restriction modules, upstream
`DerivedCategory.isZero_iff`, and the Mathlib affine-basis, etale, residue-extension, and
quasi-compactness inputs. The unstated proof dependencies `lem-kun-0bkz`,
`lem-kun-0f1f-vanish` and `lem-kun-0f1f-gen` are described in
full in the proof plan but are not needed to type this theorem and have no importable module
in their records. No import cycle is introduced.

Edge cases checked mathematically: the empty scheme is allowed; then all sheaves and derived
objects vanish. The zero object has empty support. All positive, zero and negative degrees
are quantified, including complexes unbounded in both directions. An infinite union of closed
points is allowed, since only subset inclusion is required. Positive characteristic and an
imperfect separably closed base field are allowed. No torsion, constructibility, support
finiteness, or boundedness hypothesis appears. All variables and the universe `u` are explicitly
bound, with the standard `u + 1` coefficient universe of the existing etale-sheaf interface.

Searches made before writing (the launcher's msearch log records the remote search results):

- `msearch.py ... leansearch`: "Unbounded derived etale cohomology detects zero objects
  supported on closed points over a separably closed field". Service unavailable, Internal
  Server Error; this is recorded as unavailable, not a negative result.
- `msearch.py ... leanfinder`: "Derived global sections detect vanishing of unbounded etale
  abelian sheaf complexes supported at closed points over a separably closed field".
  Eight hits concern the etale locus, formal etaleness and sections of inverse limits;
  none states the desired detection theorem.
- `msearch.py ... loogle`: `CategoryTheory.Limits.IsZero, DerivedCategory`. Six hits are
  degree-wise vanishing for bounded-above/below objects and the descriptions of the
  standard t-structure. None detects vanishing via global sections on closed-point support.
- `msearch.py ... grep`: `closed.point|support.*closed|conservative`, under
  `Mathlib/AlgebraicGeometry`. Twenty-four hits concern closed points, ideal-sheaf support,
  and conservative families of geometric points; no match.
- Direct `rg` of `WeilConjectures` and `lean/Sheaf` for `lem-kun-0f1g`, `0F1G`,
  `etaleComplexSupport`, `isZero.*cohomology`, and `cohomology.*isZero`: support definitions
  and unrelated vanishing statements only. The blueprint id has no upstream match, also
  checked using the requested `grep -rn` search.
- Further direct `rg` for `vanishing.closed.points|supported.*closed|support.*closedPoints`
  and inspection of upstream `AlgebraicGeometry/Sites/FiniteSupport.lean`: the latter treats
  sheaves supported on finitely many points and positive-degree acyclicity, not arbitrary
  supported unbounded derived objects. No duplicate theorem was found.
- Checked the proposed declaration name against the upstream name index, source library,
  and side library; no match.

Validation: `scompile.py Q07 lem-kun-0f1g` compiled the delivered file as a single file through
its local side-project overlay, with no errors or warnings. No global build was run.

## Second reading by Q07

I independently read the node copy, the full proposed Lean module, all five statement
prerequisite nodes and the signatures and definitions they record. I also reread Stacks
`etale-cohomology.tex`, `lemma-vanishing-closed-points` (Tag 0F1G), obtained from the
Stacks repository, and the start of its Kunneth section. The section imposes no additional
standing hypothesis. The source's general-case paragraph establishes the unbounded
statement; its preceding bounded-below argument is not a restriction on the lemma.
The node and source agree. No statement correction, new node, or dependency repair is
needed.

The following is my object/hypothesis/conclusion checklist, made from the node before
checking the Lean. Every row passes.

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| A field K | `{K : Type u} [Field K]` | Same arbitrary field, not a ring or prescribed characteristic. |
| K is separably closed | `[IsSepClosed K]` | Mathlib's separable-polynomial splitting class, the equivalent field notion recorded by `def-kun-separably-closed`; does not require algebraic closedness. |
| A scheme X over K | `(X : Scheme.{u}) [X.Over (Spec (.of K))]` | The structure morphism is `X ↘ Spec (.of K)`, using the project's existing over-base encoding. |
| X is finite type over K | `[LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]` | Exactly Mathlib's two-part finite-type definition. No separatedness, smoothness or extra finiteness hypothesis. |
| An arbitrary Q in D(X_et) | `(Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))` | Unbounded derived category of abelian sheaves, explicitly the coefficient-free case of `def-weil-pbc-derived-categories`. |
| Q has nonzero geometric stalks only over closed points | `(hQ : X.etaleComplexSupport Q ⊆ closedPoints X)` | The recorded support is the union over every integer degree of cohomology-sheaf supports. Each support uses existence of a nonzero geometric stalk. Exactness of stalks makes this equivalent to the node's condition on derived stalks. |
| Q vanishes | `IsZero Q` | Categorical zero, equivalent to the mathematical Q = 0. |
| Every global hypercohomology group vanishes | `∀ i : ℤ, IsZero ((cohomology AddCommGrpCat.{u + 1} X i).obj Q)` | All integer degrees, and global hypercohomology rather than cohomology sheaves. |
| Both implications | `IsZero Q ↔ ∀ i : ℤ, ...` | Exact equivalence, after the support hypothesis, with the original quantifier order. |

For the support row I opened `EtaleSupport.lean`: `etaleComplexSupport` really is the
union of `DerivedCategory.homologyFunctor` supports, and `etaleSheafSupport` really
uses `(Scheme.pointSmallEtale s).sheafFiber`, with `s default = x`. I opened Mathlib's
`EtalePoint.lean` and `Sites/Point/Basic.lean`: the fiber consists of lifts of the
geometric point to etale neighborhoods, and `presheafFiber` takes the colimit over the
opposite category of elements. `sheafFiber` restricts this functor to sheaves; it has
finite-limit preservation and colimit preservation. Thus the support is not an unrelated
topological support or a finite-support condition. Algebraically closed fields in this
support definition provide the usual geometric points; allowing larger geometric fields
does not change stalk vanishing. Algebraic closures of residue fields exist in the
scheme's universe, so the support condition is not vacuous.

For the cohomology row I opened upstream `SixFunctors/Etale/Derived/LowerShriek.lean`:
`rightDerivedGlobalSections` is `R(Sheaf.Γ X.smallEtaleTopology A)`, and `cohomology A X i`
is that functor followed by `DerivedCategory.homologyFunctor A i`. Its ambient
Grothendieck abelian and sheafification instances specialize to `AddCommGrpCat.{u+1}`;
they are provided instances, not extra hypotheses on X or Q. I opened
`DerivedCategories.lean` as well: its documentation explicitly records this abelian
unbounded category; its separate torsion predicate is not part of the present statement.
The existing `IsSepClosed` and `closedPoints` definitions were checked in Mathlib.

Edge cases: the empty scheme is admitted (no nonemptiness binder); both sides then
express vanishing. The zero object has empty support. Arbitrary, including infinite,
sets of closed support points are admitted. The union and the conclusion both cover
all of Z, including degree zero and negative degrees, with no boundedness requirement.
There is no integer n, index-family nonemptiness, torsion, constructibility, perfectness
or characteristic restriction. A separably closed imperfect field in positive
characteristic is admitted. The explicitly declared universe u and `u+1` coefficient
universe agree with the existing small-etale/derived interfaces; no extra equality
between independent site universes is imposed. Every binder and universe is bound.

Independent duplicate searches used different descriptions from the author's searches:

- LeanFinder: `Hypercohomology of a complex of abelian etale sheaves with support in closed
  points is conservative`. Eight hits, all about one-hypercover preservation and the
  sheaf-cohomology presheaf/functor (`Sheaf.H`, `Sheaf.cohomologyPresheaf` and related
  declarations). None is this closed-point detection theorem.
- Loogle: `CategoryTheory.Limits.IsZero, AlgebraicGeometry.Etale.cohomology`. The service
  does not index the project cohomology identifier and rejected that identifier. This
  is an unavailable query, not evidence of absence.
- LeanSearch: `A complex of etale abelian sheaves on a finite type scheme over a separably
  closed field with closed point support vanishes if its derived global sections vanish`.
  Service returned Internal Server Error; recorded as unavailable, not a negative result.
- Direct `rg` of Mathlib, upstream `WeilConjectures` and project `lean/Sheaf` for
  `hypercohomology`, `vanishing.closed`, `closed.*support`, `support.*closed`,
  `conservative`, and then `closed.point.*(support|cohomology)|support.*closed.point|0F1G|vanishing-closed-points`.
  Inspected upstream `AlgebraicGeometry/Sites/FiniteSupport.lean` in full: its relevant
  results are positive-degree acyclicity of sheaves with finite support and comparisons
  outside finite sets, not arbitrary unbounded-object detection. Opened the project's
  `ClosedPointSheafApproximation.lean`, which is filtered-colimit finite-support
  approximation of sheaves, not this theorem. Other hits concern Weil-sheaf supports,
  coherent ideal supports, and unrelated base-change/cohomology statements. No match.
- Checked the theorem name, blueprint id and `0F1G` against upstream Lean, the project's
  Lean files and `dag/lean_names_upstream.json`; no duplicate declaration.

Mismatch found and repaired: the currently recorded proof dependency
`def-kun-global-generated` now has module `Sheaf.AlgebraicGeometry.EtaleGloballyGenerated`.
The worker file omitted its non-public proof import and the worker report incorrectly
listed it as unstated. I opened that module, checked the abelian evaluation construction
and epimorphism predicate, added its ordinary `import`, and corrected that report list.
No signature, definition, hypothesis, conclusion or DAG field was changed. The remaining
three unstated proof dependencies still have no recorded module and need no import.
All other recorded proof modules are imported. The seven numbered docstring steps match
the seven node proof steps, including restriction to quasi-compact etale objects,
residue-field/closed-point checks, unbounded acyclicity, global generation and the
cohomology-sheaf zero criterion. The only theorem proof is `by sorry`; there are no
local/private definitions or additional constructions, and no hollow definition.

Validation: compared `lean.statement` programmatically with the file's entire signature;
they are verbatim equal. Compiled the final file using the required `scompile.py` wrapper
and checked that no error or warning was left. Delivery preflight is checked with
`deliver2.py --no-push` before delivery.
