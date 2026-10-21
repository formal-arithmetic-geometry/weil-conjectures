## Worker report

The item is stated in `Sheaf.Paper.CompletionTriangleComparison`, declaration
`AlgebraicGeometry.ProEtale.CompletionTriangle.completion_triangle_comparison`.
Its statement and all dependency lists are unchanged. There are no new DAG nodes.
The only dependency repair changes the `lean` record of
`lem-pe-principal-reduction-cone-calculus`; see below.

I read the item and the full statements and Lean records of its four statement
dependencies, the signatures/docstrings in PrincipalReductionConeCalculus,
RoosConeCalculus, DerivedCompletion, and Mathlib's DerivedCategory.Basic, and the
Cones paragraph and shifts sentence of the main-20261015 first-reduction proof.
The example CompactObject module has been withdrawn and contains no declarations.
The current principal-calculus module supplied the header and namespace convention.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite E/Q_ell | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Its uniformizer | The dependency structure's `d` is pinned by the first clause of `IsCanonical` to `Padic.coefficientExtensionUniformizer l E`, pointwise on every profinite test object. |
| Any scheme X | `(X : Scheme.{u})`, with no finiteness, separation or nonemptiness condition. |
| R is the pulled-back continuous integral ring | The recorded `AdicCompletion.Modules l E X`, namely internal modules over `AdicCompletion.ring l E X`, is used throughout. This is not a constant coefficient sheaf or the coefficient ring before pullback. |
| Unbounded complexes and localization Q | `CochainComplex (Modules l E X) ℤ`, `DerivedCategory`, and `DerivedCategory.Q`. No boundedness or flatness condition is imposed on M or K. |
| Strict D_n, transitions and j_n | The existential `data : PrincipalReductionConeData l E X` has `data.IsCanonical l E X`; its `D`, `T` and `j` are the specified strict fields. These equations pin the cone object, diagonal maps, transition `(x,pi y)` and unit `(m,0)`. Positive n is indexed by n-1, consistently with DerivedCompletion. |
| Apply H | `tower` assembles that existing tower degreewise; `complexCompletion = tower ⋙ CategoryTheory.roosF`. No second Roos construction is introduced. |
| Additive endofunctor F and descent formula | Existential `F`, conjunct `F.Additive`, and natural isomorphism `κ : Q ⋙ F ≅ complexCompletion ⋙ Q`. This is the formula F(QM)=QH(D(M)) with the localization comparison retained. |
| Explicit canonical c_M | Existential natural chain map `a`. Its entire component in the existing `roosχ` coordinates equals `biprod.lift 0 ((Pi.lift (fun n ↦ (data.j n).app M)).f (p+1))`. These coordinates are shifted product first, unshifted product second, so this is precisely `(((m,0))_n,0)` in the node's reordered coordinates. `p+1` covers every integer degree. |
| c descends naturally | `c : 𝟭 _ ⟶ F`, and `c.app (Q.obj M) ≫ κ.hom.app M = Q.map (a.app M)`. The same κ occurs for all objects and arrows. |
| Isomorphic to the specified completion, retaining its map | For every K, every K-flat P and every `e : Q.obj P ≅ K`, there is `ψ : F.obj K ≅ Q.obj (AdicCompletion.roos l E X P)` satisfying `c.app K ≫ ψ.hom = completionMap l E X K P e`. Thus this is an augmented comparison to exactly the dependency's chosen construction, not merely some triangulated homotopy-limit object. K-flat P computes derived tensor reductions; this is a universally quantified computation rule, not an assumption on K. |
| Completeness iff c_K invertible | `∀ K, IsDerivedComplete l E X K ↔ IsIso (c.app K)`. |
| Coherent natural shifts for all integers | Existential `sF : F.CommShift ℤ`. By Mathlib's structure this supplies natural isomorphisms with zero/addition coherence, not independently chosen objectwise comparisons. |
| Shift compatibility of c | `c.app (K⟦r⟧) ≫ (Functor.commShiftIso (self := sF) F r).hom.app K = (c.app K)⟦r⟧'`, for every K and integer r. |
| F(T) distinguished with specified last arrow | The final universal clause takes any distinguished T and asserts distinguishedness of `Triangle.mk (F.map T.mor₁) (F.map T.mor₂) (F.map T.mor₃ ≫ sigma)`. This has the node's precise boundary, including sigma at shift one. |
| Three c components form a morphism of triangles | The same clause supplies `γ : T ⟶ F(T)` with all three component equations. `γ.comm₃` is the last square with `(c.app T.obj₁)⟦1⟧'`; triangle morphisms enforce it as well as the first two squares. |

Dependency declarations used:

- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`:
  `AdicCompletion.Modules`, `AdicCompletion.roos`, `AdicCompletion.completionMap`,
  `IsDerivedComplete`; read also the derivedReduction/restrict, canonical tower and
  `roos_isDerivedLimit` declarations and their augmentation normalization.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `DerivedCategory.Q`, the coherent shifts and triangulated
  structures, and `DerivedCategory.mem_distTriang_iff`.
- `Sheaf.Paper.PrincipalReductionConeCalculus`:
  `PrincipalReduction.scalar`, `PrincipalReduction.reductionFunctor`,
  `principalConeCoordinates`, `principalConeInterchange`, and the complete
  signature/docstring of `principal_reduction_cone_calculus`. The repaired
  `Sheaf.Paper.PrincipalReductionConeCalculus` retains those declarations verbatim and packages
  exactly that signature as `PrincipalReductionConeData` and
  `principalReductionConeData`, together with `PrincipalReductionConeData.IsCanonical`.
- `Sheaf.Algebra.Homology.RoosConeCalculus`:
  read `roos_cone_calculus`, CoordinateCalculus, DerivedRoos and all cone/shift/
  augmentation predicates. Its `CategoryTheory.roosF`/`roosχ` construction from
  `Sheaf.CategoryTheory.StrictRoosModel` is used directly on the internal module
  category. Its ringed-site theorem is a proof input, to be transported through
  the cited internal/section-module comparison; no smaller or different
  coefficient category occurs in the item's signature.

All recorded, stated proof-dependency modules are imported. For the Mathlib leaf
`lem-weil-pbc-localization-universal-property`, I read Localization.Predicate
lines 278-357: lift/fac, liftNatTrans, natTrans_ext and fully faithful whiskering.
Its three clauses provide descent of F, c, and the comparison identities.
The item's theorem docstring records all nine proof steps and all their cited
inputs, including the augmented K-flat comparison and the boundary sign.

Edge cases checked before drafting: zero complex; empty scheme; first positive
level n=1 (represented by index 0); arbitrary positive/negative/zero integer
shifts; the identity chain map and its contractible cone; unbounded complexes;
and an arbitrary K-flat representative rather than only a termwise-flat one.
All use the same definitions and formulas. No nonzero, nonempty, bounded,
Noetherian, constructibility, or fixed-cohomological-degree assumption was added.
The valuation uniformizer is the dependency's recorded canonical choice, as in
all the coefficient nodes.

Searches actually run with msearch.py:

- LeanFinder: "Derived completion is an additive triangulated endofunctor with a
  canonical natural augmentation from the identity compatible with shifts".
  Eight results included exact-functor mapDerivedCategory instances and generic
  triangulated localization lemmas; none constructs this augmented completion.
- Loogle: `"DerivedCategory", "completion"`: zero hits.
- Mathlib grep: `completion.*[Tt]riang|[Cc]ompletion[Ff]unctor|completion_triangle`:
  six hits, all metric/uniform-space completion, no derived-completion match.
- LeanSearch: "Derived completion is a triangulated endofunctor and its unit is
  compatible with all shifts": eight results, including generic
  Functor.IsTriangulated and triangulated adjunctions; no completion construction.
- Direct rg of WeilConjectures, Sheaf and dag/lean_names_upstream.json for the
  node id, completion-triangle wording, completionFunctor, and the proposed
  declaration names. Formal-scheme completion, general ideal/Koszul completion,
  completed-adic levelwise-isomorphism-cones and the supplied-datum completed
  Koszul Roos triangle are different statements. I opened their signatures;
  none supplies this unrestricted internal-coefficient strict-cone/Roos descent
  and its augmented comparison. No proposed declaration name was already used.

No statement dispute or mathematical correction is needed.

## Dependency modules

`lem-pe-principal-reduction-cone-calculus` retains the module
`Sheaf.Paper.PrincipalReductionConeCalculus`, its primary declaration
`principal_reduction_cone_calculus`, and all five landed declarations. Three
helpers are appended to the same live module; its Lean record lists all eight
declarations. The prior record's mathematical
content was complete, but its nested existential interface was not consumable
within the mandatory 60-second limit. Direct `.choose_spec` extraction timed
out both in the whole consumer and in a diagnostic file containing only three
small definitions. Server confirmation reproduced it. The profiler showed
expansion of the full dependent existential into many generated `_proof_`
declarations during kernel checking of the first projection.

The appended interface states the same simultaneous result as
`∃ data : PrincipalReductionConeData l E X, data.IsCanonical l E X`. The structure has the strict data d, D, hobj, χ, T and j; `IsCanonical`
contains the pointwise uniformizer equation, the simultaneous existential
comparison data sD, sF, κ and Φ, and every original conjunct,
verbatim modulo indentation and record-field qualification, with the conjunction
inside the already-present profinite scalar-test binders. This has exactly the
same meaning: specialize at the one-point profinite set, its zero section and
its point to recover every independent conjunct. Conversely the original
conjunction gives the displayed universal one. This scope arrangement avoids
Lean repeatedly extracting closed proof terms from the large dependent type;
it adds no hypothesis and drops no case. In particular it retains the natural derived
reduction interpretation, quasi-isomorphism preservation, exactness,
canonical coordinates, diagonal maps, transition and unit formulas,
all cone/shift compatibility equations and the Q/shift comparison.
It reuses the published scalar, cone coordinates, interchange and
reductionFunctor rather than redefining any of them.

The theorem supplies this fully characterized structure directly, without a
choice-based helper definition. The consumed d/D/T/j fields are pinned by the pointwise scalar,
canonical cone-coordinate and diagonal/transition/unit equations; hobj and
other proof fields are irrelevant. Any family satisfying these equations is the same
specified strict construction up to the equalities relevant downstream.
Every comparison datum and normalization remains available
in the `IsCanonical` predicate. Its additional existence theorem is sorry with the dependency's complete
ten-step proof plan in its docstring; the original existence theorem and its
docstring remain verbatim in the owning module. The dependency node is changed only in
`lean`, with a note documenting this interface repair. The main consumer is
compiled against this repaired module in the same packet.

The main theorem quantifies existentially over this characterized calculus before
asserting its descent and completion properties. This supplies exactly the
canonical family whose existence the dependency asserts; it is not an extra
hypothesis on E, X or K, nor an arbitrary tower. `tower data` and
`complexCompletion data` have direct structural data. No definition selects
unspecified data from an existence theorem. This formulation also avoids the
costly proof abstraction of repeated choice projections.

Validation: both files are checked together by scompile.py/the delivery wrapper,
in dependency order, with the unchanged 60-second per-file limit.

The repaired same-module superset and its consumer both passed server
confirmation through `scompile.py`: PrincipalReductionConeCalculus took 35.0 s
and CompletionTriangleComparison took 48.7 s, with nice 19, two threads and the
unchanged 60-second limit. There were no Lean errors or warnings. Earlier runs
timed out; the successful run used the identical sources and default settings.


## Return repair (L, immutable head 2f89f3c9436b)

H13/H4 is repaired using the requested same-module superset. The published server
source of `Sheaf.Paper.PrincipalReductionConeCalculus` was read with
`scompile.py --source` and matched the current read clone (apart from the source
wrapper's extra final newline). The delivered module begins with that entire
source byte for byte, including all imports, the five original declarations,
`principal_reduction_cone_calculus` and its proof docstring. It then appends
`PrincipalReductionConeData`, `PrincipalReductionConeData.IsCanonical` and
`principalReductionConeData` in the original namespace. Its DAG record keeps the
original primary theorem/module/file and lists all five old plus all three new
names. Only the `lean` field of this dependency node changes.

The separate `PrincipalReductionConeData.lean` module is removed from the packet.
`CompletionTriangleComparison.lean` imports `PrincipalReductionConeCalculus`
directly. A source comparison confirms that this import line is its sole change
from the returned item module; its theorem, definitions and docstrings are
unchanged. In particular all clauses accepted in L's review remain present:
`roosχ` pins the chain augmentation, κ identifies descent of c, every K-flat
representative has the augmented ψ comparison, completeness is equivalent to
invertibility of c, CommShift is coherent with c, and every distinguished image
triangle carries the three components of c including its shifted last square.

## Self-check by Q01

Re-read the return against the node/module packet. No original dependency
statement or declaration was replaced; all original data constructions and proof
imports are retained. The eight recorded names now belong to one module and one
node. The item is byte-identical after undoing its one import swap. The full
hypothesis/clause correspondence and edge-case checks above still apply. No new
node, changed mathematical statement, additional assumption, axiom, or proof was
introduced. The maintainer performs the independent second reading.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
