## Worker report

The module `Sheaf.CategoryTheory.OperadicWeakApproximation` defines
`SSet.Enhanced.Nonsymmetric.IsWeakApproximation` and the concrete coherent
factorization categories appearing in its definition. All data are constructed;
there are no new theorems, axioms, or `sorry`s. The statement was checked against
Gepner–Haugseng, *Enriched infinity-categories via nonsymmetric infinity-operads*,
Definition A.6.1, including its extension to arbitrary maps:
https://arxiv.org/html/1312.3178#A6.SS1 . No statement correction is made.

Clause-by-clause correspondence:

- Small generalized source `M`, ordinary target `O`, and common simplex base:
  the main definition takes `q : M ⟶ monoidalSimplexBase` and
  `p : O ⟶ monoidalSimplexBase`; its first conjuncts are
  `Presentability.IsSmall.{u} M`, `Presentability.IsSmall.{u} O`,
  `IsGeneralizedOperad q`, and `IsOperad p`. Both operad predicates include the
  quasicategory and inner-fibration axioms. The ambient simplicial-set universe
  is `max u v`; smallness is separately measured in `u`, without imposing any
  equality with the ambient universe. The complete-algebroid module is imported
  for the node's shared operadic and universe conventions.
- Inert-preserving functor over the base: `IsLaxMonoidalInfinityFunctor q p f`.
  Its definition explicitly requires `f ≫ p = q` and preservation of
  `IsMonoidalInertEdge`. The latter means cocartesian over the opposite of a
  consecutive interval inclusion, including intervals of length zero.
- Active edges: `IsActiveBase` requires that the opposite order map sends both
  endpoints to endpoints, including the coincident endpoints at arity zero;
  `Nonsymmetric.IsActiveEdge` asks that the image of the edge equal such a base
  edge. No cocartesian condition is added for active edges.
- Categorical fibration: the existing `SSet.Enhanced.IsIsofibration` is reused.
  It includes both quasicategory conditions, `InnerFibration`, and a lift of
  every equivalence edge with prescribed source, strict equality of its image,
  and equivalence of the lift. The target of the lift is unrestricted. Its
  quasicategory conjuncts are already supplied by the operad axioms.
- Slice and coslice: `WeakApproximation.slice M c` is only an abbreviation for
  the existing `joinSlice (yonedaEquiv.symm c)`. `joinSlice` stores an extension
  `Δⁿ ⋆ Δ⁰ → M` with fixed last point; its `base` is uniquely the initial-block
  restriction. Its equations under every simplex operator retain no extra data.
  `coherentJoinCoslice (yonedaEquiv.symm a)` is the recorded join coslice in
  `B = O_/f(c)`, with initial point `a` fixed and free final block.
- The degreewise pullback `H`: `factorizationSubcomplex f c a` is the subcomplex
  of the Cartesian simplicial product of those two sets of extensions imposing
  `(joinSlicePostcomp f c).app n z.1 =
  (coherentCosliceProjection (yonedaEquiv.symm a)).app n z.2`.
  Thus the entire final block of the triangle agrees with the image of the
  source slice extension, in every degree. Faces and degeneracies are inherited
  coordinatewise. The coslice-in-slice description is the specified iterated
  ordered join, with first-to-last edge `a` fixed. The abbreviation
  `factorization` takes this actual subcomplex's underlying simplicial set.
- The first triangle edge `γ` is `firstEdge`: apply the coslice extension to
  `joinPointTopSimplex 0` in `Δ⁰ ⋆ Δ⁰`, obtaining an edge in `B`, then apply
  `joinSliceProjection` to obtain its initial-block edge in `O`. This is
  `X → f(D)`, rather than `f(D) → f(c)` or a comparison arrow between objects.
- The full subcategory `F`: `inertFactorizations` uses the dependency's
  `fullSubcomplex` with vertex predicate
  `IsMonoidalInertEdge p (yonedaEquiv.symm (firstEdge f c a z))`.
  All morphisms and higher simplices between admitted vertices remain present.
  No inertness condition is imposed on the comparison edge `h`.
- The categorical-fibration case is `IsFibrationWeakApproximation p f`:
  `IsIsofibration f` together with `∀ c a, IsContractible
  (inertFactorizations p f c a)`. Here `a` ranges over **all** vertices of
  `O_/f(c)`, exactly the node's interpretation of every arrow into `f(c)`;
  there is no active-arrow restriction.
- Weak contractibility is exactly the existing `IsContractible`, which tests
  the unique map to `Δ⁰` using geometric realization, the component bijection,
  and every positive based homotopy group. It does not mean `Nonempty`,
  categorical equivalence to a point, or strict contractibility.
- The arbitrary-map case existentially quantifies `M'`, `q'`, `e`, and `g`,
  with smallness and `IsGeneralizedOperad q'`, both over-base/inert-preservation
  conditions, `IsFunctorEquivalence e`, the strict equation `e ≫ g = f`, and
  `IsFibrationWeakApproximation p g`. No replacement or inverse is chosen.
  An inert-preserving equivalence over the base is the existing underlying
  coherent functor equivalence, as in the recorded operad-equivalence interface.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`: common operadic conventions; read
  `Algebroid.completeCategory` and the imported base/size interface. No algebroid
  or monoidal coefficient datum is added to the weak-approximation parameters.
- `Sheaf.CategoryTheory.OperadicAlgebraPresentability`:
  `Nonsymmetric.IsGeneralizedOperad`, `Nonsymmetric.IsOperad`. Their definitions,
  not the presentability theorem's conclusion, supply the operad notions.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `IsEquivalenceEdge`, `fullSubcomplex`, `IsFunctorEquivalence`, `IsContractible`.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` publicly reexports
  `InfinityFibrations` and its horn/cocartesian-edge interface.
- `Sheaf.CategoryTheory.MonoidalInfinityCategory`:
  `monoidalSimplexBase`, `monoidalBaseEdge`, `IsMonoidalInert`,
  `IsMonoidalInertEdge`, `IsLaxMonoidalInfinityFunctor`.
- `Sheaf.CategoryTheory.RelativeCosliceLeftFibration`:
  `coherentJoinCoslice`, `coherentCosliceProjection`, using the recorded
  `CoherentJoinSimplex.extension` interface.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`, publicly reexported there:
  `joinSlice`, `joinSliceProjection`, `joinPointTopSimplex`.
- `Sheaf.CategoryTheory.TwistedArrowLeftFibration`: `joinSlicePostcomp`.
  Its owning landed node `lem-coef-twisted-arrow-left-fibration` is added to
  `stmt_deps` to reuse the canonical map rather than define it again.
- `Sheaf.CategoryTheory.IsofibrationExponentiation`: `IsIsofibration`.
  Its owning landed node `lem-coef-infinity-isofibration-exponentiation` is
  added to `stmt_deps` rather than duplicate categorical fibrations.

Edge cases checked by reading the formulas: an empty source makes the all-objects
condition vacuous, as the node requires; an empty factorization category for an
existing test arrow fails the component-bijection part of `IsContractible`.
Arity zero is retained in the operad predicates and the active/inert base-map
predicates. Identities and equivalences are among the universally quantified test
arrows, and all comparison morphisms are retained. At simplicial degree zero the
pair is exactly an arrow into `c` and a triangle out of the fixed test arrow.
Higher degrees retain full join maps and whole-block equalities, not only
vertexwise commutativity. General maps need not be categorical fibrations;
only the existential map `g` has that requirement. All universes and variables
are bound explicitly (`autoImplicit false`). The universe linter is disabled
because the signature combines the small and ambient levels in `max u v`,
while the smallness predicate in its body still distinguishes `u`.

Searches on 2026-10-17:

- `msearch.py ... leanfinder "weak approximation of nonsymmetric infinity operads by contractible inert factorization categories"`:
  eight hits, including strict Segal nerves, simplex-category factorization and
  `SSet.QCat`; none defines operadic weak approximation.
- `msearch.py ... loogle '"WeakApproximation", "CategoricalFibration"'`:
  zero hits.
- `msearch.py ... grep 'WeakApproximation|weakApproximation|CategoricalFibration|categoricalFibration'`:
  only two Mathlib section markers in `Analysis/AbsoluteValue/Equivalence`.
- `msearch.py ... leansearch "weak approximation nonsymmetric infinity operad inert factorizations"`:
  eight hits about ordinary weak factorization systems and model-category
  fibrations, not the infinity-operadic definition.
- `rg` for the same names and the item id in upstream `WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no weak-approximation
  declaration; the specialized left-module categorical-fibration predicate
  is for a fixed, different base. A follow-up search for `IsIsofibration`
  found the exact general notion in `IsofibrationExponentiation`, which is used.
- `rg` for slice postcomposition/map helpers in `lean/Sheaf/CategoryTheory`
  found `joinSlicePostcomp` (and a more general diagram version). The exact
  point-slice map is imported and reused; the provisional duplicate was removed.

No new nodes, dependency repairs, or disputed statements. Only `lean` and the
two permitted additions of landed dependencies in `stmt_deps` change.
The module compiles through the prescribed `scompile.py` wrapper, as both its
sandbox module and its actual library module, with no errors or warnings.

## Second reading by N5

Independent maintainer second reading, 2026-10-17, of immutable delivery
`4b8dfae19f10654c5709abc0b00c8da34b027a57`. This reader did not write or
previously second-read the delivery. The original section described a self-audit;
this replacement records the independent reading required by H11. The Worker
report above is retained verbatim. The Lean module and node records need no change.

Source and scope: read `check-brief2.md` in full, the packet, the snapshot item,
all seven snapshot statement-dependency records, the delivered module and report.
Read Gepner--Haugseng Definition A.6.1, including its final factorization paragraph,
at https://arxiv.org/html/1312.3178#A6.SS1 (HTML lines 4134--4142). It tests arbitrary
arrows and restricts the first triangle edge to be inert. Proposition A.6.3's
active-arrow criterion is a separate theorem and is not substituted here. The
explicit join model in the node agrees with that full factorization category.

Clause-by-clause independent verdicts:

1. Objects and size: `IsWeakApproximation` binds `M O`, the two base maps `q p`
   and `f`. `IsSmall.{u}` is imposed on both objects and on the replacement.
   Read `PresentableInfinityCategory.lean:42`: it measures the smallness of the
   sigma type of nondegenerate simplices. `SSet.{max u v}` accommodates every
   small/ambient pair; it does not identify the universes or restrict to finite
   or discrete categories. No monoidal coefficient datum or algebroid is assumed.
   The complete-algebroid dependency supplies conventions, not extra parameters.
   Verdict: exact.
2. Generalized source and ordinary target: the conjuncts are `IsGeneralizedOperad q`
   and `IsOperad p`. Read `OperadicAlgebraPresentability.lean:57` and `:187`,
   including `HasInertLifts`, `HasIncidenceSegal` and the relative-limit predicates.
   They include quasicategories and inner fibrations; the generalized zero fiber
   is Kan and is not required to be terminal. The ordinary predicate supplies the
   ordinary Segal and relative-limit axioms. Verdict: uses the recorded notions.
3. Functors and inert/active edges: read `MonoidalInfinityCategory.lean:67`, `:249`
   and `:257`. `IsLaxMonoidalInfinityFunctor q p f` is precisely the over-base
   equation and preservation of cocartesian edges over consecutive-interval
   inclusions. `IsActiveBase` requires both opposite endpoints to be preserved;
   `IsActiveEdge` adds no cocartesian requirement. Verdict: exact, including arity zero.
4. Categorical fibration: read `IsofibrationExponentiation.lean:47`,
   `IsIsofibration`. It includes inner fibration and both quasicategory conditions,
   then lifts every outgoing equivalence edge with specified source and exact
   image. The lift itself must be an equivalence. No target is prescribed beyond
   its image, as required. The quasicategory conjuncts are already consequences
   of the operad assumptions. Verdict: no additional hypothesis.
5. Slice and operators: `WeakApproximation.slice` abbreviates the recorded
   `joinSlice`. Read `JoinSliceRightFibration.lean:121` onward: its extension is
   a map from the ordered join of the variable simplex and fixed point. The
   final restriction is fixed; the stored initial restriction is uniquely
   determined by that extension. Operators precompose on the variable block.
   `RelativeCosliceLeftFibration.lean:68` onward defines `CoherentJoinSimplex`,
   `coherentJoinCoslice` and its last-block projection with the opposite orientation.
   Verdict: the requested slice/coslice, with no additional simplex data.
6. Pullback H: read `TwistedArrowLeftFibration.lean:179`, `joinSlicePostcomp`,
   which postcomposes the whole extension with `f`. `factorizationSubcomplex`
   takes the Cartesian product and imposes equality of its image and the coslice
   target in every degree. The structure's map field is just the naturality
   calculation preserving this equality. Thus the equality holds on the entire
   final block, not merely on vertices. A map into the slice is an iterated join
   map into O; its initial fixed edge is alpha. Verdict: the displayed degreewise
   pullback and all stated simplicial operators are present.
7. First edge and full subcategory F: read `joinPointTopSimplex` at
   `JoinSliceRightFibration.lean:188`. At degree zero it is the ordered edge of
   the join of two points. `firstEdge` evaluates the coslice extension on it,
   then projects the resulting edge in the slice to O. This selects X to f(D),
   not f(D) to f(C). `inertFactorizations` uses the recorded `fullSubcomplex`
   (`EnhancedDiagramsCones.lean:50`), admitting exactly the simplices whose
   vertices satisfy this inertness condition. Comparison arrows and their
   compatible triangles are unrestricted. Verdict: exact orientation and fullness.
8. Fibration case: `IsFibrationWeakApproximation` conjoins `IsIsofibration f`
   with `forall c a`, where a ranges over every vertex of the slice O_/f(c).
   `IsContractible` at `EnhancedDiagramsCones.lean:101` is weak homotopy equivalence
   of the unique map to the actual zero-simplex. Its preceding definition tests
   realization path components and every positive based homotopy group.
   Verdict: every arrow, with weak contractibility rather than equivalence to a point.
9. Arbitrary-map case: the existential binds M', q', e and g. It supplies smallness,
   generalized operad axioms, inert-preserving over-base conditions for both maps,
   the recorded `IsFunctorEquivalence e`, the strict equation `e >> g = f`, and
   the fibration-case predicate for g. Read `EnhancedDiagramsCones.lean:233`:
   equivalence means a coherent quasi-inverse with natural equivalences. No
   replacement is chosen and f need not be a categorical fibration. Verdict: exact.

Dependency audit: all seven snapshot records were read, including their statements,
source fields and Lean bindings. In addition to the locations above, read the module
and declaration docstrings for `CompleteAlgebroid.completeCategory` (line 472),
`InfinityFibrationsOverSimplicialBases.cocartesianFibrationOver`, and the reexported
`InfinityFibrations` horn and cocartesian-edge interface. The relative-coslice
source is Kerodon 01BZ/018F; the point-slice/top-simplex source is 018F/01KX;
the canonical slice postcomposition is the 03K0 naturality helper; categorical
fibrations use the recorded 01F1 source-fixed convention. The enhanced dependency
specifies its realization and coherent-functor conventions explicitly. These are
landed helper definitions used directly, not private copies or arbitrary maps.
No dependency module or new node is delivered, and no missing prerequisite or
universe repair is needed. No statement correction is made, so no citer audit is due.

Independent duplicate searches, 2026-10-17: `msearch.py ... loogle
'"WeakApproximation"'` returned zero hits. `msearch.py ... leansearch
'infinity operad weak approximation inert factorization category'` returned eight
hits about ordinary weak factorization systems/model categories, none the notion.
`rg -n -i 'weak.?approximation|inertfactorizations|factorizationSubcomplex|IsActiveBase'`
over group `lean/Sheaf`, upstream `WeilConjectures`, Mathlib and
`dag/lean_names_upstream.json` found only unrelated number-theoretic and
absolute-value approximation material. The report also records the three required
search kinds. The existing canonical slice and isofibration helpers are reused.

Edge cases: empty source makes the all-objects condition vacuous; an empty
factorization set for an existing test arrow fails the component-bijection test.
All arities, including zero and length-zero inert intervals, remain allowed.
The active endpoint equations handle coincident endpoints. Identities,
equivalences and nonactive test arrows are included. Degree zero gives exactly
an arrow and a triangle; higher degrees retain whole-block compatibility and
all comparison simplices. Empty target causes no extra inhabitedness condition.
No characteristic or ring assumptions occur. All variables and universes are
explicitly bound, with `autoImplicit false`; disabling the universe linter does
not impose an equality between the small and ambient levels.

Maintainer gates: all nine declarations are listed in `lean.declarations` and
have source-place/blueprint docstrings. The module docstring names Definition
A.6.1 and the item. `lean.statement` equals the source signature verbatim,
including whitespace after stripping the noncomputable modifier in the usual
record convention. All lines are at most 100 characters. All data are real
constructions: there are no axioms, theorem/lemma declarations or sorries.
The short subcomplex closure proof only assembles the definition using naturality;
no mathematical theorem is proved locally. There is no arbitrary replacement,
Nonempty choice, local notation, private notion or pro-etale substitute.

Compiler evidence independently reproduced with the immutable file:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N5
 def-coef-operadic-weak-approximation
 snapshot/lean/Sheaf/CategoryTheory/OperadicWeakApproximation.lean`.
Exit status 0; sandbox `Sheaf/Stage2/Sandbox0.lean` 1.9 s and library
`Sheaf/CategoryTheory/OperadicWeakApproximation.lean` 1.9 s; no errors or warnings.
The installed wrapper currently runs its side-overlay checks on the server via
`nt_srv_compile.py --wire-confirm`; this was invoked only through the authorized
wrapper. No direct ssh, global build, live Lean write, clone edit, delivery or
Git mutation was performed.

Finding and fix: H11 (also H1's substantive report requirement): the original
second-reading section explicitly said it was a self-audit and deferred independent
review. Replace that section with this independent reading. The complete report
replacement preserves the Worker report. No mathematical or Lean correction is needed.
