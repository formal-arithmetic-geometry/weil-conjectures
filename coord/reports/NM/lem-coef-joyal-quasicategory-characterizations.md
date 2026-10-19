## Worker report

The module `Sheaf.AlgebraicTopology.JoyalQuasicategoryCharacterizations` states
`SSet.joyal_quasicategory_characterizations`, with one postponed proof (`sorry`).
It introduces no definitions and proves nothing. The node's mathematical statement
is unchanged. The already landed node
`lem-coef-infinity-isofibration-exponentiation` is added to `stmt_deps` so that its
existing `SSet.Enhanced.IsIsofibration` is used rather than copied.

The source checked is Cisinski, *Higher Categories and Homotopical Algebra*,
revision July 30, 2026, Definition 3.3.15 (printed p.97), Theorem 3.6.1
(pp.112–113), Remark 3.6.5 and Corollary 3.6.6 (p.114), and Theorem 3.6.8
(pp.115–116): <https://cisinski.app.uni-regensburg.de/CatLR.pdf>.
The definition uses outgoing equivalences with prescribed source; the theorems
identify this isofibration condition, coherent quasi-invertibility and the hFun
testing convention with the corresponding Joyal classes. The module docstring
carries all seven proof steps of the DAG, including the core/interval argument
and the two-test Yoneda and whiskering argument. No statement dispute or
source-based correction is needed.

Clause-by-clause correspondence:

- The Joyal model structure is the parameter
  `M : HomotopicalAlgebra.ModelCategory SSet.{u}`. The hypotheses `hcof` and
  `hweak` specify exactly its two classes in the recorded
  `SSet.exists_joyal_model_structure`: degreewise injections and equivalences of
  ordinary homotopy categories after restriction into every test quasicategory.
  They identify the model named by the node; they do not impose conditions on
  `f`, `C` or `D` beyond the node. The existence theorem supplies an M and both
  hypotheses simultaneously. Model axioms determine the fibrations as the RLP
  class of the intersection, so the statement applies to the entire specified
  Joyal structure without choosing data from an unproved existence statement.
- Two arbitrary quasicategories in the same universe are
  `{C D : SSet.{u}} [Quasicategory C] [Quasicategory D]`. The map is
  `(f : C ⟶ D)`, an actual simplicial map, with no finiteness or size restriction
  beyond their common, arbitrary universe `u`.
- Clause (1) is
  `M.categoryWithFibrations.fibrations f ↔ Enhanced.IsIsofibration f`.
  The recorded definition of `IsIsofibration` contains the quasicategory
  conditions, `InnerFibration f`, and the equivalence-edge lifting assertion.
  `InnerFibration` in Mathlib means RLP against every inner horn inclusion
  (`innerHornInclusions.rlp`), exactly `0 < i < n`.
- In that same definition, the prescribed source is `c : C _⦋0⦌`; a target
  equivalence is `e : D _⦋1⦌` with
  `D.δ 1 e = f.app _ c` and `IsEquivalenceEdge D e`.
  Its lift is `∃ e' : C _⦋1⦌, C.δ 1 e' = c ∧
  IsEquivalenceEdge C e' ∧ f.app _ e' = e`.
  Thus the image equals the prescribed edge strictly, the source is fixed,
  and the terminal vertex of the lift is free, as in the node.
- Clause (2) is
  `M.categoryWithWeakEquivalences.weakEquivalences f ↔
  Enhanced.IsFunctorEquivalence f`.
  The existing definition expands to a simplicial map `g : D ⟶ C` with
  `AreNaturallyEquivalent (f ≫ g) (𝟙 C)` and
  `AreNaturallyEquivalent (g ≫ f) (𝟙 D)`.
  Lean's composition convention means these are respectively `gf` and `fg`.
  Each `AreNaturallyEquivalent` is an equivalence edge in the corresponding
  internal-hom simplicial set, with exactly the two stated endpoints. Its
  `IsEquivalenceEdge` demands a single inverse edge and both inverse triangles.
  Hence these are coherent natural equivalences, not ordinary homotopies or
  isomorphisms of ordinary homotopy categories. No adjoint triangle identities
  between the two chosen natural equivalences have been added.
- The final hFun convention is explicitly the `hweak` hypothesis:
  `∀ (E : SSet.{max u v}), E.Quasicategory →
  ((hoFunctor.map ((MonoidalClosed.pre
  (uliftFunctor.{v, u}.map i)).app E)).toFunctor).IsEquivalence`.
  `MonoidalClosed.pre` is restriction; `hoFunctor` forms the generated ordinary
  homotopy category. The lift of `i` makes source and test universes agree.
  Both universes are explicitly bound, and `v` is arbitrary, retaining every
  enlarged testing universe from the recorded Joyal model declaration. The
  final sentence is therefore part of identifying the very weak-equivalence
  class characterized in (2), not a replacement by another notion.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsEquivalenceEdge`, `diagramVertex`,
  `AreNaturallyEquivalent`, and `IsFunctorEquivalence`, with their full
  definitions and docstrings; Mathlib's `SSet`, `Quasicategory` and internal hom
  supply the underlying notions without private copies.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`; the full signature and proof docstring
  were read, and the theorem's two class identifications are reproduced as
  the model-parameter specification. Neither this node nor its record needs
  an interface repair.
- `Sheaf.CategoryTheory.IsofibrationExponentiation`:
  `SSet.Enhanced.IsIsofibration` and `isofibration_exponentiation`, read with
  docstrings. This is both the existing proof dependency and the now explicit
  statement dependency for the exact isofibration notion.
- Mathlib `AlgebraicTopology.Quasicategory.InnerFibration`:
  `SSet.innerHornInclusions`, `innerFibrations`, `InnerFibration`.
  Mathlib `AlgebraicTopology.ModelCategory.Basic`:
  `HomotopicalAlgebra.ModelCategory` and its three class projections.
  Mathlib `AlgebraicTopology.SimplicialSet.HomotopyCat`:
  `SSet.hoFunctor` is the generated category stipulated by the model node.

The other proof dependencies, `lem-coef-quasicategory-edge-triangle-presentation`,
`lem-coef-joyal-interval-boundary-tests` and
`lem-coef-infinity-core-kan-fibration`, have no recorded Lean or Mathlib match
in the supplied DAG. There are no modules to import for them; they are explicitly
named in the proof docstring for stage 3. They are not prerequisites to typing
this statement, and no theorem about them is introduced here.

Edge cases checked mathematically before writing:

- Empty source and target are allowed: no `Nonempty` assumptions occur. The
  map from the empty quasicategory to any quasicategory has vacuous equivalence
  lifting and inner lifting, hence is a Joyal fibration. It is a weak equivalence
  only if a quasi-inverse can exist, as the statement requires.
- In horn dimensions zero and one there are no inner horns; Mathlib's inner
  horn family starts in dimension two. No erroneous dimension-zero vertex
  surjectivity is imposed. The proof's interval-boundary test includes n = 0.
- Identity maps satisfy both characterizations, including identity natural
  equivalences. An equivalence need not be an isofibration: including one
  vertex into the nerve of the two-object contractible groupoid has a coherent
  quasi-inverse but cannot lift the outgoing edge to the other vertex with
  its exact image. The two assertions are independent as required.
- A nerve of a non-equivalence ordinary functor may still be an isofibration
  (e.g. the source-vertex inclusion into the nerve of `[1]`); no equivalence
  assumption is silently imposed on a fibration.
- The entire formulation works for every common universe `u`, and tests are
  in `max u v`, avoiding a smaller, vacuous testing universe.

Searches made (2026-10-16 UTC; machine-local date 2026-10-17):

- `msearch.py ... leanfinder`, query: "A map between quasicategories is a
  Joyal fibration precisely when it lifts inner horns and equivalence edges
  and is a categorical weak equivalence precisely when it has a simplicial
  quasi inverse". Eight hits, principally
  `SSet.modelCategoryQuillen.fibrations_eq`, `fibration_iff`,
  `instHasLiftingPropertyιHornHAddNatOfNatOfFibration`, and generic bifibrant
  homotopy lemmas. These concern all-horn Kan fibrations or general model
  categories, not this Joyal characterization.
- `msearch.py ... loogle`, query `"Quasicategory", "WeakEquivalence"`:
  zero hits.
- `msearch.py ... leansearch`, query: "Joyal fibrations of quasicategories
  lift equivalence edges and Joyal weak equivalences have coherent quasi
  inverses". Eight hits: generic Joyal-trick lemmas, all-horn Kan fibrations,
  and general lifting-class identities; none is the desired theorem.
- `msearch.py ... grep`, query
  `Joyal|joyal|categoricalEquivalence|FunctorEquivalence`, subdirectory
  `AlgebraicTopology`: five hits, all in `ModelCategory/JoyalTrick.lean`.
  These are general model-category tricks, not the Joyal model on simplicial
  sets. Read the candidate all-horn and inner-fibration APIs to distinguish
  their hypotheses and exact classes.
- `rg -n` with the same pattern in upstream `WeilConjectures/`: only an
  unrelated `pullFunctorEquivalence` in affine descent. A search for this
  item's id there gives no match.
- `rg -n` with the same pattern in `lean/Sheaf`: existing model existence,
  coherent-nerve model data, and uses of `IsFunctorEquivalence`; no theorem
  giving both requested characterizations. The coherent-nerve module's
  `JoyalModelData` is presentation data and does not prove this theorem.
- `rg -n 'joyal_quasicategory_characterizations' dag/lean_names_upstream.json`:
  no collision. None in Mathlib, upstream or the project from the preceding
  name/concept searches.

Validation: `scompile.py NM lem-coef-joyal-quasicategory-characterizations`
compiled the module cleanly, with no errors or warnings, under the prescribed
per-file limit. The final dry run is recorded below once completed. The second
reading is left to the separately assigned reader; no second-reading section
has been written by this worker.

Dry run result: `deliver2.py NM lem-coef-joyal-quasicategory-characterizations
--no-push` printed `OK (dry run)` for commit `29697f936c`: compiles and passes
preflight except for the independent second reading, which the second reader
writes. Nothing was pushed.

## Second reading by NM

I read the node statement, its three statement dependencies, the complete Lean
signature, and Cisinski's cited source pages independently. The object and
clause list is as follows.

- The model object is `M : HomotopicalAlgebra.ModelCategory SSet.{u}`.
- `hcof` identifies its cofibrations with degreewise injective maps in every
  simplicial degree.
- `hweak` identifies its weak equivalences with the stated `hFun` tests in every
  test universe `SSet.{max u v}`; `v` is universally polymorphic.
- `C` and `D` are arbitrary quasicategories in the common universe `u`, and
  `f : C ⟶ D` is an arbitrary simplicial map.
- Clause (1) is the equivalence between
  `M.categoryWithFibrations.fibrations f` and
  `SSet.Enhanced.IsIsofibration f`.
- Clause (2) is the equivalence between
  `M.categoryWithWeakEquivalences.weakEquivalences f` and
  `SSet.Enhanced.IsFunctorEquivalence f`.

The Lean renders every item exactly. `IsIsofibration` expands to quasicategory
source and target, `InnerFibration`, and lifting an outgoing target equivalence
with prescribed source and exact image. `IsFunctorEquivalence` expands to a
single simplicial `g : D ⟶ C` and equivalence edges in the two internal functor
quasicategories, with endpoints `f ≫ g` and `g ≫ f` against the respective
identities. The hFun test in `hweak` is the dependency's `hoFunctor` test after
`uliftFunctor`, with the same `max u v` convention. No extra finiteness,
Noetherian, characteristic, or universe-equality hypothesis occurs.

The source check agrees: Cisinski Definition 3.3.15 requires inner-fibration
lifting of an invertible edge with its source fixed; Theorem 3.6.1 identifies
these isofibrations with Joyal fibrations; Remark 3.6.5 and Corollary 3.6.6
identify invertible natural transformations and equivalences of
quasicategories; Theorem 3.6.8 gives the `hFun` characterization. Thus the
source-prescribed direction, exact edge equality, coherent inverse data, and
test convention all match the node.

I checked edge cases: empty simplicial sets and empty mapping spaces are
allowed; no `Nonempty` assumption is introduced. Inner horns begin in the
correct dimensions, so no spurious vertex or outer-horn condition is added.
Identity maps satisfy both clauses, and the statement permits arbitrary
quasicategories, including the zero-dimensional cases. The common universe is
arbitrary and the enlarged testing universe is `max u v`.

Searches were rechecked with `msearch.py` (LeanFinder, Loogle, and LeanSearch),
`rg` in Mathlib, `WeilConjectures/`, and project `lean/Sheaf/`, and the upstream
name index. They found only generic Kan/model-category results and the already
recorded dependency declarations; no existing theorem states this combined
characterization. The dependency declarations read are
`SSet.Enhanced.IsIsofibration`, `SSet.Enhanced.IsFunctorEquivalence`,
`SSet.Enhanced.AreNaturallyEquivalent`, and
`SSet.exists_joyal_model_structure`.

No mismatch was found, so no Lean, node, or dependency repair was needed. The
module compiles cleanly with the prescribed `scompile.py` wrapper (no errors or
warnings other than permitted postponed proofs).
