## Worker report

States `SSet.rightAnodyneExtensions_iff_hasLiftingProperty` in
`Sheaf.CategoryTheory.RightAnodyneLiftingCharacterization`. Its only proof is `sorry`.
No definition or auxiliary node is added, and the node changes only in `lean`.
The theorem docstring carries all six steps of the recorded proof.

Clause-by-clause correspondence:

- Simplicial sets in any fixed containing universe: the explicitly declared universe
  `u`, with `U V E S : SSet.{u}`. Simplicial maps are category morphisms.
- The given map `v : U → V`: `(v : U ⟶ V)`.
- The node's right anodyne predicate: `rightAnodyneExtensions v`, using the recorded
  weak-saturation definition without replacing it by an LLP definition.
- “If and only if”: `↔`, preserving both implications.
- Every right fibration `q : E → S`: `∀ {E S : SSet.{u}} (q : E ⟶ S),
  Enhanced.rightFibration q → ...`. Implicit binders are still universally quantified.
- Every pair of maps `u : U → E`, `w : V → S` with `qu = wv`, and existence of
  `d : V → E` satisfying `dv = u`, `qd = w`: `HasLiftingProperty v q`.
  Reading Mathlib's full definition shows `sq_hasLift` quantifies over all
  `CommSq u v q w`; its equation is `u ≫ q = v ≫ w`.
  `CommSq.HasLift.exists_lift` is `Nonempty sq.LiftStruct`, whose data are
  `l : V ⟶ E`, `fac_left : v ≫ l = u`, `fac_right : l ≫ q = w`.
  Thus this is exactly the existential diagonal property, without uniqueness.
- No Kan or quasicategory hypotheses: there are no such instance or explicit binders
  on any of the four simplicial sets. The right-fibration definition itself has none.

Dependency declarations and imports:

- `def-cbc-enhanced-diagrams-cones`: public import
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`; uses its Mathlib `SSet` and
  simplicial-map conventions. Its recorded `SSet.Enhanced.coneCategory` and
  docstring were read; cones are not used in this node.
- `def-coef-infinity-fibrations`: public import of its recorded
  `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`, which publicly imports
  `Sheaf.CategoryTheory.InfinityFibrations`. The used declaration is
  `SSet.Enhanced.rightFibration {E B : SSet.{u}} (p : E ⟶ B) : Prop` from the latter.
  Its full body requires `HasLiftingProperty (horn n i).ι p` for `1 ≤ n`, `0 < i`.
  `i : Fin (n + 1)` ensures `i ≤ n`. The current record highlights
  `cocartesianFibrationOver`, but explicitly reexports this usable right-fibration
  interface, so no dependency repair is necessary.
- `def-coef-infinity-right-anodyne`: public import
  `Sheaf.CategoryTheory.RightAnodyne`, using `SSet.rightAnodyneExtensions`. Its `sInf`
  ranges over properties containing isomorphisms and all positive-index horns,
  closed under pushouts, universe-`u` transfinite compositions and retracts.
- `HasLiftingProperty` is Mathlib's existing notion from
  `Mathlib.CategoryTheory.LiftingProperties.Basic`, reexported by the dependencies.
- Proof-only imports match the remaining proof dependencies:
  `Mathlib.CategoryTheory.Limits.HasLimits` (`CategoryTheory.Limits.colimit`);
  `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`
  (`llp_isStableUnderRetracts`, `rlp_isStableUnderRetracts`,
  `llp_isStableUnderCobaseChange`, `llp_isMultiplicative`);
  `Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument`
  (`CategoryTheory.SmallObject.functorialFactorizationData`);
  `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting`
  (`CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp`).
  These recorded Mathlib signatures and docstrings were read. There is no import
  of the downstream cancellation theorem, so the proof-import plan creates no cycle.

Edge cases checked before writing:

- Isomorphisms, including identities of the empty simplicial set: belong to the
  defining saturation, and lift against every map by inverse composition.
- Dimension zero: the positive horn-index condition is impossible for `Fin 1`,
  hence the anodyne definition adds no dimension-zero generator; the right-fibration
  definition explicitly requires dimension at least one. No nonemptiness appears.
- Dimension one: `i = 1` is included; `i = 0` is excluded, confirming the right
  rather than left convention. Both definitions include the final outer horn.
- Empty sources/targets and non-Kan/non-quasicategory simplicial sets are permitted.
  In particular `∅ → Δ[0]` is a right fibration (there are no top horn maps to ∅),
  so the same map cannot satisfy the asserted LLP: the square with identities
  cannot have a map `Δ[0] → ∅`. Neither side silently accepts this counterexample.
- Universe `u` is arbitrary, shared by all four simplicial sets and the saturation's
  small transfinite compositions. No size equation or extra restriction is imposed.

Searches (all 2026-10-17; complete service metadata in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder "A simplicial map is right anodyne if and only if it has
  the left lifting property against every right fibration"`: eight hits about the
  Quillen all-horn class (`SSet.modelCategoryQuillen.J`, `fibration_iff`, etc.);
  no right-horn characterization.
- `msearch.py ... loogle '\"llp\", \"rlp\"'`: twelve generic lifting-class results,
  including `llp_rlp_llp` and `transfiniteCompositions_le_llp_rlp`; no theorem
  identifying the project's right-horn weak saturation with its LLP class.
- `msearch.py ... leansearch "right anodyne simplicial map if and only if left lifting
  property against right fibrations"`: eight hits about all-horn Quillen fibrations,
  model-category lifting axioms and generic `MorphismProperty.rlp`; no exact match.
- `msearch.py ... grep 'right.?anodyne|rightAnodyne|right.?fibration|rightFibration'
  AlgebraicTopology`: zero Mathlib hits.
- `rg` with the same right-anodyne/right-fibration names on upstream
  `WeilConjectures` and `grep -rn` for this item id: no hits.
- `rg` on project `lean/Sheaf` found the recorded definitions and downstream theorems
  (products, exponentiation, cancellation), but no lifting characterization. The
  narrower search `rightAnodyne.*iff|rightAnodyne.*lift|rightAnodyneExtensions_iff|
  rightAnodyneExtensions.*↔|right anodyne.*lifting` confirmed this. The proposed
  theorem name also has no hit in the upstream-name index or project/upstream sources.

Source verification: read online [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Definition the project server (printed p. 53), Remark the project server, and Appendix A.1.2,
Proposition A.1.2.5 and Corollary A.1.2.7 (printed pp. 790–792).
Definition the project server gives right fibrations by exactly the positive-index horns and
right anodyne maps by exactly this LLP. Corollary A.1.2.7 identifies the latter
with the smallest weakly saturated class generated by these horns. The node's
source description calls Definition the project server a weak-saturation definition; that
wording is imprecise (the saturation identification is the appendix corollary),
but its combined references and mathematical statement are correct. No statement
correction or disputed claim is needed. Definitions are reused in full.

Validation: `scompile.py NV lem-coef-right-anodyne-lifting-characterization`
compiled both the sandbox probe and the named module cleanly (1.8 s and 1.7 s);
no errors or warnings. The required `deliver2.py --no-push` dry run is the final gate.

## Second reading by NV

Independent second reader, 2026-10-17. Read the sandbox node and module, all three
statement dependency records, their source modules, the four remaining proof-dependency
records and the relevant Mathlib declarations. There is no repair note for this item.
The node copy has no statement_change and differs from the repository node only in lean.
There are no new nodes or dependency modules to review. Verdict: the statement is exact;
no mathematical, signature, import or docstring repair is needed.

Object/hypothesis/conclusion checklist, written from the node before checking the Lean:

1. Work with arbitrary simplicial sets and simplicial maps in one fixed containing
   universe. Rendered by `universe u`, `{U V : SSet.{u}}` and `{E S : SSet.{u}}`,
   with categorical arrows. Read Mathlib's `SSet := SimplicialObject (Type u)`
   in AlgebraicTopology/SimplicialSet/Basic.lean:36 and the enhanced-diagrams module's
   imports and `coneCategory` declaration. Verdict: the same underlying simplicial
   sets, without a quasicategory condition inherited from the enhanced terminology.
2. Introduce the particular map `v : U → V`. Rendered by `(v : U ⟶ V)`.
   Verdict: exact, and the map remains fixed before the lifting tests are quantified.
3. Membership in the right-anodyne class. Rendered by `rightAnodyneExtensions v`.
   Read RightAnodyne.lean: the definition is the infimum of morphism properties
   containing isomorphisms and `(horn n i).ι` with `0 < i`, closed under pushouts,
   universe-u transfinite compositions and arrow retracts. Because
   `i : Fin (n + 1)`, positivity excludes n=0 and enforces `i ≤ n`.
   Verdict: the dependency's actual weak saturation, not a replacement LLP definition.
4. Equivalence, including the converse implication. Rendered by `↔`.
   Verdict: neither implication omitted, and no monomorphism assumption added.
5. Every right fibration between arbitrary simplicial sets in that universe.
   Rendered by `∀ {E S : SSet.{u}} (q : E ⟶ S), Enhanced.rightFibration q →`.
   Opened InfinityFibrationsOverSimplicialBases.lean and its public import
   InfinityFibrations.lean. The latter defines `rightFibration` with exactly
   `∀ (n : ℕ) (i : Fin (n + 1)), 1 ≤ n → 0 < i →
   HasLiftingProperty (horn n i).ι p`. It takes no Kan/quasicategory instances.
   Verdict: every right fibration, including the final outer horn and arbitrary bases.
   The dependency record's highlighted cocartesian predicate does not hide or
   specialize the publicly reexported right-fibration declaration actually used here.
6. For every top map `u : U → E` and bottom map `w : V → S` satisfying `qu=wv`,
   a diagonal `d : V → E` must exist with `dv=u` and `qd=w`.
   Rendered by `HasLiftingProperty v q`. Independently read LiftingProperties/Basic.lean:48,
   where `sq_hasLift` quantifies over `CommSq u v q w`; CommSq.lean:49 gives
   `u ≫ q = v ≫ w`. CommSq.lean:187 gives the lift field `l : V ⟶ E`,
   `fac_left : v ≫ l = u`, `fac_right : l ≫ q = w`; its `HasLift` field is
   `Nonempty sq.LiftStruct`. Verdict: both required equations, existence without
   uniqueness, and all squares after the fixed map and the right-fibration condition.
7. No Kan or quasicategory hypothesis on any of the four objects. The entire
   theorem signature contains no such binder or typeclass. Verdict: exact.

Source check: independently opened [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Definition the project server, Remark the project server, Definitions A.1.1.2 and A.1.2.2,
Proposition A.1.2.5 and Corollary A.1.2.7. Definition the project server directly gives the
positive-index right horns and the LLP characterization on arbitrary simplicial
sets. The appendix identifies that LLP class with the weak saturation. Its
presentability assumption concerns the ambient category of small simplicial sets;
it introduces no additional hypothesis on these four objects. The node's loose
source description of Definition the project server as a saturation definition is resolved by
its accompanying appendix reference, already made precise in the worker's docstring.
No correction to the node's mathematical statement is necessary.

Edge cases: n=0 supplies no generator and no right-fibration requirement; n=1 has
exactly the i=1 generator. Empty simplicial sets and arbitrary non-Kan/non-quasicategory
objects remain allowed. The map from the empty simplicial set to the point is a
right fibration, but fails its own left lifting test in the square with identity
horizontal maps, so this case does not accidentally become right anodyne. Identities
on empty objects and all other isomorphisms satisfy both sides. Empty coproduct
attachments and ordinal-zero compositions are covered by identities; no index set
or nonemptiness assumption is introduced in the theorem. There is no ring,
characteristic or scheme parameter. The universe is arbitrary, including u=0;
all test objects and small compositions use the node's same fixed universe.

Independent searches, with different semantic formulations from the worker:

- LeanFinder via msearch.py: `Simplicial morphisms generated by horns with positive
  missing vertex are precisely those orthogonal on the left to right fibrations`.
  Eight hits: all-horn Quillen generators/fibrations and quasicategory horn filling;
  none uses precisely the right horns or identifies this project's saturation.
- Loogle via msearch.py: `"transfiniteCompositions", "llp"`. Five generic
  transfinite-composition inclusions into an LLP class, including
  `transfiniteCompositions_le_llp_rlp`; none is the requested equivalence.
- LeanSearch via msearch.py: `The weakly saturated closure of final horns is the
  class of maps with left lifting against all right fibrations`. Eight hits:
  generic weak-factorization-system characterizations and all-horn Quillen lifting.
  Those require an already supplied weak factorization system; they do not state
  this result for the right-horn saturation.
- Independent rg over Mathlib/AlgebraicTopology, upstream WeilConjectures and
  project lean/Sheaf used `positive.?horn`, `horn.*(llp|rlp)` and their reversals,
  as well as right-anodyne/right-fibration names. The upstream has no right-horn
  counterpart. Read Inner/Basic.lean:38-98: its saturation and smallness results
  use inner horns, so do not give this theorem. The narrower semantic search
  `rightAnodyne.*(iff|lifting|llp)|rightAnodyneExtensions.*↔|right anodyne.*(exactly|if and only if|left lifting)`
  found only project terminal-object and cancellation characterizations, whose
  conclusions are different. The upstream-name index contains no proposed name.
  No usable existing declaration was found; retain the delivered module.

H5/H6/H8/H9 checks: there is only the one named theorem, with its sole proof
`sorry`, and no definition, auxiliary claim, local notation or local instance.
The module and theorem docstrings name the precise source and blueprint id.
All six proof steps are present: generating horn lifts; closure including
isomorphisms; small-object factorization and finite-horn smallness; identification
of the two factors and the diagonal; the arrow retract; absence of Kan assumptions.
Read the generic closure, small-object factorization and transfinite LLP signatures
behind the four proof-only Mathlib imports; these are exactly the recorded proof
leaves. No downstream cancellation import or cycle is introduced.
All Lean lines are at most 100 characters. `autoImplicit false`, the explicit
universe and every binder leave no variable or universe unbound. An exact string
comparison confirms lean.statement equals the source signature verbatim.

Changes: appended this independent reading only; no mismatch found and no correct
Lean or node text rewritten. Validation: the required scompile.py invocation on
the absolute sandbox file passed both sandbox and named-library compilation
(1.8 s and 2.0 s), with no errors or warnings. Delivery preflight is recorded below.

Required deliver2.py --no-push gate: OK; preflight and compilation passed.
The dry run staged exactly the module, item node and report and pushed nothing.
