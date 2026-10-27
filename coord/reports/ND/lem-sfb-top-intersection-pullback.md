## Worker report

The module `Sheaf.AlgebraicGeometry.TopIntersectionPullback` states
`AlgebraicGeometry.Scheme.Modules.selfIntersectionNumber_tensorPullback`, with a single
`sorry` proof. It states both branches of the accepted node and the finiteness assertion.
No definition or mathematical statement is changed; no new node or dependency repair is needed.
The accepted stage-1 split is preserved. Its passing review is not a Lean statement: the
live item had no `lean` record, and `coord/queue.tsv` lists it in stage 2. The stage handoff
in brief-stage2 §0 expressly covers the previous worker's inherited stage-1 refusal.
No released repair note for this item was found.

Hypotheses and clauses, in the order of the node:

- The field is `(k : Type u) [Field k]`. The universe `u` is explicitly declared.
- The schemes are `(X Y : Scheme.{u})`, each with its own
  `[X.Over (Spec (.of k))]` and `[Y.Over (Spec (.of k))]` structure.
- Integrality and nonemptiness are `[IsIntegral X] [IsIntegral Y]`. Mathlib's integral
  scheme class includes `Nonempty`; it is not an omitted condition.
- Properness is `[IsProper (X ↘ Spec (.of k))]` and the corresponding instance for Y.
  Finite type is already included: `IsProper` supplies `LocallyOfFiniteType`, and
  universal closedness supplies `QuasiCompact`. Separate redundant hypotheses are unnecessary.
- The common dimension is `(g : ℕ)` with `(_hg : 1 ≤ g)` and the two equalities
  `hX : topologicalKrullDim X = ((g : ℕ∞) : WithBot ℕ∞)` and `hY` with Y.
- The k-morphism is `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`.
- The invertible module is `(L : Y.Modules) [L.IsInvertible]`.
- The pulled-back module is exactly `((tensorPullback f).obj L)`, never Mathlib's
  differently implemented module pullback. Its invertibility proof is supplied directly by
  `((invertible_pullback_tensor f).1 L).2` to the existing intersection definition.
  This introduces no additional hypothesis or choice of a module.
- The whole-source self-intersection on X is the existing `selfIntersectionNumber`,
  evaluated at ambient X, closed subscheme X, and the identity closed immersion.
  The term is written with explicit arguments solely to supply the invertibility proof.
  On Y the same definition is `selfIntersectionNumber k Y Y (𝟙 Y) g hY L`.
- Dominance is the actual `IsDominant f` (dense range of the underlying map).
  The first conjunct quantifies `∀ [IsDominant f]`, so the theorem also applies to
  nondominant morphisms. It asserts both finiteness and the formula whenever dominant.
- The extension uses `(f.dominantFunctionFieldAlgebra).toModule`, the recorded generic
  stalk algebra, explicitly in both `Module.Finite` and `Module.finrank`. Thus the degree
  is that of the actual pullback of function-field germs, not an arbitrary field embedding.
  Finiteness is a conclusion. The natural-number degree is coerced into ℚ, the carrier
  of the recorded intersection numbers.
- The nondominant clause is `¬ IsDominant f → ... = 0`, the second conjunct.
- No `IsFinite f`, separability, smoothness, projectivity, algebraic closure, or
  geometric-integrality hypothesis is present. Inseparable and nonfinite maps are retained.

The identity immersion realizes exactly the node's convention `(L^g · X)` and `(L^g · Y)`.
The definition of intersection numbers is reused unchanged; there is no auxiliary
polynomial, substitute degree, or copied definition. The signature has no local notation,
local instance, hidden arbitrary map, unbound implicit, or `let` binder.

Dependency declarations read and used:

| Node | Module | Declaration or interface |
| --- | --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs | Field |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsIntegral |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | AlgebraicGeometry.IsProper |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType; Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact | LocallyOfFiniteType; QuasiCompact (included in properness) |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension | topologicalKrullDim |
| def-sc-invertible-module | WeilConjectures.AlgebraicGeometry.Modules.Invertible | AlgebraicGeometry.Scheme.Modules.IsInvertible |
| def-sc-intersection-number | Sheaf.AlgebraicGeometry.IntersectionNumber | AlgebraicGeometry.Scheme.Modules.selfIntersectionNumber; intersectionNumber |
| def-sc-function-field | WeilConjectures.AlgebraicGeometry.FunctionField | Mathlib Scheme.functionField, as the node's recorded arbitrary integral-scheme clause specifies |
| def-pc-module-pullback | Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction | AlgebraicGeometry.Scheme.Modules.tensorPullback, publicly imported from the upstream real tensor construction |
| def-sfb-dominant-function-field-map | Sheaf.TraceFormula.LocalDimensionFormula | AlgebraicGeometry.Scheme.Hom.dominantFunctionFieldAlgebra |
| lem-weil-pbc-invertible-pullback-tensor | WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor | AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor, first conjunct, second clause |

The last already-landed node is added to `stmt_deps` because its invertibility clause
occurs in the signature, as allowed for landed dependencies by brief-stage2 §5.
There are no new or dependency-module node copies. Public imports supply the recorded
statement interfaces (some through their public transitive imports); plain imports supply
the already-stated proof dependencies: properness and Noetherian results, coherent higher
images, Euler additivity, projection formula, higher-image restriction, and the numerical
polynomial leading term. Snapper is already a public dependency of IntersectionNumber.
`lem-sfb-equal-dimension-generic-structure-image` has no Lean record and is a proof-only
prerequisite: its proof plan is included in the theorem docstring and it is not imported.
It is not needed to type this stage-2 statement. No import cycle is introduced.

The docstring gives all four accepted proof steps: Euler--Leray plus projection formula;
lower-dimensional support in the nondominant case; finite generic extension and removal of
higher images in the dominant case; and generic multiplicity followed by coefficient
extraction. Every postponed theorem in this delivery is the one matching the item node.

Edge cases checked against Stacks Varieties Tag 0BET in the local source:

- Identity: canonical degree one and equal self-intersections.
- A constant morphism in positive dimension: the nondominant branch, giving zero.
- A birational proper nonfinite morphism, such as a surface blow-up: degree one;
  no finite-morphism assumption excludes it.
- Frobenius on the projective line over the prime field: purely inseparable degree p,
  not separable degree one. `Module.finrank` records the full extension degree.
- g = 1 is allowed; g = 0 is excluded exactly by the node's g ≥ 1 hypothesis.
  Empty schemes are excluded by the node and by `IsIntegral`.
- A trivial or torsion line bundle is allowed; the formula imposes no positivity claim.
- Finite and imperfect ground fields are allowed. No claim of separability is introduced.

Searches made with the prescribed wrapper (no exact statement found):

- LeanFinder: “Top self intersection number of a pulled back line bundle under a proper
  variety morphism”: eight hits on proper pullback projections, ranges and scheme images;
  none states intersection-number pullback.
- LeanSearch: “The intersection number of the pullback of an invertible module along a
  proper morphism is multiplied by the degree of the function field extension”: eight
  hits on ideal norms, projective charts, ramification, relative field rank and field
  inseparable degrees; none is this result.
- Loogle: `AlgebraicGeometry.Scheme.Modules.selfIntersectionNumber, Module.Finite,
  Module.finrank`: zero hits, unknown identifier for the project-only intersection number.
- msearch grep: `selfIntersectionNumber|intersectionNumber.*pullback|pullback.*intersectionNumber`:
  zero Mathlib hits.
- rg over Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for
  `selfIntersectionNumber_tensorPullback|selfIntersectionNumber|intersectionNumber.*pullback|pullback.*intersectionNumber`:
  only the existing IntersectionNumber definition and an unrelated top-dimensional
  reduction-intersection consumer; no pullback theorem or name clash.
- rg for tensorPullback and invertibility found the existing upstream
  `invertible_pullback_tensor`; its full signature and documentation were read and its
  first conjunct used. It avoids adding an invertibility assumption or helper theorem.
- rg for this item id in WeilConjectures and Sheaf found no existing Lean statement.

Validation: the delivered module compiled in both sandbox and library modes through
`scompile.py`, cleanly (15.3 s and 24.1 s respectively). All theorem proofs in this
stage-2 module are `sorry`; there are no new definitions. The node JSON is indented by
one space, Unicode preserved, with a final newline and the signature verbatim from the file.

No statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
