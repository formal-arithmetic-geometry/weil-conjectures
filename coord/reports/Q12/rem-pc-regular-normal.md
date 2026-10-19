## Worker report

The module `Sheaf.AlgebraicGeometry.RegularNormalDecomposition` states
`AlgebraicGeometry.regular_normal_and_normal_decomposition` for a scheme `X`, with one
`sorry` proof. It has no definitions, no statement correction, no new nodes, and no
dependency-module repair. The theorem docstring records the seven source proof steps
from Stacks Tags 0569, 02IT, and 033M.

The Lean statement renders the node clause by clause:

- The scheme is `X : Scheme.{u}`. The regular hypothesis is the recorded affine-cover
  form from `def-weil-regular-scheme`: `∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens)
  ∧ IsRegularRing Γ(X, U)`. The first conclusion is normality at every point, written
  `∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed
  (X.presheaf.stalk x)`, using the recorded normal-domain conjunction.
- The Noetherian hypothesis in (2) is exactly `IsNoetherian X`, which includes local
  Noetherianity and quasi-compactness in Mathlib. Its normality hypothesis repeats the
  same pointwise stalk conjunction, with no extra assumptions.
- The decomposition conclusion is `∃ (n : ℕ) (U : Fin n → X.Opens)`. Its clauses are,
  in order: `Set.range (fun i : Fin n ↦ (U i : Set X)) = irreducibleComponents X`;
  every component is closed; distinct components are disjoint; their supremum is `⊤`;
  each `(U i).toScheme` is `IsIntegral` and every one of its stalks is a domain and
  integrally closed; and `Nonempty (IsColimit (Cofan.mk X (fun i : Fin n ↦ (U i).ι)))`,
  which specifies the canonical scheme coproduct with the open inclusions as legs.
- The final implication is exactly the node's (3): the same regular affine-cover
  hypothesis, then `IsNoetherian X`, `Nonempty X`, and `PreconnectedSpace X`, imply
  `IrreducibleSpace X`. Nonemptiness is explicit, so the empty connected scheme does
  not incorrectly imply irreducibility.

The statement dependencies used are:

- `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`, for schemes and open
  subschemes/morphisms.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, declaration
  `IsIntegrallyClosed` (with `IsDomain` for the normal-domain conjunction).
- `Mathlib.RingTheory.RegularLocalRing.Defs`, declaration `IsRegularRing` (and its
  recorded companion `IsRegularLocalRing`), for the affine regular-ring condition.
- `Mathlib.AlgebraicGeometry.Noetherian`, declaration
  `AlgebraicGeometry.IsLocallyNoetherian` and the Mathlib `IsNoetherian` scheme class.
  The recorded `pqf-def-locnoeth` match supplies the locally Noetherian meaning and its
  affine-cover equivalence.
- `Mathlib.AlgebraicGeometry.Properties`, declaration `AlgebraicGeometry.IsIntegral`,
  for the integral open components.
- The `def-weil-irreducible-components` Mathlib match `irreducibleComponents` from
  `Mathlib.Topology.Irreducible`, together with `IsClosed` and `IsIrreducible`.
- The coproduct conclusion uses Mathlib category-theory limits (`IsColimit` and
  `Cofan.mk`), imported from `Mathlib.CategoryTheory.Limits.Shapes.Products`.

The module also imports the recorded proof-dependency modules
`Sheaf.RingTheory.RegularRingNormal` and
`Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`, plus the Mathlib
modules needed by the documented proof route. These imports are retained so the stage-3
proof plan is visible even though this stage leaves the proof as `sorry`.

Edge cases checked before drafting include the empty scheme and empty affine cover in
(1), the empty component index (`n = 0`) and empty coproduct in (2), repeated or
intersecting candidate opens (ruled out by the stated disjointness clause), and the
empty connected scheme in (3), which is excluded by `Nonempty X`. No finite-index,
nonempty, separated, characteristic, or universe-equality assumption was added.

Searches for an existing combined declaration (2026-10-17):

- `msearch.py Q12 rem-pc-regular-normal leanfinder "Regular schemes are normal; Noetherian normal schemes decompose into finite disjoint union normal integral components"`: eight hits, including `AlgebraicGeometry.IsIntegral` and finite-component results, but no combined regular-normal/decomposition theorem.
- `msearch.py Q12 rem-pc-regular-normal loogle "regular_normal_and_normal_decomposition, IsNormalScheme"`: zero hits; the proposed name is unknown.
- `msearch.py Q12 rem-pc-regular-normal grep "regular_normal_and_normal_decomposition|normal decomposition" Mathlib/AlgebraicGeometry`: zero hits.
- `rg` over `WeilConjectures` and `lean/Sheaf` found no other declaration with this theorem name; the only matching project file is this module. The Mathlib candidates are partial (`IsIntegral`, finite irreducible components, reducedness) and do not state the three clauses together, so a new theorem module is required.

No `STATEMENT-DISPUTED` flag or node fault remains. The required single-file
`scompile.py` check passed with no errors or non-sorry warnings.

## Second reading by Q12

I reread the node, all six statement-dependency records, and the complete Lean signature.
The regular, Noetherian, normal, component, integral, and nonempty/connected hypotheses
are all present exactly once; every decomposition clause is present in the node's order.
The `Fin n` family and `Cofan.mk` legs retain the canonical open-subscheme structure,
and the empty case is represented by `n = 0`. No mismatch was found and no statement was
changed. Independent review is performed by the maintainer under the direct-delivery
workflow.

## Validation

`scompile.py Q12 rem-pc-regular-normal` compiled the sandbox file and the corresponding
library file successfully, each within the 60-second per-file limit. The required
`deliver2.py --no-push` dry run is the next validation step.
