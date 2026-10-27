## Worker report

The module `Sheaf.AlgebraicGeometry.ReducedNoetherianBlowupGeometry` states
`AlgebraicGeometry.Scheme.IdealSheafData.reducedNoetherian_blowup_geometry`.
Its only theorem has proof `sorry`; there are no new definitions or helper theorems.
The item JSON changes only by adding `lean`. No statement correction or dependency
repair is needed, and no statement is disputed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A scheme X | `(X : Scheme.{u})`, with explicit arbitrary universe `u` |
| X is reduced | `[IsReduced X]`, the recorded sectionwise predicate, equivalent to reduced stalks |
| X is Noetherian, meaning a finite affine cover by Noetherian rings | `[IsNoetherian X]`; Mathlib's class is locally Noetherian plus `CompactSpace`. `isNoetherian_iff_of_finite_iSup_eq_top` identifies this with the node's convention; quasi-compactness extracts a finite subcover of the affine cover. |
| J is a quasi-coherent ideal in O_X | `(J : X.IdealSheafData)`; its affine ideals and localization compatibility encode precisely a quasi-coherent ideal. `J.toModules` is its existing actual ideal module. |
| J is coherent | `(hJ : RingedSpace.IsCoherent X.toRingedSpace J.toModules)`, including finite type and the finite-type-kernel condition, rather than only finite type |
| The ordinary blowup W and its structure map b | The recorded `J.blowup` and `J.blowupMap` from `WeilConjectures.Blowup.Gluing` |
| b is of finite type | `LocallyOfFiniteType J.blowupMap ∧ QuasiCompact J.blowupMap`, exactly the recorded convention of def-weil-finite-type-morphism |
| W is reduced | `IsReduced J.blowup` |
| W is Noetherian in the same convention | `IsNoetherian J.blowup`, using exactly the same Mathlib class as for X |
| No integrality, nowhere-density, excellence, dimension bound or ground field | No corresponding binders or restrictions occur. |
| Zero ideal, unit ideal and empty scheme allowed | There is no nonzero, proper-ideal, nonempty, dense-complement or surjectivity hypothesis. |

Statement dependency declarations read and used:

- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`; read also the stalk equivalence and
  `AlgebraicGeometry.affine_isReduced_iff`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`. The existing `AlgebraicGeometry.IsNoetherian`
  and its finite-affine-cover criterion render the explicitly stipulated global convention.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, the Noetherian condition on affine rings in the preceding class.
- `pqf-def-coherent`: its recorded module
  `Sheaf.AlgebraicGeometry.CoherentFiniteType` is publicly imported. Its recorded
  `AlgebraicGeometry.RingedSpace.IsCoherent` is defined in
  `WeilConjectures.AlgebraicGeometry.Coherent`, also publicly imported directly.
  The latter is the full coherence predicate; the module's
  `Scheme.Modules.IsQuasiCoherentFiniteType` alone would not state coherence.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `.blowupMap`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- Existing ideal-module bridge:
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`,
  `AlgebraicGeometry.Scheme.IdealSheafData.toModules`; the kernel construction has
  actual data and its affine sections identify with `J.ideal U`.

Proof dependencies are imported as plain imports when their modules are not already
public statement imports: blowup properness (`WeilConjectures.Blowup.Proper`), proper
morphisms, affine quasi-compactness and quasi-separatedness, scheme gluing, the finite
generator chart cover (`WeilConjectures.Blowup.FiniteDegree.Algebra`), the chart algebra,
and localization away. The remaining proof dependencies use the already public
Noetherian, properties, coherence and blowup-gluing modules. In particular the proof
imports include `isProper_blowupMap`, `LocallyOfFiniteType.isLocallyNoetherian`,
`QuasiCompact.compactSpace_of_compactSpace`, `blowupGluingData`, `blowupFunctor`,
the scheme gluing cover, `iSup_basicOpen_reesX_eq_top_of_span`, `chartRing`,
`Localization.Away`, and `affine_isReduced_iff`. The module docstring includes all six
proof steps from the node, including the localization calculation without cancellation.

Sources checked in the local Stacks source: Divisors `lemma-blow-up-reduced-scheme`
(0808) and `lemma-blowing-up-projective` (02NS); Morphisms
`lemma-finite-type-noetherian` (01T6); Properties `definition-noetherian` (01OV).
These require neither integrality nor a condition on the support of the center.

Edge cases checked before writing:

- J = 0: the Rees algebra has no positive part; equivalently the chart at 0 has
  zero coordinate ring. The blowup is empty, hence reduced and Noetherian, and its
  map is of finite type. No nonzero-ideal hypothesis is needed.
- J = O_X: the chart at 1 is the original affine scheme. The blowup map is the
  identity, so the three asserted conclusions hold.
- X empty, including an affine presentation by the zero ring: the blowup is empty;
  both the locally Noetherian and compactness conditions include this case.
- Reduced rings with zero divisors: for example k times k and the ideal generated
  by (1,0). The blowup can discard a component, so no surjectivity is asserted.
  The nilpotent-fraction argument uses a power annihilator, never cancellation.
- No assumption on dimension, characteristic, a ground field or nonemptiness is
  hidden in the universe or scheme type. There are no test-object universe binders.

Searches made for an existing complete statement (2026-10-24):

- `msearch.py leanfinder`, query `Blowup of a coherent ideal on a reduced Noetherian
  scheme is reduced Noetherian and of finite type`: 8 hits on locally Noetherian
  schemes, Noetherian Rees algebras and reduced normalization. None is the assertion
  about this ordinary global blowup.
- `msearch.py leansearch`, query `The ordinary blowup of a coherent ideal on a reduced
  Noetherian scheme is reduced Noetherian and of finite type`: 8 hits, including
  reducedness on stalks/open covers and finite-type Noetherian permanence, but no
  complete blowup statement.
- `msearch.py loogle`, query `"blowup", "IsReduced"`: 0 hits.
- `msearch.py grep`, query
  `(blowup|blowUp|Blowup).*(IsReduced|IsNoetherian|FiniteType)`, restricted to
  `AlgebraicGeometry`: 0 hits in Mathlib.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for blowup and reducedness,
  plus the proposed declaration name; `grep -rn` of the item ID in
  `lean/WeilConjectures`: no existing declaration of this complete statement and
  no conflicting proposed name. `NormalizedBlowupCalculus.lean` contains private
  reducedness lemmas, which neither give the complete statement nor provide a public
  interface. `reducedBlowup_generic_geometry` requires a finite-type rational scheme
  and dense complement; it excludes the zero ideal on a nonempty scheme, so it cannot
  be reused as this statement. `NoetherianNormalizedBlowupFinality.lean` is a different
  multi-clause result with generic-support restrictions and refers to this node in
  its proof. No new copy of any definition is introduced.

Validation: `scompile.py NR lem-per-reduced-noetherian-blowup-geometry` compiled the
delivered file in both sandbox and actual module-path modes successfully, 1.6 seconds
each, with no errors or unexpected warnings. The initial attempt found that the
coherence declaration was not visible through the dependency module's compiled public
interface; adding the direct owning-module import fixed it. The current server source
of the dependency was checked with `scompile.py --source` before this repair. All
variables and universes are explicit, with `autoImplicit false`, and no Lean line
exceeds 100 characters.

## Second reading by NR

A separate rereading by the same dispatched worker compared the unchanged node to the
finished module; no other agent was started. The maintainer supplies the independent
delivery review. The hypothesis check found precisely X, reducedness, global
Noetherianity, J as a quasi-coherent ideal and coherence of its associated module.
In particular this uses the full finite-type-kernel predicate, not the weaker
quasi-coherent finite-type conjunction. The conclusion check found finite type of
the structure map, reducedness of its source and global Noetherianity of its source.
The global Noetherian class, rather than only local Noetherianity or topological
Noetherianity, agrees with the node's finite affine cover convention. The zero and unit
ideal cases and empty scheme are included by the unrestricted ideal and scheme binders.
The theorem states the ordinary blowup, not its normalization; it asserts no density
or surjectivity. No mathematical changes were needed after this check; only the direct
coherence import was added to repair visibility. The declaration signature stored
in the JSON was extracted verbatim from the finished file up to, but excluding, `:=`.
The first dry run caught the inclusion of that delimiter in the record; it has been
removed to match the preflight signature format.
