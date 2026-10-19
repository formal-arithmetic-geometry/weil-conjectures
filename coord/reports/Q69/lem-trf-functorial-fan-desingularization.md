## Worker report

The module `Sheaf.AlgebraicGeometry.FunctorialFanDesingularization` states
`AlgebraicGeometry.FineFan.exists_smoothFunctorialDesingularization`, with its sole
proof `sorry`. The conclusion is `Nonempty (SmoothFunctorialDesingularization.{u})`.
This asserts the existence of the entire rule, rather than separately chosen resolutions
for individual fans. No definition, dependency record, or natural-language statement changes.

I read the item and its statement dependency, the complete dependency module and its
recorded declaration/docstrings, and ILO Exposé VIII 3.1.26--3.1.28 and 3.2.19--3.2.21
in the source PDF. The current published source was also checked with `scompile.py --source`.
The theorem docstring carries all five steps of the node's natural-language proof.

Clause-by-clause correspondence, using the recorded dependency module
`Sheaf.AlgebraicGeometry.FineFanBlowup`, namespace `AlgebraicGeometry.FineFan`:

- “There exists a smooth-functorial saturated desingularization” is exactly `Nonempty
  (SmoothFunctorialDesingularization.{u})`. The same witness supplies `resolution` on
  every `ResolutionInput.{u}` and `comparison` on all smooth morphisms.
- “Fine torsion-free fans with finite affine covers” is precisely `ResolutionInput`:
  its `fan : Fan` has fine affine charts and sharp stalks; `torsionFree` is
  `fan.IsTorsionFree`, and `finiteCover` is `fan.HasFiniteAffineCover`. There is no
  extra saturatedness, separatedness, connectedness, or nonemptiness assumption.
- “Finite tower of saturated blowups” is `Resolution.length : ℕ` and
  `Resolution.tower : Tower length`, with `Resolution.base` fixing level zero.
  `Tower.arrow` and `Tower.blowup` describe each actual saturated blowup by the
  prescribed affine charts and gluing in `IsSaturatedBlowup` and `BlowupPatch`.
- “Along nonempty coherent monoid ideals” is `Tower.center` and the first conjunct of
  `IsSaturatedBlowup`, namely `IsNonemptyCoherentIdeal`. Its finite nonempty local
  generating lists and ideal-subsheaf conditions are explicit in that dependency.
- “Smooth last fan” is `Resolution.smooth` at `Fin.last length`; `Fan.IsSmooth`
  identifies each stalk with the monoid `Multiplicative (Fin r → ℕ)` for finite `r`.
- “For a smooth morphism g : G → F” is the `comparison` field's arbitrary
  `g : Hom G.fan F.fan` and `g.IsSmooth`. `Hom` retains locality, continuity and
  section maps; `Hom.IsSmooth` is the stated product inclusion on stalks.
- “Canonically the contraction of the pulled-back tower” is `ResolutionComparison`:
  `pulled` and `pullback : PullbackTower` specify the recursive blowup tower with
  pulled-back centers, `baseMap` fixes its map over `g`, and `contraction` together
  with `baseIso` supplies the specified identification over the original source fan.
- “Retaining the centers and their order” is `Contraction.index`, an ordered
  surjection, with `adjacent`, `keptMap` and `keptCenter`. `deleted` deletes exactly
  whole-ideal isomorphisms, and `deletedMap` records the collapsed arrows.
- “Identifications respect composition” is `compositionIndex` and `compositionMap`;
  `identityIndex` and `identityMap` include identity compatibility. `HEq` transports
  only the level types determined by the required index equalities.
- “Apply also to open localizations, isomorphisms, and inclusions into finite disjoint
  unions” is a specialization of the same unrestricted `comparison`: these maps have
  stalk isomorphisms, so `Hom.IsSmooth` holds with `r = 0`. The domain includes their
  fine torsion-free sources and finite disjoint unions with finite affine covers.
  No separate comparison or choice is introduced for these cases.

The four other proof dependencies (`lem-trf-toric-normalized-desingularization`,
`def-trf-monoscheme-toric-realization`, `lem-trf-toric-monoid-comparison`, and
`lem-trf-sharpening-fan-bijection`) have no Lean records, Mathlib matches, or closed
upstream audit declarations in the current DAG. Their future proof imports are therefore
not available; the proof docstring names their exact roles. The only available
statement/proof dependency is imported in the transitive legacy format. The new file uses ordinary
`import` and omits the `module` command because the recorded dependency is a non-`module` file; the first compile
reported this incompatibility, which was corrected without changing the dependency.

Edge cases checked against the actual structure fields before writing:

- `length = 0` is allowed: `Fin 0` gives no centers/arrows and a single terminal/base level.
- The empty fan is included: its finite affine cover may have length zero, and its
  stalk conditions are vacuous. Nonempty centers are locally nonempty, not a
  requirement of a globally inhabited fan.
- Disconnected fans and finite disjoint unions are included, without a connectedness
  hypothesis. Functoriality restricts the synchronized global tower to each component.
- Rank zero stalks are allowed, as `Fin 0 → ℕ` is the trivial monoid; hence the named
  localizations and isomorphisms are covered by smooth rank-zero maps.
- The input need not be saturated. `Contraction.deleted` requires both a whole center
  and an isomorphism, so an initial nontrivial saturation cannot be discarded.
- `u` is explicitly declared and unconstrained. The theorem asserts the rule at every
  universe level of the dependency, with no additional independent universe constraint.

Searches for an existing statement (all returned types inspected):

- `msearch.py leanfinder`: “There exists a smooth functorial saturated desingularization
  of every fine torsion free Kato fan with a finite affine cover”. Eight results concerned
  ordinary scheme affine transition limits, smooth scheme morphisms, or normalization;
  none asserts monoidal fan resolution.
- `msearch.py leansearch`: “There exists a smooth functorial desingularization of finite
  fine torsion free monoidal fans by saturated blowups”. Eight results concerned scheme
  smoothness, free monoidal-category coherence, and smooth manifold monoid morphisms;
  none matches.
- `msearch.py loogle`: `"desingularization"`; zero hits.
- `msearch.py grep`: `desingulari[sz]|KatoFan|SmoothFunctorialDesingularization`;
  zero Mathlib hits.
- `rg` in upstream `WeilConjectures`, Mathlib, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for `SmoothFunctorialDesingularization`,
  `exists_smoothFunctorialDesingularization`, `KatoFan`, and
  `functorial.*fan.*desingular`: only the recorded structure in `FineFanBlowup` and a
  future-proof mention in `MonoidalResolutionTower`. The structure supplies the
  notion, not its existence theorem.
- `grep -rn` for the exact item id in upstream `WeilConjectures`: no result.
- No repair note for this item was present in `coord/repair-notes`.

No statement fault or dispute was found. No additional nodes or dependency modules are needed.

Validation: the final single-file compilation is run through `scompile.py`; the dry-run
and final delivery are run through `deliver2.py`. The maintainer supplies the independent
mathematical review; this report is the author's own correspondence check.

## Second reading by Q69

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
