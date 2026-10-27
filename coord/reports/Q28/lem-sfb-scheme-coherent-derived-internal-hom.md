## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeCoherentDerivedInternalHom` states
`AlgebraicGeometry.scheme_coherent_derived_internal_hom`, with proof `sorry`.
Its source is Stacks Project, perfect.tex, Tag 0D0C,
`lemma-coherent-internal-hom`, read in full, including its two Ext spectral
sequences. It gives coherent cohomology and a global lower cohomological bound
for derived internal Hom. The accepted stage-1 split is unchanged. The old
BLOCKED ending referred to stage-1 re-splitting; the current stage-2 handoff
explicitly permits recording the missing Lean statement. The live node has no
Lean record and appears as stage 2 in coord/queue.tsv.

Hypothesis and conclusion correspondence:

- The locally Noetherian scheme is `(X : Scheme.{u}) [IsLocallyNoetherian X]`.
  Mathlib's every-affine-open definition is equivalent to the node's affine
  Noetherian cover definition, as recorded in pqf-def-locnoeth. There is no
  quasi-compactness or separatedness assumption.
- The Zariski module category is
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`. Here `moduleRings` is the
  existing structure sheaf viewed as a sheaf of rings, on `Opens X`, with its
  Zariski topology. This is the same carrier as `X.Modules`, and also the
  specialization of `ringedSiteModules` to that ringed site. No replacement
  category or Abelian structure is chosen.
- The unbounded derived category is `DerivedCategory` of that category.
  `[HasDerivedCategory.{w} ...]` records the chosen localization and its
  morphism universe, exactly as def-weil-abstract-derived-category requires.
  The universes `u w` are explicitly bound; `autoImplicit` is disabled.
- `(K L : DerivedCategory ...)` introduces the two objects, with no
  representative, bounded-complex or injectivity assumptions.
- `hK : ∀ j : ℤ, RingedSpace.IsCoherent ... (homologyFunctor ... j |>.obj K)`
  and the corresponding `hL` express coherence in EVERY integer degree.
  These are the exact finite-type/kernel coherence predicate of Stacks 01BV.
- `hK_bound : ∃ a : ℤ, ∀ j : ℤ, a < j → IsZero (...obj K)` is precisely
  vanishing for all sufficiently large degrees. The strict inequality leaves
  degree a unrestricted.
- `hL_bound : ∃ b : ℤ, ∀ j : ℤ, j < b → IsZero (...obj L)` is precisely
  vanishing for all sufficiently negative degrees. Degree b is unrestricted.
- The derived Hom object is
  `(derivedInternalHomOfUniverses.{u, u, u, w}
    (Opens.grothendieckTopology X) X.sheaf).obj (op K, L)`.
  This is the recorded dependency's existing Hom-complex localization with
  functorial K-injective replacement in the second argument. It is publicly
  available through the dependency's recorded
  `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` import. The ordinary
  ModuleCat abbreviation is not applied to sheaves. No second RHom is defined.
  The existing generic interface is used at equal universes for the Zariski
  opens; its `max u u u` is u, with no extra universe equality imposed.
- The first conclusion conjunct quantifies over all `j : ℤ` and applies
  `RingedSpace.IsCoherent` to the homology sheaf of exactly that RHom object.
- The second conclusion conjunct is `∃ b : ℤ, ∀ j : ℤ, j < b → IsZero ...`
  for the homology sheaves of the same object. It asserts exactly a global
  eventual lower vanishing bound, not an extra upper bound or a specified
  optimal lower bound.

The module docstring identifies the source; the theorem docstring carries all
five proof steps of the accepted DAG, with the named dependencies. Stage 3 can
restrict to Noetherian affine charts, pass to finite module cohomology via the
affine derived equivalence, use pseudo-coherence and the module RHom finiteness
calculation, and glue coherence and the uniform lower vanishing bound.

Statement dependencies read and used:

| Node | Module and declaration |
| --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian |
| def-weil-sheaf-of-modules-category | Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules; its existing SheafOfModules specialization |
| def-weil-abstract-derived-category | Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory |
| pqf-def-coherent | Live primary: Sheaf.AlgebraicGeometry.CoherentFiniteType / AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType. This theorem uses WeilConjectures.AlgebraicGeometry.Coherent / AlgebraicGeometry.RingedSpace.IsCoherent, equivalent on locally Noetherian X by AlgebraicGeometry.Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType. |
| def-pur-derived-internal-hom | Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom: publicly imports CategoryTheory.derivedInternalHomOfUniverses from Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses |

I read the full signatures and docstrings in the recorded source modules,
including the generic RHom construction and coherence predicate. The
cohomology functor is `DerivedCategory.homologyFunctor` from Mathlib's
DerivedCategory.HomologySequence. Every stated proof dependency is imported
with plain `import`, including the affine RHom and module-RHom results.
Statement dependencies use public imports. There are no new definition nodes,
no mathematical statement correction, and no disputed mathematical statement.

Edge cases checked before writing:

- Empty scheme: no nonemptiness or affine-chart choice is assumed; zero
  cohomology sheaves and the existential bounds make sense and hold.
- K=0 or L=0: the cohomology hypotheses and any chosen bounds allow this, and
  RHom is zero. Bounds a,b may be negative, zero or positive.
- A non-quasi-compact locally Noetherian scheme is included. The input bounds
  are global, and the affine proof yields the same b-a on every chart, so the
  output global bound needs no finite subcover.
- A coherent sheaf in degree zero gives coherent sheaf Ext in nonnegative
  degrees; degree zero is included in the coherence conclusion.
- K can be unbounded below; L can be unbounded above. No strict support bounds
  on chosen complexes are substituted for cohomological bounds.
- No regularity, properness, finite Krull dimension or characteristic
  restriction enters. Zariski opens have object and arrow universes u, so the
  existing arbitrary-universe RHom interface applies without size restriction.

Searches made for an existing exact statement:

- msearch.py, leanfinder: "Derived internal Hom of bounded above and bounded
  below coherent complexes on a locally noetherian scheme has coherent
  cohomology". Eight hits: derived IsLE/IsGE localization bounds, small shifted
  Hom and sheaf cohomology, but no coherent derived-internal-Hom theorem.
- msearch.py, leansearch: "Derived sheaf Hom of coherent bounded above and
  bounded below complexes has coherent cohomology on a locally Noetherian
  scheme". Eight hits including derived-category Hom bounds, small Ext and
  scheme-module Hom; none is this theorem.
- msearch.py, loogle: `AlgebraicGeometry, IsCoherent, DerivedCategory` returned
  no hits (unknown identifier AlgebraicGeometry). The follow-up query
  `"IsCoherent"` returned topological coherent-space declarations, not module
  coherence or this derived theorem.
- msearch.py, grep: `(coher.*(rhom|internal.hom))|((rhom|internal.hom).*coher)`
  returned zero Mathlib hits. An earlier grep `coherent.*internal.*hom` on
  WeilConjectures also returned zero hits.
- Direct rg of the same coherence/RHom patterns and the item id in
  lean/WeilConjectures and lean/Sheaf found the module-only algebra theorem
  BoundedAboveCoherentRHom, affine quasi-coherence statements, SheafExtCoherent,
  and the consumer ProperSchemeCoherentExtFinite. I read their statements:
  module finiteness, affine or pseudo-coherent quasi-coherence, and degree-zero
  sheaf Ext are not this general coherent-complex theorem. There is no exact
  already-stated theorem. The exact proposed declaration name was also absent
  from both project source roots, Mathlib and dag/lean_names_upstream.json.

Validation: scompile.py Q28 lem-sfb-scheme-coherent-derived-internal-hom compiled
both the sandbox module and its actual library module identity cleanly
(2.8 seconds each), with no errors and no unexpected warnings. All compilation
used the prescribed wrapper, against the published live server library.

## Return repair (H13)

The returned immutable head was `019f91fb3786`. Its saved packet passed the
required initial `deliver2.py --no-push` run (commit `7e60cceeda8`), but retained
the dependency-record replacement rejected by the maintainer. Removed the
sandbox copy of `dag/nodes/sec-abelian-varieties/pqf-def-coherent.json`; this
delivery therefore leaves its live Q25 primary record intact. No dependency
module or dependency-node update is delivered.

Added an item `lean.note`: `RingedSpace.IsCoherent` is exactly the Stacks 01BV
clause-3 predicate. On the locally Noetherian scheme assumed in this theorem,
it agrees with the live recorded `Scheme.Modules.IsQuasiCoherentFiniteType`:
the latter unfolds to quasi-coherent and finite type, and the existing
`Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType` in
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
is precisely this equivalence (Stacks 01XZ). That module is already imported
for the proof plan. The Lean file is byte-identical to the returned packet;
its hypotheses, conclusion, imports, proof docstring and sole `sorry` are
unchanged. The item differs from current main only in `lean`.

## Second reading by Q28

No second reading by a worker: the dispatcher starts this worker directly and
forbids spawning other agents. The maintainer's independent delivery review
provides the independent reading. This section does not claim such a reading.

## Repair self-check by Q28

Reread the saved module and current item statement against Stacks 0D0C,
`perfect.tex` lines 2682–2712. The match remains exact: arbitrary-universe
locally Noetherian X; the Zariski module-derived category with its localization
universe; K and L with coherent cohomology in every integer degree; an
existential global upper bound for K and lower bound for L; coherent
cohomology and an existential global lower bound for their canonical RHom.
No quasi-compactness is introduced, and empty X and zero K or L remain
included. The coherence bridge above resolves the recorded-interface issue
without changing the mathematical statement or any dependency record.

H11 advisory: this is a self-check by the repairing worker, not an independent
second reading. The dispatcher forbids starting agents; the section above
continues to say that plainly. The maintainer independently reviewed the
unchanged Lean statement in the return entry.

Repair validation (2026-10-23 UTC): the prescribed `scompile.py Q28
lem-sfb-scheme-coherent-derived-internal-hom` compiled both the sandbox identity
and actual library module identity in 2.8 seconds each, without errors or
unexpected warnings. Self-check confirms the node differs from current main
only in `lean`, the recorded signature is verbatim, every Lean line is within
100 characters, the only postponed proof is the named theorem's `sorry`, and
no dependency node is included. Unchanged Lean SHA256:
`c0257d24f3d5cf21c7c0d0dc91867dea43c6c94f6cec5acf75eb9f5a990a55df`.
