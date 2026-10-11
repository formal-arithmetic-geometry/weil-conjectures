## Worker report

The module Sheaf.AlgebraicGeometry.EtaleZariskiCohomology states all clauses of
lem-sc-ga-cohomology in three declarations, each with a sorry proof. No definition
is added, no statement is corrected, and no dependency record is replaced.

Hypothesis and clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]` in
  each declaration.
- The curve over k is `{C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]` in
  the first two declarations. The recorded IsCurve class extends IsSeparated,
  LocallyOfFiniteType and QuasiCompact, and has topologicalKrullDim C ≤ 1. Thus
  it gives exactly separated, finite type and dimension at most one.
- Every quasi-coherent O_C-module is `(F : C.Modules) [F.IsQuasicoherent]` in
  etale_zariski_cohomology_agree. This is Mathlib's SheafOfModules.IsQuasicoherent,
  the existing notion documented by pqf-def-coherent. The node's coherent and
  finite-type notions are not hypotheses here.
- Its associated étale sheaf is exactly Scheme.Modules.etaleTensorSectionsSheaf F,
  using the recorded dependency, not a new sheafification or an arbitrary sheaf.
  Its source declaration retains sections Γ(U,u^*F) with the specified restrictions.
- Every q ≥ 0 is `(q : ℕ)`. The first theorem asserts Nonempty of an additive
  equivalence from Sheaf.H of that sheaf in degree q to the underlying additive
  group of `(RingedSpace.moduleCohomology C.toRingedSpace q).obj F`.
  This is an isomorphism of the two cohomology groups, with the node's orientation.
- For G_a = (O_C)_et, etale_ga_cohomology_agree repeats that conclusion with
  F literally Scheme.Modules.unit C, the existing structure module. The associated
  sheaf is therefore the additive sheaf with Γ(U,O_U) sections, as in the node.
  Its quasi-coherence is supplied explicitly by the upstream
  SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf), not by an extra hypothesis.
- The last theorem has `[IsConnectedCurve f] [Smooth f]`. IsConnectedCurve extends
  IsCurve and requires ConnectedSpace C and dimension exactly one, matching the
  recorded meaning of connected curve (including nonemptiness).
- `(q : ℕ) (hq : 2 ≤ q)` is precisely the final degree condition. The conclusion
  is the conjunction of Subsingleton of the same étale and Zariski structure-module
  cohomology groups. Each group has zero, so Subsingleton means that it is zero.
  No vanishing is claimed in degrees zero or one; no properness is assumed.

Dependency declarations read and used:

- def-sc-curves: WeilConjectures.AlgebraicGeometry.Curve,
  AlgebraicGeometry.IsCurve and IsConnectedCurve; the class signatures and
  docstrings were read. Smoothness is Mathlib's Smooth on f.
- pqf-def-coherent: Sheaf.AlgebraicGeometry.Coherent documents that quasi-coherent
  is Mathlib's SheafOfModules.IsQuasicoherent. Its full signature and docstring in
  Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent were read. IsCoherent
  itself is irrelevant to this statement, which assumes only quasi-coherence.
- def-sc-etale-qcoherent-module: Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf,
  AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf, imported directly.
- def-weil-pbc-etale-cohomology: WeilConjectures.SixFunctors.Etale.Derived.LowerShriek,
  AlgebraicGeometry.Etale.cohomology and rightDerivedGlobalSections were read.
  The dependency's record and STATE's ÉTALE COHOMOLOGY convention explicitly
  prescribe Sheaf.H F q for sheaf-valued citers and a stage-3 bridge to cohomology
  applied to singleFunctor 0. This module follows that prescription without wrappers.
  The import of UpperLowerStar.TopologicalInvariance supplies the standard Sheaf.H
  instance setup, as in the landed EtaleAffineQcoherent module.
- pqf-def-cohomology: Sheaf.Paper.PQFCohomology,
  AlgebraicGeometry.sheafCohomologyAndHigherDirectImages was read. It uses the
  existing RingedSpace.moduleCohomology, defined in and imported directly from
  Sheaf.Topology.RingedSpaceModuleCohomology as the right derived global-sections
  functor on O_C-modules. That declaration and globalSectionsFunctor were read.
- The structure module is Scheme.Modules.unit from the upstream
  WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf, definitionally
  SheafOfModules.unit C.ringCatSheaf. Its quasi-coherence proof comes from
  WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent (imported).

Edge cases checked: q = 0 and q = 1 retain the comparison and do not trigger
vanishing; q = 2 does trigger it. The first two theorems allow an empty,
disconnected or zero-dimensional curve via IsCurve, while the last uses the
recorded connected dimension-one meaning. Zero modules are included; no coherence,
finite generation or properness is required. No restriction on characteristic is
introduced. The field, scheme and module universe u is arbitrary, including zero;
all universes and variables are explicitly bound. The comparisons are only of
additive groups, as the node states, rather than of modules over unrelated rings.

Searches performed with msearch.py U1 lem-sc-ga-cohomology:

- LeanFinder: "etale Zariski cohomology comparison quasi coherent module" returned
  eight hits, including SheafOfModules.IsQuasicoherent and unrelated étale algebra
  results; no comparison theorem.
- Loogle: "CategoryTheory.Sheaf.H, AlgebraicGeometry.IsCurve" returned zero hits
  (IsCurve is not in the Mathlib index).
- LeanSearch: "etale Zariski cohomology quasi coherent sheaves" was unavailable
  with Internal Server Error; no mathematical verdict is inferred from this failure.
- grep: "etale.*[Zz]ariski|[Zz]ariski.*etale" returned three topology results in
  Mathlib (WeaklyEtale local properties and zariskiTopology_le_etaleTopology),
  none a cohomology comparison.
- rg of WeilConjectures and lean/Sheaf for the comparison, cohomology and additive
  group names found the upstream ArtinSchreier TODO, the landed affine acyclicity
  statement, and other cohomology statements, but no declaration giving this node's
  comparisons and final vanishings. grep by the exact blueprint id in
  WeilConjectures found none. Exact searches of all three proposed declaration
  names in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  found none.

The source files named in the node are not copied into this checkout. I read the
primary Stacks pages https://stacks.math.columbia.edu/tag/03DW (part 2) and
https://stacks.math.columbia.edu/tag/02UZ. They give the comparison and the
Noetherian dimension vanishing used in the node's three proof steps; these steps
are reproduced in the declaration docstrings. The comparison node already in the
DAG is a general proof input, not a duplicate full statement of this curve node.

The previous sandbox attempted only the first clause and timed out with a different
instance/import setup and a raised instance limit. The repaired file uses the landed
affine statement's Sheaf.H import setup, no extra hypotheses, no raised heartbeat
limits, and passes local compilation cleanly (9.6 seconds). All three proofs are
sorry, as required for stage 2. No node fault or statement dispute was found.

## Second reading by U1

I read `dag/nodes/sec-curve-estimates/lem-sc-ga-cohomology.json` and the complete
module independently. The node introduces an algebraically closed field `k`, a scheme
`C` with structure morphism `f`, and the `[IsCurve f]` hypothesis. The first Lean
declaration renders these as `{k : Type u} [Field k] [IsAlgClosed k]`, `{C :
Scheme.{u}}`, `(f : C ⟶ Spec (.of k)) [IsCurve f]`; the `IsCurve` declaration read from
`WeilConjectures.AlgebraicGeometry.Curve` supplies separated, finite type, and
dimension at most one exactly as required. It introduces `(F : C.Modules)
[F.IsQuasicoherent]`, matching the node's quasi-coherent module, and uses the recorded
`Scheme.Modules.etaleTensorSectionsSheaf F` for the associated small-etale sheaf.

The first conclusion clause, for every `q ≥ 0`, is rendered by `(q : ℕ)` and
`Nonempty (Sheaf.H (...) q ≃+ ((RingedSpace.moduleCohomology C.toRingedSpace q).obj F))`.
Natural-number degrees are precisely the nonnegative degrees, and `Nonempty` of an
additive equivalence expresses the node's isomorphism with the stated orientation.
The second declaration specializes `F` to `Scheme.Modules.unit C` and supplies the
recorded `SheafOfModules.isQuasicoherent_unit`; it therefore renders the node's
`G_a = (O_C)_et` clause without adding a hypothesis. The final declaration adds
`[IsConnectedCurve f] [Smooth f]`, `(q : ℕ) (hq : 2 ≤ q)`, and concludes the conjunction
of `Subsingleton` for the same etale and Zariski groups, exactly the node's two
vanishings. No clause, quantifier, or hypothesis was missing or strengthened.

Edge cases checked explicitly: `q = 0` and `q = 1` satisfy the comparison and do not
satisfy `2 ≤ q`; `q = 2` activates vanishing. `IsCurve` permits empty, disconnected,
and zero-dimensional schemes, while `IsConnectedCurve` supplies connectedness and
dimension one (and hence nonemptiness). The zero module is allowed, characteristic is
unrestricted, and the shared universe `u` includes `0`. No properness, coherence, or
finite-generation assumption appears. The empty scheme and zero-dimensional cases
remain covered by the comparison declaration.

Searches were rechecked with `msearch.py` (LeanFinder query “etale Zariski cohomology
comparison quasi coherent module”, Loogle query “CategoryTheory.Sheaf.H,
AlgebraicGeometry.IsCurve”, and LeanSearch query “etale Zariski cohomology
quasi-coherent sheaves”), plus `rg` in `WeilConjectures`, `lean/Sheaf`, Mathlib, and
`dag/lean_names_upstream.json`. Results contained only the existing component
definitions and unrelated topology/cohomology declarations; no declaration states
this comparison or the combined vanishing. LeanSearch returned a service error, which
does not affect the negative conclusions from the other searches.

No mismatch was found, so no Lean or node repair was needed. I compiled
`Sheaf/AlgebraicGeometry/EtaleZariskiCohomology.lean` locally successfully; all three
proofs remain `sorry` as required for stage 2, and all declaration variables and
universes are explicit.
