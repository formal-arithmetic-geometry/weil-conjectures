## Worker report

The module `Sheaf.Paper.CoefficientHeartCurveComplement` states
`AlgebraicGeometry.ProEtale.coefficientHeart_curve_complement`, with proof `by sorry`.
It introduces no definitions, auxiliary theorems, axioms, or replacement coefficient
operations. All variables and the universe `u` are explicit; `autoImplicit` is false.

The node's statement is unchanged. Its `stmt_deps` gains the already stated
`def-sfb-module-open-lower-shriek-adjunction`, as requested in the current stage-1
review, to identify precisely the counit appearing in the signature. This is the
addition of an existing landed node allowed by brief-stage2 section 5. All other
non-`lean` fields are unchanged, including the seven-step proof and its dependencies.
No repair note for this item exists. The previous worker's stage-1 split/review
objection does not prevent stage 2 from stating this reviewed node.

Sources read: the current node and every statement dependency; blueprint
main-20261015 `sk-lem-coefficient-heart/_section.md`, final curve paragraph, and its
proof file; Stacks `schemes.tex`, `lemma-reduced-closed-subscheme` (01J3),
`properties.tex`, `lemma-locally-Noetherian-dimension-0` (0AAX), and `proetale.tex`,
`lemma-ses-associated-to-open` (09AH). The current proof file spells out the general
filtration; its final curve specialization is in `_section.md`. The node explicitly
isolates the general coefficient localization input needed for that specialization.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Any commutative condensed ring | `Λ : Profinite.CondensedRing.{u}` and `[IsCommMonObj Λ.X]`. The existing transparent abbreviation is `Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u+1})`; no presentation by a topological ring is assumed. |
| Scheme X | `X : Scheme.{u}`. |
| Noetherian, meaning locally Noetherian and quasi-compact | `[IsLocallyNoetherian X] [CompactSpace X]`, exactly those two hypotheses. |
| Topological Krull dimension at most one | `hdim : topologicalKrullDim X ≤ 1`, with values in `WithBot ℕ∞`, so the empty scheme is included. |
| Open subset U and its inclusion u | `U : X.Opens`, with the canonical scheme open immersion `U.ι : U.toScheme ⟶ X`. |
| U contains every component's generic point | `hU : ∀ C ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η C → η ∈ U`. Schemes are sober and T0, so these are precisely their component generic points. |
| The reduced induced closed subscheme i:Z→X on X minus U | `Z : Scheme.{u}`, `i : Z ⟶ X`, `[IsClosedImmersion i] [IsReduced Z]`, and `hi : Set.range i = (U : Set X)ᶜ`. These are exactly the unique-characterization hypotheses of `reduced_induced_closed_subscheme`, clause (3), and Stacks 01J3. They name any presentation of that uniquely determined closed subscheme; they do not require X to be reduced or select an arbitrary coefficient map. |
| Any internal module over Λ_X=p_X^*Λ | `F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) (condensedRingObj Λ.X X)`. The existing `condensedRingObj` is the underlying coefficient ring from `coefficientRing`. |
| dim Z≤0 | `topologicalKrullDim Z ≤ 0`. |
| Its underlying set is finite | `Finite Z`, a proposition about the underlying type of scheme points, without choosing an enumeration or a nonempty witness. |
| Every point is closed in X | `∀ z : Z, IsClosed ({i z} : Set X)`. The closed immersion identifies these precisely with the points of the complement via `hi`. |
| The first arrow is the actual adjunction counit | `(CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ.X U.ι).counit.app F`, whose source is the actual `u_!u^*F`. |
| The second arrow is the actual adjunction unit | `(CondensedRing.upperStarLowerStarAdjunction Λ.X i).unit.app F`, whose target is the actual `i_*i^*F`. |
| Short exact sequence 0→u_!u^*F→F→i_*i^*F→0 | `Mono` of that counit, `Epi` of that unit, and `(ComposableArrows.mk₂ counit unit).Exact`. In this abelian module category this expresses exactly short exactness, including zero composite and image equal to kernel. |
| u^*i_*i^*F=0 | `IsZero ((CondensedRing.upperStar Λ.X U.ι).obj ((CondensedRing.lowerStar Λ.X i).obj ((CondensedRing.upperStar Λ.X i).obj F)))`. |
| In particular, if u^*F is lisse, extension by u_!L, L=u^*F, with finite closed support quotient | The same universally quantified sequence, with `L := (CondensedRing.upperStar Λ.X U.ι).obj F` and `G := (CondensedRing.upperStar Λ.X i).obj F`, has exactly those terms. The last conjunct says its quotient `i_*G` restricts to zero on U, and the geometric conjuncts say its supporting complement is finite closed points. If `IsLisseCoefficientModule Λ.X L` holds, this is precisely the stated lisse extension. No lisse hypothesis is imposed on the general localization statement, and no second exactness predicate is introduced for this immediate substitution. |

Dependency declarations read and used (publicly imported directly or transitively):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj`, and its commutative monoid instance.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its module-object
  structure and action-compatible morphisms, specialized to pro-etale abelian sheaves.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar`, `lowerStar`, and
  `upperStarLowerStarAdjunction`. The definitions really perform scalar extension
  along α and restriction along its mate η, respectively.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.Topology.Sober`: `IsGenericPoint` (closure of the singleton equals C).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  instantiated by `U.ι`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  especially its existence and unique-isomorphism characterization.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek` and
  `openImmersionLowerShriekUpperStarAdjunction`. The source was read through the
  restriction/coextension composite defining the adjunction, so its counit is pinned.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`. Its pro-etale cover and
  `Mod.IsFree` definitions were read; the latter requires an isomorphism with a
  finite free module of some natural-number rank, including zero.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff assumption).

Proof-only imports record the plan without exposing proof dependencies:
`WeilConjectures.Mathlib.Topology.KrullDimension`,
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`,
`Sheaf.CategoryTheory.SheafTensor`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`,
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations`, and
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafClosedLocalization`.
The last module's arbitrary-ring localization statement was read; it supplies the
specified counit/unit exactness before cancellation of scalar-change equivalences.
Other proof dependencies are already publicly available through statement imports.
The theorem docstring follows all seven proof steps and names their DAG inputs.

Edge cases checked mathematically before writing:

- Empty X: component/generic-point condition is vacuous, Z is empty, its dimension
  is minus infinity (hence at most zero), and every module term is zero.
- Empty complement (U=X): Z is empty and the exact sequence reduces to the open
  counit isomorphism with zero quotient. No nonempty binder excludes this.
- Empty U: a nonempty scheme has a component with a generic point, contradicting hU;
  thus precisely the allowed empty-X case remains.
- F=0, the zero condensed ring, and locally free rank zero are all permitted.
- A reducible curve with an isolated zero-dimensional component: hU must include
  its generic point, so it cannot be accidentally left in the complement. No
  `IrreducibleSpace` or `IsIntegral` assumption is present.
- Nonreduced X is allowed; only the induced closed scheme Z is required reduced.
- A DVR with U its generic point gives the single closed-point complement. Removing
  finitely many closed points from an affine line gives the usual finite complement.
- No field, characteristic, coefficient admissibility, finite-rank, constructibility,
  connectedness, or separatedness assumption is imposed. Quasi-separatedness and
  quasi-compactness of U.ι used by the proof follow from the stated Noetherian hypotheses.

Searches performed in this run:

- `msearch.py ... leanfinder`, query: `Noetherian scheme dimension at most one open
  containing generic points finite closed complement and exact module open closed
  localization sequence`. Eight hits: `AlgebraicGeometry.IsNoetherian`,
  `IsLocallyArtinian.of_topologicalKrullDim_le_zero`, `IsNoetherian.toIsLocallyNoetherian`,
  `IsLocallyNoetherian`, `IsLocallyArtinian`, `finite_irreducibleComponents_of_isNoetherian`,
  `instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier`, and
  `IsLocallyNoetherian.quasiSeparatedSpace`. None states the combined coefficient-module result.
- `msearch.py ... loogle`, query: `topologicalKrullDim, CompactSpace`: zero hits.
- `msearch.py ... grep`, query: `finite_compl|openClosed|closedLocalization`, subdirectory
  `Topology`: two unrelated `infinite_compl` hits in `Irreducible.lean` and
  `Compactification/OnePoint/Basic.lean`; no match.
- Source `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `curveComplement|curve_complement|finite.*[Cc]omplement|lem-sfb-coefficient-heart-curve-complement`
  finds related finite-complement geometry and the parent `CoefficientHeart` assertion,
  but no declaration of this result. Its parent requires a constructible sheaf and
  special coefficients, and asserts existence of a dense lisse open; this node
  instead takes a specified open and every coefficient ring/module.
- Exact-name/source-id search in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `curveComplement|curve_complement|coefficientHeart_curve|coefficientHeartCurveComplement|lem-sfb-coefficient-heart-curve-complement`
  returns no hits. There is no declaration-name collision.
- Mathlib source searches located the recorded definitions of dimension, generic
  points, components, open immersions, local Noetherianity, compactness and module
  objects. Upstream searches located the existing finite-rank `Mod.IsFree`, scalar
  functors, reduced-induced theorem and both specified adjunctions; these are reused.

No statement fault or disputed mathematical assertion was found. No new node or
dependency replacement module is needed. The Lean signature is copied verbatim to
the node's `lean.statement`. The clean `scompile.py` run checked both sandbox and
library module names under the required 60-second per-file limit (8.4 s and 11.2 s),
with no warnings or errors; the only proof body is `sorry` as stage 2 requires.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
