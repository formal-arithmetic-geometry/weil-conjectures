## Worker report

This is a stage-2 statement delivery, not a resplitting of the reviewed stage-1
proof. The current item has a Q02 stage-1 `reviewed` record but no `lean` record.
Its statement, proof, proof dependencies and review are retained verbatim. The
only changes are its `lean` record and the addition of the new differential
module definition to `stmt_deps`.

`Sheaf.AlgebraicGeometry.LogSmoothDifferentialGenerators` states
`AlgebraicGeometry.EtaleLogHom.exists_logDifferential_generators`, with `sorry`
as its whole proof. Its two definition helpers construct the canonical
characteristic class and the image subgroup of the specified generators; no
arbitrary comparison homomorphism is assumed or chosen.

The statement follows ILO XVI Proposition 3.6.3, printed p.252, with the
modulo-units interpretation explained in Lemma 3.6.4, and X Proposition 1.2,
printed pp.136--138. The local PDF was opened at both passages. The stage-1
review already explains why taking the cokernel in the full log group would
be false: units must first be divided out. This delivery retains the reviewed
modulo-units statement.

Hypotheses and clauses, in order:

- Locally Noetherian fs log schemes are `X Y : FineSaturatedLogScheme.{u}`.
  The existing structure includes locality/Noetherianity and the fs chart
  condition; none is replaced by log regularity or an affine hypothesis.
- The log morphism is `f : EtaleLogHom X Y`; `hf : f.IsLogSmooth` is exactly
  the recorded chart-sense smoothness predicate, not ordinary smoothness.
- The fixed global base chart is `β : Q →* Y.logStructure.monoidSheaf.obj.obj
  (op (Scheme.Etale.mk (𝟙 Y.scheme)))`, with `hβ : ...IsChart ... β`.
  This is the value of the sheaf on the final small-etale object.
- Fineness and saturation of Q are `hQ : IsFineSaturatedMonoid Q`;
  torsion-freeness of its group completion is
  `[IsMulTorsionFree (Algebra.GrothendieckGroup Q)]`.
- The geometric point is `t : Spec (.of Ω) ⟶ X.scheme`, with explicit
  `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`, following the dependency's
  geometric-point convention. All universe variables and other variables
  are explicitly bound, with `autoImplicit false`.
- A is the existing `strictLocalRing X.scheme t`, the ring-valued
  pointed-neighbourhood colimit. The log stalk is
  `X.logStructure.toEtalePrelogStructure.stalk t` (inherited projection
  syntax `X.logStructure.stalk t` in the file), the recorded monoid colimit.
- The differential module is `f.LogDifferential t`, the actual free-module
  quotient in the new definition module, not a module parameter, arbitrary
  model, or a choice from a mere existence theorem.
- The additive and Leibniz relations for d are the first two disjuncts in
  `f.logDifferentialRelations t`; multiplicative additivity of dlog is the
  third; `dα(m)=α(m)dlog(m)` is the fourth. The final two disjuncts kill all
  base ring/log germs. Every base stalk element has a representative on a
  pointed etale neighbourhood; pulling that neighbourhood back to X
  realizes it among the relative test diagrams used in these disjuncts.
  Conversely every such relation is a base stalk image. Thus these are
  exactly `dc=0` and `dlog f♭(b)=0`, not additional vanishing relations.
- The existing `M.characteristic t` is `Associates (M.stalk t)`, the
  quotient by log units. The log unit condition canonically identifies
  these units with A-units. Its group completion is therefore canonically
  B/A-units. This uses the existing characteristic quotient; no second
  private quotient notion is introduced.
- Finite generation and torsion-freeness of C are respectively `Group.FG`
  and `IsMulTorsionFree` of this characteristic group completion.
- The witnesses are `r : ℕ`, `ts : Fin r → X.logStructure.stalk t`, and
  `n : ℕ`. Thus each t_i belongs to the monoid, not merely its completion.
- Positivity and invertibility are `1 ≤ n` and
  `IsUnit (n : strictLocalRing X.scheme t)`. Positive natural exponents
  represent exactly the positive integers in the node.
- The basis assertion is an existential `Module.Basis (Fin r) A ...`
  together with `∀ i, b i = f.logDLog t (ts i)`. A Mathlib module basis
  supplies precisely existence and uniqueness of all linear expansions.
- The specified image subgroup `f.differentialGeneratorImage t β ts` is
  the subgroup closure of the classes of all t_i and all base chart
  elements. This is exactly the image of Z^r ⊕ Q^gp: the first summand
  generates the t_i classes and the second extends the chart homomorphism
  by the universal property of group completion. Its quotient is therefore
  exactly the cokernel in the statement, including all integral multiples.
- `Finite (C ⧸ image)` states finiteness, separately from
  `∀ c : C ⧸ image, c ^ n = 1`, which states annihilation by n in
  multiplicative group notation. We do not assert n equals the order.
- The final clause `∀ a : Aˣ, ∃ b : Aˣ, b ^ n = a` is n-divisibility
  of units, with the root itself required to be a unit.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogHom`,
  `EtalePrelogStructure.stalk`, `.germ`, `.stalkAlpha`,
  `EtaleLogStructure.IsChart`, `.characteristic`, `.unitsIn`.
  The quotient by units and the chart condition are reused exactly.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`:
  `EtaleLogHom.IsLogSmooth`, together with its `FSLogChart` definitions.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`:
  `pointedEtaleStalk`, `pointedEtaleStalkDiagram`, `pointedEtaleGerm`,
  through the imported log stalk definitions. `strictLocalRing` and
  `strictLocalGerm` come from the existing `LogRegularPair` module.
- The new definition node supplies `EtaleLogHom.LogDifferential`,
  `.logDifferentialRelations`, `.logDLog`, `.logD`, `.baseChartGerm`.
- Ordinary Mathlib constructions are reused: `Finsupp`, `Submodule.span`,
  `Submodule.mkQ`, `Module.Basis`, `Algebra.GrothendieckGroup`,
  `Associates.mkMonoidHom`, `Subgroup.closure`, the group quotient,
  `Group.FG` and `IsMulTorsionFree`.

Recorded proof-dependency imports are retained where already stated:
`StrictHenselization`, `StrictHenselizationCompatibility`, `FsFaceSharpening`,
`SelectedBasisOfLocalizedSplit`, Mathlib's finite-abelian-group structure
module, and upstream `HenselianLocalRootLifting`. The affine cofinality and
henselian terminology modules are reached through these imports. The
proof-only node `lem-per-log-smooth-differential-local-freeness` has no Lean
record yet, so its module cannot be imported; this is not a missing object
needed to state the present theorem. It remains named in the theorem's
complete natural-language proof and in the unchanged DAG proof.

Edge cases checked before writing:

- r=0: `Fin 0` is empty and `Module.Basis` admits exactly a zero differential
  module; the image subgroup is still generated by the base chart.
- n=1: the cokernel condition forces the trivial group, while every unit
  is its own first root. No n>1 restriction is present.
- Trivial logs and the identity morphism: both characteristic and
  differential groups are zero, r=0,n=1 is the expected result.
- An empty source has no geometric point t, so the theorem requires no
  unsupported stalk on the empty scheme.
- Q need not be sharp or inject into the log structure. The recorded
  chart predicate is used without either additional assumption.
- Tame Kummer examples can have nontrivial finite cokernel while their
  logarithmic differential module has rank zero; the statement allows
  this. Residue characteristic dividing n is excluded exactly by IsUnit.
- Arbitrarily large fs schemes and charts use one explicit universe u as
  in the recorded dependency definitions, with no new universe equality
  or independent small test-object universe.

Searches (all service searches were actually run with msearch.py):

- LeanSearch: `For a log smooth morphism logarithmic differentials admit
  a basis of dlog sections with finite characteristic cokernel` returned
  ordinary formally-smooth/Kahler differential results, including
  `Algebra.FormallySmooth.projective_kaehlerDifferential` and
  `Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential`.
- LeanFinder: `Module of relative logarithmic differentials generated by
  da and dlog m modulo Leibniz and logarithmic relations` returned ordinary
  Kahler presentations and `CommRingCat.KaehlerDifferential`.
- Loogle: `"LogDifferential"` returned no hits.
- Mathlib grep: `LogDifferential|logarithmic.*differential|logDifferential`
  returned only FieldTheory/Differential/Basic.lean, concerning the
  logarithmic derivative of a field element, not this module.
- Direct rg on the source WeilConjectures tree and lean/Sheaf for the
  same concepts and all proposed names found no existing module or
  declaration. Searching the item id upstream also found no match.
- DAG grep and `tools/blueprint_refs.py search` for logarithmic
  differentials/log differential found no definition node. The other
  existing nodes are statements about the same as-yet-undefined module.
  The existing log structure, characteristic quotient, and chart data
  were found and reused rather than redeclared.

Validation: both delivered modules compiled separately, in dependency order,
using scompile.py. The clean run reported no warnings or errors. There is
one postponed theorem, the item itself; all added definitions have real data.
The UTC date from `date -u +%F` is 2026-10-18 on this run, used in both Lean
records and the new node. No statement correction or disputed statement.

## New nodes

`def-per-log-differential-stalk` defines the relative logarithmic differential
module by its actual free-module quotient and the canonical ordinary/log
symbols. Its base relations use all actual relative pointed neighbourhoods,
so no unprovided ring/log stalk comparison is assumed. It also supplies the
canonical germ of a global base chart. Source: ILO XVI 3.6.3 p.252 and X 1.2
pp.136--138; the explicit relations are already spelled out in the parent's
reviewed statement. The searches above find only ordinary Kahler
constructions and no existing logarithmic module or definition node. Its
statement depends precisely on the existing log scheme and geometric stalk
nodes. The parent gains this single statement dependency.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
