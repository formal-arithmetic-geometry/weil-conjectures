## Worker report

`Sheaf.Paper.PfRefinementCompatibility` states
`AlgebraicGeometry.ProEtale.pf_refinement_compatibility`, with proof `sorry`.
The node's statement is unchanged. There are no new DAG nodes, dependency-node
changes, or postponed helper theorems. The seven declarations in `lean.declarations`
include real specializations of existing constructions and the displayed equation;
only the final named theorem is postponed. Every declaration has its source and
blueprint tag. Its theorem docstring carries the four-step proof of the DAG node.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| The fixed finite-field and coefficient datum of def-pur-conventions, including ell distinct from p, the finite subextension E of the fixed closure and n at least 1 | `P : WeilConjectures.PurityFiniteSetting.{u}`; the coefficient is exactly `P.Coefficient`, the conventional universe lift of `P.Ring = O_E/(varpi_E^n)` |
| Separated finite-type k-schemes X and Y | `X.Over (Spec (.of P.field.k))` and `Y.Over ...`; each structure morphism has `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` instances |
| A separated finite-type k-morphism f | `(f : X ⟶ Y)`, `f.IsOver ...`, `IsSeparated f`, `LocallyOfFiniteType f`, and `QuasiCompact f` |
| Two compactifications | `c₁ c₂ : Compactification f`, with the existing open immersions, proper maps and factorization equation |
| A proper refinement with vj₁=j₂ and p₂v=p₁ | The first conjunct quantifies `r : c₁ ⟶ c₂`; `r.i_hom` and `r.hom_g` are exactly these equations, and properness is the existing `Compactification.Refinement.isProper` instance |
| F_i=Rp_i* j_i! with exact open extension | `rightDerivedLowerShriekOfCompactification (ModuleCat.{u+1} P.Coefficient) cᵢ`; this is the published termwise open extension followed by derived direct image |
| The specified normalized theta_v | `pfRefinementComparison P r`, exactly `refinementComparisonAtWitness` at the finite purity coefficient, including its prescribed witness conjugation and direct-image compositor; this is the underlying construction of `refinementComparisonIsomorphism` and the normalization in `compactification_coherence` |
| K and L bounded below with retained etale-origin witnesses | `O_K : PfRefinementOrigin P X` and `O_L : PfRefinementOrigin P Y`, abbreviations of the existing `RefinementFiniteLevelOrigin`; each retains the actual D+ object, its D+ etale antecedent and the specified isomorphism |
| The tensor K tensor Lf*L also bounded below and witnessed | `O_T : PfRefinementOrigin P X` and `hT : pfRefinementTensor P f O_K O_L ≅ pfRefinementObject P X O_T` |
| Precisely the counit-defined PF for each chosen compactification | The two components of `projectionMapOfCompactification` in `PfRefinementSquare` |
| theta_T after PF_c1 equals PF_c2 after theta_K tensor identity | The first conjunct instantiates `PfRefinementSquare` with `pfRefinementComparison P r O_K` and `... O_T`. Its definition expands both composites in Lean's left-to-right composition order |
| The same equation through every common refinement | The second conjunct independently quantifies `d,r₁,r₂` for arbitrary `c₁,c₂` and inserts `(theta r₁).symm ≪≫ theta r₂` at K and the tensor |
| No invertibility of PF; no constructibility or finite Tor amplitude | The conclusion is an equality, and no such hypothesis or `IsIso` conclusion appears |

Witness coordinates and maps: `pfRefinementObject` is an abbreviation in effect
(a real wrapper definition) for the existing canonical inverse coefficient realization.
The pair `(O_T,hT)` is the witness on the actual tensor in those coordinates, with its
bounded-below assertion. Conjugating theta on `O_T` by `F₁(hT)` and `F₂(hT⁻¹)` gives
exactly theta on that tensor. An arbitrary `hT` is permitted because it transports the
retained witness itself; it supplies no extra mathematical condition beyond the
node's witnessed tensor. Both composites therefore start at F₁K tensor L and end at
F₂(K tensor Lf*L). The helpers neither choose an arbitrary comparison nor assert the
square as a hypothesis. `PfRefinementSquare` is a definition of the expanded equality;
the theorem fills its theta arguments only with the specified comparisons.

Dependency interfaces read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient` and their field/coefficient data.
- `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement`,
  `.category`, the two commuting equations, and `.Refinement.isProper`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero`, whose definition is the same fixed-scalar
  extension transported by `sfIntrinsicModuleEquivalence`. The PF construction
  uses its published fixed-scalar presentation, not a second extension functor.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`: the current recorded module,
  reexporting `Sheaf.Paper.RingedEtaleOriginWitness` and its original retained pair.
  `Sheaf.Paper.EtaleOriginDerivedCategory` packages that same pair with its D+ object;
  `Sheaf.Paper.RefinementComparisonIsomorphism` supplies its finite specialization,
  fixed realization and normalized `refinementComparisonAtWitness`.
- `Sheaf.Paper.CompactificationCoherence`: its `compactification_coherence`
  normalization was read in full. The comparison used here is the precise
  `refinementComparisonAtWitness` construction underlying its recorded
  `refinementComparisonIsomorphism` component, not an existentially chosen theta.
- `Sheaf.Paper.ExchangeProjection`: its `finiteExchangeProjection` is the product
  whose third component is `projectionMapOfCompactification`. The latter's full
  signature, component formula and counit definition were read in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`
  and the corresponding published source.
- Proof imports retain `ProperOpenInterchangeCoherence`,
  `StrictTowerProperOpenCalculus`, `ProperOpenComparison`,
  `FiniteDirectImageComposition`, and `ProEtaleProperOpenComparison`.

Import compatibility: full imports of `Sheaf.Paper.CompactificationCoherence` and
`Sheaf.Paper.ExchangeProjection` failed before the item could elaborate: the former
pulls `ComparisonGlobalCohomology`, importing the legacy `Derived.LowerShriek` while
the normalized comparison imports `FiniteCoefficient.Derived.LowerShriek`; Lean
reports that both declare `rightDerivedLowerShriekOfCompactification`. The latter
pulls the legacy open base-change module and fails on the duplicate
`upperStarIsoLowerStarInv`. As the brief directs for duplicate declarations, this
module imports the smaller published `FiniteCoefficient` modules giving the exact
canonical maps it needs. The same reason excludes the full legacy import closure
of `ProperOpenComparisonSiteNormalization`; its explicit site-normalization formula
remains in the theorem's proof plan. The unspecified proof nodes
`fix-prop-adjunctions`, `lem-pur-derived-pullback-tensor-iso`, and
`lem-sf-proper-open-projection-mate` have no current Lean module to import.
No mathematical interface is replaced and no live source was edited.

Edge cases checked against the formal statement: identity refinement; a proper f
with identity open compactification; empty X or Y whenever the morphisms exist;
zero K or L; positive level n=1; and a common refinement with either identity leg.
No Cartesian refinement hypothesis appears: boundary components are permitted by
`Compactification.Refinement`. The common-refinement clause has no prerequisite
arrow from c₁ to c₂. No additional flatness hypothesis is present: coefficient
finiteness is derived by `pfRefinementCoefficientFinite`, and the published
`upperStarPreservesFlat_moduleCat` instance supplies preservation of flat sheaves.
The small site retains object universe u+1 and morphism universe u.

Searches made with the prescribed wrapper (logs in `searches.jsonl`):

- LeanSearch: "Derived sheaf projection transformations commute with normalized
  comparison isomorphisms under proper refinement of compactifications". Eight
  hits on open-cover refinement, constant sheaf functors, sheafification and
  underived pushforward comparisons; none is the requested derived square.
- LeanFinder: "projection transformation compatible with compactification
  refinement". Eight unrelated Profinite/Nobeling projection hits.
- Loogle: `CategoryTheory.NatTrans`. Twelve generic natural transformation hits.
- Mathlib grep: `compactification.*projection|refinement.*projection` in
  `AlgebraicGeometry`. No hits.
- Source/project grep for `projectionMapOfCompactification`, refinement/projection
  comparisons, the node ID, and every new full declaration name. The ordinary
  etale `Etale.projectionMapOfCompactification_comparison` requires a Cartesian
  refinement and has etale endpoints; its arbitrary-pair comparison remains an
  etale statement. Neither is the finite pro-etale witnessed square here.
  No matching existing theorem or duplicate helper declaration was found.

No statement correction or disputed statement is needed. Compilation and delivery
preflight use only the prescribed wrappers, with the unchanged 60-second file limit.

## Second reading by Q76

Independent maintainer reading, 2026-10-18, of immutable delivery
28f4c19c485cc3dcee9e4c91833882a985f4d6dc. I did not write this delivery.
The following replaces the delivered placeholder; the worker report above is retained.

I read packet.md, check-brief2.md in full, the immutable item, all six statement
dependencies and their Lean records, the delivered module and its docstrings, and the
source sentence in literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md. I also read the cited proof
statements and the actual coefficient, origin, compactification, comparison, extension
and projection interfaces in the read-only group/source clones. The finite-coefficient
LowerShriekProjection, LowerStarProjection and FlatModuleCat sources absent from the
local group clone were read through scompile.py --source, rather than inferred from
legacy file names.

Hypotheses and conclusions, checked individually:

| Node clause | Actual Lean and verdict |
| --- | --- |
| Fixed finite-field datum, ell different from p, E in the fixed closure, positive level | PurityFiniteSetting retains precisely these data; P.Coefficient is ULift of the published quotient P.Ring. The finite instance is obtained from coefficient-extension finiteness. Agrees. |
| Separated finite-type k-schemes X,Y | Over instances and IsSeparated, LocallyOfFiniteType, QuasiCompact on both structure maps. Agrees. |
| Separated finite-type k-morphism f | f.IsOver and the three corresponding morphism instances. Agrees. |
| Two compactifications and proper refinement, v j1 = j2, p2 v = p1 | Compactification f and r : c1 to c2 use the recorded Refinement structure; i_hom and hom_g give the equations, and Refinement.isProper supplies properness. No Cartesian condition. Agrees. |
| Fi = Rpi* ji! | rightDerivedLowerShriekOfCompactification uses the published exact open extension termwise followed by derived direct image. The intrinsic extension dependency is the canonical realization of this same functor. Agrees. |
| Specified normalized theta | pfRefinementComparison unfolds to refinementComparisonAtWitness, including the equality transport, finiteDirectImageComposition and proper image of refinementProperOpenIso inverse. It is the construction used by refinementComparisonIsomorphism and compactification_coherence, not an arbitrary isomorphism. Agrees. |
| Bounded-below K,L with retained etale origins | PfRefinementOrigin is RefinementFiniteLevelOrigin, whose objects retain the D+ object, D+ antecedent and comparison alpha. pfRefinementObject is its canonical inverse coefficient realization. Agrees. |
| Bounded-below witnessed tensor | O_T plus hT identifies the actual derived tensor with a realized retained origin. This transports the witness to that actual tensor; hT is not a projection compatibility hypothesis. Agrees. |
| Exactly the counit-defined PF maps | PfRefinementSquare uses projectionMapOfCompactification. Its component is the proper right-adjoint projection mate followed by proper image of the inverse open projection isomorphism and the pullback compositor. Agrees. |
| Required equation and endpoints | Lean composition runs left to right. The left side is PF_c1 followed by F1(hT), theta_T, F2(hT inverse); the right is tensor(theta_K,id) followed by PF_c2. Both run from F1K tensor L to F2(K tensor Lf*L). Agrees. |
| Every refinement and comparison through any common refinement | The first conjunct quantifies every r. The second quantifies d,r1,r2 independently of an arrow c1 to c2 and uses theta_r1 inverse followed by theta_r2 at both objects. Agrees. |
| No constructibility, finite Tor amplitude or PF invertibility | None is imposed or concluded. No flatness assumption is added: finite coefficients supply Noetherianity and the published pullback-preserves-flat instance. Agrees. |

The four-step proof docstring follows the immutable node: (1) site normalization,
the etale proper/open refinement normalization, and strict-tower evaluation identify
Gamma with the clopen-projection mate on etale antecedents, then naturality transports
it along alpha; (2) specialize the proper/open tensor-mate identity to the refinement
square with identity left side; (3) paste the ordinary counit projection composition
law and use naturality through beta; (4) compose the squares for the two common
refinement legs. Only comparison isomorphisms are inverted. Quasi-compactness of the
open immersions follows because the compactification schemes are finite type over
k and hence Noetherian. The strict towers used here are ordinary D(Tow), with
termwise operations, not enhanced localizations or coherent sections. The proof-only
nodes without Lean declarations are not missing objects needed to state this theorem.
No dependency or source-based statement repair is needed.

One-definition-per-notion: independently searched project and upstream six-functor
sources with projection/comparison/refinement words and read the actual candidate
Etale.projectionMapOfCompactification_comparison in LowerShriekProjectionRefinement.
It has etale endpoints and a Cartesian refinement hypothesis. The arbitrary-pair
compactSupportProjectionMap_comparison in ShriekTensorComposition is also etale.
Neither states this finite pro-etale witnessed equation. The delivered helpers are
transparent specializations or the displayed equation, and introduce no alternative
tensor, extension, witness or comparison construction. The worker's recorded
LeanSearch, LeanFinder/Loogle and grep searches are retained above; I do not claim
to have rerun the remote semantic searches.

Edge cases: identity refinement; proper f with identity open compactification;
empty X, and empty Y whenever the morphism exists; zero K or L; n=1; a common
refinement with either leg the identity; and refinements with extra boundary
components. All remain covered. Level zero and ell=p are outside the conventional
datum, not newly excluded. Universe u is arbitrary, with small pro-etale object
universe u+1, morphism universe u and ModuleCat at u+1; no extra universe equality
is imposed. Tensor boundedness is retained explicitly, rather than inferred for an
arbitrary derived tensor over the nonregular finite ring.

Mechanical checks: all seven declarations are listed; every declaration and the
module have source/blueprint docstrings; autoImplicit is false; there are no lines
over 100 characters. The sole sorry is the final named theorem. All helpers have
real terms, including the finiteness instance. Exact string comparison confirms
lean.statement is verbatim the theorem signature, excluding ':= by'. The delivery
changes only its Lean record, new module and report; no statement_change or citer
audit is called for. Smaller published finite-coefficient imports are justified by
the duplicate legacy declarations documented by the worker; the maps are the same
recorded constructions. No pro-etale substitute is used.

Route pivot: checked origin/newtargets-dag:coord/route-pivot-dropped.txt against all
statement and proof dependency IDs: no intersection. There is no repair note at
coord/repair-notes/lem-pur-pf-refinement-compatibility.json on that ref. No discarded
infinity/dg/model-category route is introduced by this delivery.

Compiler evidence: independently ran the prescribed command
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q76
lem-pur-pf-refinement-compatibility <immutable snapshot>/lean/Sheaf/Paper/
PfRefinementCompatibility.lean. It exited 0: sandbox Sheaf/Stage2/Sandbox0.lean
passed in 4.6 seconds and library Sheaf/Paper/PfRefinementCompatibility.lean passed
in 5.1 seconds, with no diagnostics. This installed scompile.py uses server-side
nt_srv_compile.py --wire-confirm and a private side overlay; it does not currently
run the local lcompile.py route described by the brief. These are server-overlay
results, not a claim of local reproduction. No direct ssh command, live Lean write,
lake build, global build or repository mutation was performed.

Finding H11 (also H1's substantive report requirement): the delivered heading
contained only 'No second reading by a worker', not a reading. Replaced it with
this actual independent reading and compiler evidence. The complete replacement
report is fixes/lem-pur-pf-refinement-compatibility.report.md, accepted by the stage-2
merge tool's report override format. No Lean or node correction is necessary.
Verdict: FIX, report only.
