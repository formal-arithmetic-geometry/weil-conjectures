## Worker report

The main module is `Sheaf.Paper.PurityRankOneLocalCalculation`. Its main declaration is
`WeilConjectures.PurityFiniteSetting.RankOne.rankOne_local_calculation`.
It states the finite-coefficient calculation, without proving it. The coefficient sheaf,
Kummer class, section complexes, and comparison map have actual definitions. The only
`sorry` in this module is the theorem corresponding to this DAG node.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
| --- | --- |
| Finite-field/coefficient setting, arbitrary level n ≥ 1, A = A_(E,n) | `P : PurityFiniteSetting`, `P.level_pos`, `P.Coefficient`; the latter is the prescribed universe lift of the actual quotient ring |
| N ≥ 1 and ell^N A = 0 | `N`, `hN`, `hA`; the power in `hA` is explicitly a natural number before casting |
| Y a k-scheme | `Y`, its displayed structure map `aY` |
| Geometric point Spec Ω → Y, Ω algebraically closed over k | `Ω`, `[Field Ω]`, `[IsAlgClosed Ω]`, `[Algebra P.field.k Ω]`, `y`, and the over-k equation `hy` |
| X = affine line over Ω, Z = origin, U = punctured line | `Line (Spec (CommRingCat.of Ω))`, `openObject (Spec (CommRingCat.of Ω))`, and `restriction (Spec (CommRingCat.of Ω))`; these use the recorded affine-line datum, whose basic open is the complement of its zero section |
| A(1) = mu_(ell^N) tensor A | `Scheme.finiteEtaleTateSheaf P.Coefficient (P.coefficients.l ^ N) (Line (Spec (CommRingCat.of Ω))) hA 1`; this existing construction is sheafified scalar extension. Its tensor order A tensor mu is the canonical symmetry of the node's mu tensor A |

Clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Kummer exponent invertible on X | The conclusion supplies `hm : IsUnit (m : Γ(X, ⊤))`, rather than adding this consequence as an assumption |
| Coefficient map x ↦ x tensor 1 | The existential `f` is fixed on EVERY etale object and EVERY root section by `finiteEtaleTateOneGenerator A m X hA V 1 z`; equality on sections determines this map uniquely |
| Actual Kummer class kappa_A(u) | `kummerClass` precomposes `kummerSequence_shortExact.extClass` with the section represented by u, then postcomposes with f; `evaluationExt` and `moduleEvaluationForgetComparison` give the canonical derived-evaluation class |
| Actual H1(U,F) | `sections ... W` is evaluation at the open etale object; its right derived functors compute cohomology of the restriction on U. The free-abelian representing object, Yoneda section equivalence, and normalized Ext comparison keep this identification canonical |
| Actual support cohomology | `Het` and `Hpro` are right derived functors of the recorded generic `Sheaf.supportedSectionsFunctor`, namely the kernel of restriction to the actual punctured open, in ModuleCat A. This retains the A action; it is the module enhancement of the recorded abelian etale support construction |
| Actual boundary, with its sign | `IsBoundary ... δet` and its pro-etale version require equality, on EVERY injective resolution, with `ShortComplex.ShortExact.δ 1 2 rfl` of the section-complex sequence, transported by `isoRightDerivedObj`. Thus the existential maps are not arbitrary isomorphisms |
| Boundary is an isomorphism | `IsIso δet` and `IsIso δpro` |
| Unique A-linear rho, normalized at kappa(t) | `ρet : Het ≅ ModuleCat.of A A` and `ρpro` are module isomorphisms; the two normalization equations and the two universally quantified uniqueness clauses give precisely the unique normalized A-linear isomorphisms |
| Vanishing at every nonnegative q different from 2 | The `∀ q : ℕ, q ≠ 2 → ...` clause asserts `IsZero` on both sites |
| Every unit is c t^r | The universal `v` clause supplies c and integer r with `v = constantUnit Ω c * coordinateUnit S ^ r` |
| ord_0 is the ordinary t-adic order in Ω(t), including local-ring units | The actual Mathlib valuation at `Polynomial.idealX Ω` sends `C(c) * X^r` to `WithZero.exp (-r)`. Mathlib uses the multiplicative convention v(t) = exp(-1), so its negative exponent is ord_0. The preceding clause sends `RatFunc.mk a b` to 1 whenever a(0) and b(0) are nonzero: these fractions are exactly the units of Ω[t]_(t). In particular the r=1 case gives ord_0(t)=1 |
| Residue of every c t^r is r times 1_A | The final two equations, for all c and r, on the two sites |
| Independence of a primitive root | None of F, f's tensor characterization, kappa, the snake boundary, or the normalized rho has a primitive-root parameter. Uniqueness fixes rho independently of any root used in a proof |
| Actual inverse-image coefficient sheaf on the pro-etale site | `proCoefficient P.Coefficient (Line (Spec (CommRingCat.of Ω))) ...` is `comparisonUpperStar.obj F`, rather than a separately chosen coefficient sheaf |
| Canonical cohomology comparison | `cU` is `comparisonCohomology ... 1`, constructed by `rightDerivedBaseChange` from the evaluated comparison-adjunction unit; `IsIso cU` is asserted |
| Comparison respects boundary and normalization | `δet ≫ cZ.hom = cU ≫ δpro` and `cZ.hom ≫ ρpro.hom = ρet.hom`. Because δet is invertible, the first equation determines cZ uniquely and gives the actual support comparison |

Definitions used from recorded dependencies:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Coefficient` and its actual quotient-ring structure.
- `Sheaf.Paper.PurityAffineLineDatum`: `Line`, `Punctured`, `openImmersion`,
  `puncturedProjection`, `coordinateUnit`. Only the unrestricted geometric definitions
  are used: the restricted e-divides-n coefficient interface is not used.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`:
  `Scheme.finiteEtaleTateSheaf`, `Scheme.finiteEtaleTateOneGenerator`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `Sheaf.supportedSectionsFunctor`; `SupportLongExact`: `supportedSectionsInclusion`.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`:
  `Scheme.kummerSequence`, `Scheme.kummerSequence_shortExact`, and its `extClass`.
- `Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison`:
  `EtaleOpenComparison.sectionsEquiv` and `sectionsEquiv_naturality`.
- `Sheaf.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison`:
  `exists_ext_rightDerived_cocycle_comparison`. Its cocycle normalization determines
  the chosen comparison uniquely, because every Ext class has an injective representative.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyConventions`:
  `Etale.moduleAbelianForget`, `moduleEvaluationForgetComparison`,
  `module_cohomology_conventions`; the inverse is of this specified bijective map.
- `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`:
  `comparisonUpperStar`, `comparisonAdjunction`; `Scheme.toProEt` is the recorded
  small-site inclusion.
- Mathlib: `ShortComplex.ShortExact.δ`, `InjectiveResolution.isoRightDerivedObj`,
  `Polynomial.idealX`, its `valuation`, `RatFunc.mk`, `RatFunc.C`, `RatFunc.X`.
- The recorded primitive-root/trivialization and all stated proof-dependency modules
  are imported for the seven-step proof plan. The repaired global-comparison dependency
  is described below.

Edge cases checked before finalizing: N=1; n not divisible by the ramification index;
A not free over Z/ell^N; q=0 and q=1 in the vanishing assertion; r=0 and negative r;
c=1; constant units; local-ring units with nonvanishing numerator/denominator at zero.
The module-valued normalization is essential: additive normalization alone would not
imply uniqueness for a coefficient ring of additive rank greater than one. The prior
worker draft's e-divides-n restriction and arbitrary-boundary/additive-uniqueness clauses
were removed before delivery. The node statement itself has not been corrected or changed.

Searches for existing statements:

- `msearch.py ... leanfinder`: “For a punctured affine line over an algebraically closed
  field, the Kummer residue identifies degree two supported cohomology with finite
  coefficients”: eight hits, Hilbert-90 and unrelated function-field results; no match.
- `msearch.py ... loogle`: `AlgebraicGeometry.Etale.supportCohomology,
  Scheme.kummerδ₀, ShortComplex.ShortExact.δ`: zero hits; index did not know the
  project-only support name. The actual declarations were read in source instead.
- A further Loogle query `IsPrimitiveRoot, RatFunc.valuation_X_eq_neg_one` also returned
  zero hits; the source identifies the valuation lemma as
  `Polynomial.valuation_X_eq_neg_one`.
- `msearch.py ... grep`: `kummer.*residue|rankOne_local_calculation|rank_one_local`:
  zero Mathlib hits.
- `rg` of upstream and `lean/Sheaf` for rank-one/local-calculation names and the node id
  found the abstract `HasKummerClass.IsNormalized` in upstream
  `EtaleCohomology/Purity/Smooth/KummerClass.lean`. Its signature was read: it ASSUMES
  normalization for an abstract twist/Kummer datum, and supplies neither the actual
  finite coefficient construction nor the residue formula, so it is not this theorem.
- `rg` in RatFunc source found the genuine X-adic valuation and its sign convention;
  `rg` in finite Tate and support sources found the constructions reused above.

No `STATEMENT-DISPUTED` issue was found in the stored DAG statement. The current
`blueprint_update` retains an erroneous explanatory phrase calling t a unit of
Omega[[t]]: t belongs to its maximal ideal. Its substantive calculation and normalization
are precisely those formalized here. The stored DAG statement already replaces this
phrase by the correct rational-function order and local-ring-unit convention; the actual
X-adic valuation clauses retain that correction. Thus no node statement change is needed.

No independent new mathematical notion is
introduced: helper declarations in the owning module name the canonical section,
cohomology, boundary characterization, and Kummer constructions needed to state this
one calculation, as authorized by the finite-comparison isolation update.

Self-check of the retained packet (2026-10-17): the initial `deliver2.py --no-push`
printed `OK (dry run)` for commit `8cb81a7de5`. The required source review then
found local `let` binders in the theorem signature, forbidden by the stage-2
conventions. They were expanded into their exact defining terms. No mathematical
hypothesis, conclusion, canonical map, module import, or dependency record was changed.
In the correspondence table, A, m, X, W, F, G, Het, Hpro, κ and cU are explanatory
labels for the explicit expressions: A is `P.Coefficient`, m is the natural power
`P.coefficients.l ^ N`, X is `Line (Spec (CommRingCat.of Ω))`, W is the corresponding
`openObject`, F is the finite Tate sheaf, G its `proCoefficient`, Het/Hpro are the
right-derived support objects, κ is `kummerClass`, and cU is the component of
`comparisonCohomology`. These labels are not new definitions or hypotheses.
The source declaration signatures and docstrings were reread against the current
shared checkout and the current main-20261015 blueprint. No repair handoff note
exists for this item. The sole postponed assertion in each delivered module is
its owning DAG theorem. Both JSON signatures are recorded verbatim.

## Dependency modules

`lem-weil-pbc-comparison-global-cohomology` is restated in
`Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`.
The original recorded module failed compilation by importing the retired
`ProEtale.Derived.LowerShriek` and then, after replacing that direct import, the retired
`ProEtale.UpperLowerStar.Iso`. Both collide with the `FiniteCoefficient` modules already
loaded by the published library. Changing direct imports alone did not repair the
transitive imports through `Comparison.CohomologicalDimension` and `GlobalSections`.
The delivered replacement needs no lower-shriek API. It evaluates the actual adjunction
unit at the terminal object and applies `rightDerivedFunctorPlusBaseChange`.
`isIso_finiteComparisonGlobalSections` says that this canonical comparison is invertible
for every scheme and finite ring, on all bounded-below complexes. This is the same
ordinary RΓ statement via canonical derived-plus compatibility, with no additional
hypotheses. Its docstring contains the original unit/Leray proof. Only this dependency's
`lean` record changes. Its id is also cited in the item's `stmt_deps`.

## Earlier second reading (a previous round; superseded)

Pending the separately assigned independent second reader. This is the worker's
no-push dry run; the worker does not claim to have performed an independent second
reading and does not push or deliver the packet.

Validation: both delivered modules compiled cleanly through `scompile.py`, separately
in dependency order. No direct local compiler, global build, live-source edit, or Git
command was used. The required `deliver2.py --no-push` is the delivery preflight.

## Second reading by Q76

I independently opened the stored node, its sandbox Lean module, every statement
dependency record, the signatures and constructions used from those dependencies,
and the replacement global-comparison module and its dependency node. I read both
the master blueprint source named by the node and the main-20261015 version, then
Milne's local PDF, Theorem 9.4 (pp. 65-67), Proposition 14.3 (p. 91), and Example 16.3
(p. 109). For the identifications used in the helpers I also read the Stacks TeX:
03F3 (`sites-cohomology.tex`, cohomology over an object), 06XR (`derived.tex`, Ext
computed by resolutions), and 099W (`proetale.tex`, ordinary and D+ comparison).
There is no repair handoff file for this item and no `statement_change` in this packet.
The previously corrected rational-function order convention is already in the base
node. No node statement is changed in this second reading.

Here is my inventory of the node, matched clause by clause. In this table only,
S means `Spec (CommRingCat.of Ω)`, X means `Line S`, W means `openObject S`,
A means `P.Coefficient`, m means the natural number `P.coefficients.l ^ N`,
and F means `Scheme.finiteEtaleTateSheaf A m X hA 1`. These abbreviations expand
literally in the delivered signature; they introduce no hidden binders.

| Object, hypothesis, or conclusion in the node | Lean rendering and second-reader verdict |
| --- | --- |
| The fixed finite-field and coefficient setting, with ell different from p | `P : PurityFiniteSetting.{u}`. I read the structure, its `FiniteFieldDatum` and coefficient datum: these are the fixed finite-field algebraic closure and finite subextension of the coefficient closure. Match. |
| Any n at least one and A = O_E/(varpi_E^n) | `P.level`, `P.level_pos`, and `P.Coefficient`. The latter is `ULift` of the actual quotient `Padic.coefficientExtensionRing`, with its inherited ring structure. There is no e-divides-n or freeness binder. Match. |
| An integer N at least one killing A | `(N : ℕ) (hN : 1 ≤ N)` and `hA : ((P.coefficients.l ^ N : ℕ) : P.Coefficient) = 0`. Vanishing of this ring element is exactly annihilation of the whole coefficient ring. Match. |
| A k-scheme Y and geometric point Spec Omega to Y over k | `Y`, `aY`, `Ω`, `[Field Ω]`, `[IsAlgClosed Ω]`, `[Algebra P.field.k Ω]`, `y`, and `hy`. No finite-type, separatedness, or Noetherian condition is imposed on Y. Match. |
| X is the affine line over Omega, with its coordinate t | `Line S`, whose definition is the one-variable relative affine space, with `coordinate S`. Its affine coordinate ring is canonically Omega[t]. Match. |
| Z is the zero section fibre and U its complement | `Punctured S` is the coordinate basic open, `openObject S` is its actual etale object, and `restriction S` is its inclusion into the terminal etale object. Support is the kernel of restriction across exactly this open. No arbitrary closed subset or open immersion is substituted. Match. |
| A(1) is mu_m tensor over Z/m with constant A | F. I unfolded `finiteEtaleTateSheaf`, `finiteEtaleTateTwist`, `finiteEtaleTateLine`, `finiteEtaleMuModulePresheaf`, and `finiteEtaleTwistScalar`. This is sheafification of the actual extension of scalars `A tensor mu_m`; tensor symmetry gives the displayed order in the node. Match. |
| The Kummer sequence is used with invertible m | The theorem produces `hm : IsUnit (m : Γ(X, ⊤))`. This is a consequence, not an extra hypothesis: ell differs from the characteristic and Omega is over k. `kummerClass` uses the recorded `X.kummerSequence_shortExact m hm`. Match. |
| The coefficient map is x mapping to x tensor 1 | The existential f is constrained on every etale object V and every root section z by `f.hom.app V z = Scheme.finiteEtaleTateOneGenerator A m X hA V 1 z`. These equations determine a sheaf map, and the right side is the sheafification image of `1 tensor z`. Match. |
| The actual image kappa_A(u) of the Kummer boundary | `kummerClass A X W F m hm f u`. The section-to-Hom map is the canonical free-abelian Yoneda equivalence, its Ext class is composed with the Kummer extension and then f, and the normalized Ext/evaluation and module/abelian comparisons transport it. The Ext comparison is characterized on every injective cocycle, so its choice is uniquely determined. Match; no arbitrary class or root choice. |
| H1(U,F) and H2_Z(X,F) are the actual cohomology groups | The former is derived evaluation at W; the latter is `((Sheaf.supportedSectionsFunctor X.smallEtaleTopology (ModuleCat A) (restriction S)).rightDerived 2).obj F`. Stacks 03F3 and the recorded module-cohomology conventions identify these module-valued groups with the stated cohomology and its retained A action. The generic recorded kernel functor is reused. Match. |
| The actual support boundary is an isomorphism | `IsBoundary ... δet` and `IsIso δet`. `IsBoundary` quantifies over every injective resolution and requires equality with `hI.δ 1 2 rfl` of `sectionComplex`, transported by `isoRightDerivedObj`. I checked the two arrows: the actual kernel inclusion, followed by actual restriction. Thus existence does not weaken the specified boundary or leave its sign free. Match. |
| A unique A-linear isomorphism rho normalized at the coordinate | `ρet : Het ≅ ModuleCat.of A A`, the equation `ρet.hom (δet (kummerClass ... (coordinateUnit S))) = 1`, and the universal clause asserting `ρ = ρet` for every normalized module isomorphism ρ. Morphisms in ModuleCat are A-linear. Match, including uniqueness for rings of additive rank greater than one. |
| Every nonnegative support degree other than two vanishes | `∀ q : ℕ, q ≠ 2 → IsZero ... ∧ IsZero ...`, for etale and pro-etale coefficients. Both q=0 and q=1 are included. Match. |
| Residue on every global unit c t^r | The unit decomposition clause ranges over every `v : Γ(Punctured S, ⊤)ˣ`. The final universal clause ranges over all `c : Ωˣ` and `r : ℤ` and sends their actual product of pulled-back constant unit and `coordinateUnit S ^ r` to `r • (1 : A)`. Match. |
| ord_0(t)=1, ord_0(c t^r)=r, and local-ring units have order zero | The genuine `Polynomial.idealX Ω` valuation on `RatFunc Ω` is `WithZero.exp (-r)` on `RatFunc.C c * RatFunc.X ^ r`. I read `Polynomial.valuation_X_eq_neg_one`; this fixes the conversion from the multiplicative valuation to ordinary order. The separate `RatFunc.mk a b` clause with both evaluations at zero nonzero gives valuation one, hence order zero, for exactly the local-ring units. Match. |
| Independence of a primitive root | No root appears in any defining term or theorem parameter. The coefficient map and resolution boundaries are uniquely fixed, and the universally quantified normalization clause uniquely fixes rho. A primitive root is only a proof tool. Match. |
| The same result on the small pro-etale site, under comparison | `proCoefficient A X F` is the recorded `comparisonUpperStar.obj F`. The boundary, invertibility, normalized module isomorphism, uniqueness, all-degree vanishing, and residue formula are all repeated for this precise sheaf. Match. |
| Transport preserves the canonical classes, boundary, and normalization | `comparisonCohomology` is `rightDerivedBaseChange` of the comparison-adjunction unit evaluated at W. Its component cU is asserted invertible; the equations are `δet ≫ cZ.hom = cU ≫ δpro` and `cZ.hom ≫ ρpro.hom = ρet.hom`. Since δet is invertible, this square uniquely determines cZ, exactly as in the node's last proof step. Match. |

Dependency delivery (H13): I read the full replacement
`ComparisonGlobalCohomologyFiniteNormalized.lean` against
`lem-weil-pbc-comparison-global-cohomology`. Its source statement is for every scheme,
every finite discrete ring, and every bounded-below complex, with no constructibility
restriction. The new signature uses `(T : Scheme.{u}) (A : Type (u+1)) [Ring A]
[Finite A]`, and asserts invertibility of the natural transformation on all of D+.
The transformation is concretely derived from the actual adjunction unit at the
terminal etale object, evaluated at the same object on the pro-etale site. The source
of `rightDerivedFunctorPlusBaseChange` explicitly characterizes it by compatibility
with derived units. Thus canonical D+/ordinary-derived compatibility identifies it
with the node's unit followed by final-object Leray comparison. It does not replace
that composite by a bare isomorphism, restrict to sheaves, or require commutativity.
The old module's transitive retired pro-etale imports make its interface unusable
with the finite-coefficient framework; the replacement avoids those imports. Only
this dependency's `lean` field differs from the shared node. There are no new nodes.

Edge cases: n and N independently range over all positive naturals, including one;
there is no n/e restriction. The allowed characteristic is any p different from ell,
as fixed by the convention datum; invertibility is concluded. The ambient Y may be
arbitrary and is not silently made Noetherian. An empty Y has no displayed geometric
point, so no permitted empty case is lost; X and U over a field are nonempty.
There is no index set or sum to make empty. Both signs of r and r=0 are included by
`ℤ` and group powers, and c=1 is included. The zero coefficient/module case makes
the normalization equation 0=1 valid in the zero ring and the unique zero-module
isomorphism remains meaningful; the actual positive coefficient quotients are retained.
All vanishing degrees, including zero and one, are explicit. The arbitrary universe u
is shared by the geometric schemes and fields, as in the recorded small-site convention;
site objects have universe u+1, morphisms u, and coefficient modules u+1. No equality
of site object and morphism universes, unbound universe, or unstated instance is added.

Independent H4 searches, with different phrasing from the worker:

- LeanSearch: “The Kummer residue at the origin of the affine line over an
  algebraically closed field identifies supported cohomology in degree two with
  finite coefficients and kills all other degrees”. Eight results were residue-field
  maps and finite-cyclic group cohomology, not this calculation.
- LeanFinder: “The localization connecting map for etale cohomology on A1 over an
  algebraically closed field takes the Kummer torsor of the coordinate to the
  canonical generator of local cohomology at zero”. Eight results concerned standard
  etale algebra presentations and cotangent localization, not supported cohomology.
- Loogle: `"residue", "cohomology"` returned zero results.
- The separate full-Mathlib `msearch.py ... grep` query
  `supported.*[Cc]ohomology|[Kk]ummer.*boundary|[Ll]ocal.*[Pp]urity` returned zero hits.
- I searched Mathlib, the named upstream `WeilConjectures` tree, and project
  `lean/Sheaf` using `residue`, `localCohomology`, `localCalculation`,
  `support.*Kummer`, `Kummer.*support`, and comparison/helper names. I opened the
  tempting upstream `HasKummerClass.IsNormalized`: it assumes the geometric
  normalization of an abstract Kummer datum and proves none of this concrete finite
  calculation. `OrdinarySupportedKummerBoundary` supplies supported Cartier-class
  constructions, not this residue theorem. `comparisonCohomologyMap` in
  `AbelianEtaleProEtaleCohomologyComparison` is an abelian Ext/global-sections map,
  whereas this statement requires module-valued derived evaluation at an arbitrary
  etale object. No exact existing declaration or usable duplicate was found.

I found no mathematical mismatch to repair. I did find that the seven-step proof-plan
docstring omitted the IDs of the dependency nodes it uses (H8). I added those IDs
and spelled out the already prescribed coefficient-induction and level-compatibility
steps. The theorem signature, definitions, imports, and both node records are unchanged
by the second reading. Each module has only its owning theorem postponed by `sorry`;
all helper definitions have real data, and the sole `Classical.choose` of an Ext
comparison is fixed uniquely by its cocycle characterization. No private declaration,
file-local notation or instance, hidden statement `let`, or proved theorem was added.
I checked that both `lean.statement` strings are verbatim the declarations' signatures
and that every Lean line is at most 100 characters. The first independent compile
through `scompile.py`, with both sibling modules in dependency order, passed cleanly.
The final version was compiled again with both sibling modules through the same
wrapper: the dependency took 2.6 seconds and the main module 18.0 seconds in their
library checks, with no errors or warnings.
