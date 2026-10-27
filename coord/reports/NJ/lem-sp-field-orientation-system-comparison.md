## Worker report

The module `Sheaf.Paper.FieldOrientationSystemComparison` states `AlgebraicGeometry.ProEtale.FieldOrientationSystem.field_orientation_system_comparison`. It also states the node's restricted equality-detection clause as `FieldOrientationSystem.shifted_sheaf_map_ext`. Both theorem proofs are exactly `sorry`; all helper definitions have actual data. The returned delivery 67c58497ee8f is repaired in `lean` and, as explicitly requested by H2, `stmt_deps`. There are no new nodes or natural-language statement corrections. A sandbox consumer-module repair of upstream instance-synthesis failures is described under Dependency modules below; they change no declaration signature. The current base node still has the same statement and original 16 statement dependencies; this repair retains all other base fields and adds the 15 landed definition owners listed below.

Source read: current `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md`, paragraph (2), including its transpose definition and its restriction to rank-one orientations; the item's expanded proof steps were read in full. The module docstring and main theorem docstring retain that proof plan. The source's informal “checked levelwise” is interpreted through the shifted heart, not a faithfulness assertion for general derived tower evaluations.

Hypotheses and clauses, checked with the node and module open:

- The finite-field datum, algebraic closure, coefficient prime and its inequality with the characteristic are `P : PurityFiniteSetting`. `Index P` is the published `Padic.FiniteCoefficientFields` inside its fixed coefficient closure. `E F` and `hEF : E ≤ F` are the specified field inclusion. Rings and actual inclusion maps are `SpTowerShriek.R` and `D.coefficients E F hEF`, normalized on residue classes in `FieldShriekSystem.Coefficients`. Positive exponent n+1 is indexed by n : ℕ, so n=0 includes the first quotient.
- Separated finite-type k-schemes are the two `Over`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` structure-morphism instances. The morphism is displayed as `j ≫ p`; `j` is open and `p` proper. This presents the fixed compactification. `IsOver`, `IsSeparated`, and `SmoothOfRelativeDimension d` express k-linearity, separatedness and pure relative dimension. `d : ℕ` includes zero. `IsNoetherian X`, `QuasiCompact (j ≫ p)`, and `HasCompactification` are the published tower-gamma instances, not new geometric assumptions.
- `D : FieldShriekSystem.Models P` supplies the section-preserving ordinary derived category of strict varying coefficient towers and universal K-flat scalar extension. `normalized P D` is the recorded normalized full subcategory with independent uniform bounds.
- `b : FieldShriekSystem.Laws ...` retains the specified proper coefficient mate followed by open tensor identification. `a : FieldExceptionalSystem.Domains ...` supplies preservation. `A : Adjoints ...` supplies actual right adjoints with units, counits, finite realizations and counit normalization. Scalar extension is literally `(D.scalars E F hEF T).T`.
- `coefficientUnit` is the actual `SpTowerGamma.unit`, included in N. `omega` is `A.right` applied to this unit, exactly the dualizing system. `Coordinates` groups the published twists, root lines, coefficient coordinates and tensor coordinates. `line` is `SpTowerGamma.orderedLine`, with d=0 the coefficient unit. `lineWord` and `unitWord` are the explicit finite comparison words.
- `IsOrientation` concretely states at every level the `OrientationNormalized` diagonal/DNC condition, the canonical unit origin equation, and the final equation through `finiteRightComparison`, `rightIso`, and evaluation. It is therefore the specified finite orientation, not an arbitrary endpoint map.
- The conclusion's `q` and `t` are actual whole-system isomorphisms implementing C_Y J_A = J_B and C_X(J_A(d)[2d]) = J_B(d)[2d]. `IsUnitComparison` pins q to the scalar unitor and `IsLineComparison` pins t to the root-generator-normalized `CoefficientLineComparison.tensorPower`, with identity root map.
- The displayed equation is `(C_X.map oE) ≫ component ≫ G_B.map q = t ≫ oF`. `component` is the dependency's actual adjunction transpose of scalar extension of epsilon_A composed with b inverse, so this is precisely c_J C_X(a_A)=a_B as a whole-system arrow.
- The next two conjuncts state cohomology concentration outside degree -2d. `IsHeartInduced` uses `heartSheaf` = H^0(V[-2d]) for both the concrete ordered source and the target. Its two single-sheaf identifications induce the canonical identity on H^0, so neither can be rescaled. `heartIdentification` shifts these fixed identifications back. The unique strict-system sheaf morphism h reconstructs o, and, for every level and every candidate finite sheaf morphism beta, the full finite reconstruction equation holds if and only if beta = ev.map h. The finite reconstruction equation has right side `Ev.map o`; transporting it by the already fixed, invertible `lineWord.comparison` gives precisely `IsOrientation`’s prescribed finite diagonal/DNC map. The equation is written after canceling that canonical comparison to avoid expensive repeated unfolding. Thus this clause identifies the sheaf maps themselves with the finite orientations, using the same canonical source cohomology, rather than choosing an unconstrained iso from an abstract Tate line. `shifted_sheaf_map_ext` states componentwise equality only for shifted single maps; no arbitrary derived evaluation faithfulness is asserted.
- The two finite-unit conjuncts state Tor amplitude `[0,0]` at every positive level before twisting. The last two conjuncts quantify all candidate maps with the prescribed finite orientations, including non-isomorphisms, and state uniqueness.

Dependency declarations read and used: `Sheaf.Paper.PurityFiniteSetting` (`WeilConjectures.PurityFiniteSetting`); `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (`Padic.finite_coefficientExtensionRing`); Mathlib smoothness (`AlgebraicGeometry.Smooth`); `Etale.DerivedCategoryModule`; `spCoefficientTowers`, `sp_coefficient_towers_abelian`, `spNormalizedConstructibleTorTowerCategory`; `SemilinearSections.semilinearDerivedSections` and `ScalarData`; `sfQbarTwistingFunctor`; `SpTowerGluing.tower_gluing`; `SpTowerShriek.R/S/D/Ev`; `FieldShriekSystem.Models/Laws/normalized`; `FieldExceptionalSystem.N/Domains/Adjoints/component`; `SpTowerGamma.unit/orderedLine/coefficientWord/factorization/finiteRightComparison/tower_gamma`; `scalarExtensionFunctor`; and `reductionCompatibilities_purity`. The proof-only imports are `FieldScalarNormalizedSystems`, `FiniteOrientationReduction`, `StrictLineHeartAssembly`, Mathlib `DerivedCategory.ExactFunctor`, and `DerivedCategory.FullyFaithful`. All declarations were read from their full source signatures and docstrings.

Edge cases checked: d=0, empty schemes, E=F and identity scalar unitor, first level n=0, ramified extensions (actual ell-power quotients and no flatness assumption), object/morphism universes u+1/u, candidate non-isomorphism in uniqueness, and the restriction of componentwise detection to shifted degree-zero systems.

Searches actually run: LeanFinder for “Coefficient change preserves diagonal purity orientations as maps of shifted degree zero coefficient towers” (eight unrelated algebraic hits); LeanSearch for “Scalar extension preserves smooth purity orientations on coefficient tower systems” (eight unrelated smooth/scalar hits); Loogle for `DerivedCategory.singleFunctor` (generic single/full/faithful declarations only); Mathlib grep for `orientation|dualizing` in `Algebra/Homology/DerivedCategory` (no hits); `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the item and field-orientation patterns (no exact existing theorem). Related finite orientation, scalar, exceptional, and tower-gamma interfaces were read and reused.

Validation of the returned version: scompile passed in 46.4 seconds. Repair validation is recorded below. In the item’s module, both postponed theorems are explicitly bound under `autoImplicit false` and both proofs are `sorry`. The consumer modules retain their existing proofs apart from the explicitly described elaboration repair.

## Second reading by NJ

No second worker was started because the dispatcher brief prohibits subagents; the maintainer's independent review is the delivery review. A separate self-check against the node and source confirmed the coefficient-unit and twist source words, direction of q, t and c, concentration at -2d, uniqueness for arbitrary candidate morphisms, heart assembly, finite-unit Tor bounds, and restricted componentwise detection. The initial abstract draft was replaced by concrete OrientationNormalized, unit/root and counit predicates after compilation review. No node or source correction was needed.

## Returned delivery repairs

H2: added the following already landed owners to `stmt_deps` and imported their
modules publicly. No duplicate notions or replacement dependency interfaces were introduced.

| Owner | Module | Declarations used |
|---|---|---|
| def-sp-field-shriek-system-models | Sheaf.Paper.FieldShriekSystemModels | FieldShriekSystem.Models, Index, normalized |
| def-sp-field-exceptional-system-domains | Sheaf.Paper.FieldExceptionalSystemDomains | FieldExceptionalSystem.N, Domains, level |
| def-sp-field-exceptional-system-adjoints | Sheaf.Paper.FieldExceptionalSystemAdjoints | Adjoints and its right, finite and evaluation projections |
| def-sp-field-exceptional-system-components | Sheaf.Paper.FieldExceptionalSystemComponents | component |
| def-sp-chart-tate-tower-data | Sheaf.Paper.SmoothPurityTowerChartData | SpChartAdmissibility.Twists |
| def-sp-coordinate-right-comparisons | Sheaf.Paper.SmoothPurityCoordinateRightComparisons | SpCoordinateAdjunction.RootLines |
| def-sp-p1-coefficient-coordinates | Sheaf.Paper.TowerP1CoefficientCoordinates | SpTowerP1.CoefficientCoordinates, unitWord |
| def-sp-p1-tensor-derived-coordinates | Sheaf.Paper.TowerP1TensorCoordinates | SpTowerP1.TensorCoordinates |
| def-sp-p1-level-words | Sheaf.Paper.TowerP1LevelWords | SpTowerP1.LevelWord, levelRing, levelAnnihilates, nu |
| def-pur-finite-smooth-canonical-maps | Sheaf.Paper.FiniteSmoothPurityMaps | Etale.FiniteSmoothPurity.line, OrientationNormalized |
| def-pur-finite-smooth-coefficient-arrows | Sheaf.Paper.FiniteSmoothCoefficientArrows | CoefficientLineComparison, tensorPower, scalarZeroLineIso |
| def-pur-finite-ring-section-data | Sheaf.Paper.FiniteRingSectionDeformation | Etale.FiniteRingSectionDeformation.Geometry |
| def-sp-reduction-exceptional-realization-objects | Sheaf.SecSmoothPurity.ReductionExceptionalObjects | reductionSiteScalarIso; ReductionExceptionalRealization and its origin/right/adjunction/originIso/rightIso projections via A.finite |
| def-sp-tower-gamma-data | Sheaf.Paper.SmoothPurityTowerGammaData | SpTowerGamma.unit, orderedLine, coefficientWord, factorization, finiteRightComparison |
| def-asd-ordinary-finite-p1-kummer-class | Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer | Etale.ordinaryFiniteUnit |

H3: replaced the unpinned source isomorphism by the canonical cohomology presentation
of the concrete ordered source. Both source and target identifications satisfy the
standard H^0 normalization. Added the levelwise beta/evaluation equivalence, with
canonical exact single/shift comparisons, in the same form as
`SpStrictLineHeart.strict_line_heart_assembly` (allowing all beta morphisms, so the
uniqueness covers the node's non-isomorphism candidates too). The prescribed finite
map is `Ev.map o`, whose transport by `lineWord.comparison` is the map normalized
by `IsOrientation`. The invertible comparison is canceled from the equation for
elaboration efficiency; no arbitrary source isomorphism is introduced.
A rescaling of the source identification fails its H^0 normalization, and a
rescaling of h fails its beta/evaluation equation. The source cohomology is that
of the actual ordered tensor Tate line, not a newly chosen isomorphic object.

The helpers `heartSheaf`, `heartIdentification`, and `evaluationSingleShift` carry
actual functor/shift data and are listed in `lean.declarations`. They belong to this
node's concentrated-object clause; none asserts an extra independent theorem.
For d=0 the common shift is zero and both H^0 normalizations and finite equations
remain in force. For n=0 the first positive quotient is still checked. For E=F the
same finite constraints prevent an undetected unit automorphism.

Repair searches: `rg` for `orderedLine`, `coefficientWord`, `evaluationSingleShift`
and `strict_line_heart_assembly` in the existing gamma/assembly modules, then
`rg` for `SpEllTwistComparisons`, `spEllTwistLine`, `RootLines`, `Models`, and
`normalized` in Sheaf. These located the existing source words and canonical
single/shift comparisons. The assembly theorem is in strict-tower realization
coordinates; this module uses the equivalent semilinear sequence-site coordinates,
so its single/shift helper is the actual exact-evaluation composite for those
categories. No extra mathematical notion or new dependency repair is required.

## Dependency modules

The only remaining consumer repair is
`Sheaf.Paper.NormalizedCompletionRealization`. Its existing normalization proofs
use `SemilinearSections.moduleAbelian`, which server confirmation could not find
through the published imports. The sandbox copy adds exactly
`import all Sheaf.Paper.SemilinearSystemModels`, the owning module confirmed by
`scompile.py --source`. No declaration, signature, definition data, or proof text
is changed. This repair compiled in the private overlay in 41.7 seconds and in current-source
server confirmation in 54.8 seconds.

Three earlier dependency failures were repaired independently on current main
while this request was running. Fresh server `--source` checks matched the
refreshed read clone for each: `IntegralObjectPullbackQuotientBasis` now exports
its fixed site-size witness; `EmbeddedFiniteHeartMonoidalPresentation` supplies
explicit smallness locally; and `CoefficientScalarTensorRealization` transports
the monoidal-adjunction proposition along `internalPullOplax_eq_canonical` using
its new private helper. All three obsolete sandbox copies have been removed.
The final delivery uses those current published modules without editing them.

## Compilation refactor

The unsplit repaired statement elaborated but took 60.3 seconds, above the
per-file limit. Its expensive finite normalization definitions are now split
without changing their declarations or bodies:

- `FieldOrientationSystemCoordinates`: coefficient unit, coordinates, source
  line and finite words, and dualizing object.
- `FieldOrientationSystemFiniteOrientation`: actual finite diagonal/DNC
  normalization predicate.
- `FieldOrientationSystemNormalizations`: unit- and root-normalized scalar
  comparison predicates.
- `FieldOrientationSystemHeart`: canonical cohomology sheaf, canonical shift
  and exact-evaluation comparisons, and the pinned heart-assembly predicate.

The owning `FieldOrientationSystemComparison` publicly imports these definitions
and contains both postponed theorems. Every helper is still listed in the item's
`lean.declarations`, and all four support modules contain real data and no sorry.
Proof-only imports remain in the theorem module. Large normalization predicates
are irreducible after construction; `heartSheaf` stays transparent so the canonical
H^0 normalization elaborates. The generic `scalarReductionSiteSmall` instance is
disabled in this construction to avoid an unconstrained coefficient universe;
the already fixed site uses ordinary self-smallness. No extra universe equality
or mathematical hypothesis is imposed. No diagnostic profiler or trace options
are retained.

Final `scompile.py` validation passed, exit 0, with no errors or warnings:
coordinates 9.1 seconds, finite orientation 22.1 seconds, scalar normalizations
25.2 seconds, canonical heart 9.3 seconds, comparison 16.5 seconds, and the
completion import repair 41.7 seconds. Each was also compiled independently in
its sandbox namespace, with a maximum of 42.6 seconds. All are below 60 seconds.
The owning theorem signature was checked verbatim against `lean.statement`;
only `lean` and the requested landed-definition additions to `stmt_deps` differ from the base
node. All Lean lines are at most 100 characters, and debug options are absent.

Required delivery dry run passed: `OK (dry run): commit e946a15476f passes
the preflight and compiles; nothing pushed`. All six modules were included;
preflight accepted the four real-data support modules and the import-only
consumer repair.

## Returned H2 ownership repair (a6aca24552c4)

The previous report-only format repair did not apply the required statement-edge
correction. This delivery now edits the item node itself: `stmt_deps` replaces
`det-sp-reduction-exceptional` by
`def-sp-reduction-exceptional-realization-objects` and adds
`def-sp-tower-gamma-data`. These are already landed definition nodes, whose Lean
records, full signatures and docstrings were read from the current base.

Both `FieldOrientationSystemCoordinates.lean` and
`FieldOrientationSystemComparison.lean` replace their public import of
`Sheaf.SecSmoothPurity.ReductionExceptional` by
`Sheaf.SecSmoothPurity.ReductionExceptionalObjects`, and explicitly add
`public import Sheaf.Paper.SmoothPurityTowerGammaData`. The definition ownership
table above has the same two corrected owners. The existing tower-gamma theorem
import is retained for the orientation theorem already cited by the item.

`reductionSiteScalarIso` is the canonical site/scalar comparison definition, not
the theorem `reductionExceptional_isIso`. The finite realization fields used
through `A.finite` belong to `ReductionExceptionalRealization` in that same
objects module. `SpTowerGamma.unit`, `orderedLine`, `coefficientWord`,
`factorization` and `finiteRightComparison` belong to the extracted gamma-data
module; the comparison of ordinary right adjoints preserves the given counit.

The mathematical declaration signatures and bodies are unchanged; the Lean
source delta consists of the two requested import changes in each of the two
modules. H3's normalized i/j and beta/evaluation characterization of h remain
in force. The natural-language node statement, proof and proof dependencies are
unchanged. No new node or statement correction is introduced.

Rebase check: the current base node has the original 16 statement dependencies
and no Lean record. This delivery has those 16 plus 15 landed definition owners.
The completion consumer still differs from current main by precisely its
`import all Sheaf.Paper.SemilinearSystemModels` line. Earlier compile and dry-run
timings above refer to the preceding source version; this repair is compiled
and dry-run separately below.

This H2 repair passed the prescribed six-file `scompile.py` call, exit 0,
with no errors or warnings. Library timings: coordinates 12.8 seconds, finite
orientation 30.2 seconds, scalar normalizations 33.5 seconds, heart 18.3 seconds,
comparison 18.9 seconds, completion consumer 41.7 seconds. Independent sandbox
checks also passed; the maximum was 42.6 seconds.

Required H2-repair dry run passed: `OK (dry run): commit ea88ad8b7fd passes
the preflight and compiles; nothing pushed`. The delivery contains the actual
node dependency swap/addition and both pairs of Lean import edits.
