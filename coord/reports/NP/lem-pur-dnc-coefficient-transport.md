## Worker report

This repair retains the saved canonical-map implementation in
`Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` and repairs its explicit
coefficient universes and stale delivery records. The theorem is
`WeilConjectures.dncCoefficientTransport`; its conclusion is the proposition
`DncCoefficientTransport.Assertions`, whose constituent propositions have actual
maps and equations as their definitions. All postponed proofs are `sorry`.

The source is main-20261015,
`sec-smooth-purity/sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md`,
Proof (2), together with the seven proof steps already in the DAG node. The prose
statement is restored verbatim from the current base. There is no statement
correction and no `statement_change` record.

Hypothesis and object correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field | `D : FiniteFieldDatum.{u}`, including its field, algebraic-closure and cardinality fields. |
| Prime ell distinct from the characteristic | `ell : ℕ`, `[Fact ell.Prime]`, `hell : ell ≠ D.p`. |
| Positive n, R = Z/ell^n | `n : ℕ`, `hn : 1 ≤ n`, `BaseRing ell n = ULift (ZMod (ell ^ n))`. This is not an arbitrary extension's residue quotient. |
| Finite commutative B and unital map R → B | `{B : Type u} [CommRing B] [Finite B]` and `φ : BaseRing ell n →+* B`. RingHom preserves one; no nonzero or flatness hypothesis occurs. |
| Separated finite-type k-schemes and k-morphisms | `aS : S ⟶ Spec (.of D.k)` with separated, locally-finite-type and quasi-compact instances; the structure map on V is `g ≫ aS`. The retraction equation makes s a k-morphism. The schemes quantified by `MixedBaseChange` and `ChartCompatibility` are explicitly objects of `Over (Spec (.of D.k))` with separated finite-type structure maps. |
| Smooth separated g of pure relative dimension r ≥ 0 | `d : ℕ`, `g : V ⟶ S`, `[SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]`. Smooth relative dimension supplies smoothness and local finite type. |
| Closed section s | `s : S ⟶ V`, `[IsClosedImmersion s]`, `hs : s ≫ g = 𝟙 S`. |
| Fixed coefficient-independent compactifications | The proof-valued `Geometry g s`, supplied by the named theorem `geometry D d g aS s hs`, provides compactification instances for g, the actual deformation projection, and the actual normal projection. The same instances are used at both rings. They are consequences, not extra hypotheses. |
| Ordinary uncompleted coefficients and constructible exceptional adjoints | `Etale.sectionInvariant` uses the ordinary compact-support right adjoint. `sectionObject A g s` is its canonical realization by `ProEtale.reductionSite A S` in `Scheme.proEtaleDerivedCategory S A`. The published reduction-exceptional interface identifies this finite constructible adjoint with the specified constructible pro-etale one. No derived completion is used. |
| Tate lines from roots of unity and their pullbacks | `ChartCompatibility` uses the published `OrdinaryFiniteTwistTransport`, `OrdinaryFiniteP1Datum`, and `reductionEtaleChartScalarIso`; these fix the root-normalized finite Tate lines and ordered affine trace, including the shift. No arbitrary `HasTateTwist B` is a theorem hypothesis. |
| C_D(g,s) = Ls* g_D! D_S | `Etale.sectionInvariant A g s` is literally section pullback of the ordinary dualizing complex for the ring A. `sectionObject` realizes it on the pro-etale site. |
| Actual deformation and family F_D | `Scheme.Hom.deformationSpaceProj g s` and `s.deformationSpaceSection` are the published extended-Rees construction and augmentation. `NoetherianSectionSpecialization.family A g s` is the section invariant of precisely these maps. The dependency module retains the recorded `purityDncIntrinsicFamily` on this same geometry. |
| Actual normal bundle and zero section | `Scheme.Hom.normalConeProj g s` and `s.normalConeZeroSection`. `purityNormalProjection_eq` and `purityNormalCone_comparison` identify this actual Rees zero fibre with the recorded normal projection and Spec Sym(I/I²). In particular the normal coefficient map is evaluated at this projection, not at g. |

Conclusion correspondence, including each compatibility:

| Node clause | Lean rendering |
| --- | --- |
| Counit-characterized c_g | `dualizingMap φ g` is `ExceptionalCoefficients.mateMap φ g (𝟙_ _)` followed by exceptional inverse image of `unitIso φ S`. The former is explicitly the transpose of the scalar-extended counit through compact-support comparison. |
| q_(g,s), q_F, q_normal are the specified isomorphisms | `sectionMap` is the inverse scalar/pullback exchange followed by pullback of `dualizingMap`. It is applied separately to `(g,s)`, the Rees projection/augmentation, and the normal projection/zero section. `Assertions` asserts `IsIso` for all three maps both in their etale-origin presentation and after `realizedSectionMap`. Their targets use the exceptional inverse image for B itself. |
| Canonical fibre identifications at one and zero | The four `IsIso` assertions on `NoetherianSectionSpecialization.atOne` and `.atZero`, for R and B. Those definitions use the specified Cartesian Rees fibre squares and the canonical exceptional base-change mates pulled to sections. |
| Arbitrary smooth base-change exchange and coefficient square, with no section on g0 | `MixedBaseChange D (RingHom.ulift φ)` quantifies independently over V, S, S', a smooth relative-dimension morphism g and any base morphism h. It asserts invertibility of both `smoothDualizingBaseChangeMap`s and `ExceptionalCoefficients.BaseChangeCompatibility φ g.left h.left (𝟙_ _)`. This is the displayed e/c square with scalar/pullback and unit identifications written into the existing definition. No section binder is present. |
| q respects both fibre identifications | `FibreCompatibility` is a conjunction of two actual morphism equations, with `atOne` and `atZero` respectively. Each says exchange, then pullback of q_F, then eta_B equals scalar extension of eta_R, then q of the corresponding fibre pair. |
| Etale localization of pairs | `LocalizationCompatibility` quantifies over an etale Cartesian base localization and compatible sections, and equates the two actual composites through `NoetherianSectionSpecialization.sectionMap`. `ChartCompatibility` additionally handles source coordinate charts, by its open immersion i and etale coordinate map e; it does not replace source charts by base localization. |
| Standard coordinate pair gives the canonical shifted Tate coefficient map | `ChartCompatibility` equates scalar extension of the counit-normalized chart identification followed by `reductionEtaleChartScalarIso` with pullback of `dualizingMap` followed by the B chart identification. The identity chart is the standard pair. Pulling this equation along its zero section gives `(R_S(d)[2d])_B ≅ B_S(d)[2d]` through the specified root-normalized scalar and pullback identifications. |
| The given normalized R comparison | The `∃! κR` conjunct in `Assertions` uses the actual family and canonical `Normalized` predicate. `NormalizedTransport` then quantifies over every such κR, so it applies in particular to the comparison of `prop-pur-dnc-family-constancy`. |
| Formula for κ_B | In `NormalizedTransport`, the coefficient equation is `qF ≫ κB.hom = scalar.map κR.hom ≫ exchange.inv ≫ aStar.map q`. Since qF is asserted invertible, this is exactly conjugation by qF inverse in the node. κB has source the independently formed B family. |
| Normalized to identity at t=1 | `NoetherianSectionSpecialization.Normalized B g s hs κB` says pullback of κB followed by the canonical section/composition unit identification equals `atOne B g s hs`. This is the required identity after identifying the fibre, not reflexivity of an arbitrarily supplied isomorphism. |
| Uniqueness | The conjunct `∀ κ, Normalized B g s hs κ → κ = κB` quantifies over every family isomorphism of the required type. It does not assume the competing κ is coefficient-compatible. |
| Local constant-family comparison on every etale coordinate chart | `CoordinateNormalization` equates restriction of κB, followed by line-pullback comparison and the constant model read at one by `sectionRestrictionIso`, with the given constant-family model e. Quantification covers every such etale local constant model, including the standard centered coordinate models. |
| δ_D is inverse zero restriction of κ_D | The published `NoetherianSectionSpecialization.specialization A g s κ` is section/composition identification, pullback of `κ.inv` at zero, then `atZero`. Its source and target are the section objects of g and the actual normal projection. |
| δ_B q = q_normal (δ_R)_B | The last equation of `NormalizedTransport` is precisely `sectionMap φ g s ≫ specialization B ... κB = scalar.map (specialization A ... κR) ≫ sectionMap φ normalProj zeroSection`. Its preceding `IsIso` conjunct asserts the specialization is invertible. R invertibility also follows from κR and the asserted zero-fibre isomorphism. |
| Dimension zero and zero coefficient ring | d is unrestricted in ℕ; no `Nontrivial B`, nonempty scheme, positive dimension, or flatness assumption is added. |

The equations are written in the ordinary etale-origin presentation, using the
published actual etale section invariant rather than a second copy of it. Their
pro-etale interpretation is through the fixed `reductionSite` realization and
its `reductionSiteScalarIso`; these are the canonical site and coefficient
comparisons of `det-sp-reduction-exceptional`. In particular the three realized
coefficient maps have targets in B-coefficients and are asserted invertible.
This does not identify the etale and pro-etale ambient derived categories without
a comparison, nor impose that arbitrary pro-etale complexes have etale origin.
Only the finite constructible section, family and normal objects are involved.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.PurityDncFamilyIntrinsic`: the recorded constructed geometry and
  `WeilConjectures.purityDncIntrinsicFamily` (dependency repair below).
- `WeilConjectures.AlgebraicGeometry.DeformationToNormalCone`: the actual Rees
  deformation, its projection, augmentation, fibres and normal-cone projection.
- `Sheaf.Paper.PurityNormalCone`: `purityNormalProjection_eq` and
  `purityNormalCone_comparison`, connecting these to the recorded normal bundle.
- `WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions`:
  `AlgebraicGeometry.Etale.sectionInvariant`, whose signature and definition
  really use the ordinary exceptional image for the indicated coefficient ring.
- `Sheaf.Paper.NoetherianEtaleSectionSpecialization`: `family`, `sectionMap`,
  `atOne`, `atZero`, `Normalized`, `specialization`, `linePullback`.
  Its already-landed node is added to `stmt_deps` to record the actual interface.
- `Sheaf.SecSmoothPurity.ReductionExceptional`: `reductionSite`,
  `reductionSiteScalarIso`, `reductionEtaleChartRightIso`,
  `reductionEtaleChartScalarIso`, `reductionExceptional_isIso`.
- `Sheaf.Paper.ExceptionalCoefficientComparison`: `mateMap`, `unitIso`,
  `BaseChangeCompatibility`; `Sheaf.Paper.PurEtaleScalarMateProjection`:
  `scalarPullbackIso`; `Sheaf.Paper.EtaleDerivedScalarTensor`: `scalarExtension`.
  These are published constituent interfaces of the recorded reduction module.
- `WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation`:
  `DeformationToNormalConeData.existsUnique_familyObject_iso`. The older local
  source omits this declaration, so the current source was read with
  `scompile.py --source`; it supplies normalization and uniqueness against a
  fixed one-fibre identification.
- Constructible pro-etale coefficient categories, constructibility, finite Tor,
  localizing exceptional adjoints and their finite preservation are those
  reexported by the recorded intrinsic-family and reduction modules; none is
  privately redefined here. The tensor/pullback comparison is the recorded
  representative-normalized comparison reexported through `scalarPullbackIso`.
- Smoothness, closed immersion, finite type, properness and affine space are
  Mathlib's recorded definitions. Finite type is locally finite type plus
  quasi-compactness; the affine line uses `ULift (Fin 1)` coordinates.

Edge cases checked by expanding the definitions: d=0 gives the same formulas
with shift zero; empty S gives unique maps; B=0 remains a finite unital ring
and every assertion still has its required object and map; identity coefficient
maps are allowed; nonflat maps R→B still use derived scalar extension. Only the
named theorem proofs are postponed. `Geometry` contains propositions, not a
selected deformation or an arbitrary exceptional functor. The theorem docstring
now carries all seven DAG proof steps, including the finite-underlying-R-module
argument for uniqueness over a possibly nonflat B.

Searches retained in `searches.jsonl` and checked against their actual results:

- LeanFinder, “coefficient transport for deformation to the normal cone normalized
  family comparison”: eight normalization-diagram results, no matching theorem.
- Loogle, `CategoryTheory.Iso, Scheme.proEtaleDerivedCategory, scalarExtensionFunctor`:
  no hits; its note says the project identifier is unknown to Loogle, so this is
  not counted as evidence that the project has no declaration.
- Mathlib grep, `coefficient.*transport|DncCoefficientTransport`: no hits.
- LeanFinder, “canonical smooth exceptional inverse image scalar extension
  deformation normal cone family normalization”: normalization and smoothness
  results, no matching coefficient theorem.
- Loogle, `CategoryTheory.Iso, CategoryTheory.Adjunction`: generic adjunction
  transport results, no matching theorem.
- Mathlib AlgebraicGeometry grep, `deformation.*coefficient|coefficient.*deformation`:
  no hits.
- Source/shared `rg` found the actual Rees construction, recorded normal-cone
  comparison, ordinary section invariant, Noetherian fibre/normalization helpers,
  and counit-mate coefficient interfaces. Those are reused. No existing theorem
  with this entire coefficient-transport statement was found.

No new definition node and no `STATEMENT-DISPUTED` flag is needed.

## New nodes

This delivery records four existing plain definitions as explicit definition
owners, as required by the returned review:

- `def-pur-noetherian-section-specialization-arrows` owns `family`, `sectionMap`,
  `atOne`, `atZero`, `Normalized`, `specialization`, and `linePullback` in
  `Sheaf.Paper.NoetherianEtaleSectionSpecialization`.
- `def-pur-exceptional-coefficient-base-change-square` owns
  `ExceptionalCoefficients.BaseChangeCompatibility` in
  `Sheaf.Paper.ExceptionalCoefficientComparison`.
- `def-asd-smooth-dualizing-base-change-arrows` owns the smooth dualizing
  base-change maps in `Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange`.
- `def-amb-affine-trace-right-functor` owns the affine trace right functors in
  `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`.

The existing theorem nodes `lem-pur-exceptional-coefficient-comparison` and
`lem-pur-etale-scalar-mate-projection` remain cited as proof dependencies for
their uniquely selected `unitIso` and `scalarPullbackIso` data; their theorem
statements are not statement dependencies.

## Dependency modules

`def-pur-dnc-section-family`: the saved packet repairs the recorded
`Sheaf.Paper.PurityDncFamilyIntrinsic` import closure. The old import of
`PurityDncFamily` unnecessarily loads the retired mixed-interface section
invariant alongside the current canonical upper-shriek interface. The delivery
removes that import and supplies the required compactifiability statement as
`purityDncIntrinsicCompactifiable`, with its own source and proof docstring.
The actual Rees geometry, structural map, augmentation, finite family and finite
Tor/tensor-invertibility assertion are retained. The dependency node changes only
in `lean`, with an explanatory note. No scheme or coefficient object is chosen
from a bare existence theorem. The new postponed theorem proves only a geometric
compactifiability property and belongs to this same definition node.

## Second reading by NP

This is a fresh repair worker's reading of the inherited packet, with the current
prose node, saved Lean modules and the return open. The earlier report was stale:
it named removed declarations and omitted this reading. It has been replaced
with the hypothesis/object and conclusion tables above. The current node copy
has the original prose, no `statement_change`, and only `lean` plus the added
already-landed helper dependency changed. The five existing citers remain
`lem-pur-orientation-ground-field-retagging`,
`lem-pur-finite-dnc-normalization-reduction`,
`lem-pur-finite-universal-smooth-trace`, `det-sp-purity-bc-factors`, and
`det-sp-finite-general-ring`; none is modified or falsely marked `holds:false`.

Return-point check:

1. H5/H3: expanding `sectionMap` shows an actual counit mate whose target is the
   independently formed B exceptional image. The same definition is evaluated
   at the Rees and actual normal projections. Expanding `FibreCompatibility`,
   `MixedBaseChange`, `NormalizedTransport` and `ChartCompatibility` gives actual
   categorical equations. There is no replacement of a coefficient square by a
   scheme-morphism equality, or an arbitrary isomorphism field filled by refl.
2. H3: `BaseRing` is explicitly lifted `ZMod (ell ^ n)`; the theorem takes a
   positive n and no arbitrary `PurityFiniteSetting` coefficient extension.
3. H7/H2: the original prose is unchanged and `statement_change` is absent;
   all five citers are retained unchanged. Node signatures and declaration lists
   are updated to the actual current file, including its helper declarations.
4. H11: the report now describes the actual saved canonical-map implementation
   and its etale-origin/pro-etale comparison precisely. It contains no failed
   self-check conclusion paired with an assertion of success.
5. H8: both postponed geometric facts and the main theorem have source/blueprint
   docstrings. The main theorem lists the seven proof steps, including the two
   fibre squares, arbitrary base change without a section, local counit
   normalization, nonflat uniqueness, and the final inverse-zero-fibre equation.
6. H9: each helper has its own source/blueprint docstring; the obsolete duplicate
   import is removed in the dependency repair; there are no auto-bound variables
   or local notation. Coefficient lifts now explicitly use
   `RingHom.ulift.{u+1,u+1,u,u}`, repairing the concrete universe failure from the
   first dry run without changing the mathematical coefficient rings.

Validation is recorded after the final compile and dry run below.


## Interrupted-turn continuation and validation

The prescribed initial dry run of the saved packet on 2026-10-18 failed with
unknown identifiers `ProEtale.affineTraceTower` and
`ProEtale.affineTraceProjection`, followed by a dependent elaboration timeout.
Reading `Sheaf.AlgebraicGeometry.AffineTraceTower` shows that both declarations
are in `AlgebraicGeometry`; the two references now use those existing names.
No new coordinate-space definition is introduced. The dependency module's Picard
proof docstring now names its actual compactifiability helper rather than the
removed import's helper.

The fresh self-check opened the current prose node, both saved modules, the
source's Proof (2), and the published signatures of `mateMap`, the chart
comparisons and the section-specialization maps. The original prose is unchanged;
only `lean` and the recorded helper dependency differ in the item, and only
`lean` differs in the dependency node. The repaired chart equation uses the
published ordered affine tower and its projection. Its two sides start at the
scalar extension of the A-dualizing object restricted to the chart, and end at
the independently formed B chart object. The normal map uses the actual normal
projection. The normalized comparison is quantified as an isomorphism between
the actual B family and the pulled-back B section object; the last equation uses
the inverse zero restriction through the canonical fibre maps. These checks
confirm the six return-point checks above, including d=0 and B=0.

`scompile.py NP lem-pur-dnc-coefficient-transport` compiled both delivered modules
separately in dependency order with no errors or warnings: the main sandbox
compile took 11.7 seconds and its library-name compile 17.1 seconds. The final
dry run below recompiles both files after the docstring correction.

## Final namespace repair and self-check

The fresh dry run on 2026-10-18 compiled both modules but preflight could not
recognize `WeilConjectures.dncCoefficientTransport`: its namespace scanner treated
the dotted opening `namespace WeilConjectures.DncCoefficientTransport` as one
block and popped it entirely at `end DncCoefficientTransport`. The module now
opens `WeilConjectures` and `DncCoefficientTransport` in separate blocks. This
preserves the compiler's declaration names and mathematical signatures and makes
the scope boundaries explicit to preflight. No tool was changed.

I reread the actual source Proof (2), the restored prose, the two saved modules,
and the definitions `family`, `sectionMap`, `atOne`, `atZero`, `Normalized`, and
`specialization` in the published Noetherian specialization module. The fibre
maps use the actual Cartesian Rees fibre squares, normalization is equality
with the canonical one-fibre mate, and specialization uses the inverse of the
zero restriction. These are the maps used by the saved transport equations.
The item differs from the current base only in `lean` and the added published
helper dependency; the dependency node differs only in `lean`. There is no
`statement_change`. The five citers listed above retain their uses unchanged.
The explicit coefficient target, normal projection, prime-power base ring,
proof docstrings, and helper documentation address the substantive return.

The preceding dry run's compile passed with no errors or warnings; the final
compile and preflight are rerun after the namespace spelling change.

Final validation on 2026-10-18: `scompile.py` compiled both delivered modules
without errors or warnings after the namespace repair. The prescribed
`deliver2.py NP lem-pur-dnc-coefficient-transport --no-push` returned
`OK (dry run): commit c037fe698c passes the preflight and compiles; nothing pushed`.
The delivery command repeats those checks on the packet including this report.
