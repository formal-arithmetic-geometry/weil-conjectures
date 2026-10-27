## Worker report

The delivery states `lem-sfb-relative-duality-polynomial-base-change` in
`Sheaf.AlgebraicGeometry.RelativeDualityPolynomialBaseChange`. Its primary declaration is
`AlgebraicGeometry.relativeDualityPolynomialBaseChange_unique`; the other declarations
in `lean.declarations` give the remaining clauses and their canonical comparison maps.
The original statement, proof, proof dependencies and other metadata are unchanged.
The statement dependencies cite the landed definition owners and the genuine
chosen/asIso comparison owners used by these signatures; the H2 repair below
records the replacement of two theorem citations that supplied only plain definitions.
There are no new independent definition nodes and no dependency record replacements.
All postponed proofs are named theorems with source and complete proof-plan docstrings.
All definitions have actual data, not sorry. This is a stage-2 delivery, not a claim
that the theorems have been proved.

### Hypotheses and clauses

* Schemes and the geometric hypotheses: `X S X' S' : Scheme.{u}`, `f`, `f'`,
  `[IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]`
  and their primed versions. The latter geometric properties are inherited by base
  change; writing their instances names that inherited structure and does not require
  an additional geometric assumption. `a`, `b` and `sq : IsPullback b f' f a` express
  the fibre square invariantly, including every choice of its fibre-product object.
* Supplied pairs: `K`, `ξ`, `hK : IsCoherentRelativeDualizingPair f K ξ`, and `L`,
  `η`, `hL` are the exact dependency predicate. No replacement predicate for a
  coherent relative dualizing pair is introduced. The source and target classes are
  morphisms from the actual degree-zero diagonal object to first-projection pullback.
* Unique intrinsic isomorphism: `_unique` concludes `∃! β : (derivedPullback b).obj K ≅ L`
  satisfying `IsRelativeDualityBaseChange`. The latter is precisely the equality
  between the published canonical `relativeDualizingBaseChangeClass`, followed by
  first-projection pullback of β, and η. Its diagonal comparison is the published
  actual augmentation, with the published isomorphism theorem; it is not an arbitrary
  isomorphism of diagonal objects.
* Identity: `_id` identifies every marked β with `relativeDualizingPullbackId.app`.
  Composition: `_comp` equates the two marked maps using the fixed
  `recordedDerivedPullbackComposition`, for arbitrary successive base changes.
  Isomorphisms of families: `_isoNaturality` gives the four-family commuting square,
  including its canonical pullback associator and the actual commuting-family equation.
* Polynomial charts: `PolynomialKoszulChart` supplies the ordered polynomial algebra,
  its quotient, the top exterior power of Kahler differentials, and its derived
  coinduction object with the natural quotient-ring action. Its coefficient is the
  top differential module in degree `-n`; equivalently the unshifted derived Hom
  shifted by `[n]`. The chart interface also permits principal localizations, which
  are needed for the restriction clause. Genuine polynomial presentations are its
  special case with no localization.
* Specified normalized comparisons: `IsPolynomialBaseChangeNormalizedChart` pins
  `e : LjB* K ≅ tilde C.model` to the supplied ξ and to
  `C.diagonalClass κ`, with `IsKoszulDiagonalNormalization C κ` in the theorems.
  `polynomialBaseChangeAffineDiagonal` is constructed from the original derived
  counit, the actual module base-change map for the diagonal square, and the
  structure-sheaf map. `polynomialBaseChangeAffineTarget` is the recorded pullback
  composition. The auxiliary η in the predicate must satisfy the two independently
  fixed diagonal equations. No freely chosen source/target identification can rescale
  ξ. `exists_polynomialBaseChangeNormalizedChart` supplies these pinned comparisons
  for any supplied pair and any normalized polynomial presentation. This supplements
  the recorded chart theorem, whose displayed atlas only identifies underlying
  objects; it does not replace that dependency's pair or chart notion.
* Native affine transport: `polynomialAffineTilde` is the exact native associated-sheaf
  functor on derived categories. `IsPolynomialBaseChangeTildeComparison` tests τ on
  every complex against the original two derived counits and the ordinary
  unit-normalized tilde comparison. The ordinary comparison is chosen from the
  published theorem fixing its value on the adjunction unit; those values uniquely
  determine it by adjunction. It is not a choice from an unconstrained Nonempty iso.
  `exists_polynomialBaseChangeTildeComparison` supplies the canonical derived τ.
* Affine formula: `_affine` quantifies over the source/base affine opens and the
  primed affine opens with their actual Spec-map equations. A
  `KoszulDiagonalChartChange F` and `F.IsAdmissible` specify the scalar pushouts or
  principal-open restrictions, and the canonical differential and volume maps.
  For the base-change case these are exactly `B' = B tensor_R R'` and
  `P' = P tensor_R R'`, expressed by the universal pushout condition, not by an
  extra flatness assumption on `R → R'`. Its conclusion identifies the restriction
  of β with tilde of `c`, using the canonical chart-square comparison and τ.
  `F.IsComparison c` is the published evaluation-counit equation, including the
  coefficient map; thus the displayed isomorphism is the specified derived-Hom
  scalar map with its natural B'-action. `_model` supplies such a c for every
  admissible change of flat finitely presented algebras over Noetherian bases.
* Every resolution and the tensor formula: `_resolution` quantifies over every
  complex F, every quasi-isomorphism `s : F → B[0]`, its two strict bounds and finite
  projectivity in each degree. It supplies the actual extended augmentation `sT`,
  proves it is a quasi-isomorphism, and fixes its pure-tensor value. Its χ satisfies
  the published `ModuleCat.CoinductionHomScalarFormula`: the value of an extended
  functional at an extended vector is the product of the two scalar factors times
  the extended old value. This is exactly
  `(h tensor r')(z tensor s') = r's'(h(z) tensor 1)` after the pushout identifications.
  `CoinductionHomModel` fixes eP and eP' by their K-injective comparison and
  augmentation. The last equation identifies that concrete chain map with the
  specified counit mate after forgetting the B'-action. The coefficient is pinned
  to the same ordered volume by its displayed equation with `G.coefficientMap`.
* Open restrictions: `_affine` applies to all compatible admissible affine opens.
  `_restriction` states the exact composition equality for any two admissible changes
  and their composite, allowing base changes and simultaneous localizations in either
  order. Its associator is `koszulDiagonalExtensionComp`, fixed by adjunction.
  Therefore restricting the base-change map and forming it on smaller charts agree.
  This is also compatible with the existing exact-open-restriction interface.
* Ordered refinements: `_refinement` states the square between the two scalar
  comparisons and `KoszulDiagonalRefinement.modelMap`. Its hypotheses use the
  published `IsContraction` predicate, which imposes the actual graph differential
  boundary normalization `dual(t-u) tensor d(t-u) → 1`. The ordered chart coordinates,
  exterior top wedge and shifted complex retain the exterior and total complex signs;
  these are not replaced by an arbitrary unit or by an unnormalized iso.
* Proper case: `_proper` uses the actual right adjunctions of quasi-coherent derived
  direct image, with their source/target QCoh categories and structure-sheaf values
  P and P'. These data are available from
  `exists_properFlatDualizingPolynomialModel`. The marked intrinsic pair identifications
  α and α' transport β to the unique marked comparison γ on those values. The
  conclusion states both uniqueness and the exact transport equality, so the
  preceding polynomial formula is the same proper-duality formula. The QCoh
  preservation and unit membership hypotheses only type the chosen right adjunctions;
  they are supplied by that dependency, not extra geometric hypotheses.
* Locally free concentration: `_homology` takes integer d, finite locally free ω and
  ω', and the concentration isomorphisms to the single complexes in degree `-d`.
  The q/q' equations identify these modules with `H^(-d)` of the supplied objects.
  `polynomialBaseChangeSingleMap` is the original derived counit on that single
  complex; `_isIso` uses local freeness. `polynomialBaseChangeSingleHomology` is its
  actual homology isomorphism. The unique ordinary tensor-pullback isomorphism γ in
  `_homology` is characterized by the square with `H^(-d)(β)`. Applying it to the
  proper-pair objects in `_proper` gives exactly the node's final clause.
* No lci, nodal, dimension, Cohen--Macaulay or Gorenstein hypotheses occur. Properness
  occurs only in the two proper consequences. Neither a nor the affine base ring map
  is assumed flat. Local Tor bounds and resolution bounds are local/per-resolution,
  not a new uniform bound on the whole scheme.

### Dependency declarations used

All original statement dependencies were read, including full signatures and docstrings.
Their Mathlib leaves use Scheme, IsProper/IsSeparated, Flat,
LocallyOfFinitePresentation, IsLocallyNoetherian, pullbacks, KaehlerDifferential and
exteriorPower. The project declarations used are:

* `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`;
  `WeilConjectures.AlgebraicGeometry.DerivedPullback`: `derivedPullback`,
  `recordedDerivedPullbackCounit`, `recordedDerivedPullbackComposition`. The latter
  two are owned by `lem-pc-recorded-pullback-composition` in
  `WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition`.
* `Sheaf.AlgebraicGeometry.RelativeDualizingPair`: the diagonal complex and
  `IsCoherentRelativeDualizingPair`;
  `Sheaf.AlgebraicGeometry.RelativeDualityPolynomialChart`:
  `exists_relativeDualityPolynomialChart` (the underlying-object chart interface).
* `Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison`:
  `relativeDualizingDerivedExtension`, `relativeDualizingExtensionCounit`,
  `relativeDualizingModuleDiagonal`, `relativeDualizingProductChart`.
* `Sheaf.AlgebraicGeometry.RelativeDualizingPairBaseChange`:
  `relativeDualizingBaseChangeClass`, `relativeDualizingDiagonalBaseChangeMap_isIso`,
  `relativeDualizingPullbackId`, and its base-change/coherence theorems.
* `Sheaf.Algebra.Homology.PolynomialKoszulDiagonalData`:
  `PolynomialKoszulChart`, its top/coefficient/model/diagonalClass,
  `IsKoszulDiagonalNormalization`, `KoszulDiagonalChartChange.IsAdmissible`,
  `.IsComparison`, `koszulDiagonalScalarMate`, `KoszulDiagonalRefinement`,
  `.IsContraction`, `.modelMap`;
  `PolynomialKoszulDiagonalSystem`: `koszulDiagonalExtensionComp`.
* `Sheaf.AlgebraicGeometry.PolynomialDualityAffineRealization`:
  `polynomialAffineTilde` (native exact tilde, not a new affine-equivalence choice).
* `Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentExchange`:
  `ModuleCat.CoinductionHomModel`, `ModuleCat.CoinductionHomScalarFormula`.
  `PerfectCoinductionTorIndependentBaseChange` supplies the specialized perfect
  exchange used in the proof plan.
* `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`:
  `Scheme.Modules.exists_tensorPullback_tilde_iso`;
  `Scheme.Modules.moduleBaseChangeMap`, `tensorPullback`, and the structure-sheaf
  comparison use the published ordinary module interfaces.
* `Sheaf.AlgebraicGeometry.ProperFlatDualizingPolynomialModel`:
  `exists_properFlatDualizingPolynomialModel`;
  `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage` and the existing QCoh full subcategories.
* `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` supplies the existing
  internal-Hom/coinduction coefficient conventions. The natural quotient-algebra
  action is retained by derived coinduction throughout.

### Returned-head repair: H2 ownership audit

The returned immutable head is `4930a72f2e5b`. The sandbox module is retained byte
for byte (SHA256 `527056b9bdb9802811e7b61df775b2761ff33c040464b41f7910b8a90141fbc3`).
I compared the node with current main: only the packet's `lean` and added
`stmt_deps` differ. All other fields agree. The repaired node starts from current
main and carries the retained Lean record and the corrected dependency list.
The delivery wrapper constructs the new commit on current `sheaf-dag`.

1. Removed `lem-trf-affine-relative-dualizing-comparison` from the packet's added
   statement dependencies. Its plain definitions are now cited through
   `def-trf-affine-diagonal-module-data` (`relativeDualizingDerivedExtension`,
   `relativeDualizingModuleDiagonal`) and
   `def-sfb-affine-relative-dualizing-comparison-data`
   (`relativeDualizingExtensionCounit`, `relativeDualizingProductChart`). The
   theorem remains in `proof_deps`; no choice from that theorem defines these data.
2. Removed `lem-sfb-perfect-coinduction-tor-independent-exchange` from the packet's
   added statement dependencies. `CoinductionHomModel` and
   `CoinductionHomScalarFormula` now cite
   `def-sfb-perfect-coinduction-exchange-data`, the landed existing:true owner in the
   same module. The exchange theorem remains in `proof_deps`.
3. Added every other owner requested by the return:

   | Node | Declaration actually used |
   | --- | --- |
   | `def-sfb-module-base-change-map` | `Scheme.Modules.moduleBaseChangeMap` |
   | `def-sfb-tensor-pullback-structure-sheaf-map` | `Scheme.Modules.tensorPullbackObjUnitToUnit` |
   | `def-trf-polynomial-duality-affine-realization` | `polynomialAffineTilde` |
   | `def-trf-derived-coinduction` | `ModuleCat.derivedCoinduction` and its actual adjunction |
   | `def-sc-module-total-hom-complex` | `CochainComplex.moduleHomComplex` |
   | `lem-pc-recorded-pullback-composition` | original counit and `recordedDerivedPullbackComposition` |
   | `lem-weil-pbc-pushforward-spec-global-sections` | `Scheme.Modules.pushforwardSpecMapCompΓIso` |

4. The last theorem-node citation is explicit and justified: the real ordinary
   diagonal map `polynomialBaseChangeDiagonalTildeMap` uses
   `pushforwardSpecMapCompΓIso.inv.app` to transport restricted global sections
   through affine pushforward before applying the tilde/Gamma adjunction. Both
   directions are the identity on underlying sections with the restricted scalar
   action. This is the exact identity-on-elements normalization in that owner's
   statement, not a theorem cited only for a conveniently colocated unrelated
   definition. The live DAG has no separate definition owner for this comparison.
5. Retained `lem-sfb-relative-dualizing-pair-base-change`: the marking predicate uses
   its actual diagonal `IsIso` theorem term inside `relativeDualizingBaseChangeClass`,
   and the identity uses its chosen normalized pullback identification. Retained
   `lem-weil-pbc-tilde-pullback-base-change`: the ordinary affine comparison is
   chosen from the proved unit-pinned `exists_tensorPullback_tilde_iso`, whose
   normalization determines the comparison. Retained the newly cited
   `lem-pc-recorded-pullback-composition` because its composition iso is `asIso`
   of the explicit derived lift, with invertibility supplied by its theorem.

No theorem is moved out of `proof_deps`; no new nodes, replacement declarations,
changed Lean imports, statement corrections or mathematical changes are needed.
I read each new owner's statement, `lean` record, and source signature/docstring.

The plain proof imports include the recorded rigidity, affine pullback/open restriction,
flat polynomial quotient perfection, normalized graph class, and derived internal-Hom
open restriction results. The DAG's scalar-naturality theorem has no Lean record;
its equivalent evaluation/graph-normalization calculation is spelled out in the owning
item's affine proof docstring rather than assumed as an unbound extra map.

### Edge cases and size

Checked the identity and composed squares, arbitrary nonflat base change, the empty
scheme/zero ring, n = 0 (empty wedge, coefficient in degree zero), any integer d,
nonproper families, nontrivial finite locally free modules without a chosen basis,
localized polynomial presentations and extra ordered graph variables. Empty objects
have the unique marked comparison. No characteristic assumption occurs. Scheme and
module carriers use u; the shared sheaf-derived localization uses independent w.
Native module derived categories use their published universe, and exact tilde bridges
it to w. No equality between the module and sheaf localization universes is imposed.
The source is flat of finite presentation on each affine chart; this ensures the
base-changed resolution remains a resolution even when R' is not R-flat.

### Searches

The actual msearch calls are logged in `searches.jsonl` in the sandbox:

* LeanFinder: `Relative dualizing pairs on flat finitely presented schemes have unique
  class preserving base change isomorphisms computed on polynomial charts`:
  eight flatness/Spec-pullback hits, none the requested statement.
* Loogle: `"dualizing", "baseChange"`: zero hits.
* Mathlib grep: `relativeDualizing|relative_dualizing|dualizing.*base.change`: zero hits.
* LeanSearch: `Canonical derived affine pullback of tilde module complexes is extension
  of scalars compatible with relative dualizing diagonal classes`: eight ordinary
  pullback/adjunction hits, none the requested normalized derived statement.
* rg in the exact upstream `lean/WeilConjectures` and project `lean/Sheaf`, and the
  item-id search in upstream: found the ordinary/derived pullback and existing pair,
  coinduction and graph interfaces used above; no declaration already states this node.
  DAG searches found the published graph-data and graph-system nodes, which are reused.
* Read the current blueprint and the local Stacks duality/dualizing source places,
  including the ordered top-differential normalization. No older blueprint snapshot
  was used. There is no source-based correction to the accepted statement.

### Validation

The complete file compiled through scompile.py against the live published build, with
no errors or non-sorry warnings. Both wrapper phases passed in about 30 seconds each.
Every declaration has the owning blueprint marker; all lines have at most 100
characters, all variables/universes are bound, and diagnostic commands were removed.
Repair validation: scompile.py recompiled the unchanged complete file cleanly in
33.1 seconds (sandbox) and 37.1 seconds (library), with no errors or non-sorry
warnings. The prescribed deliver2.py dry run and final delivery follow this report.

## Second reading by NF

The dispatcher prohibits starting other agents. This is an explicit clause-by-clause
self-rereading of the returned node, the unchanged Lean file, and the new owner records;
it does not claim an independent worker. The maintainer's independent mathematical
reading of `4930a72f2e5b` found the mathematics faithful. This repair addresses H2 and
H11 without changing those declarations.

1. **Geometric inputs.** `_unique` binds separated, flat, locally finitely presented
   f and a locally Noetherian S. It binds arbitrary a with S' locally Noetherian
   and a genuine `IsPullback` square. The f' instances are inherited from that
   square; they introduce no independent geometric restriction. Checked against
   the first two sentences of the node. No flatness of a is present.
2. **Pairs and marking.** K/ξ and L/η use exactly the recorded
   `IsCoherentRelativeDualizingPair` predicate. `IsRelativeDualityBaseChange` uses
   the existing canonical diagonal augmentation, its actual invertibility theorem,
   and pullback of β under the first projection. `_unique` asserts existence and
   uniqueness of an isomorphism satisfying precisely this class equation. This is
   stronger than an arbitrary underlying-object iso in exactly the way the node asks.
3. **Identity and composition.** `_id` names the recorded pullback identity on K.
   `_comp` compares successive marked maps with the direct one through
   `recordedDerivedPullbackComposition`. Checked both arrow directions and the
   composite square `sq'.paste_horiz sq`. The cited recorded-composition owner
   supplies the actual `asIso` construction; it is not merely an unused proof lemma.
4. **Family naturality.** `_isoNaturality` uses genuine family isomorphisms, their
   base changes, commuting maps, and independently marked pair comparisons. Its
   equation is the naturality square with the fixed pullback composition route.
   Identity family isomorphisms are included; no affine trivialization is assumed.
5. **Normalized charts.** The published chart's polynomial quotient and ordered
   coordinates determine top differentials, shifted coefficient, and C.model.
   `IsPolynomialBaseChangeNormalizedChart` pins e/e' to ξ/η using canonical
   diagonal and first-projection maps and the normalized graph class. The auxiliary
   map satisfies two fixed equations and cannot rescale the class freely. The
   existence helper supplies these normalized comparisons for every supplied pair.
6. **Affine derived-Hom formula.** `_affine` uses the actual affine-open Spec squares.
   `IsAdmissible` imposes the required P' and B' pushouts and also handles compatible
   localized charts. `IsComparison` fixes c by the evaluation counit and ordered
   coefficient map, retaining the natural B'-action via derived coinduction.
   The conclusion identifies restricted β with exactly this c after the fixed
   native tilde and chart-square comparisons. `_model` supplies c. The more general
   localized charts are true instances of the required restriction clause.
7. **Every finite-projective resolution.** `_resolution` quantifies over every
   bounded degreewise finite-projective F and quasi-isomorphic augmentation s.
   Checked that sT has the required scalar-extension augmentation formula and is
   a quasi-isomorphism; χ has `CoinductionHomScalarFormula`; eP/eP' have the
   K-injective `CoinductionHomModel` normalization; v is pinned by the coefficient
   counit equation. The final equality relates these maps to the specified c after
   restriction of scalars. Thus no unnormalized Hom identification can alter
   `(h tensor r')(z tensor s') = r's'(h(z) tensor 1)`.
8. **Open restriction.** `_restriction` compares successive admissible scalar maps
   with the direct one through the actual adjunction associator. Admissible maps
   include simultaneous localization; checking both orders gives restriction of
   the base-change comparison and base change on the smaller charts. Principal
   opens cover arbitrary opens. This clause has an explicit equality in the Lean.
9. **Ordered refinement and signs.** `_refinement` uses the existing
   `KoszulDiagonalRefinement.IsContraction` and its modelMap. This contraction
   normalizes the extra graph equation to `(t-u)^dual tensor d(t-u) → 1`.
   Ordered graph variables, the top exterior wedge and degree `-n` coefficient
   retain the exterior and total-complex signs. The displayed square commutes
   with both scalar comparison routes, rather than only asserting existence of
   refinement isomorphisms.
10. **Proper interpretation.** `_proper` binds right adjunctions on the existing
    quasi-coherent derived categories and identifies P/P' with their values at
    the structure sheaves. It quantifies over coherent pair classes ζ/ζ' and
    marked identifications α/α', and states the unique comparison and exact
    transport equality. This universal conditional statement applies to the
    intrinsic classes whose existence the dependency supplies; it does not
    incorrectly assume that dependency chooses arbitrary classes or a new adjoint.
11. **Locally free concentration and cohomology.** `_homology` uses degree `-d`,
    arbitrary integer d, locally free ω/ω', and concentration isomorphisms e/e'.
    The q/q' normalization equations pin ω/ω' to H^(-d). The single-pullback map
    is the original derived counit; its invertibility follows from local freeness.
    The final equation characterizes the ordinary tensor-pullback isomorphism as
    H^(-d)(β). Applying the proper transport equality gives exactly the final
    dualizing-module clause in the node, without a change of shift convention.
12. **Excluded extra hypotheses and edge cases.** Rechecked n = 0, empty schemes
    and zero rings, nonflat base-ring maps, nonproper f in the general clauses,
    nontrivial locally free modules without a basis, and independent u/w
    localizations. There is no lci, nodal, dimension or Gorenstein assumption.
    All original statements and all declaration signatures are unchanged; no
    hollow definition or new sorry has been introduced. The existing named
    postponed proofs still have their source and full proof-plan docstrings.
13. **Citation audit and repair findings.** Matched each direct helper to the
    landed owner listed in the H2 section. Removed the two theorem-only plain-def
    citations, retained their theorem proof dependencies, and added all requested
    owners and the normalized global-sections comparison justification. This is
    the only node change beyond the Lean record's repair note/date. H11 is
    addressed by this explicit reading of every hypothesis and conclusion clause.

No unresolved mismatch, statement dispute, new node or dependency-module repair remains.
