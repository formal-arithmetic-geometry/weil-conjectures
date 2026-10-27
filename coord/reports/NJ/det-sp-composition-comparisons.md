## Worker report

The module `Sheaf.Paper.CompositionComparisons` states the node in three declarations:
`AlgebraicGeometry.ProEtale.compositionComparisons_finite` for (1)--(2),
`compositionComparisons_towers` for the tower part of (3), and
`compositionComparisons_integral` for its integral part. All three proofs are `sorry`.
Every other new declaration is a structure collecting the displayed data/equations,
a fully written result-type definition, or the degree-one ULift instance obtained
from Mathlib's existing linear equivalence. There is no chosen map or object from a
mere existence theorem and no definition data using `sorry`.

Source read: current `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-comparisons.md` and its entire proof,
the item's accepted re-split and resolved stage-1 repair note. The current source
agrees with the DAG statement. The proof docstrings retain the accepted route through
proper/open coefficient square pasting (rather than assuming B has a finite projective
resolution). No statement correction or dispute is needed.

Hypotheses, one by one:

- The finite theorem explicitly binds `k : Type u`, `Field k`, prime `p`, `CharP k p`,
  prime `ℓ`, and `p ≠ ℓ`. A field's positive characteristic is prime, so this is exactly
  characteristic p>0. It binds three schemes in the same arbitrary universe with
  their `Over (Spec (.of k))`, `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`
  structure-map instances, and both `IsOver` map instances. No algebraic closure or
  finite-field restriction appears in (1)--(2) or the tower theorem.
- `d e : ℕ`, `SmoothOfRelativeDimension d f` and `SmoothOfRelativeDimension e g`
  encode smooth pure nonnegative dimensions, including d=0 and e=0.
- `A B : Type u`, `CommRing`, `Finite`, the two existential annihilator formulas
  `∀ x, (ℓ^n) • x = 0`, and `φ : A →+* B` encode exactly arbitrary unital maps of
  finite commutative ℓ-primary rings. A=B, the zero ring and nonflat quotient maps
  are permitted. No flatness, projectivity or finite projective dimension is bound.
- The same `cf`, `cg`, `ch` are used at both coefficients: compactifications are
  coefficient independent. They are arbitrary fixed compactifications. The wrappers
  derive quasi-compactness and separated/finite-type map properties from the standing
  scheme assumptions rather than asking for new hypotheses.
- Towers bind prime l and an arbitrary `E : Type u` with `Field`, `Algebra (Padic l) E`
  and `FiniteDimensional`, exactly a finite extension. Recorded Base/Operations,
  Coordinates, FiniteCoordinates, Preservation and Calculus supply the already
  constructed tower functors and their proper/open normalization. Pair packages the
  given adjunction and its prescribed evaluations, not a new choice of operation.
- The integral theorem uses the recorded `FiniteFieldDatum`, `l ≠ D.p`, separated
  finite-type schemes over `D.k`, and the two smooth dimensions. The three explicit
  open/proper factorizations present f, g and gf; `_hcomp` is precisely their composite
  equality. The coefficient field is `ULift.{u} (Padic l)`: a universe copy of Q_l,
  with its standard algebra and finite-dimensional structure. Its ring of integers
  is the same Z_l coefficient field convention, expressed without forcing u=0.
  The reduction, normalized-equivalence, tower-adjunction and integral-realization
  arguments are the recorded data for the functors the node instructs us to use.

Clauses, one by one:

- (1), existence and normalization of alpha: `SpCompositionFinite.DA` and `.DB`
  are `FiniteAdjointCompositorDatum` at A,B. Its alpha is an actual natural isomorphism
  of the recorded full Dctf compact-support restrictions. Its normalization field
  identifies it with the specified proper/open etale compositor through the actual
  site-support comparisons on every origin witness. This is not a bare Nonempty
  isomorphism without normalization.
- (1), theta and uniqueness: `right_composition` supplies thetaA and thetaB, the two
  displayed counit-preserving equations and uniqueness among all such isomorphisms.
  Composition is `≫` in diagrammatic order, hence H_g ⋙ H_f means f! g!.
- (1), composite counit: the next two conjuncts are exactly
  `Fg.map (adjf.counit.app (Hg.obj K)) ≫ adjg.counit.app K =
  (adjf.comp adjg).counit.app K`, at both coefficients.
- (2), the left comparison maps: bf/bg/bh are actual natural isomorphisms, and
  hbf/hbg/hbh pin their underlying arrows to `reductionDirectImageComparison` for
  the same compactification. `left_composition` is
  `S_Z.map alphaA ≫ b_h = b_g ≫ FgB.map b_f ≫ alphaB`, exactly the first displayed
  equation, with Lean's diagrammatic composition order reversed from the TeX order.
- (2), exceptional comparison maps: cfCoeff/cgCoeff/chCoeff are natural isomorphisms;
  hfCounit/hgCounit/hhCounit pin them to the defining counit transposes of the
  recorded exceptional coefficient comparison. The last right_composition conjunct
  is `c_h ≫ thetaB = S_X.map thetaA ≫ c_f ≫ HfB.map c_g`, exactly the second displayed
  equation. Everything is in the full B-linear Dctf category, so its underlying
  equality is the required equality in the B-module derived category.
- (3), actual tower maps: `spCompositionTowerResult` concludes an A_n family with
  its FiniteIdentities, then actual alpha/theta natural isomorphisms between the
  recorded functors on `SpTowerCalculus.C`. This C is the uniformly bounded
  constructible finite-Tor full subcategory of the ordinary derived category of
  strict varying-coefficient towers. It is not a diagram category of derived objects.
- (3), evaluation and counits: `TowerAdjointCompositor.Laws` includes proper_open,
  counit, unique, composite_counit, left_evaluation and right_evaluation. Its finite
  theta is the unique normalized adjunction comparison; its finite alpha is the
  `FiniteAdjointCompositorDatum` alpha. These are the finite compositors in (1).
- (3), reductions and normalized restriction: Laws includes reductions_f/g/gf,
  left_square/right_square, and normalized_f/g/gf for both members of each pair.
  The reductions are the actual `SpTowerCalculus.reduction`, transported from the
  recorded derived tensor reduction along the quotient ring map. Index n means
  positive exponent n+1; m≤n includes equal levels and excludes no positive exponent.
- (3), integral comparisons: `spCompositionIntegralResult` concludes actual natural
  isomorphisms of the recorded `SpIntegralAdjunction.support` and `.right` functors.
  The former is independently derived completed-ring compact support; the latter is
  actual total derived inverse limit of the tower exceptional functor after reduction.
  These act on `sfIntegralConstructibleCategory`, the published Dbc category.
  `SpCompositionIntegralLaws.left_reduction/right_reduction` identify their images
  with the specified tower alpha/theta through the canonical leftComparison and
  rightComparison maps of the published integral realization. Those maps are pinned
  there by its reconstruction unit, actual limit comparison and equivalence counit.
  Thus full faithfulness fixes the integral maps and expresses exactly Rlim realization.
  The remaining counit/unique/composite_counit fields give the integral adjunction
  normalization, including the induced unit identification. The integral theorem
  is the transport clause applied to the actual tower compositors supplied by the
  preceding theorem; `_ht` is their counit equation, not an extra geometric assumption.

Dependency declarations used (the modules are public imports where their objects
occur in a statement, otherwise proof imports):

- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`.
- `def-weil-proetale-constructible-sheaf`: `Sheaf.Paper.ProEtaleFixedModuleConstructible`, `AlgebraicGeometry.Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
- `def-weil-proetale-tor-amplitude`: `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`, `AlgebraicGeometry.Scheme.HasFixedCoefficientProEtaleTorAmplitude`.
- `det-sp-scalar-extension-functor`: `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`, `AlgebraicGeometry.ProEtale.scalarExtensionFunctor`.
- `sk-prop-sf-rf-shriek-preservation`: `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`, `AlgebraicGeometry.ProEtale.CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible`.
- `det-sp-reduction-direct-image`: `Sheaf.SecSmoothPurity.ReductionDirectImage`, `AlgebraicGeometry.ProEtale.reductionDirectImage_isIso`.
- `det-sp-reduction-exceptional`: `Sheaf.SecSmoothPurity.ReductionExceptional`, `AlgebraicGeometry.ProEtale.reductionExceptional_isIso`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `sk-def-sp-coefficient-towers`: `Sheaf.Paper.SmoothPurityCoefficientTowers`, `AlgebraicGeometry.ProEtale.spCoefficientTowers`.
- `sk-def-sp-normalized-towers`: `Sheaf.Paper.SmoothPurityNormalizedTowers`, `AlgebraicGeometry.ProEtale.spNormalizedConstructibleTorTowerCategory`.
- `det-sp-tower-shriek-levels`: `Sheaf.Paper.SmoothPurityTowerShriekLevels`, `AlgebraicGeometry.ProEtale.SpTowerShriek.tower_shriek_levels`.
- `det-sp-tower-gluing`: `Sheaf.Paper.SmoothPurityTowerGluing`, `AlgebraicGeometry.ProEtale.SpTowerGluing.tower_gluing`.
- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `det-sp-normalized-equivalence`: `Sheaf.Paper.SmoothPurityNormalizedEquivalence`, `AlgebraicGeometry.ProEtale.sp_normalized_equivalence`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `det-sp-integral-direct-image-tower`: `Sheaf.Paper.IntegralDirectImageTower`, `AlgebraicGeometry.ProEtale.IntegralDirectImageTower.integral_direct_image_tower`.
- `det-sp-integral-adjunction-bijection`: `Sheaf.Paper.IntegralAdjunctionBijection`, `AlgebraicGeometry.ProEtale.SpIntegralAdjunction.integral_adjunction_bijection`.
- Proof only, `lem-sp-finite-adjoint-compositor-transposes`: `Sheaf.Paper.FiniteAdjointCompositorTransposes`, `AlgebraicGeometry.ProEtale.finiteAdjointCompositorTransposes`.
- Proof only, `lem-sp-tower-adjoint-compositor-realization`: `Sheaf.Paper.TowerAdjointCompositorRealization`, `AlgebraicGeometry.ProEtale.TowerAdjointCompositor.towerAdjointCompositorRealization`.

In particular the definition-level interfaces reused are `spFiniteConstructibleTorCategory`,
`finiteAdjointSupport`, `FiniteAdjointCompositorDatum`, `scalarExtensionFunctor`,
`reductionCtfScalar`, `reductionDirectImageComparison`, `TowerAdjointCompositor.Pair`,
`FiniteIdentities`, `Laws`, `SpIntegralAdjunction.realizationResult`, `support`, `right`,
`reduce`, and the recorded canonical comparison fields of Realization/Reconstruction.
The intrinsic constructible and Tor predicates exported by the recorded presentation
modules are the same predicates used by these ordinary ring-sheaf Dctf interfaces.
No second constructibility, Tor-amplitude, scalar-extension or tower category is defined.

The definition dependency is now `def-sp-adjoint-compositor-data`, whose existing-declaration record owns `finiteAdjointSupport`,
`finiteAdjointSiteSupportIso`, `FiniteAdjointCompositorDatum`, and all ten
`TowerAdjointCompositor` interfaces listed below. The two theorem nodes remain proof dependencies; the tower module is public because it
exports the definitions bound to the new definition node. Their theorem conclusions
are not statement dependencies. `lem-sp-integral-compositor-limit-realization` has no recorded Lean module
in this checkout and its expected source is unavailable through `scompile --source`.
It is a proof dependency only: no missing object from it occurs in this statement,
so it is not imported; its complete categorical transport argument is in the integral
proof docstring. The other stated proof dependencies are imported as the proof plan.

Edge cases checked against the types and formulas: identity f or g; d=e=0; A=B with
identity scalar extension; the nonflat quotient Z/ℓ²→Z/ℓ; zero rings and zero complexes;
empty schemes; equal reduction indices m=n; level n=0 representing exponent one;
ramified finite extensions E; arbitrary scheme universe u. No Nonempty assumption on
a scheme or index, no finite projective resolution of B, no faithfulness of finite
evaluation and no small-universe restriction are introduced. Actual whole-tower
morphisms are constructed before evaluation; only conservativity detects their
invertibility, while integral descent uses full faithfulness of reduction.

Searches for an existing statement:

- msearch leanfinder: "Composition of compactly supported direct images and exceptional
  inverse images commutes with finite coefficient extension and normalized adic towers".
  Eight hits, all ordinary adic-completion linear-map identities; none concerns this
  pro-etale compact-support/exceptional/tower comparison.
- msearch loogle: "CategoryTheory.Adjunction.comp, CategoryTheory.Adjunction.rightAdjointUniq".
  Zero hits for the combined query. These generic constructions are reused through the
  recorded interfaces; neither states the present finite plus tower plus integral result.
- msearch grep: "rightAdjointUniq|comp_counit" in CategoryTheory/Adjunction.
  Nine hits in Unique, Triple and Mates; only the generic categorical calculus.
- rg of both lean/WeilConjectures and lean/Sheaf for the item id and
  "compositionComparisons|composition_comparisons": no existing exact declaration.
  Broader compositor searches found the recorded FiniteAdjointCompositorTransposes and
  TowerAdjointCompositorRealization modules, which are used. The narrower
  FiniteExceptionalCompositorCoefficients concerns its separately specified interfaces;
  it does not supply this node's whole statement.

Validation of the returned version (historical): the item module compiled both as the sandbox file and its actual library
module on the server, with no warnings (36.4 s / 36.7 s). No local Lean or global build
was run. Three named theorem proofs remain `sorry`, as required at stage 2.


## Repair of returned delivery

Return at immutable head `9e84b5c8390b`: all thirteen declarations in the attempted
AdjointCompositorData relocation already exist in the live theorem modules. The repair
removes that new module and both attempted replacement theorem modules from the packet.
No declaration is renamed or copied. The item publicly imports the existing tower
module, whose public finite-module import provides the three finite declarations.
The new definition node is retained as their DAG owner using existing:true.
Both theorem nodes receive lean-only existing:true records listing only their theorem;
their live Lean sources and proofs are unchanged. The item's mathematical signatures,
bodies and three proof docstrings are unchanged; only imports and metadata change.

Compared the retained returned packet with current main and read both current live
sources using scompile.py --source. They still declare the thirteen original names.
The discarded relocation was identical in data but cannot coexist as a second owner
module. The current repair uses precisely those existing definitions and records their
original modules explicitly. This follows the return's instruction to import and reuse.
No shared source was edited and no git command was run there.

## New nodes

`def-sp-adjoint-compositor-data` binds existing definitions, rather than delivering a
new module. Its main declaration is `TowerAdjointCompositor.Pair` in
`Sheaf.Paper.TowerAdjointCompositorRealization`. Its declarations list also binds
`left`, `finiteLeft`, `coefficient`, `finiteTheta`, `FiniteIdentities`,
`PreservesNormalized`, `Reductions`, `ReductionSquare`, `Laws` in that module and
`finiteAdjointSupport`, `finiteAdjointSiteSupportIso`, `FiniteAdjointCompositorDatum`
in its public import `Sheaf.Paper.FiniteAdjointCompositorTransposes`.
The module paths in lean.note make this two-module existing binding explicit.

Source: current blueprint comparisons proof (1)--(3). The complete original
hypothesis/clause map above applies to the reused definitions. The datum normalization
is the proper/open site paste on every etale witness; Pair packages the supplied
adjunction and finite evaluations; finiteTheta uses rightAdjointUniq; FiniteIdentities
contains the canonical b/c equations; Laws contains both counit and finite evaluation
equations, all three normalized/reduction pairs and both reduction squares.
No new data or proof is chosen. The original edge-case checks remain valid.

The node retains the raw required searches: LeanFinder's finite/adic adjoint-compositor
query returned eight unrelated adic algebra hits; Loogle's rightAdjointUniq/comp query
returned zero; Mathlib grep returned six generic adjunction hits; LeanSearch returned
eight inner-product adjoint hits. DAG/project grep and blueprint_refs search found no
definition owner. The original project definitions are now reused exactly, as the latest
return requires; this node supplies ownership rather than another notion or theorem.

## Dependency modules

`lem-sp-finite-adjoint-compositor-transposes`: the earlier record bundled three
unowned definitions. Its lean-only repair now records its existing theorem only and
explains that the three unchanged existing definitions are owned by the new definition
node. No Lean file for this dependency is delivered, and its proven theorem is reused.

`lem-sp-tower-adjoint-compositor-realization`: the earlier record bundled ten
unowned definitions. Its lean-only repair likewise records its existing theorem only;
the ten original definitions remain in their live source and are bound to the new
definition node. No Lean file for this dependency is delivered. This removes the
collisions while preserving all theorem proofs and all existing consumers.


Validation of this repair: the item compiled cleanly through the prescribed server
scompile.py, both sandbox (24.6 s) and library module (17.0 s), using the existing live
finite/tower modules. The packet contains only the item Lean file; no duplicate-name
interface declaration is delivered. Both dependency JSON copies differ only in lean;
the item differs only in lean and the added definition-owner statement edge.
The delivery wrapper will additionally #check every existing:true declaration listed
by the three repaired records against their recorded public module imports.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
