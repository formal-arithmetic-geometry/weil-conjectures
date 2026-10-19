## Worker report

`Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` states
`AlgebraicGeometry.ProEtale.finiteRingSiteTensorTranspose`. Its conclusion is `finiteRingSiteTensorTransposeWithCoefficients`, which supplies
all canonical site maps to `finiteRingSiteTensorTransposeStatement` for the
ordinary unbounded etale/pro-etale categories and every named canonical map.
Keeping that proposition categorical avoids repeatedly expanding K-flat
constructions during elaboration. It does not quantify over extra choices of
comparison maps in the theorem: the theorem supplies each argument explicitly.
The main module postpones only this theorem; all definitions contain real data.

Hypotheses, individually matched:

* `D : WeilConjectures.FiniteFieldDatum.{u}` fixes the global finite-field datum
  and its algebraic closure `D.k`. `ℓ`, `[Fact ℓ.Prime]`, and `hℓ : ℓ ≠ D.p`
  specify the prime invertible in that closure.
* `B : Type`, `[CommRing B]`, `[Finite B]`, and
  `hB : ∃ n : ℕ, (ℓ : B) ^ n = 0` specify an arbitrary finite primary ring.
  `ULift.{u+1} B` places this finite ring in the common coefficient universe,
  as in the recorded finite comparison. There is no flatness, principal-ideal,
  cyclic-ring or nonzero-ring assumption.
* `[TopologicalSpace B] [DiscreteTopology B] [IsTopologicalRing B]` give the
  discrete convention. `eR` and `[IsMonHom eR.hom]` are exactly the coefficient
  identification used in `finiteComparisonProEtaleClosure`; the theorem holds
  for any such identification, including the canonical one. No geometric map
  is replaced by an arbitrary map.
* `X`, `Y` have `Over (Spec (.of D.k))` instances; `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` on their structural maps express separated
  finite-type schemes over that same field.
* `f : X ⟶ Y`, its `IsOver` instance, and `c : Compactification f` give the
  chosen factorization, its open immersion `c.i`, proper map `c.g` and
  composite equality. The structural-map conditions on `c.Z` and the `IsOver`
  instances on the two arrows put this compactification in the standing setting.
* `finiteRingEtaleShriek` and `finiteRingProShriek` abbreviate the recorded
  ordinary `rightDerivedLowerShriekOfCompactification` functors with the same
  `ModuleCat (ULift B)` coefficients. The proposition's `FE` and `FP` arguments
  are exactly these functors, and `PE`, `PP` are the actual derived inverse
  images (canonically equal to the termwise exact ones).
* Inside the proposition, `finiteRingRestriction FP PX PY hs` is precisely
  restriction of `FP` to the two specified localizing closures. `hs` types that
  already stipulated restriction. `R, ae` and `G, ap` range over choices of the
  right adjoints and their adjunctions, exactly as the node's given adjoints do.
  There is no boundedness, constructibility or Tor-amplitude condition on any
  object in the three assertions.

Conclusions, individually matched:

1. The proposition begins with `EX.Full`, `EX.Faithful`, and
   `EX.essImage N ↔ PX N`. In the theorem specialization `EX` is the functor abbreviated by `finiteRingSitePull B X`,
   the exact termwise `comparisonUpperStar.mapDerivedCategory`, and `PX` is
   `finiteComparisonProEtaleClosure B eR X`. `hX`, `hY` merely type the image
   functors with their codomains restricted to the closures. `rho` is a natural
   isomorphism from `R ⋙ finiteRingImageLift EX PX hX` to
   `finiteRingImageLift EY PY hY ⋙ G`. Its first equation is literally
   `β ; Rf_!(rho) ; εpro = ν*(εet)`. The next clause states uniqueness among
   all natural isomorphisms satisfying that counit equation alone.
2. `b` is required componentwise to have hom `beta M`; the theorem supplies
   exactly `finiteComparisonCompactSupportMap B c.i c.g`, the unbounded proper
   counit mate followed by proper pushforward of the canonical open-extension
   comparison. `pe`, `pp` are objectwise isomorphisms pinned by hom equalities
   to `pfE`, `pfP`. The coefficient wrapper supplies exactly the two upstream
   `projectionMapOfCompactification` components, packaged by `finiteRingEtalePF`
   and `finiteRingProPF`. The square starts on one side with `EY.map (pfE M K)`,
   then `b` at `M ⊗ PE.obj K`, then `FP` of the tensor/pullback comparison.
   The other side is `tensorY`, `b(M) ⊗ identity`, and `pfP` on the site images.
   Thus it asserts equality of the node's named routes and invertibility of
   the actual two projection maps, rather than existence of arbitrary maps.
3. For all `M`, `K`, `e : FE.obj M ⟶ 𝟙_ _`, the first transpose uses
   `ae.homEquiv` on `pe.inv ; (e ⊗ identity) ; leftUnitor`. The pro-etale
   transpose uses `ap.homEquiv` on `pp.inv` followed by
   `((b.inv ; EY.map e ; unitY.hom) ⊗ identity)` and the left unitor.
   `finiteRingTensorPullbackComparison` is the explicit composite
   `tensorX M (PE.obj K) ≪≫ tensorIso refl (pullback K)`. Its factors in the
   theorem are the canonical site tensor comparison and the recorded canonical
   `unboundedDirectImagePullbackIso`, with the exact/left-derived identifications.
   The equation compares these transposes by that composite and `rho`.
   The existential `ht` supplies membership of the pro-etale tensor source in
   the closure; it is a conclusion, not an extra input restriction. The last
   equation is the same equality after reversing the tensor factors with
   `symE`, `symP`. The coefficient wrapper supplies
   `DerivedCategory.braidedCategory` on each of the two module-sheaf categories.
   The proposition takes its components with `BraidedCategory.braiding`. These
   structures descend the Koszul signed swap through K-flat localization, the
   same construction as the existing etale `derivedTensorSymmetry`. Adjunction
   naturality identifies precomposition of the transpose with transposition
   from the reversed source, exactly as in the node.

The proposition and its generic restriction/composite helpers and canonical
partial applications are declarations
of the item's own categorical assertion, listed in `lean.declarations`; they
introduce no independent mathematical notion or postponed theorem. Their
categories have separately bound object and morphism universes. They impose
no new universe equality on either site.

Dependency declarations read and used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* Mathlib finite-type/proper modules: `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, `IsProper`; the structural-map setting is explicit in the theorem.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` and the standing compactification
  setting; an arbitrary chosen compactification in that setting is exposed here.
* `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`; the derived categories are unbounded.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: fixed-scalar realization,
  exactness, and equivalence with the intrinsic finite module-sheaf encoding.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules` and underlying `comparisonUpperStar`.
* `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.
  ringedTopoiCanonicalDerivedTensorPullback`. The finite constant-coefficient
  instance is the upstream `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`,
  from `Functor.leftDerivedTensorComparison` and the canonical comparison with
  the exact termwise functor, with the same ordinary and K-flat normalization.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification`.
* `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
* `Sheaf.Paper.LocalizingExceptionalAdjoint`:
  `CondensedRing.localizingLowerShriek`, `exists_localizingExceptionalAdjoint`;
  here the ordinary finite-discrete realization is explicitly restricted.
* `Sheaf.Paper.FiniteComparisonLocalizing`:
  `finiteComparisonProEtaleClosure`, `finiteComparisonCompactSupportMap`,
  `finiteComparisonOpenIso`, `finiteComparisonLocalizing`.
* `Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison`:
  `unboundedDirectImagePullbackIso`, `unboundedDirectImageComparisonMap`,
  and its isomorphism theorem.
* `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso`, its coherence theorem.
* `Sheaf.AlgebraicGeometry.ProperProjectionFormula`:
  `Etale.isIso_proper_projection_formula_reordered`; the maps themselves are
  the existing etale/pro-etale `projectionMapOfCompactification` maps.

All stated proof-dependency imports of the retained packet remain. The main
proof docstring retains all eleven node steps, including the proper counit
mate calculation, open adjunct calculation, pasting, transpose and symmetry.

Edge cases checked: the empty scheme is allowed, since no point or nonempty
instance is used. The zero ring is allowed, since no `Nontrivial` instance is
used; exponent zero gives exactly that case. Nonprincipal finite primary rings
and finite products of primary rings fit. `M`, `K`, `L` range over the entire
unbounded categories. Neither tensor order drops its signed braiding.

Searches retained from the earlier attempt and checked against current sources:

* `msearch.py ... leanfinder`: "Transport projection formula maps and exceptional
  adjunction transposes across etale proetale site comparison for finite
  coefficient rings" returned eight unrelated condensed/site/sheaf results.
* `msearch.py ... loogle`: "Adjunction, NatIso, projection" returned no hits,
  reporting that `Adjunction` was unknown in that index.
* `msearch.py ... grep`: `projectionMapOfCompactification|leftDerivedTensorComparison`
  in Mathlib `CategoryTheory` returned no hits. The upstream extension supplies
  these actual constructions and is reused.
* `rg` in upstream `WeilConjectures` and side `lean/Sheaf`, for finite-ring
  transpose names, `finiteRingSite`, `integrationTranspose` and the exact node
  id, found no theorem giving this three-clause transport. The published
  finite-coefficient comparison monoidal and lower-shriek projection modules
  supply the canonical component maps, not this theorem. Their current sources
  were read through `scompile.py --source` when missing from the older checkout.

No mathematical statement dispute or node correction is needed.

## Second reading by Q21

The dispatcher explicitly forbids starting another agent. This is the author's
renewed reading with the node and the final module open; independent maintainer
review remains required.

Every original hypothesis appears among the theorem binders. Reading through
`finiteRingSiteTensorTransposeStatement`, its first three conjuncts give full
faithfulness and the exact essential image. `b.hom = beta` pins down the named
compact-support comparison. The counit equation and its separate uniqueness
clause give exactly assertion 1. The hom equations for `pe` and `pp`, followed
by the two-route equation, give precisely assertion 2. Both `homEquiv`
expressions have the inverse projection, evaluation, tensor identity and unit
constraint in the stipulated order. The final equation retains the two actual
signed symmetries and the reversed pullback/tensor comparison.

In particular, all arguments of the categorical proposition supplied by the coefficient wrapper are
specified canonical constructions, not extra hypotheses. The braiding arguments are the actual named canonical structures on both sites,
with no extra braiding assumption on the theorem. The closure categories
are the recorded ones; `finiteRingRestriction` and `finiteRingImageLift` are
ordinary `ObjectProperty.lift` constructions. Their actual adjunction counit is
used directly. No recursive helper, unknown datum, arbitrary comparison map,
stronger coefficient hypothesis or boundedness assumption survives.

The main module retains the saved categorical packaging of the same formulas;
the final theorem supplies every canonical coefficient-site argument explicitly.
The current repair changes its import alone. Both node copies differ from the
current shared nodes only in `lean`.

## Dependency modules

`det-ctf-finite-comparison-localizing`: the delivery repairs the import in the
existing owning module `Sheaf.Paper.FiniteComparisonLocalizing`. Every declaration,
definition, signature and docstring is identical to the current main module. The
only module change replaces `ProEtale.Derived.LowerShriekComparison` by
`ProEtale.FiniteCoefficient.Derived.LowerShriekComparison`. The node changes only
`lean`; `lean.note` records the concrete compiler diagnostic. The item imports
and reuses all fourteen original declarations from their original module.

## Repair of immutable head 40ee3a5bb081

The return's duplicate-declaration point is repaired: the delivered
`FiniteComparisonLocalizingRepair.lean` is removed, its node record now names the
original owning module, and the main module imports
`Sheaf.Paper.FiniteComparisonLocalizing`. No declaration is renamed or restated
in a second module. A source comparison with the current main branch found the
single import difference described above; all fourteen declaration bodies match.
The rest of the saved main module, including the statement and complete proof
docstring, is retained.

The required initial dry run of the saved packet passed mechanical preflight and
per-file compilation (dry-run commit a2385073d2). That did not resolve the
maintainer's independent duplicate-declaration finding. Testing the main module
with the original owning module then reproduced the import incompatibility:
`FiniteCoefficient.Derived.Comparison` failed because the environment already
contained `AlgebraicGeometry.ProEtale.derivedComparisonAdjunctionPlus` from
`Derived.Comparison`. This concrete diagnostic requires the import-only repair
of the original module in the same delivery, rather than the duplicate module.

The self-check reread all three assertion formulas and the final coefficient
specialization against the unchanged node. The full-faithfulness/image clause,
counit equation and uniqueness, the equality of the two projection routes and
invertibility of their named maps, and both transpose orders all remain exactly
as described above. Empty schemes, the zero ring, arbitrary finite primary rings,
and unbounded inputs remain included. Every variable/universe is explicitly
bound (`autoImplicit false`), every definition has real data, and the main theorem
retains `sorry` with its eleven-step proof docstring. No statement correction or
new node is needed.

All validation uses the prescribed `scompile.py` and `deliver2.py` wrappers with
the unchanged 60-second file limit. No launcher script or source checkout is
edited, no global build is run, and all manual edits remain in this sandbox.

The repaired packet passed `scompile.py` for both delivered files in dependency
order. The owning module passed preliminary, sandbox and library checks (6.8,
7.1 and 7.4 seconds); the main module passed sandbox and library checks (9.9 and
11.1 seconds), with no diagnostics. The source-only comparison confirms that the
owning module has exactly the one import change. Both `lean.statement` fields
match the source signatures verbatim and both node copies change only `lean`.
