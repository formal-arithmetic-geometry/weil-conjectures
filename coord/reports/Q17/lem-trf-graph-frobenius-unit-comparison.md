## Worker report

The module `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` states
`WeilConjectures.TraceFormulaCoefficientConventions.graphFrobenius_unit_comparison`.
The repaired theorem retains the accepted constant-object and normalized kappa clauses.
Its ordinary-cohomology clause now uses precisely `finiteOrdinarySections T.datum
T.coefficients.l T.coefficientField T.geometricBaseChange T.level T.level_pos`.
`graphFrobeniusOrdinaryPullback` has those exact objects in its signature. Its map is the
recorded derived adjunction unit followed by `finiteOrdinaryLeray`, the canonical
sections-of-direct-image identification on that same model. The supporting new module
constructs the comparison with absolute derived sections and records its compatibility
with rho for every endomorphism. There is no statement correction or dependency repair.

Hypotheses and clauses, matched against the node:

- `T : TraceFormulaCoefficientConventions.{u}` supplies the full global datum
  `T.datum` (`p`, `a ≥ 1`, `q = p^a`, `k₀` of cardinality `q`, and its fixed algebraic
  closure `k`), the distinct coefficient prime `T.coefficients.l`, a finite extension
  in the chosen algebraic closure, and `T.level_pos : 1 ≤ T.level`.
  `T.coefficientRing` is the recorded `Padic.coefficientExtensionRing` at this level,
  hence precisely `O_E / varpi_E^n`; it is not an arbitrary finite ring substitute.
- `T.X₀` is the model over `Spec k₀`. Its stored `LocallyOfFiniteType` and
  `QuasiCompact` instances express finite type. `[IsProper T.X₀.hom]` is the additional
  properness hypothesis. The convention's separation field is entailed by properness.
  `T.geometricBaseChange` is exactly `(T.datum.geometricFiber T.X₀).left`.
- `(m : ℕ) (hm : 1 ≤ m)` retains every positive iterate. The scheme map is
  `T.datum.schemeFrobeniusIterate T.X₀ m`; the Galois map is `HPow.hPow` in
  `End T.geometricBaseChange` applied to the recorded geometric Galois Frobenius.
- The witnesses `r` and `τ`, their two normalization conjuncts, the equality `w`,
  and the formula for `κ.hom` specify the *canonical* comparison. This is the same
  existential presentation used by the recorded `schemeGaloisComparison` theorem.
  The first projection of `r_V` is the absolute Frobenius on `V`; its second projection
  is forced by its being a morphism over the base. Thus `r` is uniquely determined.
  The unit equation for every module, every object and every section uniquely
  determines `τ` by the fixed adjunction's Hom bijection. `w` expresses
  `Phi^m = F^(am) ≫ g^m`, i.e. `Phi^m = g^m ∘ F^(am)` in mathematical order.
  The formula for `κ` uses `proEtaleConstantRingPullbackComposition.inv`, then
  `Functor.whiskerLeft` of `proEtaleFrobeniusDerivedIso`, then the right unitor.
  Hence the existential statement cannot be satisfied by choosing a scalar multiple
  or a different natural isomorphism. It asserts the node's property of the specified
  comparison; it is not a bare existence of an isomorphism satisfying the conclusion.
  Its absolute exponent is `T.datum.a * m`; the normalized relative-Frobenius map at
  that exponent agrees with the multiplicative iterate by the recorded Frobenius-site
  theorem. No independent trivialization is used.
- The constant object `A_Y` is `DerivedCategory.singleFunctor _ 0` applied to
  `proEtaleConstantModule T.geometricBaseChange T.coefficientRing`, the existing
  abbreviation for the ring sheaf as its own module. `graphFrobeniusConstantDirectImage`
  applies Mathlib's `SheafOfModules.unitToPushforwardObjUnit` to the actual scalar
  structure map of the recorded direct image. `graphFrobeniusConstantPullback` is its
  adjunct under `proEtaleConstantRingAdjunction`. `graphFrobeniusDerivedConstantPullback`
  applies the exact derived/single comparison and then the degree-zero functor.
  These are the actual canonical `d_h` maps, with real construction data. The two
  `IsIso` conjuncts retain the node's specification that the identifications are
  isomorphisms, and the next conjunct is exactly `κ_A ≫ d_g = d_Phi`.
  Because these coefficient maps are normalized on scalars, this is the asserted
  preservation of the canonical constant section `1` (indeed, of every scalar).
- `graphFrobeniusOrdinaryPullback T h M` defines `rho_{h,M}` on the exact
  `finiteOrdinarySections` objects named above. Its implementation is
  `finiteOrdinaryPullback T.datum T.coefficientRing h M`. The functor on morphisms is
  `finiteOrdinarySectionsFunctor T.datum T.coefficientRing T.geometricBaseChange`;
  its object formula is definitionally the recorded `finiteOrdinarySections`, namely
  `proEtaleConstantDerivedDirectImage T.structureMap T.coefficientRing` followed by
  `(pointFiniteSections T.datum.k T.coefficientRing).mapDerivedCategory`.
  `graphFrobeniusGeometricOver` installs the actual stored structure map, with no new
  geometric hypothesis.
- `finiteOrdinarySectionsComparison` is the canonical comparison from that point-fibre
  model to absolute derived sections: inverse exact-postcomposition derived comparison,
  scalar-normalized point identification, then the a_Y terminal/Leray comparison.
  Its definition contains real isomorphism data. The point identification is selected
  from `finiteOrdinaryPointComparison_existsUnique`: its equation on every section of
  every realized fixed-scalar sheaf uniquely specifies the entire natural isomorphism.
  Thus this is a permitted uniquely determined object, not an arbitrary isomorphism.
  `finiteOrdinaryPullback_absolute_compatibility` explicitly states the commuting square
  for the derived unit for every scheme endomorphism, including both Phi^m and g^m.
  Both postponed supporting proofs are clauses of the new definition node and have
  complete proof docstrings. They do not supply unspecified construction data.
- The coefficient category is exactly the existing `ModuleCat.{u+1} (ULift.{u+1} A)`.
  Its derived localization in `finiteOrdinarySections` has Hom universe `u+2`.
  `finiteOrdinaryAbsoluteSections` and its actual Leray isomorphism are constructed
  in that same universe, without changing the small site (objects `u+1`, arrows `u`).
  No equality of independent mathematical universes is assumed. The old graph-specific
  derived-category instance and absolute-sections abbreviation have been removed.
- `∀ M : T.boundedConstructibleFiniteTor.FullSubcategory` restricts the last
  equality to exactly `D^b_ctf(Y,A)`. The equality is
  `rho_Phi M ≫ (finiteOrdinarySectionsFunctor _ _ _).map (κ.hom.app M) = rho_g M`, with the required arrow direction.
  Both rho families are composites of the natural derived unit and natural Leray
  comparison, and `κ` is a natural isomorphism. Thus these are natural morphisms in
  `M`, not selected pointwise maps. Quantifying their component equality over every
  object is the componentwise form of equality of the two natural transformations
  restricted to the full subcategory. No extra naturality hypothesis is imposed.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, its
  `CoefficientDatum` and `geometricFiber`, through the convention structure.
- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, `coefficientField`,
  `coefficientRing`, `geometricBaseChange`, `boundedConstructibleFiniteTor`.
- `Sheaf.SixFunctors.SchemeFrobenius`: `schemeFrobeniusIterate`,
  `geometricGaloisFrobenius` and `model_characteristic` from its public dependency.
- `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` (publicly reexporting
  `SchemeGaloisComparison`):
  `WeilConjectures.FiniteFieldDatum.schemeGaloisComparison`, whose final clause is
  the exact normalized presentation used here, now with the item's constant and
  ordinary-cohomology conclusions.
- `Sheaf.AlgebraicGeometry.FrobeniusFactorization`:
  `WeilConjectures.FiniteFieldDatum.absoluteFrobenius_factorization` fixes the scheme
  identity used to obtain `w` by the inverse Galois automorphism.
- `Sheaf.Paper.IntegralFinitePullbackComposition` reexports the general
  `proEtaleCanonicalPullbackComposition`; its public constant specialization
  `AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition` is used directly.
  This is the recorded K-flat-normalized comparison, in its inverse orientation.
- `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite`:
  `proEtaleFrobeniusDerivedIso` and
  `absoluteFrobenius_proEtale_trivialization`; its arbitrary-pullback/multiplicative
  extension is imported from `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback`.
- `Sheaf.Paper.DerivedPullbackTensorHom` and
  `Sheaf.Paper.SfDerivedDirectImage` retain their finite/integral/rational interfaces.
  Here the pullback, pushforward and adjunction are their canonical constant-ring
  presentation from `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `proEtaleConstantRingDerivedPullback`, `proEtaleConstantRingPushforward`,
  `proEtaleConstantRingAdjunction`. The unit–Leray dependency explicitly fixes these
  presentations together; no extra bridge or unidentified arbitrary adjunction is used.
- `Sheaf.Paper.OrdinaryCompactWeilCohomology` publicly retains the full
  `OrdinaryCompactCohomology` interface, including `finiteOrdinarySections`, which is
  now the actual object model in this statement. `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback`
  supplies `finiteOrdinarySectionsFunctor`, `finiteOrdinarySectionsComparison`,
  `finiteOrdinaryLeray`, `finiteOrdinaryPullback`, and
  `finiteOrdinaryPullback_absolute_compatibility`. It reuses
  `proEtaleUnitLeraySections`, `proEtaleUnitLerayDirectImageIso`,
  `proEtaleUnitLerayTerminalIso`, and `sfIntrinsicRealizationUnit` from the recorded
  unit/Leray chain module. Exact point sections use the recorded `pointFiniteSections`.
  Exact postcomposition uses upstream `rightDerivedFunctorCompMapDerivedCategoryIso`;
  the absolute Leray construction uses `rightDerivedFunctorCompIso'`. The literal
  terminal-object declaration is the finite-coefficient upstream
  `Scheme.ProEt.isTerminalMkId`, avoiding the superseded duplicate general module.
- The constant module uses `proEtaleConstantModule` from
  `Sheaf.AlgebraicGeometry.ProEtaleConstantModuleUnit` and Mathlib's `SheafOfModules.unit`;
  Mathlib's `unitToPushforwardObjUnit` is reused rather than copied.
- All stated proof dependencies are imported: the K-flat resolution with independent
  coefficient universes, K-injective resolution existence with independent site
  universes, the constant-ring-map normalization, sheafification, the conjugate-unit
  equation, and localization uniqueness. Their source docstrings and full signatures
  were read. The six-step theorem docstring follows the node's complete proof.

Edge cases checked before writing: the empty scheme and disconnected schemes are
allowed, with no nonempty-site or connectedness assumption. Nilpotents are retained:
relative Frobenius on weakly etale objects is the comparison, not an assumption that
absolute Frobenius is a scheme isomorphism. `m = 1` and `n = 1` are included; `m = 0`
and `n = 0` are excluded exactly by the node. Characteristic `2` and arbitrary `a ≥ 1`
are included, and no equality of scheme and site object universes is imposed.
The small site has objects in `u+1`, arrows in `u`, coefficients and modules in `u+1`.
Zero objects of `D^b_ctf` and all its morphisms are retained. There is no assumed Weil
structure on `M`, and no assumed invertibility of a coefficient morphism.

Searches for existing statements (all negative for the exact node):

- `msearch.py`, LeanFinder: “Canonical Frobenius pullback comparison preserves constant
  coefficients and ordinary derived global sections pullback” — eight hits, chiefly
  generic module pullback/free-unit and conjugate-adjunction comparisons. They do not
  state this normalized pro-etale Frobenius/cohomology equality.
- `msearch.py`, Loogle: `SheafOfModules.pullbackObjUnitToUnit` — six hits; inspected
  its full source and the scalar direct-image unit. Reused the latter as the real
  construction for the recorded adjunction's constant-module identification.
- `msearch.py`, Mathlib grep:
  `(frobenius|Frobenius).*(globalSections|cohomology)|(globalSections|cohomology).*(frobenius|Frobenius)`
  — zero hits.
- `msearch.py`, LeanSearch: “Frobenius pullback comparison on the pro-etale derived
  category preserves constants and commutes with ordinary global sections pullback”
  — eight hits; generic pullback comparisons and global-sections definitions, no match.
- `rg` of upstream `WeilConjectures` and side `lean/Sheaf` for Frobenius comparison,
  graphFrobenius, unit and cohomology names, and upstream search for the exact item id:
  no exact declaration. Read `SchemeGeometricFrobenius.lean`: it supplies the purity
  setting's single-iterate comparison and square naturality, not this theorem.
  Upstream étale `frobeniusOperator_unit_eq_self` concerns an endomorphism of the
  coefficient unit under an additional scalar-endomorphism hypothesis; it does not
  compare ordinary pro-etale cohomology maps and is not the item. Read the upstream
  pro-etale `TraceFormula/Frobenius.lean` exchange declarations too: these construct
  proper-gap compact-support Frobenius-square exchange, rather than the normalized
  scheme/Galois comparison on ordinary cohomology.

Source checked: the current blueprint proof Step 1, the node's detailed six-step
normalization/chain proof, and local Stacks `more-morphisms.tex`,
`lemma-relative-frobenius-weakly-etale` (Tag 0F6W). No statement dispute remains.

Validation: `scompile.py` compiled BOTH delivered files separately in dependency order,
including their exact library paths, with no errors or non-sorry warnings. Times were
4.4 s for FiniteOrdinaryPullback and 13.0 s for GraphFrobeniusUnitComparison on confirmation.
There are three postponed named proofs: the item theorem and the two explicitly stated
clauses of def-trf-finite-ordinary-pullback (unique normalized point comparison and
pullback compatibility). All construction definitions contain real data.

## New nodes

`def-trf-finite-ordinary-pullback` introduces the missing canonical bridge and ordinary
pullback interface. It does not redefine ordinary cohomology: its functor is exactly
the existing point-section/direct-image composite. Its statement specifies the uniquely
normalized point comparison on every section, the real a_Y Leray plus exact point-sections
comparison, the unit/Leray definition of rho in the recorded model, and the comparison's
commuting square for every h, explicitly including Phi^m and g^m. These are precisely
the additional comparison data requested in the return. Source: the parent's blueprint
Steps 1--2 and Stacks Tags 00YV, 08J6 and 0D6E.

The new node's hypotheses are `D : FiniteFieldDatum`, a finite commutative ring `A`,
`Y : Scheme` with its map to Spec D.k, and an arbitrary scheme endomorphism `h`.
`finiteOrdinaryPointComparison_existsUnique` expresses its unique scalar-normalization
clause on every fixed-scalar sheaf M and section s; `finiteOrdinaryPointComparison`
selects that determined map and follows it by inverse terminal evaluation.
`finiteOrdinarySectionsComparison` implements its exact-postcomposition/a_Y comparison.
`finiteOrdinaryAbsoluteLeray` derives the terminal identification in the same localization
universe; `finiteOrdinaryLeray` transports it back. `finiteOrdinaryPullback` implements
its derived-unit formula, and `finiteOrdinaryPullback_absolute_compatibility` is exactly
its last displayed equality, natural in every M. No k-linearity assumption is imposed.

New-node searches (the raw three tool outputs are preserved in `mathlib_searches`):
LeanFinder, “Canonical comparison between geometric point sections of derived direct
image and absolute derived global sections, compatible with adjunction unit pullback”
returned eight generic evaluation and adjunction facts. LeanSearch, “Geometric point
evaluation of derived direct image agrees canonically with derived global sections and
transports cohomology pullback” returned eight generic evaluation facts. Mathlib grep,
`finiteOrdinary.*(Comparison|Pullback)|point.*[Ss]ections.*[Ll]eray`, returned zero hits.
The same rg search in the upstream project, side Lean and DAG found only unrelated
strict-local/etale comparisons. `tools/blueprint_refs.py search 'ordinary sections comparison'`
returned zero blueprint nodes. No existing declaration or node supplies this canonical
comparison between the two actual recorded models.

## Repair self-check

Return L at immutable head 6fe7a17da7c2 had one substantive defect (H3/H4/H7): the
ordinary-cohomology model was silently changed. I compared the saved packet with the
current shared node and declarations. The initial required dry run passed technically
(commit 8eb16e455e), but inspection confirmed that semantic defect remained, so it was
not pushed. The repair retains the accepted r/tau/w/kappa, constants, properness,
positive iterate/level and finite-field hypotheses. It changes rho's type to the exact
recorded finiteOrdinarySections objects and supplies the requested canonical comparison
and DAG-recorded compatibility instead of substituting an absolute-sections model.
The main node changes only lean and adds this new definition dependency to stmt_deps.
The current selected scheme/Galois dependency module is imported, retaining the same
fully normalized original comparison theorem through its public import.

Checked the new comparison on Y empty, M zero and identity h: the functors and units
retain these cases, with no inhabitedness hypothesis. For Y=Spec k the comparison is
exact point sections followed by the identity-map terminal identification. For a
semilinear automorphism no equality a_Y h=a_Y is used: the transported terminal/Leray
identification works for every endomorphism. In particular the g^m map is the same
unit/global-sections construction required by the sibling point-exchange node, and its
source and target are precisely the parent's point-fibre cohomology objects.

The maintainer performs the independent review; no second-reader identity is claimed.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
