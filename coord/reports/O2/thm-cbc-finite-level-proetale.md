## Worker report

The module `Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange` states
`AlgebraicGeometry.ProEtale.globalFiniteLevelCompactSupportBaseChange` with `sorry`.
It supplies ten real helper constructions belonging to this node: the fixed-scalar
coefficient coordinates and retained witness; the degreewise pullback comparison;
the two canonical endpoint comparisons; the two endpoint functors; the prescribed
exchange; and the source and target compactification comparisons. No independent
mathematical notion or additional postponed theorem is introduced.

The maintenance repair note for this item was read, including its archived binding.
The archived theorem required `D : Etale.LocalCompactSupportExtension Λ` and was
explicitly invalidated. This delivery does not import that module, introduce that
datum, use chart normalization, or choose a compactification from a mere existence
proof. It uses the supplied global compactification; the theorem also states its
existence under the qcqs alternative. All maps are on ordinary D-plus categories.
The current DAG statement and proof already incorporate the human-authorized repair,
so no statement correction is made in this delivery.

Hypotheses and clauses, matched to the current node:

- A finite commutative ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  `[TopologicalSpace Λ] [DiscreteTopology Λ]` specifies its prescribed discrete topology.
  This is the module universe used by the recorded finite-coefficient category.
- Four schemes and all four arrows are explicit binders. `sq : IsPullback g' f' f g`
  is precisely the compact-support Cartesian square; `c.ofIsPullback sq` is its
  recorded base-changed compactification. The arrows need not be literal chosen
  pullback projections: the API handles the given Cartesian square.
- Separatedness is `[IsSeparated f]`; finite type is
  `[LocallyOfFiniteType f] [QuasiCompact f]`. There is no property assumed of `g`.
- The alternative on the base is
  `h : (CompactSpace Y ∧ QuasiSeparatedSpace Y) ∨ Nonempty (Compactification f)`.
  The conclusion includes `Nonempty (Compactification f)` and then quantifies over
  **every supplied** `c : Compactification f`. Thus a given compactification is
  retained as data when the formula is evaluated, and the qcqs case supplies
  existence by Nagata. No global object is defined by choosing from that existence.
- `K : FiniteCoefficientDerivedCategoryPlus X Λ` is the actual bounded-below
  continuous-function-coefficient category of the dependency node.
  `W : EtaleOriginWitness X Λ K` is its recorded pair with fields `W.L`, `W.alpha`.
  The Scheme-namespace alias in the current dependency record reexports this same
  ProEtale-namespace structure; no witness definition is copied.
- `cbcFixedCoefficients` is the inverse of the **canonical coefficient realization**,
  applied termwise. `cbcFixedWitness` uses its unit, the standard derived composition
  comparison, and `W.alpha` to transport that same pair to fixed-scalar coordinates.
  This changes coordinates, not the coefficient ring sheaf or category. The inverse
  is the inverse of an equivalence, determined up to the relevant isomorphism;
  it is not chosen from an existence assertion about compact-support maps.
- `cbcGlobalSourceFunctor` is inverse realization, then
  `rightDerivedLowerShriekOfCompactificationPlus ... c` (the actual `j_! ⋙ Rp_*`),
  then exact `g` pullback, then realization at Y'. `cbcGlobalTargetFunctor` is
  inverse realization, exact `g'` pullback, `j'_! ⋙ Rp'_*`, and realization at Y'.
  These are the stated source and target operations written in the canonical
  fixed-scalar module-sheaf presentation of the finite coefficient category.
- `cbcGlobalPullbackComparison` is the recorded unit-normalized sheaf pullback
  comparison, applied degreewise with the standard derived composition isomorphisms.
  `cbcGlobalSource` and `cbcGlobalTarget` are exactly S and T of proof step 4.
  Their compact-support comparison is `compactSupportSiteComparisonPlus`: its
  proper factor is the specified counit mate and its open factor the exact
  degreewise site/open comparison. Neither is an arbitrary natural isomorphism.
- `cbcGlobalExchange` is explicitly, in Lean composition order,
  `P(alpha.inv) ≫ S.inv ≫ A.map(E_c.app W.L) ≫ T.hom ≫ Q(alpha.hom)`,
  followed by coefficient realization. Here E_c is exactly
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c`.
  The first conclusion is `IsIso` of this particular arrow.
- The second conclusion quantifies over **every** other witness `W'` and equates
  the two arrows. It does not merely assume an isomorphism of etale representatives:
  full faithfulness supplies the unique such isomorphism in the proof.
- `cbcGlobalSourceComparison` transports the canonical etale
  `(derivedPlusFormalism ...).shriekIso c d`, first through exact g pullback and
  comparison, then through S and the retained alpha. `cbcGlobalTargetComparison`
  transports the corresponding primed shriekIso at `g'` pullback of W.L through T
  and alpha. These are U and V of proof step 8. The third conclusion is the full
  commuting square `E_c ≫ V.hom = U.hom ≫ E_d` for every d. The last conclusion
  states that both canonical comparisons are independent of the retained witness.
  Independence of a common refinement is built into the existing canonical
  `shriekIso`, rather than adding or choosing a new refinement.
- No constructibility, coefficient invertibility, residue-characteristic, qcqs
  condition on Y', or quasi-compactness condition on g is imposed. In the supplied-c
  branch Y is also unrestricted. The open immersion's quasi-compactness follows
  from finite type of f and separatedness of the proper factor (`QuasiCompact.of_comp`)
  and is not an additional binder.

Dependency declarations read and used (including their full signatures/docstrings):

- `WeilConjectures.Compactification.BaseChange`:
  `AlgebraicGeometry.Compactification.baseChange`, `ofIsPullback`, and the two
  `isPullback_*_ofIsPullback` declarations; arbitrary base change of compactifications.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`;
  the actual etale proper/open exchange.
- `def-weil-pbc-scheme-conventions` is a convention node, not a declaration. Its
  separated and finite-type notions are precisely the Mathlib classes above.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientDerivedCategoryPlus`, `finiteCoefficientRealization`, its
  additive/exact/equivalence instances, and `finiteCoefficientComparison`.
- `Sheaf.Paper.RingedEtaleOriginWitness` reexports
  `AlgebraicGeometry.ProEtale.EtaleOriginWitness` via
  `AlgebraicGeometry.Scheme.EtaleOriginWitness`; the original structure is in
  `Sheaf.Paper.EtaleOriginWitness`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and its imported
  ordinary ring-sheaf operations supply the recorded ordinary, uncompleted
  interpretation. In fixed-scalar coordinates we use the existing exact
  `ProEtale.upperStar` and `rightDerivedLowerShriekOfCompactificationPlus`; the
  latter is extension by zero followed by ordinary right-derived direct image.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparisonCoefficientPullbackIso` and
  `supportSiteComparison_pullback_coherent`; canonical unit-normalized comparison.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit` and `compactSupportComparisonUnit`; full
  faithfulness on all D-plus, with no individual finiteness or constructibility.
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`:
  `Etale.compactSupportFiniteTorsion` and the recorded formalism comparison and
  compactification-independent exchange declarations. These identify the
  specified proper/open refinement maps with the canonical shriekIso and give
  the comparison square used in proof step 8.
- The added **already landed** statement dependency
  `lem-sf-class-compact-support-comparison` owns
  `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparisonPlus` is the canonical normalized proper/open
  comparison used in S and T. No node or dependency module is created or repaired.
- The main docstring reproduces all eight proof steps, including Nagata,
  quasi-compactness of the open, boundedness, the proper/open comparison,
  explicit transport, invertibility, full-faithful lifting, cancellation, and
  the transported compactification square. Stated proof dependencies are imported.

Edge cases checked before writing and again against the final signature:
empty X or Y', the zero ring and zero complex, disconnected schemes, identity
base change, identity open/proper factors, two genuinely different witnesses,
arbitrary two compactifications without a specified Cartesian refinement, and a
non-qcqs Y or Y' with a supplied compactification. None is excluded. The topology
and all site/module universes are those of the existing small-site declarations;
no equality of site object and morphism universes is added. The definition of the
primed comparison derives `QuasiCompact f'` by base-change stability and does not
assume it or require qcqs of Y'.

Searches for existing statements/constructions:

- `msearch.py`, LeanFinder: “Finite ring proetale compact support base change etale
  origin independent witness compactification” returned 8 ordinary etale algebra
  results, beginning with `StandardEtalePair.hasMap_X`; no matching theorem.
- `msearch.py`, Loogle: `CategoryTheory.IsIso, AlgebraicGeometry.ProEtale` returned
  no hits (the ProEtale namespace is not in the Mathlib search index).
- `msearch.py`, LeanSearch: “A finite coefficient proetale compact support base
  change map on bounded below etale origin objects is invertible and independent
  of compactification” returned 8 algebra/scheme base-change facts, including
  `AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme`; no derived theorem.
- `msearch.py`, Mathlib grep `proetale|compactSupport.*baseChange` in
  `AlgebraicGeometry` returned 10 proetale-site/ElladicCohomology references,
  none constructing or stating this exchange.
- `rg` of `compactSupport|compactification.*BaseChange|plusEtaleOrigin` in the
  upstream source found the ordinary fixed-scalar origin and operation APIs;
  the prescribed grep for the node id in the older source returned no hits.
  The shared newer framework has
  `isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`: its full
  signature concerns an ambient fixed-scalar component and an existential
  etale-origin predicate. It does not state the retained finite-coefficient
  witness transport together with the explicit compactification-independence
  square, so it is not an exact existing match for the current node.
- `rg` of `EtaleOriginWitness` and compact-support/exchange names in `lean/Sheaf`
  found the recorded witness, canonical compact-support site comparison,
  and `CompactSupportExchangeTransport`. Those canonical constructions were
  inspected and reused where applicable. The old
  `FiniteLevelProEtaleCompactSupportBaseChange` theorem takes local extension
  data and was invalidated by this item's maintenance repair note; it is not
  rebound or imported. The new names were also searched in the source and
  side library and have no existing declaration.

Validation uses only `scompile.py` and the prescribed `deliver2.py` dry run;
no global build or direct Git mutation was run. Every theorem proof in this
module is `sorry`; definitions consist entirely of the canonical data above.

## Second reading by N2

This is the worker's self-check, not a claim of independent review. The dispatcher
brief prohibits starting other agents; the maintainer provides independent review.
I reopened the current node and its repair note beside the final file. I checked
all binders and each conjunct as mapped above. The abandoned local-extension
interface was removed before delivery. The final construction keeps K and its
actual witness in the recorded coefficient category and stays on D-plus throughout.
The comparisons use the correct orientation `shriekIso c d`; the square is
`E_c ≫ V = U ≫ E_d`. Arbitrary witness independence, both compactification
comparisons, the qcqs-or-supplied-compactification alternative, and unrestricted
Y' and g are all explicit. Only the item's lean record and addition of the
already landed canonical comparison dependency change; its statement and proof
remain unchanged. There are no statement disputes or new nodes.
