## Worker report

The module `Sheaf.AlgebraicGeometry.VectorBundleIntegration` defines ordinary-etale
integration for the actual relative-spectrum vector bundle recorded by
`def-asd-vector-bundle-zero-section`. The definition has the displayed source and target
of the node, expressed using the existing ordered shifted-Tate-tensor model also used by
the affine trace and its linear invariance. Two technical instances package the existing Zariski-slice sheafification and
local-bijection instances for fast elaboration of the finite-rank module class; they add
no hypothesis. No node statement or dependency list changes.
No new nodes or dependency modules are supplied.

Hypotheses and clauses, matched with Lean:

- The integer `N ≥ 1` is `(N : ℕ) (hN : 0 < N)`. The finite commutative ring is
  `(A : Type (u + 1)) [CommRing A] [Finite A]`; its annihilator is
  `(hA : (N : A) = 0)`. This is equivalent to `N A = 0`, by applying it to 1 and then
  multiplying by each element. No flatness or prime-power assumption is imposed.
- The base is `(S : Scheme.{u}) [IsNoetherian S]`; invertibility on it is
  `(hS : IsUnit (N : Γ(S, ⊤)))`. `IsNoetherian` has exactly local Noetherianity and
  quasi-compactness, and is equivalent to the finite affine Noetherian-cover condition.
- The bundle of rank `(d : ℕ)`, including zero, is `VectorBundleZeroSection.scheme S d F`,
  projected by `VectorBundleZeroSection.π S d F`, for `(F : SheafOfModules.{u} S.ringCatSheaf)` (definitionally `S.Modules`) with
  `[F.IsFiniteLocallyFreeOfRank d]`. These are the dependency's objects, not a new
  vector-bundle record or an arbitrary scheme isomorphic to a bundle.
- The geometric paragraph is `vectorIntegration_geometry`: affineness, local finite type, and a Noetherian total
  space. The two needed morphism properties are supplied locally in the definitions. Affineness
  gives separatedness and quasi-compactness by the recorded Mathlib instances. Nagata's
  instance supplies the compactification; no compactifiability assumption is added.
  Noetherian opens are packaged directly from the dependency's Mathlib declarations
  inside the local-map definition, with no second statement of that DAG node.
- `DerivedCategoryModule A T` is exactly the dependency's ordinary derived category of
  `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} A)`. The `u+1` coefficient universe is the
  recorded six-functor size convention, not an equality imposed on site universes.
- `affineLinearBaseCoefficient A N hA S d` is the EXISTING ordered tensor of `d` copies
  of the concrete roots-of-unity Tate line shifted by two, with zero stage the unit.
  `vectorIntegrationCoefficient` pulls this along the actual projection. Exact inverse
  image, the normalized Tate pullback isomorphisms, tensor comparison and shift
  additivity identify this model with `A_E(d)[2d]`; all shifts are even. No arbitrary
  isomorphism supplied by `Nonempty` is used as that coefficient identification.
  `vectorIntegrationBaseCoefficientPullback` constructs its pullback recursively from
  tensor pullback, normalized shifted-line pullback and constant-unit pullback.
- `vectorIntegrationSource` is `Rπ_!` at that coefficient, using
  `rightDerivedLowerShriek` and its chosen Nagata compactification. On bounded-below
  inputs this is exactly the compactification-independent object of the comparisons
  dependency. `vectorIntegrationSheaf` is its `H^0` by `homologyFunctor`.
- A frame on any open is the recorded `VectorBundleZeroSection.Trivialization`.
  `vectorIntegrationChart` is the canonical tower-to-affine-space map, the inverse
  of the frame's concrete coordinate map, and the inclusion of the inverse-image open.
  `vectorIntegrationChart_isPullback` states the corresponding Cartesian square over
  `V.ι`. This is the pasted restriction square and inverse-coordinate square prescribed
  by the node, not a square with the forward frame map.
- `vectorIntegrationChartCoefficient` uses inverse-image composition, the square's
  commutativity equation, normalized base Tate pullback and the inverse of the existing
  `affineLinearCoefficientDescent`. `vectorIntegrationLocalTrace` then composes the
  ACTUAL `rightDerivedLowerShriekBaseChangeMap`, this coefficient identification, the
  inverse of `affineLinearCompactComparison`, and `affineTraceCounit`. Thus it is the
  prescribed `a_i`, including the actual exchange-defined pullback action on overlaps.
- `VectorIntegrationNormalization` says that the derived pullback of a global map,
  followed by the canonical constant-unit identification, is that local trace on EVERY
  open equipped with a linear frame. It quantifies over the normalized projective-line
  data already used in the affine-trace dependency; none is an assumption on the final
  definition. Their roots, pure-tensor, Kummer and counit normalizations determine the
  same maps. Existence of these data is supplied by `exists_affineSpaceTopTrace`, so this
  condition is not vacuous.
- `existsUnique_vectorIntegrationGluing` states vanishing of `H^q(C_π)` for every `q ≠ 0`
  and uniqueness of the pair `(α, λ)`. Here `α : C_π ≅ L_π[0]` is required to induce the
  identity on `H^0`, using `singleFunctorCompHomologyFunctorIso`; `λ : L_π ⟶ A_S` is a
  sheaf map and their composite has exactly the local normalization. Its full proof
  docstring spells out overlap matrices, exchange pasting, `t ρ_g = t`, sheaf gluing,
  the truncation roof `Q(c) Q(b)⁻¹`, the cycles-to-cohomology chain-map equation,
  naturality after localization, representative independence, exact restriction,
  full faithfulness, and uniqueness via a common refinement.
- `vectorIntegrationGluing` takes its pair from that UNIQUE-existence theorem.
  `vectorBundleIntegration` is literally `α.hom ≫ singleFunctor.map λ`, namely
  `λ[0] ∘ α` in the node's right-to-left notation. This use of a postponed proof is
  permitted by AGENTS §5: it determines the object up to the equality used downstream.
  Neither an arbitrary map nor data chosen from a mere existence theorem occurs.
  Concentration, the identity on `H^0(α)`, and all frame normalizations are part of the
  theorem's signature; only their proofs are postponed. Each postponed helper belongs
  to a clause of this same node and is recorded in `lean.declarations`.
- At rank zero the local counit is exactly the identity-adjunction counit of
  `affineTraceAdjunction`; no positive-rank restriction is present. The map is ordinary
  etale throughout; no unrequested pro-etale identification is asserted.

Dependency declarations read and reused:

| Node | Module and declarations |
|---|---|
| def-asd-vector-bundle-zero-section | `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: `scheme`, `π`, `Trivialization`, `trivializationMap`, `trivializationMap_spec`, `transition_spec` in `AlgebraicGeometry.VectorBundleZeroSection` |
| def-weil-pbc-derived-categories | `Sheaf.AlgebraicGeometry.DerivedCategories`: upstream `AlgebraicGeometry.Etale.DerivedCategoryModule`, root `DerivedCategory.homologyFunctor`, `singleFunctor` |
| lem-asd-etale-finite-twist-pullback | `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `AlgebraicGeometry.Scheme.etaleFiniteTwistPullback`; concrete `finiteEtaleTateLine`, `finiteEtaleTateSheaf` and its normalized comparisons |
| def-amb-etale-compact-support | `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `rightDerivedLowerShriekOfCompactification`, `rightDerivedLowerShriek`, their bounded-below compatibility in `AlgebraicGeometry.Etale` |
| lem-amb-etale-compact-comparisons | `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`: `etaleCompactSupport_refinementComparison_eq`, upstream comparison/composition isomorphisms |
| thm-cbc-finite-torsion | `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`: `compactSupportFiniteTorsion` and the existing `rightDerivedLowerShriekBaseChangeMap` |
| lem-amb-affine-space-top-trace | `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`: `affineTraceCounit`, `affineTraceRight`, `exists_affineSpaceTopTrace`, tower and compact-support comparisons |
| prop-weil-pbc-inverse-image-modules-exact | `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`: `AlgebraicGeometry.etaleInverseImageModulesExact` |
| lem-weil-pbc-etale-cover-detects-iso | `Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily`: `AlgebraicGeometry.Etale.isIso_iff_of_jointlySurjective_etale_family` |
| lem-amb-linear-trace-invariance | `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`: `affineSpaceLinearTraceInvariance`, `affineLinearTraceAction`, `affineLinearBaseCoefficient`, `affineLinearCoefficientDescent`, `affineLinearCompactComparison` |
| lem-pur-sheaf-hom-cover-gluing | `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`: `SheafOfModules.existsUnique_hom_of_cover` |
| lem-weil-pbc-truncation-cohomology | `Mathlib.Algebra.Homology.Embedding.CochainComplex`: `CochainComplex.quasiIsoAt_ιTruncLE`, supported truncation and zero-homology instances from its recorded Mathlib match |
| lem-weil-pbc-truncation-descends | `Sheaf.CategoryTheory.TruncationDescends`: `DerivedCategory.truncation_descends` |
| def-weil-abstract-derived-category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q` |
| lem-weil-pbc-derived-single-fully-faithful | `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`: full/faithful instances of `singleFunctor` and `singleFunctorCompHomologyFunctorIso` |
| lem-weil-pbc-affine-morphism-permanence | Mathlib `Morphisms.Affine`, `Morphisms.Separated`, `Limits`: affine base change, affine source, quasi-compactness, separatedness, finite coproduct affineness |
| lem-weil-pbc-lft-pointwise-criterion | `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`: `AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE`, specialized to `LocallyOfFiniteType` |
| lem-weil-pbc-finite-type-over-noetherian | Mathlib `Noetherian`, `Morphisms.QuasiCompact`: `LocallyOfFiniteType.isLocallyNoetherian`, `QuasiCompact.compactSpace_of_compactSpace`, `IsNoetherian.mk` |
| lem-weil-pbc-locally-noetherian-quasi-separated | `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian.quasiSeparatedSpace` |
| thm-nagata-compactification | `WeilConjectures.Compactification.NagataCompactification`: `AlgebraicGeometry.NagataCompactification` and its `HasCompactification` instance |
| lem-weil-pbc-noetherian-open-subscheme-noetherian | Mathlib `Noetherian`, `Topology.NoetherianSpace`: restriction of local Noetherianity, `IsNoetherian.noetherianSpace`, `IsInducing.noetherianSpace`, `NoetherianSpace.isCompact` |

The ring-sheaf Hom-gluing dependency uses `SheafOfModules`; its proof application is
through the standard constant-module encoding, or equivalently sectionwise gluing of
linear maps in `Sheaf ... (ModuleCat A)`. This is only a proof-level encoding change:
the maps, coefficient object and derived category in the statement stay the recorded ones.
All statement-dependency modules are imported, including those used by the construction
proof rather than by the definition's data expression.

Edge cases checked: `d=0`, the zero coefficient ring, `N=1` (which forces the coefficient
ring to be zero), the empty base, empty opens and empty overlaps, non-affine overlaps,
and non-separated Noetherian bases. The latter are allowed: the vector-bundle morphism
is separated although the base need not be. There is no choice of a finite frame cover,
no positive-rank condition, no flatness assumption on A over Z/N, no finite-Tor assumption
on an arbitrary derived object, and no restriction to a split bundle. Empty covers of an
empty scheme cause no uniqueness problem since all relevant module sheaves are zero.

Searches actually run with `msearch.py NI def-amb-vector-integration`:

- LeanFinder: `Integration along an algebraic vector bundle by gluing compactly supported
  etale affine space traces`. Eight hits: analytic compactly supported integrals and
  topological vector-bundle trivializations; none is algebraic-etale integration.
- Loogle: `"trace", "VectorBundle"`. Zero hits.
- Grep: `vectorBundleIntegration|vectorIntegration|integration.*vector.*bundle`. Zero
  Mathlib hits.
- LeanSearch: `Vector bundle integration in etale cohomology from locally normalized
  affine space compact support trace maps`. Eight hits: `Algebra.normalizedTrace`,
  integral ring traces, and topological `VectorPrebundle`/`VectorBundle`; no match.
- `rg` in upstream `WeilConjectures/`, this project's `lean/Sheaf/`, and
  `dag/lean_names_upstream.json` for `vectorBundleIntegration`, `vectorIntegration`,
  the node id, and integration/vector-bundle words. No declaration of this integration.
  Upstream `EtaleCohomology/Purity/Smooth/AffineSpace.lean` describes a different affine
  comparison and does not define the vector-bundle trace required here. The supplied
  affine-trace and linear-invariance interfaces are reused rather than copied.

No statement fault or STATEMENT-DISPUTED flag was found.

Validation: `scompile.py NI def-amb-vector-integration` compiled the delivered module
cleanly (7.2 seconds), together with the published affine linear trace dependency
in the private overlay. The worker completion status is issued only after
`deliver2.py NI def-amb-vector-integration --no-push` prints OK. Direct file writes
are restricted to this sandbox; wrapper bookkeeping follows the authorized workflow.
No push or final delivery is performed by this worker.

## Second reading by NI

I independently read the current node, its sandbox copy, all 21 statement-dependency
records, and the delivered Lean module. I read the item's actual source,
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/def-amb-vector-integration.md`,
and Step 7 with Steps 5--6 of its unit `_section.md`. The source is a blueprint definition,
not a Stacks-tagged statement. For the underlying bundle convention I also read
`literature/stacks-project/constructions.tex`, section Vector bundles, especially
`definition-vector-bundle` (01M2): it uses Spec Sym(E), with no dual inserted. The node
specializes that construction to constant finite rank and explicitly supplies the finite
coefficient and Noetherian hypotheses of its recorded affine-trace dependency.

Here is my object/hypothesis/conclusion inventory and its match to Lean. Every entry
below passes; no mathematical statement, dependency record, or Lean body needed repair.

1. **Positive annihilator N.** `N : ℕ`, `hN : 0 < N` render the positive integer.
   `hA : (N : A) = 0` is exactly NA=0 for a unital ring: evaluate NA=0 at 1 in one
   direction and multiply the displayed equation by each a in the other.
2. **Finite commutative coefficients A.** `A : Type (u + 1)`, `[CommRing A]`,
   `[Finite A]` retain every finite commutative ring, including the zero ring. There is
   no field, nontriviality, prime-power exponent, or Z/N-flatness assumption.
3. **Base S and invertibility.** `S : Scheme.{u}`, `[IsNoetherian S]`, and
   `hS : IsUnit (N : Γ(S, ⊤))` render precisely the node's base conditions. I checked
   Mathlib's `IsNoetherian` class and finite-affine-cover equivalence in Noetherian.lean.
   The base is not assumed separated or affine, nor a scheme over a field.
4. **Constant rank and actual bundle.** `d : ℕ`,
   `F : SheafOfModules.{u} S.ringCatSheaf`, `[F.IsFiniteLocallyFreeOfRank d]`,
   `VectorBundleZeroSection.scheme S d F`, and `VectorBundleZeroSection.π S d F`
   are the dependency's locally free module, Spec Sym(F), and structural map. I read
   its `algebraObject`, `over`, `scheme`, and `π` bodies, not just their names.
   `S.Modules` in that dependency unfolds to this same module category.
5. **Geometry and compactifiability.** `vectorIntegration_geometry` states affine,
   locally finite type, and Noetherian total space. The affine-morphism instances give
   quasi-compactness and separatedness; finite type means local finite type together
   with quasi-compactness here. I checked the recorded Mathlib permanence and
   Noetherian declarations and upstream Nagata's compactification instance. The local
   instances in `vectorIntegrationSource` discharge compactifiability from these
   properties, without making it an additional binder. The geometry theorem's proof
   docstring follows the node's affine polynomial charts and pointwise criterion.
6. **Ordinary etale derived categories and target.** `DerivedCategoryModule A T`
   uses `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u+1} A))`.
   `ordinaryFiniteConstant A S` is the constant sheaf on the module A, and
   `ordinaryFiniteUnit A S` is its `singleFunctor _ 0` image. I opened
   DerivedCategories.lean and OrdinaryFiniteP1Kummer.lean. Thus the target is A_S[0]
   in the required ordinary category; no pro-etale or constructible category occurs.
7. **Tate coefficient A_E(d)[2d].** `vectorIntegrationCoefficient` is the actual
   projection inverse image of `affineLinearBaseCoefficient A N hA S d`. I read that
   dependency's recursion: its zeroth term is the constant unit and its next term is
   derived tensor with the concrete `ordinaryFiniteLine ...` shifted by two. The
   line is the single complex of `Scheme.finiteEtaleTateLine`, the recorded
   scalar-extended roots-of-unity sheaf. Exactness and local freeness of this line
   identify the ordered derived tensor with the ordinary tensor powers and total
   shift 2d. This is an existing coefficient model, not a second twist definition.
   `vectorIntegrationBaseCoefficientPullback` recursively composes the actual tensor,
   constant-unit, and normalized shifted-line pullback comparisons. No unspecified
   isomorphism supplies its normalization.
8. **C_pi and L_pi.** `vectorIntegrationSource` applies the existing unbounded
   `rightDerivedLowerShriek` to that coefficient; its body uses the canonical
   Nagata instance. `vectorIntegrationSheaf` applies `homologyFunctor _ 0` to it.
   I read upstream LowerShriek.lean: the functor is D(j_!) followed by R(p_*),
   with the chosen compactification and its existing D+ compatibility. The node's
   bounded-below independence is therefore applicable to this shifted Tate input.
9. **Linear frames and inverse-coordinate square.** The frame binder is the
   dependency's `VectorBundleZeroSection.Trivialization S d F V`. I read its
   definition, `trivializationMap`, `trivializationMap_spec`, and `transition_spec`.
   `vectorIntegrationChart` composes the tower-to-affine-space isomorphism with
   `inv (trivializationMap ...)` and the inverse-image-open inclusion. Thus its
   direction is exactly phi_i inverse, as the node requires.
   `vectorIntegrationChart_isPullback` states the Cartesian square over V.ι; the
   docstring describes the two squares it pastes.
10. **Prescribed local maps a_i.** `vectorIntegrationChartCoefficient` first uses
    inverse-image composition and the actual square equation, then the base Tate
    pullback and inverse `affineLinearCoefficientDescent`. In
    `vectorIntegrationLocalTrace` the four consecutive maps are the actual
    `rightDerivedLowerShriekBaseChangeMap`, its compact-support image of this
    coefficient comparison, inverse `affineLinearCompactComparison`, and
    `affineTraceCounit`. I read the affine dependency's definitions of the tower,
    counit, and comparison. This matches the stated exchange-to-affine-trace map,
    including the constant-unit identification in the normalization equation.
11. **Concentration in degree zero.** The first conjunct of
    `existsUnique_vectorIntegrationGluing` is
    `∀ q : ℤ, q ≠ 0 → IsZero ((homologyFunctor _ q).obj C_pi)`.
    Its proof plan uses exact restriction and the jointly surjective etale
    detection theorem, after forgetting to abelian sheaves. I checked those
    dependency signatures: detection is for abelian etale sheaves and accepts an
    arbitrary jointly surjective etale family, as used here.
12. **Overlap equality and unique sheaf gluing.** The normalized local equation is
    required for every open V and every linear frame e by
    `VectorIntegrationNormalization`. Its proof docstring specifies
    g=(G transpose) inverse, phi_j inverse = phi_i inverse composed with a_g,
    horizontal exchange pasting, B_j=rho_g B_i, and t rho_g=t. I checked the
    dependency `affineLinearTraceAction`: rho_g is precisely exchange followed by
    the normalized coefficient pullback, conjugated by the tower comparison.
    Taking H^0 gives the compatible sheaf maps. The gluing dependency's signature
    gives existence and uniqueness of module-sheaf morphisms with these restrictions;
    the standard constant-module encoding, or its sectionwise linear-map gluing
    argument, applies without altering the category of the delivered definition.
13. **Canonical alpha and lambda.** The second conjunct is a unique-existence
    statement for `(alpha : C_pi ≅ single L_pi, lambda : L_pi ⟶ A_S)`.
    Its first equation explicitly makes H^0(alpha) the identity under
    `singleFunctorCompHomologyFunctorIso`, rather than allowing an arbitrary
    isomorphism. The full-faithfulness and truncation dependency signatures give
    exactly the cycles-to-cohomology projection and localization comparisons
    described in the node. The proof docstring includes the roof Q(c)Q(b) inverse,
    the boundary equation, naturality, representative independence, and restriction.
    Degree-zero faithfulness fixes alpha; the local equations fix lambda.
14. **Final map, uniqueness, and independence.** `vectorIntegrationGluing` selects
    only this uniquely characterized pair; `vectorBundleIntegration` is literally
    `alpha.hom ≫ singleFunctor.map lambda`, which is lambda[0] composed with alpha.
    The normalization quantifies normalized t and D inside a Prop, not as extra
    assumptions of the definition. I read `OrdinaryFiniteTwistTransport`,
    `OrdinaryFiniteP1Datum`, and `exists_affineSpaceTopTrace`: the first fixes roots
    inclusion and pure tensors; the second fixes the Kummer class, decomposition
    components, and counit. The theorem supplies such data, so the quantification is
    not vacuous, and these normalizations fix the same local arrows. Requiring all
    these presentations therefore expresses the single canonical trace. The proof
    docstring explains independence of covers by their intersection refinement and
    uniqueness of the derived map via single-complex full faithfulness.

I checked the following boundary cases separately. Rank zero is allowed throughout:
the ordered coefficient starts with the unit and the affine adjunction starts with
the identity. N=1 forces A to be the zero ring, which is not excluded. A=0 and empty
S are covered; on the empty site the relevant module sheaves have only zero data,
so an empty trivializing cover does not violate uniqueness. Empty opens and overlaps
are allowed. Non-affine overlaps and non-separated Noetherian bases are allowed;
the bundle projection itself is separated. There is no extra characteristic
restriction beyond invertibility of N. The explicit universe u is unrestricted;
the u+1 coefficient convention is exactly the recorded ordinary-etale category's
convention, and every finite ring can be placed there. No independent small test
universe, positive-rank binder, or nonempty-cover assumption is introduced.

My searches used different terms from the worker's, through
`python3 /home/ubuntu/weil-launcher-nt/msearch.py NI def-amb-vector-integration`:

- LeanFinder: `A canonical Gysin integration morphism for a locally free algebraic
  vector bundle obtained from finite torsion etale compact support cohomology`.
  Eight hits concerning immersions, normalization, module pullback, affine-space
  coordinate maps, and etale loci; none is this integration map.
- Loogle: `"trace", "Sheaf"`. Zero hits.
- Grep: `Gysin|gysin|integration|Integration`. The 25 returned Mathlib hits concern
  analytic integration, differential algebra, and probability, not this construction.
- LeanSearch: `Gysin trace for a finite rank algebraic vector bundle on the derived
  category of etale sheaves, defined by local affine space traces`. Eight ring trace
  and trace-form hits, none an etale compact-support integration.
- I independently ran rg for Gysin, bundle trace, and integration/bundle combinations
  in upstream WeilConjectures, this project's lean/Sheaf, the upstream name index,
  and Mathlib/AlgebraicGeometry. The related upstream
  `EtaleCohomology/Purity/Smooth/AffineSpace.lean` explicitly says its integration
  and vector-bundle forms are not constructed. I opened that module to check this;
  its Nonempty affine purity isomorphisms do not supply the node's specified map.
  The landed affine trace and linear invariance are reused by the delivered module.

H4/H5/H6/H8/H9 checks: no duplicate notion or missing prerequisite was found; there
are no new nodes or dependency modules. The three postponed declarations are
`vectorIntegration_geometry`, `vectorIntegrationChart_isPullback`, and
`existsUnique_vectorIntegrationGluing`. Each is a clause/construction obligation of
this DAG node, is listed in lean.declarations, and has a source/blueprint/proof
docstring. Every theorem body is sorry. Definition data are actual composites,
recursions, existing-instance packaging, or selection from unique existence; no
definition contains sorry. All 15 declarations have source/blueprint docstrings.
No line exceeds 100 characters. `autoImplicit false`, explicit universe u, and a
binder-by-binder reading leave no unbound variable or universe. The node's
lean.statement is verbatim the main definition's signature. No statement_change
was necessary, so no corrected-statement citer audit applies.

Changes in this second reading: appended this independent review only. The Lean
module and node record passed unchanged; I did not rewrite the worker's correct work.

Validation repeated independently:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NI def-amb-vector-integration
lean/Sheaf/AlgebraicGeometry/VectorBundleIntegration.lean` compiled both the sandbox
and library views cleanly (6.1 and 6.5 seconds respectively), with no errors or
warnings. The only delivered module is this one; scratchpad probes are not delivered.
