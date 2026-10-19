## Worker report

The module `Sheaf.Paper.EtaleSectionDeformationComparison` states
`AlgebraicGeometry.Etale.EtaleSectionDeformationComparison.etale_section_deformation_comparison`.
It constructs the specified normal chart, the two counit-normalized locality comparisons,
and the specified specialization, then states `delta ≫ normalComparison = chartComparison`.
Composition in Lean reads from left to right, so this is precisely
`chi_lambda ∘ delta = chi_e`. Every theorem proof is `sorry`; every definition has real data.

The sandbox draft from the earlier attempt was retained. Its first compile failed only
because three affine-space Noetherian instances lacked the compact-space parent instance.
Each is now supplied by `QuasiCompact.compactSpace_of_compactSpace` for the affine-space
projection. No additional geometric assumption was introduced to address that diagnostic.

The source read is the current main-20261015 `sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md`,
Local construction, normalization at one and Gluing, together with the item's eight proof steps.

Hypotheses and clauses, individually:

* Prime ell and n >= 1: `(ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)`.
* The coefficient ring Z/(ell^n): the dependency's `Coeff ell n`, literally
  `ULift.{u+1} (ZMod (ell ^ n))`; this changes only the coefficient universe.
* S,V schemes and Noetherian: `{V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]`.
  Mathlib's `IsNoetherian` is locally Noetherian plus quasi-compact, equivalently the
  finite affine-cover convention in the node.
* Ell invertible on both: `hS` and `hV`, `∀ x, IsUnit (ell : _.presheaf.stalk x)`.
* d >= 0: `(d : ℕ)`, including zero.
* Smooth pure relative dimension d: `[SmoothOfRelativeDimension d g]`, using precisely
  the recorded Mathlib definition and its standard-smooth local presentations.
* Separated and finite type: `[IsSeparated g] [QuasiCompact g]`; smoothness supplies
  locally finite presentation, hence locally finite type.
* Closed section: `(s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)`.
* Regular of codimension d: `hregular` gives an affine neighbourhood of each point
  of the centre, `r : Fin d → Γ(V, W.1)`, `Sequence.IsWeaklyRegular ... (List.ofFn r)`,
  and `Ideal.span (Set.range r) = s.ker.ideal W`. The successive multiplication maps
  are injective; the quotient is O_S because the ideal is the closed section's kernel.
* N=Spec Sym(I/I²), pi and zero: `s.ker.normalCone`, `Scheme.Hom.normalConeProj g s`,
  and `s.normalConeZeroSection` are the actual Rees-cone presentation used by the
  recorded section-specialization dependency. Its `geometry`, the conormal
  `symmetricComparison`, and `purityNormalCone_comparison` identify this presentation
  canonically with the stated relative Spec, preserving projection and augmentation.
  The landed finite-ring module additionally supplies `coneBundleIso` and
  `coneBundleIso_spec` for exactly this canonical presentation, with no arbitrary frame.
* U open and containing the whole section: `j : U ⟶ V` with `[IsOpenImmersion j]`,
  `sU : S ⟶ U`, and `sqj : IsPullback sU (𝟙 S) j s`.
  An open immersion with this square is precisely an open neighbourhood of s(S).
  `[IsNoetherian U]` and `[QuasiCompact j]` are the automatically existing structures
  on such an open in a Noetherian scheme, not restrictions on the neighbourhood.
  `[IsClosedImmersion sU]` is the pullback of the closed section.
* The coordinates e: `e : U ⟶ AffineSpace (ULift.{u} (Fin d)) S`, `[Etale e]`,
  `[IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]`. The last two express
  finite type (local finite type is also implied by etaleness).
* e an S-morphism: `w : e ≫ q = j ≫ g`, with q the recorded affine-space projection.
* e sends the section to zero and has exactly that zero inverse image scheme-theoretically:
  `sqe : IsPullback sU (𝟙 S) e (AffineSpace.zeroSection ... S)`.
  Its commutativity is used explicitly for the section identity in the conclusion.
* The specified frame lambda: `normalChart` inverts the published normal map of j,
  follows with that of e, and the standard `originNormalChart`. The latter is the
  zero-fibre inclusion followed by `deformationSpaceToAffineSpace` and affine base
  change to S. The upstream chart is literally u_i=x_i/t, so the induced coordinates
  are `[e^*x_i]`, rather than a chosen invertible matrix. `normalChart_spec` records
  its invertibility, structural map and zero-section identity.
* Whole ordinary unbounded constant-coefficient derived categories: all objects are
  `DerivedCategoryModule (Coeff ell n) S` through the recorded `sectionInvariant`;
  no boundedness, constructibility, pro-etale or Tate datum occurs in any binder.
* Omega_h=h^times A: dependency `sectionInvariant A g s` is the left-derived exact
  inverse image of `dualizingComplex A g`, the chosen compact-support right adjoint
  evaluated on the monoidal unit. The right adjoint uses ordinary etale compact supports.
* Compactifiability: explicit `HasCompactification` instances for g, j≫g, q, pi,
  and the actual deformation projection. These are the indicated smooth maps; the
  auxiliary restrictions admit compactifications by Noetherian Nagata. Compactifiability
  of the etale isomorphism lambda likewise follows, and is inferred by Lean.
* The actual extended-Rees deformation and its fixed zero fibre: dependency
  `family`, `atZero` and `specialization` use `s.ker.deformationSpace`, its canonical
  zero-fibre inclusion and the specified exceptional base-change map. They are reused,
  not passed as arbitrary schemes or fibre identifications. `delta` only supplies the
  auxiliary geometry instance and applies that same `specialization`.
* Normalized delta: `(κ : family ... ≅ a^*sectionInvariant ...)` and
  `(hκ : Normalized ... hs κ)`. This quantifies over every normalized comparison.
  The existing `existsUnique_normalized` supplies exactly one under these hypotheses,
  so no extra comparison assumption is introduced and the assertion is non-vacuous.
* Chi_e: `chartComparison` is `etaleSectionMap` for j followed by the inverse
  `etaleSectionMap` for e. Both use `FiniteRingSectionDeformation.locality`, chosen
  from the unique counit-characterized `existsUnique_etaleAmbientAdjointLocalityIso`.
* Chi_lambda: `normalComparison` is the inverse of the same section-locality map
  for the actual `normalChart`, with its projection and zero identities supplied by
  `normalChart_spec`. `sectionLocality_isIso` states the invertibility of these
  already-specified maps, rather than introducing an arbitrary comparison.
* Equality of actual maps: the final equality uses exactly those three definitions.
* No arbitrary normal frame or Tate orientation: there is no bundle trivialization,
  linear automorphism, orientation or trace parameter in the module.

Dependency declarations read and used (module paths are imports in the file):

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme Noetherianity is
  `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
* `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, projection and zero section.
* `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: `VectorBundleZeroSection.scheme`,
  `π`, `zero`, `augmentation`, `algebraIso`; these are the canonical bundle interface.
* `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra`:
  `piece`, `presentation`, `symmetricComparison`, `exists_conormalGradedAlgebra`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule` through its coefficient import, with whole derived
  categories of sheaves of `ModuleCat.{u+1} A`. Its current source was read using
  `scompile.py --source`, since the older checkout lacks that migrated module.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, D(j_!) followed by R(r_*).
* `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
* `Sheaf.AlgebraicGeometry.CompactifiableOverField`:
  existing `HasCompactification` and `Compactification` from its public imports.
* `Sheaf.Paper.NoetherianEtaleSectionSpecialization`:
  `Coeff`, `family`, `Normalized`, `specialization`, `existsUnique_normalized`.
* `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `existsUnique_etaleAmbientAdjointLocalityIso`; read its full counit equation.
* `Sheaf.Paper.FiniteRingSectionDeformation`: `geometry`, `etaleNormalMap`,
  `etaleNormalMap_spec`, `etaleSectionMap` and `locality`. This is an already-landed
  dependency added to stmt_deps, as permitted by the standing brief. Its dependencies
  were checked: it does not depend on this item, so this addition closes no cycle.
* `WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace`:
  `Scheme.Hom.deformationSpaceToAffineSpace`, constructed on charts from x_i/t.
  Read in the shared clone's `lean/WeilConjectures` side sources.

The remaining imports cover every recorded and stated proof dependency: the ordinary
unbounded compact-support comparisons, etale normalization, exceptional smooth base change,
exact inverse image, affine smoothness, Nagata, flat tensor exactness, Noetherian
permanence, separated/finite-type/etale base change and mate pasting. They are imports
without `public`, as required for proof-only dependencies.

Edge cases checked: empty S gives unique maps on the empty category of geometric points;
d=0 uses `Fin 0`, the empty regular sequence and the canonical affine-zero-dimensional
projection, without assuming positive rank. The Cartesian centre equation then forces
U to be exactly the section. n=1 is included; n=0 is excluded exactly as in the node.
Nonreduced bases remain allowed: the construction uses etale flatness and ideal powers,
not reducedness. U need not be all V and e need not be a global affine-space isomorphism.
The lifted coefficient ring and `ULift (Fin d)` preserve every scheme universe u.

Searches (the retained JSONL records are the actual tool results):

* LeanFinder, 2026-10-18: "Etale coordinates identify the normalized deformation to
  normal cone comparison for smooth section exceptional pullback"; eight standard-etale
  algebra hits, including `StandardEtalePair.homEquiv`, no comparison theorem.
* Loogle: `"normalCone", "IsEtale"`; zero hits.
* Mathlib grep through msearch: `sectionInvariant|deformation.*normal|normalCone`,
  AlgebraicGeometry; zero hits.
* LeanSearch: "Etale coordinates preserve normalized deformation to the normal cone
  comparison of extraordinary section pullbacks"; eight formally-etale algebra/base-change
  hits, no section-deformation comparison.
* rg over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id and
  the proposed comparison names: no declaration of this item. The upstream section
  invariant and actual Rees coordinate chart are reused.
* rg over the shared `lean/Sheaf` for `etale_section_deformation_comparison`,
  `EtaleSectionDeformationComparison`, `etaleNormalMap`, `originNormalChart` found
  the canonical normal-map helpers in `FiniteRingSectionDeformation`; those are used.
  It found no existing statement of the requested equation.
* `dag/lean_names_upstream.json` was checked for the item's id; no existing match.

No statement correction, disputed statement, new node or dependency repair is needed.
The node copy changes only lean and adds the already-landed finite-ring node to stmt_deps.
All eight declarations are listed in lean.declarations, including the helper facts about
invertibility and the fixed normal chart, which render the comparisons in this node.

Validation: scompile.py compiled the sandbox module and its actual library module
separately with no errors or warnings (6.0 s and 5.4 s in the successful run).

## Second reading by NH

This is a second self-check of the retained draft, not a claim that another worker was
started: the dispatcher's brief explicitly prohibits starting other agents and assigns
independent review to the maintainer. I reread the node and source against the final
module. The two potential semantic mismatches checked were normal-frame choice and
comparison normalization. `originNormalChart` uses the upstream x_i/t map; the normal
maps are induced by the actual Rees maps, hence its frame is the ideal-class frame.
`etaleSectionMap` uses the unique counit-characterized locality isomorphism, and `delta`
uses the recorded normalization at one. The equality has the required order.

The extra U/section structure binders describe structures that the two Cartesian
squares already force; they impose no new mathematical condition. Smooth finite type
uses locally finite type plus quasi-compactness. The cone presentation is the precise
one sanctioned by the section-specialization node and canonically identifies with the
relative Spec in the statement. No independent coefficients, frame, fibre map or
orientation is quantified over. All source hypotheses and the one equality are matched
above. The only draft repair was supplying derived compactness instances, as recorded.
The maintainer's independent reading remains the required review of this delivery.
