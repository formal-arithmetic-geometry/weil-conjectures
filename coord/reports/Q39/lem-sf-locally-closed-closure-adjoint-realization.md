## Worker report

Item: `lem-sf-locally-closed-closure-adjoint-realization`, group Q39, stage 2.
The single module `Sheaf.SixFunctors.LocallyClosedClosureAdjointRealization` states
`AlgebraicGeometry.locallyClosedClosureAdjointRealization`, with proof `sorry`.
The result is `Nonempty (SfLocallyClosedClosureRealization ...)`: all the properties
inside this explicitly defined conclusion bundle are supplied by the theorem.
None of its Noetherian, exactness, coefficient-finiteness or adjoint fields is an
additional hypothesis of the main theorem. Its subsidiary classes only collect
clauses of this item; they introduce no alternative sheaf, image, coefficient ring,
derived category, or extension-by-zero construction. Every helper is listed in
`lean.declarations` and carries the owning node's source and blueprint reference.

Hypotheses, in the order of the node:

- The global algebraic closure of the finite field is `D : WeilConjectures.FiniteFieldDatum`.
  Its recorded fields give the prime `D.p`, cardinality `D.q`, finite field `D.k₀`,
  and fixed algebraic closure `D.k`. No particular finite-field presentation is chosen.
- The coefficient prime is `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`.
- The finite coefficient extension is `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
  The level is `n : ℕ`, `_hn : 1 ≤ n`.
- The coefficient ring is precisely `Padic.coefficientExtensionRing l E n`, reusing
  its recorded integer ring, uniformizer and quotient, not an arbitrary finite ring.
  `finiteCoefficient` in the conclusion supplies its `Finite` instance, from the
  dependency theorem `Padic.finite_coefficientExtensionRing`.
- `S` and `T` carry `Over (Spec (.of D.k))`. Each structure morphism is separated,
  locally of finite type and quasi-compact, precisely separated finite type over k.
  `[s.IsOver (Spec (.of D.k))]` expresses that the stated immersion is a k-morphism.
- The factorization is `s : S ⟶ T`, `[IsImmersion s]`, `c : S ⟶ V`, `v : V ⟶ T`,
  `[IsClosedImmersion c]`, `[IsOpenImmersion v]`, and `hs : c ≫ v = s`.
  Composition is written in Lean's diagrammatic order.

Coefficient presentations and the two sites:

- The ordinary etale category is `Etale.DerivedCategoryModule (ULift A) X`, using
  the dependency's `ModuleCat.{u+1}` small-etale sheaf presentation.
- The ordinary pro-etale category is represented by
  `DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u+1} (ULift A)))`.
  This is the canonical fixed-scalar presentation of the recorded intrinsic
  constant-ring module category, via `Scheme.sfIntrinsicModuleEquivalence X A`.
  `sfClosureIntrinsicProEtaleIso` explicitly transports the normalized comparison
  into those intrinsic module categories by `sfIntrinsicTransportIso`. That
  transport uses the published realization and its inverse; no arbitrary scalar
  identification is assumed. Extension by zero in the intrinsic dependency is
  itself defined by this same equivalence and the same fixed-scalar open functor.
  The closed direct image is the corresponding canonical direct image, whose
  section-normalized realization comparison is published in
  `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`.
- `ULift.{u+1} A` is the standard coefficient size lift required by the recorded
  etale and fixed-scalar pro-etale interfaces. It has exactly A's ring operations;
  it is neither a completion nor a change of coefficient values. Site objects
  retain universe u+1 and site morphisms universe u. No equality between them is imposed.

Conclusions, clause by clause:

- The closure is literally `s.image = s.ker.subscheme`; its inclusion is
  `s.imageι` and its factor map is `s.toImage`. These are the recorded Mathlib
  scheme-theoretic image, not a reduced topological closure. `imageKernel` asserts
  equality with the actual section kernel on every affine open. The definition
  of `s.ker` already gives the largest quasi-coherent subideal for an arbitrary map.
- `SfLocallyClosedClosureGeometry` supplies `IsNoetherian` for T, S, V and `s.image`,
  hence their local Noetherianity and quasi-compactness. It supplies quasi-compactness
  of s, c, v and `s.toImage`, and the open-immersion property of `s.toImage`.
- Its `separatedV`, `finiteTypeV`, `qcOverV` assert separated finite type for
  `v ≫ aT`; the corresponding closure fields do so for `s.imageι ≫ aT`.
  `separatedMorph` and `finiteTypeMorph`, with `qcS`, record the separated finite-type
  morphism s used by compactification.
- `compactComplementsV` and `compactComplementsClosure` quantify over every closed
  immersion into the respective schemes and assert `IsCompact (Set.range i)ᶜ`.
  There is no Hausdorff condition and no quasi-compact-complement assumption.
- `sfClosureCompactification s` is an actual `Compactification s` with middle scheme
  `s.image`, proper arrow `s.imageι`, open arrow `s.toImage` and factorization
  `Scheme.Hom.toImage_imageι`. Its data is constructed fully from those canonical maps.
- `dimensionBound` is `∃ D : ℕ, topologicalKrullDim s.image ≤ (D : WithBot ℕ∞)`.
  A natural D incorporates the stated nonnegativity.
- `SfLocallyClosedClosureSites.etale` uses exactly
  `Etale.lowerStar c ⋙ Etale.openImmersionLowerShriek v` for F_e and the dependency's
  `etaleLocallyClosedExtension s` for E_e. `proetale` uses the same two factor orders
  with the published fixed-scalar `ProEtale` operations.
- Each `SfClosureExtensionComparison` supplies finite-limit and finite-colimit
  preservation for both F and E, which is exactness in these abelian categories.
  The separately recorded exactness of closed factors supports the canonical
  identification of their right derived functors with their termwise functors.
- Its `lowerF` and `lowerE` quantify over every unbounded derived object and every
  integer a, asserting that `IsGE a` is preserved. There is no boundedness
  restriction on these functors or their comparison isomorphisms.
- `sheafIso : F ≅ E` and `normalization : sheafIso ▷ s* ≪≫ β = α` express the
  specified identity after restriction to S. On the etale site α and β are exactly
  the recorded factorization/closure restriction helpers. On the pro-etale site
  the two helpers are fully written composites of the inverse open unit, closed
  counit and canonical pullback-composition isomorphism. This includes the
  normalization, rather than only existence of an arbitrary isomorphism.
- `SfClosureExtensionComparison.derivedIso` is the actual
  `Functor.mapDerivedCategoryNatIso sheafIso`, hence q_e and q_p are the
  localizations of the degreewise sheaf isomorphisms on unbounded derived categories.
- `sfClosureEtaleJ` and `sfClosureProEtaleJ` are the composites of derived open
  restriction and the right adjoint to the respective closed derived direct image.
  The closed adjoints are determined by their adjunction universal properties;
  in the intrinsic pro-etale presentation the recorded closed-support theorem
  identifies this adjoint with the total right derived support-kernel functor.
  Their existence is supplied by `closedAdjoint` and `closedProEtaleAdjoint` in
  the conclusion, without a new boundedness or constructibility assumption.
- `sfClosureEtalePastedAdjunction` and `sfClosureProEtalePastedAdjunction` use
  `Adjunction.comp` of those closed adjunctions and the actual open adjunctions.
  Exactness and the canonical derived-composition isomorphism identify their left
  sides with the termwise functors F. These are pasted adjunctions, not arbitrary
  adjunctions on the composite functors.
- `sfClosureEtaleCompactSupportIso` canonically identifies
  `Etale.rightDerivedLowerShriekOfCompactification (sfClosureCompactification s)`
  with E_e, using `rightDerivedFunctorIsoMapDerivedCategory` for the closed factor.
  `ambientAdjoint` asserts existence of its ordinary ambient right adjoint.
- `sfClosureEtaleAdjointIso` is defined by `conjugateIsoEquiv` applied to
  `(Functor.mapDerivedCategoryNatIso B.etale.sheafIso).symm`. It has exactly
  direction `J_e ≅ s^×`. `conjugation` in the main result asserts both explicit
  equations of `SfClosureEtaleConjugationCompatibility`: the F unit followed by
  J(q) and r equals the E unit, and q followed by E(r) and the E counit equals
  the F counit, on all derived objects.
- `boundedRestriction` quantifies over every M in the recorded
  `Etale.DerivedCategory.isBoundedConstructible A T` and gives that predicate for
  `v* M` on V. This is the finite-value constructible-sheaf predicate from the
  recorded dependency, not the different finitely-generated-stalk predicate.
- `boundedAdjoint` gives `∃ a : ℤ, (J_e.obj M).IsGE a`, precisely H in D⁺.
- `comparisonDomain` preserves a lower bound for every L under `c_*` and `u_!`.
  Together with `lowerF`, `lowerE`, and the qcqs closed maps, this places H and
  every bounded-below L, and their indicated extensions, in the domain of the
  already recorded bounded-below closed direct-image comparison. No additional
  comparison-isomorphism theorem is asserted here.

Dependency declarations and imports:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber` / `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` / `Padic.finite_coefficientExtensionRing`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` / `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion` / `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `AlgebraicGeometry.IsProper`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories` / `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` / `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`.
- `lem-exc-closed-ambient`: `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint` / `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
- `lem-exc-proetale-closed-support`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient` / `AlgebraicGeometry.Scheme.sfIntrinsicClosedAmbientAdjunction`.
- `def-weil-pbc-composite-adjunction`: `Mathlib/CategoryTheory/Adjunction/Basic.lean` / `CategoryTheory.Adjunction.comp`.
- `def-weil-pbc-extension-by-zero`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` / `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `def-weil-extension-by-zero`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` / `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`.
- `def-nagata-scheme-theoretic-image`: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` / `AlgebraicGeometry.Scheme.Hom.image`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian` / `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter` / `CompactSpace`.
- `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.RefinementCategory` / `AlgebraicGeometry.Compactification.Refinement`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension` / `topologicalKrullDim`.
- `lem-sfb-etale-locally-closed-extension-comparison`: `Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison` / `AlgebraicGeometry.etale_locallyClosed_extension_comparison`.
- `lem-sfb-locally-closed-extension-coherence`: `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence` / `AlgebraicGeometry.Scheme.locallyClosedExtensionCoherence`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` / `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `thm-amb-etale-exceptional-adjoint`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint` / `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `def-weil-pbc-adjunction-conjugate`: `Mathlib/CategoryTheory/Adjunction/Mates.lean` / `CategoryTheory.conjugateEquiv`.
- `def-weil-pbc-constructible-complexes`: `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes` / `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.


The generic identity/composite and conjugation dependencies use Mathlib
`Adjunction.id`, `Adjunction.comp`, and `conjugateIsoEquiv` directly. The
compactification dependency now has the tracked upstream
`WeilConjectures.Compactification.RefinementCategory` interface; its
`Compactification` data is used directly, with no duplicate compactification notion.
Public imports supply statement vocabulary. The additional private imports carry the
recorded proof plan: finite-type dimension, topological dimension, etale supported
kernel exactness, intrinsic open exactness, constant-ring comparison, etale module
inverse-image exactness, exact-adjunction lower bounds, and bounded-below direct-image
comparison. Mathlib leaves are already available through the corresponding statement
imports. No dependency module or node correction was needed.

Edge cases read before writing and checked against the final statement:

- S or T empty: no `Nonempty` hypothesis on a scheme or point type; the closure
  may be empty and dimension -∞ satisfies the bound with D=0.
- Identity immersion and purely open or purely closed factorization: the canonical
  image, actual open/closed adjunctions and inverse open unit are still defined.
  No strictness, proper nonempty complement or positive dimension is assumed.
- Nilpotent structures: `s.ker.subscheme` and the affine kernel equality retain them.
- Arbitrary unbounded input: comparisons and exact termwise functors are on full
  unbounded categories; only the M/H and final comparison-domain clauses use bounds.
- Every integer lower bound is included, including negative bounds; n=1 is included.
  n=0 is excluded exactly as in the node. The coefficients are never assumed to be a field.
- Finite commutative rings with zero objects and the zero sheaf cause no restriction
  in the helper interfaces. The actual coefficient ring remains the specified quotient.

Searches (2026-10-21):

- `msearch.py ... leanfinder "A locally closed immersion has exact extension by zero
  through its scheme theoretic closure and a bounded below right adjoint"`: 8 hits.
  These were `Scheme.Modules.instIsLeftAdjointRestrictFunctor`, `restrictAdjunction`,
  `Scheme.kerAdjunction`, `Hom.liftCoborder`, `liftCoborder_app`,
  `Scheme.Modules.instIsIsoFunctorCounitRestrictAdjunction`, and the two immersion
  locally-closed-range lemmas. They concern structure-sheaf restriction, the image
  construction or geometry; none states this two-site composite result.
- `msearch.py ... loogle '"Adjunction", "conjugateIsoEquiv"'`: 0 hits.
  Direct source inspection of Mathlib `Adjunction/Mates.lean` supplied the exact
  generic conjugation operation and its unit/counit identities, which are reused.
- `msearch.py ... grep 'locallyClosed|scheme.theoretic.*image' AlgebraicGeometry`:
  19 hits, including the actual `Hom.image`, `imageι`, `toImage` declarations and
  generic immersion lemmas. Their definitions and signatures were read and reused.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for this item's id, closure-adjoint
  names and the proposed declaration names: no existing statement of this item and
  no name collision. A broader search found the downstream
  `FiniteDualityLocallyClosedComparison` source; its proof describes the same closure
  and adjoint normalization, but its statement is the distinct site-comparison result.
  `dag/lean_names_upstream.json` was also searched for the proposed closure helper names.

The source blueprint's second paragraph was read along with all dependency node
statements and their recorded declarations, especially the ordinary coefficient,
constructibility and closed ambient adjoint signatures. The full theorem docstring
carries all eleven DAG proof steps. The single named theorem is the only `sorry`;
all helper definition data is explicit or a canonical published operation.
No STATEMENT-DISPUTED flag or statement correction is required.

Validation: the prescribed `scompile.py` has compiled both sandbox and final module
names cleanly against the server's published live library. The final delivery dry run
and push are recorded by the prescribed wrapper. No local/global library build,
live-file edit, direct git mutation, or sub-agent was used. Independent mathematical
review is the maintainer's review of this delivery, as specified in the worker brief.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
