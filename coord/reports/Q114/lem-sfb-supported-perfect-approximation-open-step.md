## Worker report

The module `Sheaf.AlgebraicGeometry.SupportedPerfectApproximationOpenStep` states
`AlgebraicGeometry.Scheme.hasSupportedPerfectApproximation_of_open_cover`, the open-union
step of Stacks Tag 08ER (`literature/stacks-project/perfect.tex`, lemma-induction-step).
Its only theorem has proof `sorry`. Its docstring carries all nine accepted DAG proof
steps and their named dependencies, including the stage-1 corrections to the printed
proof (the theorem statement itself is unchanged).

Hypothesis and conclusion correspondence:

- The scheme Y is `(Y : Scheme.{u})`; the recorded scheme definition is
  `AlgebraicGeometry.Scheme` in `Mathlib.AlgebraicGeometry.Scheme`. Its local-affine
  field and `Scheme.Hom` were read in the pinned source.
- The two opens with their open subscheme structures are `(U V : Y.Opens)` and
  `U.toScheme`, respectively. These use the canonical open subscheme, not an
  arbitrary isomorphic scheme or a new ringed-space model.
- The open covering Y = U ∪ V is `hcover : U ⊔ V = ⊤`. Join in the open lattice
  is set union, and top is the whole underlying space.
- Quasi-compactness of U is `hU : IsCompact (U : Set Y)`; Mathlib compactness does
  not impose Hausdorffness.
- Affineness of V is `hV : IsAffineOpen V`; the Mathlib definition says exactly
  that the associated open subscheme is affine.
- Quasi-compactness of the overlap is
  `hUV : IsCompact ((U ⊓ V : Y.Opens) : Set Y)`; infimum is intersection.
- The hypothesis A(U) is
  `hA : HasSupportedPerfectApproximation.{u, w} U.toScheme`.
- The conclusion A(Y) is `HasSupportedPerfectApproximation.{u, w} Y`.
  Both use the recorded dependency definition verbatim, with the same universe
  parameters. It quantifies over every closed support with retrocompact complement,
  chooses its integer r before m and F, requires quasi-coherent cohomology,
  (m-r)-pseudo-coherence and vanishing of all relevant cohomology stalks outside T,
  and concludes a perfect supported source and map inducing isomorphisms above m
  and an epimorphism of module sheaves at m. No clause is changed or restated.
- The explicit `HasDerivedCategory.{w}` binders provide the chosen localizations
  required by that existing definition: on Y and its opens and over-sites, and on
  opens and over-sites of U.toScheme. The localization for U itself is supplied
  by the family on Y.Opens. These are size/model infrastructure, not geometric
  finiteness, vanishing, or separation hypotheses. Universes u and w are explicit
  and independent; `autoImplicit` is false. `HasDerivedCategory.standard` supplies
  the usual model at the standard universe; this theorem permits arbitrary shared
  models at w instead of fixing a smaller universe.

Statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its open
  subscheme conventions.
- `Sheaf.AlgebraicGeometry.SupportedPerfectApproximation`:
  `AlgebraicGeometry.Scheme.HasSupportedPerfectApproximation`; read its entire
  signature, docstring, and definition, and its underlying `IsMPseudoCoherent`
  and `IsPerfect` definitions. The dependency interface is usable without repair.

Proof dependencies with recorded modules are imported privately, while the two
statement-dependency modules are public imports. The Mathlib proof interfaces
for finite affine covers, stalk detection, triangulated categories and homology
sequences are imported as well. Recorded proof modules/declarations:

- `def-sfb-supported-perfect-approximation-property`: `Sheaf.AlgebraicGeometry.SupportedPerfectApproximation`, `AlgebraicGeometry.Scheme.HasSupportedPerfectApproximation`.
- `def-sfb-m-pseudo-coherent-complex`: `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`, `AlgebraicGeometry.Scheme.IsMPseudoCoherent`.
- `def-pc-perfect-complex`: `WeilConjectures.AlgebraicGeometry.PerfectComplex`, `AlgebraicGeometry.Scheme.IsPerfect`.
- `def-pc-derived-open-restriction-maps`: `WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps`, `AlgebraicGeometry.schemeDerivedOpenDirectImageRestriction`.
- `lem-sfb-affine-supported-perfect-approximation`: `Sheaf.AlgebraicGeometry.AffineSupportedPerfectApproximation`, `AlgebraicGeometry.Scheme.exists_supported_perfect_approximation_of_isAffine`.
- `lem-pc-supported-open-pushforward`: `WeilConjectures.AlgebraicGeometry.SupportedOpenPushforward`, `AlgebraicGeometry.Scheme.supported_open_pushforward`.
- `lem-sc-derived-open-shriek-derived-adjunction`: `WeilConjectures.Algebra.Homology.DerivedOpenShriekAdjunction`, `AlgebraicGeometry.derived_open_shriek_adjunction`.
- `lem-sc-derived-open-restriction-adjunction-exact`: `WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact`, `AlgebraicGeometry.open_restriction_adjunction_exact`.
- `lem-sc-module-extension-by-zero-stalk-maps`: `WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkMaps`, `AlgebraicGeometry.module_extensionByZero_stalk_maps`.
- `lem-weil-pbc-module-stalk-exact`: `WeilConjectures.Algebra.Homology.ModuleStalkExact`, `AlgebraicGeometry.RingedSpace.module_stalk_exact`.
- `lem-sc-affine-perfect-support-extension`: `WeilConjectures.AlgebraicGeometry.AffinePerfectSupportExtension`, `AlgebraicGeometry.Scheme.exists_perfect_supported_extension`.
- `lem-sc-affine-perfect-map-lift`: `WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift`, `AlgebraicGeometry.Scheme.exists_perfect_map_lift_of_isAffine`.
- `lem-sc-derived-open-gluing`: `WeilConjectures.AlgebraicGeometry.DerivedOpenGluing`, `AlgebraicGeometry.derived_open_gluing`.
- `lem-pc-perfect-thick-closure`: `WeilConjectures.AlgebraicGeometry.PerfectThickClosure`, `AlgebraicGeometry.Scheme.perfect_thick_closure`.
- `lem-pc-perfect-pseudo-coherent-locally-finite-tor`: `WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor`, `AlgebraicGeometry.Scheme.perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension`.
- `lem-sc-pseudo-coherent-qcoh`: `WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh`, `AlgebraicGeometry.Scheme.schemeDerivedQCohProperty_of_isPseudoCoherent`.
- `lem-pc-supported-qcoh-triangulated`: `WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated`, `AlgebraicGeometry.supported_qcoh_isTriangulated`.

`lem-sfb-ringed-site-m-pseudocoherent-triangle` has no recorded Lean module yet;
its proof import is omitted until stated. It is used only in the postponed proof,
not in this theorem's type. No statement dependency is missing.

Edge cases checked before writing: Y empty (then both opens empty); U empty (the
affine base case on Y); V empty (U is the whole scheme); empty overlap (disjoint
union); U=Y or V=Y; empty closed support and full closed support inside A; all
integer degrees including zero and negative degrees; zero derived objects.
None is excluded by an inhabitedness, properness or nonempty-index hypothesis.
The theorem requires neither Y nor U to be quasi-separated; affineness is required
only of V. No node correction, new definition or dependency repair was necessary.

Searches for existing declarations:

- `msearch.py ... leanfinder`: “If uniform supported perfect approximation holds on a
  quasi compact open U it holds on the union with an affine open V with quasi compact
  intersection”. Eight hits, including `AlgebraicGeometry.compact_open_induction_on`
  and `Scheme.quasiSeparatedSpace_of_isOpenCover`; they do not state this result.
- `msearch.py ... loogle`: `HasSupportedPerfectApproximation, IsAffineOpen`.
  No hits; Loogle does not index the project-specific property.
- `msearch.py ... grep`: `SupportedPerfectApproximation|supported.*approximation|approximation.*open`
  in Mathlib/AlgebraicGeometry: no hits.
- `rg -n` with the same expression in both live `lean/WeilConjectures` and
  `lean/Sheaf`: found the intended property, affine approximation, and algebraic-space
  analogues; no scheme open-union theorem. Other hits concern Noetherian approximation
  or an open-supported homology lemma, which state different results.
- `grep -rn lem-sfb-supported-perfect-approximation-open-step lean/WeilConjectures`:
  no hits. `rg` of `dag/lean_names_upstream.json` for the property and proposed
  declaration name: no hits. The chosen theorem name has no existing declaration.

Validation: every delivered Lean file is compiled using the prescribed `scompile.py`;
the delivery is also checked by `deliver2.py --no-push` before pushing.
Result: server compilation passed for the sandbox and actual library module; the
actual module check took 3.1 seconds. `deliver2.py --no-push` returned
`OK (dry run): commit 5e4d5045d44 passes the preflight and compiles; nothing pushed`.

## Second reading by Q114

The worker re-read the node, definition body, source Tag 08ER and written signature
against the correspondence above. The signature retains all five geometric inputs
(scheme, covering, compact first open, affine second open, compact overlap), the
property assumption and exactly its conclusion. The additional binders are precisely
the chosen-derived-category infrastructure of that property's two instantiations.
No mismatch was found and the node statement was not changed. This is a worker
self-check, not an independent agent review: the dispatch brief prohibits starting
other agents and assigns independent review to the maintainer after delivery.
