## Worker report

Recorded an exact existing statement; no new module, helper, dependency repair or statement
correction is needed. The declaration is
`AlgebraicGeometry.Scheme.proEtaleCoefficientInverseImageMap_comp` in
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition` (the published module owned by
`lem-pur-proetale-constant-ring-composition`). Its complete signature and docstring were read.
The existing theorem remains a stage-2 statement with `sorry`; this delivery proves nothing.
Only the item's `lean` field changes. Its signature is copied verbatim, retaining line breaks.

Clause-by-clause correspondence:

- Schemes Z, Y, X are the binders `{Z W V : Scheme.{u}}`, respectively. The letters W and V
  rename Y and X. Morphisms h and k are `(h : Z ⟶ W) (k : W ⟶ V)`. Thus `h ≫ k`
  is the node's k composed with h, with no property imposed on either morphism.
- The finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`. No nonzero-ring,
  characteristic or invertibility assumption is present. The larger-universe value category
  uses `ULift.{u + 1, u} A`, with its canonical ring operations, as in the recorded inverse-image
  dependency. The original small site has object universe u+1 and morphism universe u;
  these universes are not forced equal.
- For each scheme T, `proEtaleConstantRing T A` is literally
  `(constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).obj
  (CommRingCat.of (ULift.{u + 1, u} A))`. It is sheafification of the constant presheaf,
  not the un-sheafified constant presheaf or an arbitrary ring sheaf.
- Each c_f is `proEtaleCoefficientInverseImageMap f A`. Unfolding gives
  `proEtaleConstantInverseImageMap`, namely inverse image of the unique sheafified
  constant-section map followed by the actual adjunction counit. This is exactly the
  structure map identified in the commutative clause of
  `prop-weil-pbc-proetale-constant-ring-map`. That proposition's
  `finiteCoefficientInverseImageMap_constant` gives the constant-preserving comparison
  with the finite-function coefficient presentation. No arbitrary coefficient map is a binder.
- Alpha is `(ProEtale.supportSiteProEtaleComparisonComp CommRingCat.{u + 1} h k).hom`.
  Read its full construction in `SupportComparisonPullbackCoherence.lean`: it is
  `conjugateIsoEquiv` applied to the canonical direct-image comparison induced by
  `MorphismProperty.Over.pullbackComp`, using the actual composite adjunction.
  Its direction is inverse image for h ≫ k to inverse image for k followed by h.
  Both inverse-image functors and both adjunctions unfold to precisely those in
  `ProEtaleInverseImage.lean`; this is the node's adjunction-compatible comparison.
- The conclusion starts `proEtaleCoefficientInverseImageMap (h ≫ k) A =` and has
  `alpha.hom.app (proEtaleConstantRing V A) ≫ inverseImage_h.map c_k ≫ c_h` on the
  right. Lean composition is written left to right, so these are exactly the three
  factors of the node's displayed equation, with the same source and target.
- All terms are morphisms of `CommRingCat`-valued sheaves on the small pro-etale site.
  This is an equality of ring-sheaf maps: homomorphisms between commutative rings have
  no additional structure beyond their underlying ring homomorphisms. Keeping commutativity
  bundled neither adds a hypothesis nor changes the equality.
- The empty-source clause is included by the unrestricted Z binder. There is no
  `Nonempty Z`, point or nonzero section hypothesis. The cited coefficient-map proposition
  explicitly supplies its empty-source zero-ring-sheaf interpretation; a separate conjunct
  would unnecessarily repeat a case already quantified by the equality.

Dependency declarations read and used by the existing module:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`,
  documenting the intrinsic coefficient/site presentation; the statement uses its
  `Scheme.ProEt` and `Scheme.ProEt.topology` small site.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `ProEtale.finiteCoefficientInverseImageMap_isIso`,
  `ProEtale.finiteCoefficientConstantComparison_isIso`,
  `ProEtale.finiteCoefficientInverseImageMap_constant`, and
  `ProEtale.finiteCoefficientInverseImageMap_empty`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` reexports the recorded
  `def-weil-proetale-inverse-image` constructions in `ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage`, `Scheme.proEtaleSheafDirectImage`,
  `Scheme.proEtaleSheafAdjunction`, `Scheme.proEtaleConstantRing`,
  `Scheme.proEtaleCoefficientDirectImageMap`, `Scheme.proEtaleCoefficientInverseImageMap`.
  Its recorded module-adjunction declaration was also opened; no replacement is required.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence` supplies the comparison
  described above. It is already imported by the reused theorem.
- The proof interfaces were read in Mathlib: `Limits.pullback` and its projections/lift,
  `presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`, `Adjunction.comp` and
  `unit_conjugateEquiv_symm`. The existing theorem's docstring gives the same adjunct
  computation as the item's proof, compressed into four steps.

Sources checked: local `literature/stacks-project/sites.tex`,
`lemma-composition-morphisms-sites` (03CB) and `example-constant-sheaf` (0H7J).
These give the canonical adjunction comparison and constant-sheaf normalization used here.

Edge cases checked before binding: Z empty (zero ring sheaves, unique map), zero coefficient
ring (allowed by CommRing), identity morphisms (canonical unit-normalized comparison),
and disconnected schemes (sheafification allows locally varying constant sections).
No case requires injectivity of the constants into sections. No statement fault or dispute.

Searches, all made for this item through msearch.py where applicable:

- LeanFinder: "Canonical constant ring sheaf inverse image coefficient maps respect
  composition of scheme morphisms" returned eight hits about structure sheaves, including
  `Scheme.comp_appTop_assoc` and `StructureSheaf.comap_comp`; none is this statement.
- LeanFinder: "canonical constant ring coefficient inverse image composition" returned
  eight polynomial/power-series hits; no match.
- LeanFinder: "constant ring sheaf inverse image composition" returned eight structure-sheaf
  or tilde-sheaf hits, including `StructureSheaf.comap_const`; no exact Mathlib match.
- Loogle: `"constant", "pullback"` returned no hits.
- Mathlib grep: `constant.*[Cc]omp|[Cc]omp.*constant` in `CategoryTheory/Sites` returned
  thirteen hits about constant-sheaf functors, global sections and cohomology; no exact match.
- Source rg with the same composition pattern in `WeilConjectures/SixFunctors` and
  `WeilConjectures/CategoryTheory` found constant-sheaf comparisons, not this equation.
  A full source grep for the item's blueprint id found no occurrence.
- Project rg for constant/composition patterns in `lean/Sheaf/AlgebraicGeometry` found
  `ProEtaleConstantRingComposition.lean`. Reading it gave the exact match recorded here.
  `StrictConstantTowerOperations.constantRingIso_comp` is an alternative isomorphism-valued
  presentation; the former theorem already expresses the requested map equality directly.
  The full declaration name is not in `dag/lean_names_upstream.json`.

Validation: `deliver2.py Q05 lem-trf-constant-coefficient-composition --no-push`
completed successfully: existing-declaration import and `#check` through scompile.py compiled
cleanly, and server preflight returned OK (dry-run commit 80ee0ea233). No Lean files are
delivered because the declaration already exists. The maintainer supplies the independent review.

## Second reading by Q05

Independent maintainer second reading, 2026-10-17, of immutable delivery
`e6e586a90e7d692da85ecc140fe973772c0addcc`. The reviewer did not write this delivery
or supply its earlier reading. The snapshot item and all five snapshot statement
dependencies were read, followed by the existing declaration and its actual definitions
in the read-only Q05 clone. This section replaces the delivered placeholder.

Clause-by-clause result: the binding is exact.

- Objects and morphisms: `{Z W V : Scheme.{u}}`, `(h : Z ⟶ W)` and `(k : W ⟶ V)`
  give the node's Z, Y, X, h and k without conditions on the schemes or arrows.
  `h ≫ k` means k composed with h.
- Coefficients: `(A : Type u) [CommRing A] [Finite A]` is a finite commutative
  ring, allowing the zero ring and every characteristic. The finite coefficient
  is represented by the canonical `ULift.{u+1,u} A`. The site retains object
  universe u+1 and Hom universe u. No equality of those universes is imposed;
  finiteness makes using a small representative of A harmless.
- Site and sheaves: Mathlib's `Scheme.ProEt` is the weakly-etale over-category,
  and `ProEt.topology` is its pro-etale/fpqc covering topology. The recorded
  `proEtaleDerivedCategory` uses this same site; no derived object occurs in
  the item itself. `proEtaleConstantRing T A` is exactly `constantSheaf` applied
  to `CommRingCat.of (ULift A)`, so it is sheafification of the constant presheaf.
- Canonical c: `proEtaleCoefficientInverseImageMap` unfolds to
  `proEtaleConstantInverseImageMap`, the inverse image of the unique
  sheafified constant-section map followed by the actual adjunction counit.
  `ProEtaleConstantRingMap.finiteCoefficientInverseImageMap_constant` (in the
  namespace `AlgebraicGeometry.ProEtale`) identifies the finite-function
  presentation with this construction after forgetting commutativity.
  Its comparison-isomorphism and empty-source theorems were also read.
- Canonical alpha: `supportSiteProEtaleComparisonComp` is constructed from
  `MorphismProperty.Over.pullbackComp`, `sheafPushforwardContinuousComp'`,
  `conjugateIsoEquiv` and `Adjunction.comp`. Its inverse-image and adjunction
  abbreviations unfold to the same Kan-extension/sheafification constructions
  used in `ProEtaleInverseImage`. The symmetries give precisely
  `(kh)^-1 → h^-1 k^-1`, with the unit normalization, rather than an arbitrary
  natural isomorphism. The direct-image comparison restricts along the
  projection-preserving fibre-product associativity isomorphism.
- Conclusion: the equality is `c_(h ≫ k) = alpha.app A_V ≫ (h^-1).map c_k ≫ c_h`.
  All factors have the node's source and target and are maps of commutative
  ring sheaves. This is the required equality of ring-sheaf maps, with no
  extra conclusion or omitted factor.
- Empty-source clause: Z is unrestricted. The empty cover makes section rings
  on the empty site singleton rings, and both sides have the same source and
  target. The dependency explicitly records this case. Distinct constants
  are not assumed to remain distinct sections. Identity h or k, disconnected
  schemes, and the zero coefficient ring are likewise included.

Source and proof reading: `literature/stacks-project/sites.tex` lines 2099ff
(Tag 0H7J, `example-constant-sheaf`) and 2764ff (Tag 03CB,
`lemma-composition-morphisms-sites`) define the constant sheaf and identify
composition through uniqueness of left adjoints. `proetale.tex` lines 4675ff
(Tag 09A5, `section-morphism`) uses arbitrary morphisms of schemes; the qcqs
hypothesis in the subsequent comparison lemma is not an ambient hypothesis.
`categories.tex` lines 3542ff and 3576ff give the conjugation and composite
adjunction formulas (Tags 0B65 and 0DV0).

The node's six proof steps and the existing theorem's four-step docstring agree:
(1) fibre-product uniqueness supplies the natural direct-image comparison;
(2) both paths preserve each constant and uniqueness of sheafification identifies
the maps; (3) the conjugation unit equation fixes alpha; (4) unit naturality
computes the composite adjunct as R_k(rho_h) rho_k; (5) naturality and cancellation
of the comparison, then injectivity of the adjunction bijection, give the equality;
(6) the empty-site case is included. The statements of the fibre-product,
sheafification, composite-adjunction and conjugate-unit proof dependencies were
also checked. There is no missing mathematical prerequisite for the existing
Lean statement: its generic adjunction interfaces are already in Mathlib.

One-definition-per-notion: reuse of the exact published theorem owned by
`lem-pur-proetale-constant-ring-composition` is correct. The existing module
imports `SfIntrinsicRealizationTransport`, `SupportComparisonPullbackCoherence`
and `ProEtaleConstantRingMap`. The recorded inverse-image module reexports
`ProEtaleInverseImage`; its module-adjunction declaration was checked as well.
The side framework's `WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/Defs.lean`
was read in the Q05 clone. No etale, condensed or module-valued substitute is
used for the ring-sheaf statement.

Independent searches: LeanSearch query "Canonical constant ring sheaf coefficient
maps commute with inverse image composition along scheme morphisms" returned
five hits, including `CategoryTheory.constantCommuteCompose`, structure-sheaf
composition and an isomorphism instance; none is this theorem. Loogle query
`"constant", "pullback"` returned no hits. Direct rg for constant/composition
patterns in Mathlib's `CategoryTheory/Sites/ConstantSheaf.lean`, upstream
`WeilConjectures/SixFunctors/ProEtale`, and the project found the recorded exact
theorem and the alternative `StrictConstantTowerOperations.constantRingIso_comp`.
The latter uses the tower-coefficient interface, so the direct map-equality
binding is preferable. `constantCommuteCompose` changes the value category on
a fixed site and is not a replacement. These supplement the worker's recorded
LeanFinder/Loogle/grep searches with an explicit LeanSearch record.

Compiler and static evidence: no Lean file is delivered (`existing: true`).
The recorded multiline `lean.statement` was compared programmatically with the
existing file from `theorem` to `:= by`; equality is exact. The existing module
has `autoImplicit false`, binds u explicitly, has no line over 100 characters,
contains source/blueprint module and declaration docstrings for its owning node,
and leaves the sole theorem proof as `by sorry`. No new definition or proof is
introduced. Reusing its owning-node blueprint docstrings does not require a
second declaration or a copy of that module.

Reproduction command:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q05 lem-trf-constant-coefficient-composition /home/ubuntu/weil-newtargets-Q05/lean/Sheaf/AlgebraicGeometry/ProEtaleConstantRingComposition.lean`
returned exit code 0 with no diagnostics: sandbox probe 2.1 seconds; library
module 2.3 seconds. The installed 2026-10-17 wrapper uses a private server side
overlay (reported `.lbuild` under `/dev/shm/nt-tmp/nt-local-compile-pf9_uw9u`),
not a local compiler on this machine. Only the prescribed wrapper was invoked;
no direct ssh command, global build, live Lean write, delivery or Git mutation
was performed. The worker separately records a clean import/#check and server
preflight at dry-run commit `80ee0ea233`; that dry run was not rerun here.

Findings and correction: H1/H11 report defect only. The delivered second-reading
heading contained a disclaimer rather than an actual reading. Replace that
section with this independent reading, preserving the Worker report in full.
The LeanSearch evidence above also completes the report's three search kinds
(H4). No mathematical, universe, canonical-map, dependency-interface, hollow
definition or statement-correction fault was found. No node or Lean correction
is required. The complete replacement report is supplied under fixes.
