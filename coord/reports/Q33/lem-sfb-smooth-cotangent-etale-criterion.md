## Worker report

The delivery states the node unchanged in
`Sheaf.AlgebraicGeometry.SmoothCotangentEtaleCriterion`, with main declaration
`AlgebraicGeometry.Scheme.Hom.smooth_cotangent_etale_criterion`. The only theorem
proof is `sorry`. The helper `smoothCotangentDeterminantMap` contains actual data:
the existing exterior sheaf comparison, the existing `siteExteriorHom` applied to
the existing canonical differential, and the inverse exterior comparison.
The comparison definition node `def-sfb-exterior-sheaf-comparison-iso` now
records the two exact existing definitions in `ExteriorSheafComparison` with
`existing: true`. The item publicly imports that existing module. No comparison
definition or replacement dependency module is delivered.

Hypothesis and clause correspondence:

- Schemes S, X, Y: `{X Y S : Scheme.{u}}`; the universe is explicit and arbitrary.
- Smooth structure maps X to S and Y to S: `(f : X ⟶ S) (g : Y ⟶ S)` and
  `[Smooth f] [Smooth g]`.
- h is an S-morphism: `(h : X ⟶ Y) (w : h ≫ g = f)`.
- The specified differential dh is `g.relativeDifferentialsPullbackMap h ≫
  ((h ≫ g).relativeDifferentialsCongr w).hom`. The first factor is the landed
  uniquely generator-characterized map sending `1 ⊗ db` to `d(h♯b)`; the second
  simply identifies the composite structure map with f. There is no arbitrary
  morphism or additional assumption on dh.
- For every x, etaleness on an open neighbourhood is exactly
  `∀ x : X, (∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ h)) ↔ ...`.
  The right side applies `RingedSpace.moduleStalkFunctor X.toRingedSpace x`
  to that very dh and asserts `IsIso`.
- The global clause is `Etale h ↔ IsIso dh`.
- The equal-rank determinant clause quantifies over every `d : ℕ`, assumes
  `f.relativeDifferentials.IsFiniteLocallyFreeOfRank d` and
  `g.relativeDifferentials.IsFiniteLocallyFreeOfRank d`, and asserts
  `Etale h ↔ IsIso (smoothCotangentDeterminantMap f g h w d)`.
  Tensor pullback preserves the rank of the latter bundle, so this is the
  stated square determinant criterion. No constant-rank condition is imposed
  on the pointwise or global criteria.
- Degree zero is explicit: conjugating the degree-zero determinant map by the
  two canonical `exteriorSheaf_zero_iso` identifications yields
  `𝟙 (SheafOfModules.unit X.ringCatSheaf)`. These isomorphisms are chosen from
  unique existence statements normalized by the empty wedge mapping to 1.
  Thus this is the identity of O_X, not merely an unspecified isomorphism.

Recorded statement dependencies used (four additional landed definition nodes
and the new comparison definition node; the mathematical statement is unchanged):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and its `Hom`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- `def-sc-relative-differential-sheaf`:
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, with the canonical
  `relativeDifferentialsCongr` identification.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, publicly exposing
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from the upstream module;
  its section-normalized adjunction fixes the generator interpretation.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-sc-sheaf-exterior-power`:
  `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`,
  `AlgebraicGeometry.Scheme.Modules.exteriorSheaf` and
  `exteriorSheaf_zero_iso`.
- Added `def-a1-relative-differentials-pullback-map`:
  `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`,
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackMap`. Its full
  generator construction and unique-existence signature were read.
- Added `def-pc-module-stalk-functor`:
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`,
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`.
- Added `def-amb-finite-locally-free-module`:
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- Added `def-sfb-site-exterior-sheaf`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteExteriorPower`,
  `SheafOfModules.siteExteriorHom`. This is sheafification of the actual
  sectionwise `exteriorPower.map`; on the Zariski site its objects are the
  upstream `Modules.exteriorPower` construction definitionally.
- Added `def-sfb-exterior-sheaf-comparison-iso`:
  `Sheaf.AlgebraicGeometry.ExteriorSheafComparison`,
  `AlgebraicGeometry.Scheme.Modules.exteriorSheafIsoExteriorPower`.
  Its two maps preserve pure wedges, so conjugation gives exactly the map
  on the original exteriorSheaf objects specified in this node.

The module also imports every already stated proof dependency, privately:
`SmoothRelativeDifferentialsFiniteLocallyFree`,
`FiniteLocallyFreeStalkIsoNeighborhood`, `SchemeEtaleSourceTargetProperties`,
`SchemeZariskiEtaleQuasiCoherentEquivalence`, `Thickening`, Mathlib's
`Morphisms.Basic` for etale source locality and `Matrix.Adjugate`.
`ExteriorSheafComparison` is now publicly imported for the existing defining
isomorphisms recorded by the new definition node. Its wedge theorems are also
available from that import; the theorem node is not added to proof_deps. The item preserves its base proof and proof_deps
exactly. Other proof dependencies are already publicly imported for their
statement roles.
The following proof nodes currently have no recorded declaration and are
therefore not imported: lem-sfb-etale-localization-relative-differentials,
lem-a1-map-over-base-finite-presentation,
lem-sfb-space-square-zero-lift-linearization,
lem-sfb-scheme-etale-relative-differentials-comparison,
lem-sfb-lfp-unique-infinitesimal-lifts-etale. They are proof prerequisites,
not missing notions needed to state this item. The docstring reproduces all
six steps of the node's proof, including their canonical-map comparisons.

Source check: read the primary BLR scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
Section 2.2, Proposition 8 and Corollary 10, printed pages 40--41 (PDF pages
46--47), and the local Stacks sources `morphisms.tex`,
`lemma-functoriality-differentials`, and `more-morphisms.tex`,
`lemma-sheaf-differentials-etale-localization`. BLR supplies the local
criterion; the global clause follows by source locality and the determinant
clause by the local square-matrix criterion. No extra base field,
noetherianity, separatedness, properness or positive-rank assumption occurs.

Edge cases checked mathematically before writing:

- Empty X: the pointwise statement is vacuous, maps of module sheaves are
  invertible, and the empty source is etale; the degree-zero identity remains.
- Empty Y forces empty X for an h, and produces the same valid case.
- d = 0: both bundles have rank zero and dh is invertible; its exterior-zero
  map preserves the empty wedge. The actual O_X identity is asserted.
- h identity: dh is the canonical identity after transport, and all criteria hold.
- Unequal or varying ranks: the first two criteria remain applicable; only the
  determinant clause has equal constant finite rank as an antecedent.
- Frobenius of affine one-space in positive characteristic: differential zero,
  so it is neither invertible nor etale. No characteristic restriction is hidden.
- General base, including nonreduced base and characteristic two: the argument
  and exterior construction require only the stated smoothness.

Searches for reuse (all read-only; wrapper group Q33 and this item):

- msearch.py LeanFinder: "A morphism between smooth schemes over a common base
  is etale if and only if its relative cotangent map is an isomorphism".
  Eight hits, including IsEtale, its smoothness instance and algebraic standard
  smooth dimension-zero criteria. None states the geometric cotangent criterion.
- msearch.py LeanSearch: "Etale morphisms between smooth schemes characterized
  by isomorphism of relative differentials". Eight hits, including algebraic
  formallyEtale_iff with first cotangent homology; no exact geometric criterion.
- msearch.py Loogle: `"Etale", "Differential"`. Five hits, all ring-level
  vanishing or tensorKaehlerEquivOfFormallyEtale and its formulas. They do not
  state the smooth-to-smooth converse or the scheme neighbourhood criterion.
- msearch.py grep `cotangent|differential`, AlgebraicGeometry/Morphisms: five
  Mathlib hits in Etale and FormallyUnramified, no exact match.
- rg on lean/WeilConjectures and lean/Sheaf for differential-map, cotangent-map,
  exterior map/functor names found the canonical relativeDifferentialsPullbackMap,
  a more specialized nonzero curve criterion, ExteriorSheafComparison and
  siteExteriorHom. Their full signatures and docstrings were read and reused.
- rg for this exact node id in lean/WeilConjectures found no declaration.
  rg on dag/lean_names_upstream.json and latest blueprint for this criterion
  found no already existing statement. DAG searches located the owning nodes
  of all reused helper declarations. The return identified that the comparison
  definitions needed their own definition node; the present repair records the
  existing declarations in place instead of moving or duplicating them.

No statement correction or STATEMENT-DISPUTED issue was found.

## Repair of return on 7096fcc73b37

The return reports that `ExteriorSheafComparisonIso` duplicates
`AlgebraicGeometry.Scheme.Modules.exteriorSheafPresheafIso` and
`AlgebraicGeometry.Scheme.Modules.exteriorSheafIsoExteriorPower`, already in
`Sheaf.AlgebraicGeometry.ExteriorSheafComparison`.

Repaired by reusing the existing declarations directly:

1. Removed the delivered `ExteriorSheafComparisonIso.lean` extraction module.
2. Removed the replacement `ExteriorSheafComparison.lean` and its dependency-node
   copy from the sandbox packet. The existing published module is reused intact.
3. Set the new definition node's `lean` to `existing: true`, referencing both
   existing names in `Sheaf.AlgebraicGeometry.ExteriorSheafComparison`, with no
   `lean.file`. The existing names and their definitions are not changed.
4. Replaced the item's public import of the removed extraction module by the
   existing comparison module and removed the now redundant private import.
   The determinant helper and theorem signatures and bodies are unchanged.
5. Preserved the item's definition-node stmt_deps, base proof and exact base
   proof_deps. No theorem node is added as a statement dependency. No mathematical
   statement is changed and no statement_change is needed.

The earlier extraction attempted to address the return on `3b5ee1614923`;
this repair keeps its separate definition-node dependency while complying with
the current return's requirement to import and reuse the existing declarations.
The `1413462624b8` repair of proof_deps remains intact. The wrapper refreshes and
rebases the packet on the current main branch through its normal bookkeeping.

## New nodes

`def-sfb-exterior-sheaf-comparison-iso` records the existing presheaf comparison
and its sheafification, rather than creating Lean definitions. Its Lean module
is `Sheaf.AlgebraicGeometry.ExteriorSheafComparison`; its `existing: true` record
lists `AlgebraicGeometry.Scheme.Modules.exteriorSheafPresheafIso` and
`AlgebraicGeometry.Scheme.Modules.exteriorSheafIsoExteriorPower`.
The latter is the primary declaration. These already published definitions
say exactly what the definition node specifies: the former is
`PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)` with the pure-wedge naturality
proof, and the latter is the module sheafification functor's `mapIso` of it.
They have real data and no sorry. The new node supplies the separate definition
record requested on the first return; it does not duplicate their construction.

Source: Stacks, Modules on Sites, Tag 03CY, local `sites-modules.tex`
`lemma-sheafification-presheaf-modules`, and the upstream sectionwise exterior
presheaf and `exteriorPower_map_ιMulti`. The node cites the scheme, module sheaf,
original exterior sheaf and module-sheafification definition nodes.

The retained search records give the actual original results:

- LeanSearch, "Canonical isomorphism between sectionwise exterior presheaves
  and their sheafifications on a scheme": eight generic sheafification results,
  including `CategoryTheory.sheafificationIso` and `isoSheafify`.
- LeanFinder, "identity comparison isomorphism between exterior sheaf and
  exterior power sheaf on a scheme": eight module exterior-power results,
  including the degree-zero and degree-one equivalences.
- msearch grep, `exteriorSheafPresheafIso|exteriorSheafIsoExteriorPower|exterior.*Iso`
  in Mathlib/Algebra/Category/ModuleCat: two module zero/one equivalence hits.
- rg of WeilConjectures, Sheaf and dag/nodes for both names found the exact
  definitions only in `ExteriorSheafComparison.lean`, bundled in the theorem
  node's existing declaration list. Other Sheaf matches are consumers.
- `tools/blueprint_refs.py search exterior comparison` returned only the unrelated
  supported exterior product; `ancestor` returned null. The node retains the
  inherited provenance and via chain. No independent definition node was found.

On this repair, reread the full signatures, docstrings and bodies of both
published definitions locally and using `scompile.py --source
Sheaf.AlgebraicGeometry.ExteriorSheafComparison`; the sources agree. Repeated
rg across dag/nodes, lean/Sheaf and lean/WeilConjectures confirms their current
location and the absence of another independent definition-node record.
The search verdicts now explicitly require reuse in place with existing: true.

Clause match: the explicit arbitrary universe and binders are
`{X : Scheme.{u}} (M : X.Modules) (n : ℕ)`. The presheaves are
`exteriorSheafPresheaf M n` and `PresheafOfModules.exteriorPower M.val n`.
The component maps are identities; the inline proof establishes their
naturality. Applying sheafification.mapIso gives exactly
`exteriorSheaf M n ≅ exteriorPower M n`. This includes degree zero, empty
opens and schemes, zero modules and every characteristic, with no local-freeness
assumption. No theorem about the comparison is needed to define either map.

## Dependency modules

None delivered. The previous replacement dependency module and node record
are removed. The existing `ExteriorSheafComparison` module is imported and
reused without any modification, as required by the current return.

## Second reading by Q33

No other agent was started, following the dispatcher instruction. I reread
the revised packet against the current source. Its only Lean file declares
`smoothCotangentDeterminantMap` and `smooth_cotangent_etale_criterion`.
Both keep their reviewed bodies, signatures and docstrings; only the comparison
import changes. All hypotheses and all four clauses still match the item as
listed above. The new definition node now references the exact two existing
definitions, and its statement matches their component identities and
sheafification construction. There is no second declaration, renaming, wrapper
alias or arbitrary replacement isomorphism. The item's proof_deps equals the
current base list in its original order; only lean and stmt_deps differ from
current main. Universes and variables remain explicitly bound.

## Validation

The only delivered Lean file is compiled using scompile.py against the live
published build and its unchanged existing comparison module. The final packet
is checked with deliver2.py --no-push before delivery. No local or global build
is run, and no published source is modified. The delivery now contains one
Lean module, the item node, the new existing-definition node and this report.
