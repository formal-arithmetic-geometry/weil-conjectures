## Worker report

The module `Sheaf.CategoryTheory.SiteTorIntervalRestriction` states
`CategoryTheory.siteTorIntervalRestriction`, with `sorry` as its entire proof. It introduces
no definitions, instances, other theorem statements, or new nodes. The earlier incomplete
sandbox attempt was replaced: it assumed arbitrary monoidal structures, flat resolutions,
and a derived-monoidal structure rather than using the specified sheaf tensor.

The node's natural-language statement is unchanged. The only added statement dependency is
the already landed `def-wf-tensor-product`: its existing auxiliary declaration
`SheafOfModules.wfSiteDerivedTensor` is precisely the canonical K-flat localization tensor
of the recorded `lem-weil-pbc-site-derived-tensor-descent`. Reusing it avoids both a second
tensor definition and arbitrary tensor data. The added dependency has no dependency path
back to this item.

Clause-by-clause correspondence:

- A site small in the chosen universe is `{C : Type u} [SmallCategory C]` with
  `J : GrothendieckTopology C`; the module and coefficient universe is `u`. This implements
  `def-weil-size-convention`. No scheme, point, nonempty-site, or enough-points assumption
  is imposed. The unbounded localization sizes are independently `w` and `w'`.
- The commutative structure sheaf is `O : Sheaf J CommRingCat.{u}`. Its underlying ring sheaf
  is `(sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O`.
- Module sheaves use the recorded `ringedSiteModules.{u}` abbreviation, definitionally
  Mathlib's `SheafOfModules.{u}`. The two `HasDerivedCategory` binders choose the unbounded
  derived categories of these actual abelian categories; they impose no boundedness.
  Abelian sheafification infrastructure is inferred for small sites, not added as hypotheses.
  The named choices `hD` and `hDU` are passed explicitly to derived restriction: this lets
  elaboration identify forgetting commutativity before/after restriction without asking
  instance search to unfold the whole categorical construction. No localization is changed.
- `a b : ℤ` and `_hab : a ≤ b` give exactly the interval restriction in the node.
- `E : DerivedCategory (SheafOfModules ... O)` is the arbitrary global derived object.
- `_hE` quantifies over **every** global module sheaf `F` and integer `r` satisfying
  `r < a ∨ b < r`. The object `(DerivedCategory.singleFunctor _ 0).obj F` is `F[0]`.
  The existing `wfSiteDerivedTensor J O` gives `E ⊗ᴸ F[0]`; applying
  `(DerivedCategory.homologyFunctor _ r).obj` and `IsZero` gives precisely its vanishing
  cohomology sheaf, not vanishing sections, stalks, or a smaller class of test sheaves.
- `U : C` is arbitrary. The localized site and coefficient sheaf are `J.over U` and
  `O.over U`. Forgetting to rings commutes definitionally with this sectionwise restriction.
- `ringedSiteDerivedRestrictionOfUniverses ... U E` is the recorded canonical-representative
  restriction `E|U`, using the global localization in universe `w` and the slice localization
  in universe `w'`.
- The conclusion quantifies over **every** module sheaf `G` on `J.over U` over `O.over U`
  and every integer outside the same closed interval. No requirement is imposed on `G`
  to be flat, finite, constructible, a restricted global sheaf, or equipped with any lift.
  `wfSiteDerivedTensor (J.over U) (O.over U)`, `singleFunctor _ 0`, `homologyFunctor`, and
  `IsZero` render exactly `H^r(E|U ⊗ᴸ G[0]) = 0`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a transparent
  abbreviation of Mathlib `SheafOfModules` (the category is not copied).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, and `DerivedCategory.singleFunctor`; the latter is the complex with
  the given module sitting in degree zero, localized through the homotopy category.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlatIndependentCoefficients` and its
  specialization `IsKFlat`; K-flatness is total-tensor acyclicity against every acyclic
  complex. These are imported through the existing tensor construction, not restated.
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`:
  `SheafOfModules.wf_site_derived_tensor_descent`, giving the flat-term K-flat resolving
  subcategory, localization equivalence, tensor comparison, and uniqueness of descent.
- `Sheaf.Paper.WeilTensorProduct`: `SheafOfModules.wfSiteDerivedTensor`, defined from that
  descent theorem, with no arbitrary tensor parameter. It uses the ordinary uncompleted
  derived tensor; no Weil structure, adic completion, or scheme data enters this statement.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and its representative comparison `homologyFunctorFactors`.
- `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`:
  `CategoryTheory.ringedSiteDerivedRestrictionOfUniverses`, the exact recorded construction.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and
  `Mathlib.CategoryTheory.Sites.Over`: `SheafOfModules.over`, `SheafOfModules.overFunctor`,
  `GrothendieckTopology.over`, and `Sheaf.over` are the existing slice constructions.

All stated proof dependencies are imported, without `public` where used only for the proof:
`CochainComplex.isKFlat_of_boundedAbove_flat` (BoundedAboveFlatSheafKFlat),
`CochainComplex.exists_functorial_boundedAbove_flat_replacement` (BoundedFlatReplacement),
`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`
(KFlatResolutionIndependentCoefficients), `SheafOfModules.tensorClosed` (TensorClosed),
`SheafOfModules.isFlat_over` (SliceRestrictionFlat),
`SheafOfModules.grothendieckAbelian_with_localized_generator` (RingedSiteGrothendieckAbelian),
`SheafOfModules.localizedModuleExactIndependent` (LocalizedModuleExactIndependent),
`CochainComplex.mapBifunctorMappingCone₂Iso`
(WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone),
`CochainComplex.mappingCone.quasiIso_iff_acyclic`
(WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic), and
`DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn`
(WeilConjectures.CategoryTheory.DerivedCategory.FlatModel). The total-tensor and K-flat
statement dependency modules are exposed by the imported tensor module. The docstring
reproduces all seven proof steps, including the cone computation for arbitrary slice tests.

Source checked: local Stacks `sites-cohomology.tex`, `lemma-tor-amplitude-pullback`
(Tag 08H5): represent E by flat terms supported in [a,b], pull back those flat terms,
and use the same flat-model criterion. Slice restriction is the exact localization case.
The construction does not assume an arbitrary slice module extends globally.

Edge cases checked mathematically before writing:

- `a = b` retains both outside-degree tests, with degree `a` unrestricted.
- Negative endpoints are allowed because all degrees and endpoints are integers.
- The zero complex and the zero coefficient ring are included; no nonzero conditions occur.
- Empty sites are included: the assertion about every `U` is vacuous when there is no object.
- Objects with trivial or degenerate slice topology are allowed, without terminal-object or
  point assumptions on the original site.
- Every slice test sheaf is included, not only restrictions of global sheaves.
- The global and slice localization universes are independent. Small categories are taken
  in the chosen universe, as the node requests, and no independent smaller test universe
  could make the module quantifier vacuous.

Searches for an existing statement (2026-10-16):

- `msearch.py ... leanfinder "Restriction of a complex of module sheaves to a slice ringed
  site preserves its Tor amplitude interval"`: eight hits, including
  `HomologicalComplex.map_isStrictlySupported`, `DerivedCategory.IsLE`, `IsGE`,
  `isGE_iff`, bounded representative existence, and factorization results. These concern
  cohomological support, not the universal derived-tensor test on a slice.
- `msearch.py ... loogle 'SheafOfModules.over, "tensor"'`: zero hits.
- `msearch.py ... grep 'torAmplitude|tor_amplitude|TorAmplitude'
  Algebra/Category/ModuleCat/Sheaf`: zero hits.
- `msearch.py ... leansearch "Restriction to the slice of a ringed site preserves the Tor
  amplitude interval of a complex of sheaves"`: eight hits on ordinary ringed-space/scheme
  restriction, sheaf section restriction, and restriction of complex shapes, without the
  asserted Tor interval theorem.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for the proposed name and
  Tor-amplitude/restriction combinations: no existing theorem with this assertion.
  The upstream generic `DerivedCategory.torAmplitudeIn` was read; it requires a specified
  derived monoidal structure and does not itself state slice preservation. The already
  existing canonical `wfSiteDerivedTensor` is reused instead of assuming extra structures.
- `rg` for the item id in upstream sources, and for `siteTorIntervalRestriction` in
  `dag/lean_names_upstream.json`: no declaration match.

No statement correction, new definition node, dependency-module delivery, or
STATEMENT-DISPUTED issue is required. Compilation and the required dry-run preflight
are recorded below after validation.

Validation: `scompile.py Q40 lem-sf-site-tor-interval-restriction
lean/Sheaf/CategoryTheory/SiteTorIntervalRestriction.lean` passed cleanly with no warnings,
compiling the sandbox check (19.2 s) and the actual library module (12.2 s), each under the
unchanged 60-second limit. Explicit universe arguments and the explicit `hD hDU` arguments
resolve the initial inference errors; all original mathematical hypotheses are retained.
The node copy differs only in `lean` and the one added landed statement dependency.

## Second reading by Q40

I reread the item node, its source place, every recorded statement dependency, the worker
module, and the Stacks source before this validation. The source is Stacks Project,
`sites-cohomology.tex`, Tag 08H5 (`lemma-tor-amplitude-pullback`), whose hypotheses are a
morphism of ringed sites, an object of the target derived category, and Tor amplitude in
`[a,b]`; its conclusion is the same interval after derived pullback. The item specializes
that morphism to the exact localization `C/U`, as the source place specifies.

Object and hypothesis correspondence is as follows.

* The source ringed site is rendered by `{C : Type u} [SmallCategory C]`, `J :
  GrothendieckTopology C`, and `O : Sheaf J CommRingCat.{u}`. The module category is the
  recorded `ringedSiteModules` abbreviation, hence Mathlib's `SheafOfModules`, and the two
  `HasDerivedCategory` binders are the unbounded derived categories on the original site and
  its slice. No scheme, point, nonempty-site, separatedness, Noetherian, boundedness, or
  finiteness hypothesis is added.
* The integers `a b` and `_hab : a ≤ b` render the closed interval from the node. `E` is an
  arbitrary object of the global derived category. `_hE` quantifies over every global module
  sheaf `F`, every `r : ℤ`, and exactly the disjunction `r < a ∨ b < r`; its `IsZero` target is
  the homology sheaf of the existing canonical K-flat derived tensor with `F[0]`.
* `U : C` is arbitrary. The displayed `ringedSiteDerivedRestrictionOfUniverses` is the
  recorded canonical representative restriction to `J.over U` and `O.over U`, with
  independent localization universes `w` and `w'`. The conclusion quantifies over every
  slice module sheaf `G`, every integer `r`, and the same outside-interval disjunction, and
  states `IsZero` for the slice derived tensor with `G[0]`.

The added `def-wf-tensor-product` dependency is used only for its recorded auxiliary
declaration `SheafOfModules.wfSiteDerivedTensor`; it is the canonical K-flat localization
tensor supplied by the existing site-derived-tensor descent result, not arbitrary tensor
data or a second tensor construction. The other dependency declarations were opened and
used as recorded: `DerivedCategory.singleFunctor` supplies degree-zero objects,
`DerivedCategory.homologyFunctor` supplies cohomology sheaves, `ringedSiteModules` supplies
the general-site module category, and `ringedSiteDerivedRestrictionOfUniverses` supplies
the derived slice restriction. No dependency module was added or privately copied.

Edge cases were checked against both the source and the Lean binders: `a = b` leaves degree
`a` unrestricted; negative endpoints and `r = 0` are allowed; zero complexes, zero module
sheaves, and a zero coefficient sheaf are allowed; an empty site makes the universal `U`
clause vacuous; degenerate slice topologies are allowed; and every slice test sheaf is
quantified, including one that is not a restriction of a global sheaf. The independent
`w,w'` localization universes do not exclude any source case. No characteristic or
nonzero assumption occurs in the source or Lean statement.

For the required existing-notion searches, I reran the semantic LeanFinder/LeanSearch and
Loogle queries recorded in the worker report, together with targeted `rg` searches for
`siteTorIntervalRestriction`, `torAmplitude`, `TorAmplitude`, and K-flat restriction in the
project and upstream source. The only relevant existing declarations are the generic
cohomological-bound and ordinary restriction APIs; none states this universal slice Tor
interval theorem. The canonical tensor and restriction declarations used by the module were
read at their source locations, including their universe parameters.

I found no mismatch in the node statement, hypotheses, quantifier order, edge cases, or
declaration identity, so no repair to the theorem text was needed. The concrete worker
changes retained after this reading are the canonical `wfSiteDerivedTensor` use, explicit
universe parameters for global and slice localizations, and explicit `hD hDU` arguments to
the recorded restriction. The module compiles cleanly through the required `scompile.py`
wrapper; no warning other than the permitted `sorry` declaration warning is emitted.
