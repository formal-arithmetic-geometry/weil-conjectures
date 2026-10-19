## Worker report

Repaired the returned ce6d83cf30a4 packet. The original theorem took its conclusions as
hypotheses and used arbitrary rings and functors. The retained partial repair had started
canonical constructions but still omitted the component derived equivalence and scalar
compatibilities; its report and node signature still described the returned theorem.
The saved packet's required initial dry run failed because its duplicate component-site
module had no owning node. The current main branch now supplies
`Sheaf.Paper.ComponentRelativeProfiniteSite`, with the reviewed canonical universal
property. This delivery uses that declaration and removes the saved duplicate module.
The retained item statement is unchanged; its repaired `stmt_deps` now names the dedicated scalar-extension definition and the derived change-of-rings model.

The module states the entire item on canonical objects, with one postponed theorem and
no postponed data. `Evaluation.Statement` and the component/scalar clause definitions
are explicit conjunctions of mathematical claims, not hypotheses assumed by the theorem.

Hypotheses and objects, read against the node clause by clause:

- A commutative condensed ring is `(Λ : Profinite.CondensedRing.{u})` with
  `[IsCommMonObj Λ.X]`. This is the recorded arbitrary ring-object encoding; no
  topological-ring presentation, characteristic, discreteness or flatness is assumed.
- The scheme case quantifies over `T : Scheme.{u}` with `[IsAffine T]` and
  `[IsWContractibleRing Γ(T, ⊤)]`. The last class is precisely the recorded geometric
  w-contractibility condition on an affine's coordinate ring.
- The other case quantifies over every `S : Profinite.{u}` with
  `ExtremallyDisconnected S`. Neither case assumes nonemptiness.
- The coefficient on the scheme site is the recorded `condensedRingObj Λ.X T`, namely
  `p_T^* Λ`. The category is `Evaluation.D (Scheme.ProEt.topology T) ...`, the ordinary
  unbounded `DerivedCategory (Mod (Sheaf ...) ...)`, with the published ordinary
  relative derived tensor. The unit is the coefficient module in degree zero.
- The profinite site is `Over S` with `(coherentTopology Profinite).over S`.
  These are actual profinite sets over S with finite jointly surjective covers.
  `profiniteCoefficient` is `overPullback` of Λ with its induced ring-object structure.
- `Evaluation.ringSheaf` uses the recorded internal/sectionwise ring reconstruction.
  `Evaluation.A J O U` evaluates that ring at the actual terminal site object U:
  `Scheme.ProEt.mk (𝟙 T)` or `Over.mk (𝟙 S)`. Hence it is Γ(T,Λ_T), not a ring
  parameter. `profiniteSectionRingIso` identifies the latter sections with Λ(S),
  using the monoidal restriction comparison and the ring reconstruction functor.
- `Evaluation.scalarMap` is the constant-ring-sheaf adjunction counit at the terminal
  object. `Evaluation.F` is derived discrete constant realization, derived extension
  along that map, and the inverse section-module equivalence. This is exactly
  Λ_T tensor over constant A_T with the constant complex.
- `Evaluation.sections` is the section-module equivalence followed by actual module
  evaluation. `Evaluation.G` is its unbounded right derived functor, hence RΓ.
  Neither a right adjoint nor its full faithfulness is assumed.
- `Evaluation.perfect` uses `DerivedCategory.IsPerfectRingComplex`, the recorded
  bounded finite projective representative predicate. `Evaluation.lisse` is the
  full-subcategory object property `IsDualizable`, the existing predicate
  `Nonempty (HasRightDual K)`. Its exact pairing includes both triangle identities.

Conclusions, in the same order as the node:

1. The first conjunct of `Evaluation.Statement` is `Nonempty F.FullyFaithful` on
   the entire D(A_T). Its next conjunct supplies `CommShift ℤ` and `IsTriangulated`.
   `Evaluation.strongSymmetric` asserts `Nonempty F.Braided` with the published
   Koszul derived braidings; `Functor.Braided` includes strong monoidality.
2. The last conjunct gives an actual equivalence of the perfect and lisse full
   subcategories. Two natural isomorphisms identify its functor with restriction
   of F and its inverse with restriction of G=RΓ. There is no claim that G is fully
   faithful on arbitrary objects of D(T).
3. The component space is the recorded `affineComponentSpace T`, exactly the
   profinite quotient `ConnectedComponents T` with the quotient topology.
   `componentTests` selects the recorded `component_relative_profinite_site`
   functor. That theorem specifies its projections by the unique relative mapping
   property, its actual finite clopen stages, and every permitted inverse-limit
   presentation. Thus this selection has uniquely determined data up to the
   compatible isomorphism; it is not a selection of arbitrary schemes or maps.
4. `componentInverse` is actual left Kan extension along those tests followed by
   sheafification. The existence of its continuity, braided monoidality and
   exactness are conclusions in `componentClause`. Its coefficient isomorphism
   `α` is an isomorphism in `Mon (Sheaf ...)`, preserving multiplication and unit.
   The monoidal factorization comparison `β : q_S^* ⋙ π_T^* ≅ p_T^*` satisfies
   `α.hom.hom = β.hom.app Λ`, explicitly expressing coefficient compatibility.
5. `componentModules` is `mapMod` of this inverse image followed by restriction
   along `α.inv.hom`. `componentDerived` is its termwise derived functor. These
   fixed constructions, rather than an auxiliary functor, occur in all conclusions.
   `componentComparisons` asserts its triangulated exactness and strong symmetric
   monoidality, the derived coefficient-unit isomorphism, and an equivalence of
   the lisse full subcategories whose included functor is this pullback.
6. The ring comparison `a : A_S ≅ A_T` in `componentComparisons`, combined with
   `profiniteSectionRingIso`, is A_T ≅ Γ(S,Λ). The two rings are fixed evaluations,
   not arbitrary parameters. Its commuting realization square uses derived scalar
   extension along `a.hom.hom`, specifying how their actions are identified.
7. That square is `F_S ⋙ componentDerived ≅ moduleDerivedExtension a.hom.hom ⋙ F_T`
   on all unbounded complexes. The next square is
   `profiniteScalarRealization ⋙ componentDerived ≅ condensedScalarRealization`.
   Thus both the section-ring realization and realization from R=Γ(*,Λ) commute
   with the actual inverse image.
8. `profiniteScalarMap` is restriction along the unique S→*, composed with the
   explicit restricted-section ring comparison. The final conjunct uses its
   composite with `a.hom.hom`, the induced R→A_T map, and asserts the natural
   isomorphism `condensedScalarRealization ≅ moduleDerivedExtension (...) ⋙ F_T`.
   On P this is Λ_T tensor_R^L P ≅ F_T(A_T tensor_R^L P). The analogous profinite
   comparison is `profiniteScalarClause`, also included in the theorem.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.mk`,
  `Scheme.ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, and transported ring-object instances.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent `SheafOfModules` encoding used by the section-module equivalence.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the localization functor Q.
- `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`.
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  `realizationRing` and `commutativeSiteDerivedConstantModuleFunctor`.
- `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`:
  `spectralSpace_connectedComponents_profinite`, used by `affineComponentSpace`.
- `Sheaf.Paper.ComponentRelativeProfiniteSite`: `affineComponentSpace` and
  `component_relative_profinite_site`; the complete signature and twelve-step
  proof docstring were read before reusing its universal construction.
- `Sheaf.AlgebraicGeometry.CondensedScalarRealization`: `condensedSectionRing`,
  `condensedScalarRing`, `condensedScalarExtensionModel`, `condensedScalarRealization`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionRingSheaf`, `sectionModuleEquivalence`, `commMonToRing`; the current source
  was read through `scompile.py --source` because it is absent in the older checkout.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `nonempty_derivedChangeOfRingsCochainModel`, with its universal counit and fixed
  K-flat computations. The chosen model is determined by this universal property.
- `Sheaf.Paper.ConstantRealizationDerivedScalarExtension`:
  `ConstantScalarRealization.moduleDerivedExtension`, the left adjoint to actual
  derived restriction, and the constant-realization comparison used in proof step 9.
- The published module-object tensor, exact mapMod, scalar comap, right-derived
  and exact-functor localization constructions are reused throughout.

All stated proof-dependency modules are imported, including the K-flat, tensor-descent,
point-basis, clopen-partition and dualizable/perfect interfaces. The unstated nodes
`lem-zl-contractible-derived-sections-tensor` and
`lem-trf-geometric-inverse-image-exact` remain named in the nine-step docstring;
they have no recorded module to import. No downstream theorem is assumed.

Edge cases checked against HRS Section 3, Remark 3.2, Lemma 4.1, Example 4.2,
construction (4.1) and Proposition 4.3(3): empty affine scheme, empty profinite base,
zero coefficient ring and zero complex, singleton component space, disconnected bases,
non-surjective profinite maps over S, arbitrary shifts, and unbounded complexes.
No boundedness is imposed on D(A), and only the perfect subcategory is bounded by
its definition. Exact means triangulated; Example 4.2 rules out requiring t-exactness
of F, so the statement makes no such assertion. All universes are explicit; the
small pro-etale site retains object universe u+1 and morphism universe u, with
coefficient universe u+1 and the published localization sizes.

Searches retained in searches.jsonl and repeated during repair:

- `msearch.py leanfinder`: “Global sections on weakly contractible affine schemes give
  a fully faithful realization whose perfect complexes are dualizable sheaves and
  commute with pullback from connected components”. Eight results included
  `AffineScheme.ΓIsEquiv`, `AffineScheme.Spec_full` and the locally constant condensed
  module full-faithfulness results; none states this derived theorem.
- `msearch.py loogle`: `CondensedMod, DerivedCategory`, zero hits.
- `msearch.py leansearch`: “Weakly contractible schemes have lisse derived sheaves
  equivalent to perfect complexes over their ring of global sections”. Eight results
  concerned scheme sections and scheme modules, with no matching theorem.
- `rg` in Mathlib, upstream WeilConjectures and lean/Sheaf for
  `w.contractible.*(lisse|perfect|dualiz)|(lisse|perfect|dualiz).*w.contractible`:
  the local-perfect-model theorem cites the mathematical evaluation input, but does
  not state it. Searching the upstream tree for the exact item id found no match.
  The existing scalar-realization definition and component-site node were reused.

The item statement is unchanged. This repair adds the dedicated definition nodes
`def-zl-ring-derived-scalar-extension` and `def-zl-derived-change-of-rings-model`
to the item’s `stmt_deps`. The latter cites `lem-pur-derived-change-of-rings`;
that theorem is not a direct statement dependency of the item. The scalar-realization
theorem is a direct proof dependency of the item and is also the published owner
cited by the scalar-extension definition node. The module and its canonical aliases are compiled below. Every helper is recorded in `lean.declarations` and has its
own source/blueprint docstring. The one postponed theorem's docstring now contains
all nine proof steps, replacing the retained placeholder.

## Second reading by NU

In a separate second pass, I opened the node and read the entire revised module,
including the definitions hidden behind every clause. This found and corrected the
retained omissions of the profinite case, derived component pullback, lisse equivalence,
coefficient-unit identification, both scalar squares and final scalar associativity.
The return's arbitrary A,F,G,FS,π,Dₛ parameters and hF,hG,hunit,hcomp,hbase hypotheses
are all gone. The only theorem inputs are the commutative condensed ring and the two
specified kinds of base, and none of its conclusion conjuncts is an input.

I checked each hypothesis and all eight conclusion groups enumerated above against
the corresponding Lean definitions. In particular the component inverse is left Kan
extension/sheafification along the recorded relative tests; the coefficient transport
is constrained by the monoidal point-factorization comparison; F and G are actual
derived extension and derived evaluation; perfectness and dualizability use the recorded
predicates; and full faithfulness of G is required only through its restricted inverse
in the equivalence. The comparison uses actual Γ(S,Λ) through the explicit section-ring
isomorphism. The two scalar formulas are natural isomorphisms on all of D(R), not
objectwise unrelated isomorphisms or hypotheses. The empty and zero cases remain
included. The source's exactness is triangulated exactness throughout.

I also rechecked the nine numbered proof steps against the DAG, removed the duplicate
component-site module in favor of the landed dependency, removed the unused monoidal
equivalence import, and added the stated proof imports. Compilation and preflight are
performed with the prescribed wrappers; their final results are recorded below.

Final validation, 2026-10-18: `scompile.py NU` compiled all three delivery modules
(`RingDerivedScalarExtension`, `DerivedChangeOfRingsModel`, and
`CondensedWContractibleLisseEvaluation`) without errors or warnings. The prescribed
`deliver2.py ... --no-push` returned `OK (dry run): commit 14dc885e32 passes the
preflight and compiles`; the three-module packet passed server preflight and
compilation. No global build was run.

## New nodes

Repair addendum: `def-zl-ring-derived-scalar-extension` and `def-zl-derived-change-of-rings-model` are new definition nodes in
this delivery. The first records `CategoryTheory.RingDerivedScalarExtension.moduleDerivedRestriction`,
its canonical right-adjoint instance, and
`CategoryTheory.RingDerivedScalarExtension.moduleDerivedExtension` in
`Sheaf.AlgebraicGeometry.RingDerivedScalarExtension`. The scalar-extension module aliases the published
universal construction from `Sheaf.Paper.ConstantRealizationDerivedScalarExtension`,
so its data is canonical and contains no choice or `sorry`. Its source is Stacks Tags
06YY and 07A6. The change-of-rings model module selects the landed universal
cochain model for `Evaluation.extensionModel` (Stacks Tags 06YT, 06YY and 06XN). LeanFinder found only Mathlib's underived `ModuleCat` adjunction;
Loogle and Mathlib grep found no derived declarations, and DAG grep found no prior
node. The item now cites both definition nodes in `stmt_deps`; the second node owns the canonical
model selected by `Evaluation.extensionModel`.

## Dependency modules

No dependency module was needed. The returned issue's other requested dependency,
`lem-pur-derived-change-of-rings`, already has its landed declaration
`SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` in
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`; it is cited by
`def-zl-derived-change-of-rings-model`, which the item directly cites.
`Evaluation.extensionModel` uses that definition’s selected universal model.
The scalar-realization theorem remains a direct proof dependency of the item;
the scalar-extension definition node also cites it as the owner of its aliases.


## Return repair: dependency ownership

The return on immutable head `07f043deb8be` identified an omitted statement
dependency, an inaccurate report, and the scalar aliases’ missing owner citation.
I retained the saved three-module packet and made these repairs:

- Restored `lem-zl-component-relative-profinite-site` to the item’s `stmt_deps`,
  using the return’s explicit alternative to introducing a selector definition node.
  The current main branch records its usable declaration in
  `Sheaf.Paper.ComponentRelativeProfiniteSite`. `componentTests` selects
  `component_relative_profinite_site T`; `affineComponentSpace` comes from the same
  owner. Their use continues through `componentInverse`, `componentModules`,
  `componentDerived`, `componentComparisons`, and `componentClause`. The theorem’s
  unique relative mapping property determines the selected functor up to its
  compatible isomorphism. Consequently it supplies definition data needed to read
  the statement, and a direct statement citation is justified. No new component
  notion or module is necessary. No dependency from the saved packet was removed.
- Corrected both false claims that `lem-pur-derived-change-of-rings` was added
  directly to the item. The actual chain is item →
  `def-zl-derived-change-of-rings-model` → `lem-pur-derived-change-of-rings`.
- Added the published owner `lem-sfb-constant-realization-derived-scalar-extension`
  to `def-zl-ring-derived-scalar-extension.stmt_deps` and cited it in that node’s
  statement. Its module re-exposes the already published ordinary-module functors;
  the canonical restriction, right-adjoint instance and left adjoint are unchanged.
  This is an ownership citation, not an independent construction or an additional
  hypothesis. The item cites this definition node. The owner theorem remains also
  a direct proof dependency of the item.

Second reading of this repair: I read the component-site theorem’s complete
signature and twelve-step docstring, the scalar owner’s restriction/adjoint/extension
signatures and docstrings, and the saved item’s component definitions. The restored
citation accounts for both selected functor data and its profinite base. The scalar
owner citation accounts for every alias. All original hypotheses, both base cases,
eight conclusion groups, universe choices, empty/zero cases and the nine-step proof
docstring remain exactly as reviewed. No mathematical statement was corrected.
The saved validation above belongs to the previous packet; the revised packet’s
validation is recorded below after the wrappers finish.

Repair validation, 2026-10-18: `scompile.py NU lem-zl-condensed-wcontractible-lisse-evaluation` compiled all three retained delivery modules separately, including their private overlays, with exit 0 and no errors or warnings. The library-file checks took 2.3 s (`DerivedChangeOfRingsModel`), 3.4 s (`RingDerivedScalarExtension`), and 9.3 s (`CondensedWContractibleLisseEvaluation`). No Lean declaration or signature changed in this return repair; the revised ownership records and report are submitted to the prescribed dry run next.
