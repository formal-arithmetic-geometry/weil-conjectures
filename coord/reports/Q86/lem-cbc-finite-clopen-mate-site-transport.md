## Worker report

Item: `lem-cbc-finite-clopen-mate-site-transport` (Q86, stage 2).
Module: `Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport`.
Main statement: `AlgebraicGeometry.ProEtale.finiteClopenMateSiteTransport`.
Its sole theorem proof is `sorry`; all six helper definitions have explicit data.
The mathematical statement, source and proof of the node are unchanged; the H2 repair adds explicit definition-node citations and keeps the etale normalization theorem as a proof dependency and removes the unused proper-open theorem from proof dependencies.

The module states transport of the prescribed finite clopen proper/open mate,
not merely existence of an isomorphism between its endpoints. The etale alpha,
mate and normalized comparison are reused from the newly landed
`Etale.ClopenMateNormalization` module. An earlier sandbox draft duplicated
these etale constructions; those definitions have been removed.

### Hypotheses and objects, clause by clause

* A finite commutative ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  There is no nontriviality, characteristic or prime-power restriction.
* The four arbitrary schemes are `{V W S T : Scheme.{u}}`; `k`, `i`, `r`, `p`
  are precisely the four named morphisms with the node's domains and codomains.
* Quasi-compact open horizontal arrows are `[IsOpenImmersion k]`,
  `[IsOpenImmersion i]`, `[QuasiCompact k]`, `[QuasiCompact i]`.
* Proper vertical arrows are `[IsProper r] [IsProper p]`.
* Commutativity is `h : k ≫ p = r ≫ i`. Composition is written in Lean's order.
  No cartesian-square hypothesis or identity-left restriction is imposed.
* `W_S`, `b`, `q`, `s` are the actual chosen `pullback p i`, `pullback.fst p i`,
  `pullback.snd p i`, and `ProEtale.StrictTower.squareLift k r p i h`.
  The latter is the existing abbreviation for `pullback.lift k r h`, with its
  published open and closed immersion instances. No geometric lift is chosen
  from a mere existence assertion.
* `A_X` is the exact `comparisonUpperStar (ModuleCat.{u + 1} Λ) X`, followed by
  `.mapDerivedCategoryPlus`. The original small sites are used throughout:
  `X.smallEtaleTopology` and `Scheme.ProEt.topology X`. There is no replacement
  of the sites by an arbitrary category and no equality between their object
  and morphism universes. Coefficient modules use the common `u+1` convention.

### Prescribed canonical maps and conclusions

* The etale alpha is the dependency's
  `Etale.ClopenMateNormalization.derivedAlphaPlus Λ k r p i h` and its mate is
  `Etale.ClopenMateNormalization.derivedMatePlus Λ k r p i h`.
  Their full signatures and definitions were read in the landed source.
* `ProEtale.cbcClopenProjection` is the direct-image adjunction unit followed
  by the inverse of the **canonical** `openImmersionLowerShriekToLowerStar`.
  The existing closed-range invertibility theorem supplies its `IsIso` proof.
  This is exactly the identity on the clopen image and zero on its complement;
  it is a map into `s_!s^*`, not an unrelated endomorphism or chosen projection.
* `ProEtale.cbcClopenAlphaSheaf` first takes the inverse of the canonical
  cartesian `openImmersionLowerShriekBaseChangeMap` for `pullback p i`.
  That map is the transpose of the open unit. It then inserts the preceding
  projection for `s`, and composes the actual open and pullback compositors.
  `cbcOpenCongr` and `cbcPullCongr` are explicit equality transports for
  `pullback.lift_fst` and `pullback.lift_snd`. Their data is `h ▸ Iso.refl _`.
* `cbcClopenAlphaPlus` is the exact derived version of that same transformation,
  using `Functor.rightDerivedFunctorPlusBaseChange` and the specified exact
  right-derived-to-termwise comparison isomorphisms. It makes no free choice
  of a derived natural transformation.
* `cbcClopenMatePlus` applies Mathlib `mateEquiv` to the proper inverse-image /
  derived-direct-image adjunctions and precisely that alpha. Its source is
  `R_r ⋙ J_i`, its target is `J_k ⋙ R_p`, as required.
* The four leading conjuncts assert `QuasiCompact p`, `QuasiSeparated p`,
  `QuasiCompact r`, `QuasiSeparated r`. These are conclusions from properness,
  not added assumptions. In particular no Noetherian or absolute quasi-compact
  hypothesis is present.
* Both comparison domains are represented by the actual bounded-below category:
  `L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat Λ))`, and
  `(Etale.openImmersionLowerShriek ... k).mapDerivedCategoryPlus.obj L`.
  The latter functor exists by exactness and preserves every cohomological
  lower bound. Thus both `L` and `k_!L` lie in the required domains; no
  independent hypothesis of boundedness of `k_!L` is assumed.
* The first universally quantified conjunct, over `M` on `S_et`, is the exact
  alpha transport equation in proof step 4: in Lean composition order it is
  `A_W(alpha_e) ≫ o_k ≫ J_k(a_r) = a_p ≫ G_p(o_i) ≫ alpha_p`.
  Its components are the canonical maps just defined or imported. Because the
  alphas use the clopen projection itself, their identity/zero normalization
  is retained before passing to mates.
* The next conjunction, for every such `L`, first identifies the actual etale
  mate component with
  `(Etale.ClopenMateNormalization.normalizedComparison ...).hom.app L`.
  That imported definition is the resolution-normalized comparison selected
  from `properOpenInterchangeCoherence`; the normalization determines its
  morphism uniquely. This includes its refinement normalization (`r = 1`).
* The next equation is the node's displayed mate equation, with Lean's forward
  composition order:
  `o_i ≫ J_i(b_r) ≫ gamma_p = A_T(gamma_e) ≫ b_p ≫ R_p(o_k)`.
  Here `b_u` is exactly `fixedComparisonDirectImageMatePlus Λ u`, never an
  arbitrary map or an inverse chosen merely to make the square commute.
  `a_u` is `fixedComparisonPullbackPlus Λ u`; the dependency's
  `fixedComparisonDirectImageMatePlus_counit` is precisely the prescribed
  counit equation for these named transformations. It applies to `r` at `L`
  and to `p` at `k_!L`, since properness supplies qcqs.
* Each `o_j` is `properOpenSiteExtensionIso Λ j`, the derived version of the
  canonical adjoint `openImmersionLowerShriekComparisonUpperStarIso`, not an
  independently selected open isomorphism. `a_u` and `o_j` are typed isos.
  Four final `IsIso` conjuncts explicitly assert invertibility of `b_r` at `L`,
  `b_p` at `k_!L`, the actual etale mate, and the actual pro-etale mate at
  `A_V L`. Functors preserve the other isomorphisms in the displayed equation.
  Together with the alpha and etale-normalization clauses these give exactly
  the finite etale proper/open and refinement normalization claimed by the node.

### Dependencies used

Recorded declaration interfaces and their source docstrings were inspected.
The following are imported as statement dependencies (directly or through the
explicit listed modules); no dependency node record is changed.

* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`.
* `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `QuasiCompact`; `...Proper`: `IsProper`; `...ClosedImmersion`:
  `IsClosedImmersion`; `...QuasiSeparated`: `QuasiSeparated`.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, whose left adjoint is the fixed
  `ProEtale.comparisonUpperStar` used here.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded derived
  category conventions and `DerivedCategory.Plus`.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the ordinary
  uncompleted constant-ring operations. Here we use their fixed-module-sheaf
  presentation, as do the recorded comparison and mate dependencies.
* `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`.
* `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`:
  `Etale.properOpenInterchangeCoherence` and its uniquely normalized comparison.
* `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `ProEtale.openImmersionLowerShriekComparison_coherence`,
  `ProEtale.proEtaleOpenExtensionComp`.
* `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `ProEtale.supportSiteComparison_pullback_coherent`; its recorded comparison
  is the canonical pullback comparison underlying `fixedComparisonPullbackPlus`.
* `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus`,
  `isIso_fixedComparisonDirectImageMatePlus`,
  `fixedComparisonDirectImageMatePlus_counit`.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.lowerStar`, `Etale.upperStar`, `Etale.upperStarLowerStarAdjunction`;
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek` and its exactness.
* `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicModuleEquivalence` and `Scheme.sfIntrinsicExtensionByZero`.
  This is the canonical intrinsic presentation of the same fixed-scalar open
  extension, transported by the recorded realization equivalence. No second
  intrinsic extension functor is introduced.
* The statement dependencies include two additional definition nodes recording the canonical helper declarations, while only the etale normalization theorem is needed as a proof dependency. Three already-landed nodes are used for the geometric lift and helper data:
  `def-cbc-strict-tower-proper-open-arrows` supplies `StrictTower.squareLift`
  and its clopen instances in `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows`;
  `def-weil-pbc-proper-open-site-extension` records the existing
  `properOpenSiteExtensionIso` declaration, without using the owning proper-open theorem; `def-cbc-etale-clopen-mate-normalization-data` records
  `derivedAlphaPlus`, `derivedMatePlus`, and `normalizedComparison`, while the
  etale theorem node remains in proof dependencies. Neither theorem-node record is used to reach plain definitions.

The additional proof-dependency imports are
`Mathlib.AlgebraicGeometry.Morphisms.Separated` (the Mathlib match
`IsSeparated.instQuasiSeparated`),
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`, and
`Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`.
The remaining proof dependencies are already among the public imports.
No proof import is omitted because of a cycle.

### Edge cases and source reading

The empty open, empty schemes, an empty complementary clopen component, the
zero ring, identity vertical arrows and the refinement case `V = S, r = 1`
are all admitted. In the empty-open case the projected component is zero;
with empty complement it is identity. Neither module definitions nor the
statement require a point, nonzero module or a nonempty index set. Schemes
need not be Noetherian and the proper morphisms need not be finite.

Sources read locally: `proetale.tex` Section comparison (Tag 099R),
`lemma-jshriek-comparison` (Tag 09AF: uniqueness of the left-adjoint comparison),
`more-etale.tex` `lemma-shriek-proper-and-open` (Tag 0F7B: its K-injective
resolution/support map), and the full seven-step proof of the assigned node.
The clopen geometric and etale resolution-normalization dependency sources
were read in their landed modules. No mathematical statement correction or dispute is needed; the citation-only correction required by the return is recorded below.

## New nodes

`def-cbc-etale-clopen-mate-normalization-data` is an existing-definition record for the three canonical derived etale clopen declarations in `Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization`; it is sourced from Stacks Tag 0F7B and has no duplicate DAG node or Mathlib match. `def-weil-pbc-proper-open-site-extension` is an existing-definition record for `AlgebraicGeometry.ProEtale.properOpenSiteExtensionIso` in `Sheaf.Paper.ProEtaleProperOpenComparison`, sourced from blueprint order 1484. The etale normalization theorem remains in `proof_deps`; the proper-open theorem is not used by the proof plan and is omitted.

### Searches

The sandbox `searches.jsonl` retains the actual msearch responses, including:

* `leanfinder`, query “Etale to pro etale comparison transports proper adjunction
  mate of open base change and clopen projection”: eight hits, e.g.
  `CompHausLike.LocallyConstant.adjunction_left_triangle`,
  `.adjunction_counit`, `Condensed.profiniteSolidCounit`; no target statement.
* `loogle`, query `CategoryTheory.mateEquiv`: twelve hits including
  `mateEquiv`, `mateEquiv_counit`, `mateEquiv_counit_symm`,
  `conjugateEquiv_mateEquiv_vcomp`, `mateEquiv_vcomp`. These supply the generic
  mate construction but not this geometric normalized site-transport result.
* `grep` via msearch, query `clopen.*mate|properOpen.*comparison`, subdirectory
  `CategoryTheory`: no hits.
* Direct `rg` in `lean/WeilConjectures` for the assigned node id: no declaration.
  Concept search for clopen/mate/comparison in upstream pro-etale sources found
  `clopenIdempotentSheaf` and `clopenIdempotent`. Their target is the identity
  functor, not `s_!s^*`, and they do not state the alpha/mate transport equation.
* Direct `rg` in `lean/Sheaf` found the already-landed
  `EtaleClopenMateNormalization` module; it is reused. Searches of ordinary
  pro-etale helper sources found open base change and direct-image comparisons,
  but no single-level clopen alpha/mate transport theorem. The existing strict
  tower alpha/mate has different objects and is not copied as a substitute.

### Validation

After removing the duplicate etale constructions, the prescribed `scompile.py`
compiled both sandbox and library module modes cleanly (37.6 s and 25.6 s),
with no errors or non-sorry warnings. `set_option autoImplicit false` is active;
all universes and variables are bound. All source lines are at most 100 characters.
The final signature is copied verbatim into the node's `lean.statement`.


## Statement corrected

The H2 return on immutable head `19b681af90b5` requires separating data from the theorems that currently list it. The old statement began “Let $\Lambda$ be a finite commutative ring” and introduced the canonical maps without their own definition-node citations. The corrected text adds references to `def-weil-pbc-proper-open-site-extension` and `def-cbc-etale-clopen-mate-normalization-data` before the existing alpha construction. `statement_change.old_statement` preserves the entire old text verbatim. This is a citation/interface correction: all mathematical hypotheses, clauses and the accepted Lean source and signature stay identical. The source remains Stacks 099R and 09AF, with the etale normalization construction in 0F7B. The theorem node `lem-cbc-etale-clopen-mate-normalization` occurs in `proof_deps`. The unused theorem node `lem-weil-pbc-proper-open-comparison-proetale` occurs in neither dependency list; the open-site helper is cited through its own definition node.

The complete citer audit (`rg -l` followed by checking both dependency fields) is:

* `lem-cbc-strict-tower-proper-open-calculus`: holds. Its finite-level transport, invertibility and refinement normalization use the identical canonical maps and unchanged theorem.
* `lem-pur-system-compatible-compositor-normalization`: holds. Its evaluated finite proper/open word uses the identical counit-normalized mate and open comparison, so the specified compositor equality is unchanged.

## Repair self-check by Q86

The new etale definition node records the actual `derivedAlphaPlus`, `derivedMatePlus`, and `normalizedComparison` declarations in the unchanged `Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization` module. `derivedAlphaPlus` and `derivedMatePlus` take an arbitrary commutative ring; only `normalizedComparison` uses finiteness. The alpha localizes the inverse open-unit comparison followed by the canonical projection and compositors, and the mate uses the induced derived adjunctions. The normalized comparison is chosen from the base `properOpenInterchangeCoherence` with its determining normalization, not from the etale normalization theorem.

The new open-site definition node records `properOpenSiteExtensionIso` in the unchanged `Sheaf.Paper.ProEtaleProperOpenComparison` module: its explicit three-factor definition is inverse derived composition, exact derived sheaf comparison, derived composition. It is valid for every commutative ring and open immersion, without finite, quasi-compact or Noetherian restrictions. Both new nodes retain the original small-site and coefficient universes. Their signatures were copied from the actual source through `:=`; no declaration was moved or copied.

Actual new searches are stored in each new node as full msearch result records: LeanSearch plus LeanFinder plus Mathlib grep. Their hits are generic derived-adjunction/clopen facts and algebraic etale facts, not these geometric definitions. `rg` in the DAG found the names as theorem helper records only; upstream `WeilConjectures/SixFunctors` has no matching names; the exact Sheaf definitions were read. `blueprint_refs.py search properOpenSiteExtensionIso` and `... search derivedAlphaPlus` each returned zero matches.

The final explicit `scompile.py` invocation reports clean sandbox and library compilation (14.8 s and 3.8 s). The repaired dry run passed all preflight and compile checks. A final script compared the main signature verbatim with `lean.statement`, verified the unchanged proof/source and exact old-field snapshots, checked both definition/theorem dependency replacements, confirmed the two new records are `existing:true` without delivered modules, and checked the 100-character Lean line limit. No proofs were added.


## Repair of return 17f488670a6e

The independent review returned the packet because `proof_deps` contained
`lem-weil-pbc-proper-open-comparison-proetale` but no proof step listed that node
in `uses`. Removed exactly that unused entry. Its full statement concerns the
proper-open isomorphism and coherence for Noetherian schemes; the seven-step
proof here uses the canonical open-site helper definition, not that theorem.
The definition remains recorded by
`def-weil-pbc-proper-open-site-extension`, and its existing module remains a
public import because the Lean signature uses `properOpenSiteExtensionIso`.
No theorem use has been invented to satisfy the check.

The proof plan and its `uses` arrays are unchanged from the current base.
`proof_deps` now equals their union and equals the base list; consequently
`statement_change.old_proof_deps` is absent, as required for an unchanged field.
The mathematical statement, Lean source, signature, helper records and citer
conclusions are unchanged.

Current repair validation: `scompile.py` completed cleanly in sandbox and library
module modes (14.8 s and 3.8 s). The self-check verified the exact proof-use
union, unchanged base proof/source, verbatim correction snapshots and Lean
signature, both existing definition signatures, line width, one postponed
theorem, and the complete two-citer audit.

## Second reading by Q86

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
