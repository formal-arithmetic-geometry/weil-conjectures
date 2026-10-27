## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleNormalizedMatesCompositionPasting` states the entire
node in eleven named theorems, each with `sorry`, and three constructed helpers. The item node
changes only in `lean`. No statement correction or dependency repair is needed. No independent
notion is introduced: the three helpers transport the specified compositor/exchange to the
arbitrary fixed compactifications already quantified by this node, and take the right mate.
Their names are listed in `lean.declarations`. All data is constructed from published maps;
there is no choice from a bare existence of isomorphisms.

Sources read: `literature/stacks-project/more-etale.tex`, `lemma-shriek-composition` (Tag 0F7J,
line 3159) and `lemma-pseudo-functor` (Tag 0F7K, line 3374), together with the existing actual
unbounded comparison interface; `literature/stacks-project/etale-cohomology.tex`,
`lemma-shriek-base-change` (Tag 03S6, line 11493). Read the current blueprint under
`literature/blueprint/latest`: `thm-pur-composition-coherence.proof.md` Step 1 and
`lem-pur-co-smooth-etale-locality.proof.md` Step 1. The DAG's eight-step proof expands the
adjunction calculations that the blueprint leaves implicit; each theorem docstring includes
its relevant steps and the named inputs.

### Hypotheses and objects

* Finite commutative coefficients: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  `u` is explicitly declared, and `set_option autoImplicit false` is enabled.
* Ordinary unbounded constant-A module derived categories: `DerivedCategoryModule A X`, the
  published `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A))`. Inputs `K` range
  over this whole category. No cohomology, boundedness, torsion or constructibility predicate
  is imposed on K. The prescribed coefficient universe and scheme universe are unchanged.
* Schemes and their morphisms: `Scheme.{u}` and `⟶`, with `[IsNoetherian ...]` on every scheme
  of each theorem's diagram. Mathlib's `IsNoetherian` is equivalent to the stated finite
  affine Noetherian cover (Noetherian.lean, `isNoetherian_iff_of_finite_iSup_eq_top`).
* Separated etale finite-type arrows: `[Etale e] [IsSeparated e] [QuasiCompact e]`, and the
  corresponding binders for v and the base-changed arrows. Etale supplies locally finite
  presentation and hence locally finite type; quasi-compact plus locally finite type is
  finite type. Composite instances are inferred. The explicit e',e'' hypotheses are the
  automatically inherited base-change properties, and exclude no Cartesian base change.
* Arbitrary chosen compactifications: `c : Compactification e`, `d : Compactification v`,
  `k : Compactification (e ≫ v)`, or the corresponding e',e'' compactifications. We do not
  fix the global `HasCompactification` choice. The helpers take these fixed candidates.
* Actual `F_a`: `rightDerivedLowerShriekOfCompactification (ModuleCat.{u+1} A) c`, the published
  `D(j_!) ⋙ R(r_*)`. All right functors `G`, `G_e`, `G_v`, `G_ve`, etc. and their adjunctions
  `adj : F_a ⊣ G_a` are universally quantified, exactly as in the node.
* Actual `S_a ⊣ a^*`: `derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat A) a inferInstance`.
  `canonicalEtaleCompactSupportComparison A a c` is the existing inverse of the constructed
  graph comparison; it is the actual support-to-sum map, not a hypothetical witness.
  Every occurrence of rho is written directly as `conjugateIsoEquiv adj sumAdj d.symm`;
  there is no second rho definition.
* Cartesian data: `sq : IsPullback w' e' e w`, and the two analogous further/pasted squares.
  This is the existing Mathlib Cartesian square, with its canonical `sq.isoPullback` and
  projection equations, so it supplies the chosen fibre-product identification of
  `ChosenCartesianSquare`. The inherited `sq.toCommSq` is exactly the input of the canonical
  square inverse-image map specified by that dependency. No new Cartesian-square notion
  or arbitrary square transformation is defined. One may form the recorded chosen structure
  with `toCommSq := sq.toCommSq`, `isoPullback := sq.isoPullback`, and its two projection
  equations; its specified inverse-image map is the same one used here.
* The changes of base `w`, `z`, and `wX,wU` are arbitrary morphisms. They have no etaleness,
  flatness, properness or finite-type assumptions. All further open restrictions are
  included by specializing these arbitrary changes of base to open immersions.

### Every clause

* The proper/open alpha is `etaleNormalizedSupportCompositor A c d k`. Its body compares c
  with `(k.ofComp d).restrict`, uses the published proper/open tower compositor, and compares
  the result back to k. This is exactly the specified unbounded compositor transported to
  the three supplied compactifications. It is the construction of
  `unboundedEtaleLowerShriekCompIso` without an imposed global choice.
* `etaleNormalizedMates_composition` states the first displayed equality at every K. Its
  first conjugate is rho_ve. `unboundedEtaleUpperStarCompIso A e v` is kappa. The second
  conjugate uses `adj_e.comp adj_v`, so it is c_(v,e): G_ve -> G_v ⋙ G_e. The last two factors
  are rho_e at G_v K, then the exact pullback e^* of rho_v at K. Lean's `≫` writes these in
  diagrammatic order. In particular c points OUT OF G_ve; no inverse c is used.
* `etaleNormalizedMates_identity` states the identity clause for every compactification c
  and every right adjunction. Its right side conjugates the canonical comparison from c
  to the proper identity compactification, followed by the identity sum-extension and
  exact-derived identity identifications. Its left side is rho followed by pullback's
  canonical identity comparison.
* `etaleNormalizedMates_refinement` states rho_hat = rho after t^c, for all pairs c,d and
  all right adjunctions, hence in particular every proper refinement. The t is the published
  canonical common-refinement comparison; its conjugate goes from the new right adjoint to
  the old one. No unspecified comparison of right adjoints is assumed.
* `etaleNormalizedMates_composition_refinement` is the corresponding square for c_(v,e),
  changing all three compactifications at once. Along with the rho refinement equation,
  it explicitly identifies both sides of the composition equation under the specified
  right-adjoint comparisons. This is DAG proof Step 3, not merely a repeated assertion of
  the composition formula for different choices.
* `etaleNormalizedSupportExchange` is the actual `unboundedEtaleCompactSupportExchange`,
  whose target initially uses `c.ofIsPullback sq`, followed by the published comparison to
  the arbitrary chosen d. Invertibility is obtained from the existing proper-base-change
  theorem for finite coefficients and the published invertibility criterion. All data is
  real, with no postponed proof inside a definition.
* `etaleNormalizedRightExchange` is `mateEquiv adj adj'` of the inverse of precisely this
  exchange, constructed as a natural transformation on the whole category.
  `etaleNormalizedMates_exchange_adjunct` spells out its component at K as
  `adj'.homEquiv _ _ (C.inv.app (G.obj K) ≫ w^*.map (adj.counit.app K))`, exactly the node's B.
* `etaleNormalizedMates_baseChange_pasting` states B_z after z'^*B_w equals B_wz after the
  source pullback-compositor inverse and before G'' of the target compositor. These last
  two factors are precisely the canonical identifications suppressed in the node's display.
  It holds for every K and arbitrary further z, not only open z or the constant complex.
* `etaleNormalizedMates_exchange_refinement` states the specified square comparing B_hat
  followed by t'^c with w'^*t^c followed by B. This is DAG proof Step 5, with independent
  compactifications of e and e'. Together with base-change pasting and the common-refinement
  cocycle it identifies the two sides of each pasted equality under refinement.
* `etaleNormalizedMates_pullback_pasting` states the chi pasting equation with the same
  source and target pullback compositors. Here chi is
  `(exactDerivedSquareUpperStarIso (ModuleCat A) sq.toCommSq).inv`: the existing square
  isomorphism points e'^* w^* -> w'^* e^*, whereas this node's chi has the inverse direction.
  The use of `.inv` is essential and was checked against both signatures.
* `etaleNormalizedMates_normalization_pasting` has two explicit hypotheses `hw` and `hz`,
  exactly the two rho B = chi pullback(rho) equations in the final paragraph. Its conclusion
  is the same equation for the pasted square and `(z ≫ w)^*K`. There is no hypothesis
  asserting the desired conclusion or the existence of a normalized map. Naturality
  accounts for the explicit pullback-composition identifications in the other statements.
* `etaleNormalizedMates_composition_restriction` states
  c' B_(ve) = (G_e' B_v)(B_e G_v)(w_U^* c) for the two vertically pasted Cartesian squares,
  exactly DAG proof Step 8. With the normalization squares of the separate
  `lem-pur-etale-support-exchange-right-mate` and the composition theorem this identifies
  the normalized composition equality with its arbitrary Cartesian restriction. Specialize
  w to ANY open immersion for the requested open-restriction clause. The general B-pasting
  equation handles further restriction of B; no second open-specific map is chosen.

* `etaleNormalizedMates_openRestriction` explicitly states the rho/B/chi square for every
  open immersion w, every unbounded K, and both arbitrary compactifications. This also
  applies to the further square after an arbitrary first base change. Together with
  the B-pasting, chi-pasting and compositor-restriction equations, it renders all the
  open-restriction assertions as Lean equalities, without relying on prose alone.

### Dependency declarations and imports

Full signatures and docstrings of the interfaces were read in the source files.

* `WeilConjectures.AlgebraicGeometry.DerivedCategories` / the public Coefficients import:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its hom type;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`.
* `def-weil-scheme-morphism-properties` is explicitly a convention node, not a declaration.
  Its relevant properties are `IsSeparated`, `QuasiCompact`, `LocallyOfFiniteType` and the
  Mathlib `Etale` of `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
* `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`,
  `Compactification.category`, building on `Compactification` in Compactification.Defs.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification` (loaded
  publicly by the comparison dependency). The delivered theorems quantify all adjunctions;
  no particular choice is substituted for the node's G.
* `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: `etaleLowerShriek` and the sheaf
  adjunction. `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality` publicly exposes the
  exact unbounded sum adjunction, whose current owning declaration is
  `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection` /
  `AlgebraicGeometry.Etale.derivedEtaleLowerShriekUpperStarAdjunction`.
* `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`:
  `AlgebraicGeometry.Etale.quasifiniteCompactSupportExact`; the actual graph-normalized d is
  `canonicalEtaleCompactSupportComparison` in
  `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso`, read with its construction.
* `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`, `conjugateEquiv`,
  `mateEquiv` and the vcomp/hcomp/conjugate pasting lemmas recorded by the relevant Mathlib
  leaves. `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, `Adjunction.id`.
* `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleLowerShriekCompIso`, `unboundedEtaleCompactSupportExchange`,
  `unboundedEtaleCompactSupport_baseChange`, its composition/pasting/refinement equations,
  `unboundedEtaleUpperStarCompIso`, `unboundedEtaleUpperStarIdIso`. The helpers use the existing
  tower and `rightDerivedLowerShriekOfCompactificationIso` of the upstream independence API.
* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `AlgebraicGeometry.ChosenCartesianSquare`,
  whose specified map is `squareUpperStarIso`; its exact derived form is the existing
  `AlgebraicGeometry.Etale.exactDerivedSquareUpperStarIso` in
  `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`, already public through the comparisons.
* `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`. The actual six-functor inverse images
  are the existing `upperStar (ModuleCat A)`, used throughout the recorded compact-support
  and sum-extension dependencies; no SheafOfModules encoding is introduced.
* Proof-only imports are `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition` /
  `derivedInverseImageComposition` (only its sheaf clause),
  `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear` /
  `etaleInverseImageCompositionModuleLinear`, and the exact-inverse-image module above.
  Localization, conjugacy, and mate-pasting proof dependencies are existing Mathlib leaves.
  The sum-composition-counit and support-exchange-right-mate nodes currently have neither
  a recorded Lean module nor an upstream audit declaration, so there is no module to import
  for these proof-only inputs yet. Their use remains in the complete proof docstrings.
  The definition-only node def-pur-etale-exact-pullback-unit-composition-comparisons records
  the compositor as owned by UnboundedEtaleCompactSupportComparisons, already publicly
  imported. Its other owning module EtaleSumRightAdjointCoherence contains the downstream
  consumer of this item and is intentionally not imported: the unit comparison is not used
  in this node, and importing the downstream consumer would obstruct its future proof import.
  The exact required pullback-compositor declaration is already the very same declaration.

### Searches and existing declarations

The prescribed msearch calls ran, not reconstructed search records:

* LeanFinder: `Adjunction conjugates of etale compact support comparison commute with
  composition and iterated base change` returned 8 hits, including
  `Scheme.Modules.conjugateEquiv_pullbackComp_inv`, sheaf-module pullback composition, and
  scheme-module pushforward comparisons. These concern different coefficient categories
  or generic adjunction identities, not the full node on actual etale compact supports.
* Loogle: `CategoryTheory.conjugateEquiv, CategoryTheory.Adjunction.comp` returned 12 hits,
  including `conjugateEquiv_whiskerLeft`, `conjugateEquiv_whiskerRight`, unitors/associator,
  and generic mate/conjugate comparisons. These are used as infrastructure, not redefined.
* Mathlib grep through msearch: `conjugateEquiv|mateEquiv`, subdirectory
  `CategoryTheory/Adjunction`, returned the existing Mates and CompositionIso declarations.
* LeanSearch: the same plain-language query as LeanFinder returned 8 hits, including
  `conjugateEquiv_comp`, `conjugateEquiv_symm_comp`, `Adjunction.comp`, and the unrelated
  scheme-module pullback conjugacy theorem. No exact full-node match.
* `rg` of both `lean/WeilConjectures` and `lean/Sheaf`, for the item id and normalized-mate
  names, plus `rg` of `dag/lean_names_upstream.json` for every new declaration prefix and
  the required `grep -rn` of the item id in WeilConjectures, found no module for
  the item and no conflict for any new full declaration name.
* The broader `etaleSumRightAdjoint` search found
  `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence`. Its composition/identity clauses
  overlap parts of the item, but its B and its open-restriction statement are only at
  `constantComplex A X`. It does not state arbitrary-input B-pasting or the conditional
  normalization for every K, and is a downstream consumer in the DAG. We did not import
  it or duplicate its named definitions; rho is written by the existing conjugacy API,
  and B is the required general right mate at arbitrary fixed compactifications.

### Edge cases and validation

Checked directions and types for identity e,v,w,z; c=d comparisons; empty U; a zero
coefficient ring; K=0; and an arbitrary unbounded K. Identity arrows are included without
extra properness assumptions on e or finite compactification factors. For a two-sheet etale
fold, the sum counit folds the two summands and its compositor nests summands, which checks
that rho and c use the indicated inverse/conjugate directions. The base-change maps w,z
are not assumed flat or etale. No assertion that a general right mate preserves
invertibility is used. The constructed C is invertible by the existing proper-base-change
result, then its inverse has a well-defined mate; B itself is merely a natural transformation.

`scompile.py Q48 lem-pur-etale-normalized-mates-composition-pasting <module>` compiled the
module successfully in module mode, both its sandbox form and library name
(11.2 s and 12.7 s), with no errors or warnings. Earlier feedback caught a missing proper
base-change invertibility instance, which was supplied from the published theorem, and
formatting issues, which were repaired. All eleven theorem proofs are exactly `sorry`; the helpers
are real definitions. Final dry-run results are recorded below after the prescribed gate.

## Second reading by Q48

This is a separate second pass by the same dispatched worker; the dispatcher explicitly
prohibits starting another agent, so no independent-worker review is claimed. The maintainer's
independent delivery review remains required. Reopened the node, its eight proof steps, the
existing dependency signatures, and the delivered module. Checked the finite-ring, Noetherian,
separated-etale finite-type and arbitrary-compactification binders against each theorem.
Checked all eleven clauses listed above, including the explicit rho/B square for open restriction. In particular checked the contravariant c direction,
the inverse direction for chi, the two pullback-compositor factors in B-pasting, the two
independent refinement conjugates, and the actual c/B square for restriction. The last theorem
about normalization has both antecedents rather than silently asserting either one.
The helper C uses the same proper/open exchange and canonical refinement, never an arbitrary
isomorphism. Found one inaccurate prose ordering in the refinement proof docstring; changed it
to `rho_hat = rho after t^c`, matching the displayed theorem. No Lean signature or node
statement needed a correction. No STATEMENT-DISPUTED flag remains.

The first dry run exposed one overlong docstring line introduced during the prose correction;
it was wrapped and the next dry run printed `OK (dry run)` at d25f43656b9. A final clause
review then added the explicit all-input rho/B square for open restriction (rather than
leaving that relation only as a consequence explained in the report). The final preflight
and compile are rerun for this additional statement.

The exchange helper was finally expressed directly as the canonical exact/left-derived
transport isomorphisms, `asIso` of the published proper/open exchange, and the canonical
compactification comparison. Its hom is definitionally the same transported exchange;
this removes even the structural `infer_instance` proof block from the definition. All
invertibility witnesses now come directly from named published theorems.

Final validation: the 545-line module (three real definitions, eleven sorry theorems)
compiled cleanly and `deliver2.py --no-push` printed
`OK (dry run): commit 21e8ed0c9be passes the preflight and compiles; nothing pushed`.
A structural comparison confirms only `lean` changed in the copied node; its recorded
signature matches the file verbatim, all fourteen declarations are listed, and no Lean
line exceeds 100 characters.
