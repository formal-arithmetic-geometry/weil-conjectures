# Stage-1 worker report: det-def-sfb-base-change-morphism-bc

## Files written

- `dag/nodes/sec-six-functors-basics/det-def-sfb-base-change-morphism-bc.json`: existing definition, now a Mathlib leaf via `CategoryTheory.mateEquiv`, `Mathlib/CategoryTheory/Adjunction/Mates.lean:84`; unchanged statement and statement dependencies. No new nodes.
- `citations.json`: empty list, because a definition/Mathlib leaf has no proof steps.
- `report.md`: this report. `searches.jsonl` was produced by the required search wrapper.

## Attachments

None. Searches by the exact blueprint tag, all five names in the parent blueprint's Lean list, and base-change terminology found no slopmaster2 declaration of this exact bounded-constructible condensed-coefficient definition. `AlgebraicGeometry.Etale.baseChange` and `AlgebraicGeometry.ProEtale.derivedBaseChangeMap` have different coefficient categories and ambient/bounded-below domains, so neither is attached. The analogous archived master `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleBaseChange` at `WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/MorphismDefs.lean:150` is reference material and does not supply a finished slopmaster2 attachment.

## WANTED

None. All sources needed for this definition were available locally.

## Findings and corrections

I read the current main-20261015 definition file and its parent `_section.md`, the unit record `dag/units/sk-def-sfb-base-change-morphism.json`, the chapter record, the three dependency statements, and the relevant archived master construction. The item is a detailed definition, not the unit's key node: it does not require altering the maintainer-owned unit realization. No statement dispute or route change was necessary. No SGA source was used.

The first search phrasing found generic derived-adjunction declarations. A second phrasing found the exact generic construction `CategoryTheory.mateEquiv`. I read its variables, signature and definition in `Mathlib/CategoryTheory/Adjunction/Mates.lean:59-122`. Take its categories C, D, E, F to be respectively D_cons(Y,Lambda), D_cons(X,Lambda), D_cons(Y',Lambda), D_cons(X',Lambda), its vertical functors G and H to be Lg* and Lg'*, its adjunctions to be those for f and f', and its input square to have natural transformation theta_sq.hom. Its output natural transformation is exactly the item. The definition at lines 85-92 inserts the unit for f', transports by theta at Rf_*, and contracts the counit for f; intervening associators and unitors only express parentheses in Lean's diagrammatic composition order. This is a one-line specialization, with no additional theorem about geometry, coefficients, or restrictions, so the item is a Mathlib leaf.

The blueprint and whole-DAG searches found the parent `sk-def-sfb-base-change-morphism`, whose statement includes exactly this construction together with the pullback comparison. It is recorded in `blueprint.same_as`; no duplicate is created. The imported `blueprint.from` stays null. The adjunct characterization is a separate later assertion depending on this definition; it is neither used nor duplicated.

Two initially recorded search results needed correction: supplying `Mathlib` as the wrapper's subdirectory searched a nonexistent `Mathlib/Mathlib`, and a LeanSearch result list was paired with the other LeanSearch phrasing. I regenerated all records from the actual wrapper log, retaining exact query texts and the first names returned, and reran grep under the correct `CategoryTheory` and `CategoryTheory/Adjunction` directories. The invalid-directory and unknown-identifier attempts are explicitly marked as unusable, not evidence of absence. The successful grep locates `mateEquiv` at line 84. No search was invented.

## Unfinished work

None for the item. The referenced definitions retain their existing project states. No Lean was written or compiled, no git command was run by this worker, and no delivery was pushed.

## Not duplicates

No new node pairs exist. The existing parent blueprint overlap is recorded in `same_as` and is not a new dependency.

## Review by Q31

I checked the source's whole definition and its hypotheses, not only the displayed formula. `det-def-sfb-base-change-morphism-comparison` states the commutative square, the restricted pullbacks and the natural isomorphism theta from Lf'^* Lg^* to Lg'^* Lf^*. `def-sfb-dc-lower-star` defines Rf_* as the restriction when the ambient direct image preserves bounded constructibility. I use that assumption for f and f', rather than inferring constructibility from the definition itself. `def-sfb-dc-upper-lower-adjunction` explicitly supplies the restricted adjunction, with the ambient Hom bijections; its unit and counit are therefore available. Each dependency says precisely the data required by the statement. No preservation theorem is proved or silently assumed for arbitrary coefficients, and no ordinary etale category is identified with the condensed module-object category.

For an object K in D_cons(X,Lambda), put A = Lg^* Rf_* K. The unit has type A -> Rf'_* Lf'^* A. Applying Rf'_* to theta at Rf_* K reaches Rf'_* Lg'^* Lf^* Rf_* K, and applying Rf'_* Lg'^* to epsilon_K reaches Rf'_* Lg'^* K. All intermediate objects lie in the stated categories by the restricted-functor hypotheses. Whiskering and composition of these natural transformations give naturality; Mathlib's mate definition supplies exactly these operations, so there is no unproved extra naturality lemma. There are no proof steps to cite: the three data are statement dependencies, and `citations.json` is correctly empty.

I tested identity and zero cases as type/sanity checks. With identity functors and identity comparisons the expression reduces to the identity by the adjunction triangle identity; on a zero input it is the unique map between zero objects. A commutative square that is not cartesian still supplies theta, so the construction remains defined, with no claim of invertibility. Empty schemes cause no additional condition because the same categorical formula applies. No finiteness, smoothness or properness condition on the square is added. The f and f' adjunctions are used in the correct order, and theta is used in the forward direction prescribed by the source.

Against delivery-errors B–E: there are no new statements, undeclared notions, hidden child proofs, duplicate children or clauses relabelled as lemmas. The source statement and single-escaped TeX are preserved. The Mathlib match records the exact file, line, all category/functor substitutions and the formula read in the source. No step borrows a dependency's proof or asserts a theorem from a definition, no new dependency creates a cycle, and no off-unit proof tool or alternative route is introduced. I corrected the metadata and search accounting described above; the mathematical statement did not change.

## Second reading by Q31

- Item statement: checked against blueprint node `det-def-sfb-base-change-morphism-bc` and the
  parent unit statement; all square, coefficient, restricted-functor, unit/counit, source and
  target hypotheses and the non-cartesian clause agree.
- Dependency `det-def-sfb-base-change-morphism-comparison`: its square and comparison
  transformation supply exactly the input `theta_sq` used by the definition.
- Dependency `def-sfb-dc-lower-star`: its preservation hypothesis supplies the restricted
  pushforwards for both `f` and `f'`; no preservation claim is added.
- Dependency `def-sfb-dc-upper-lower-adjunction`: its restricted adjunctions supply exactly
  `eta'` and `epsilon` in the displayed composite.
- Proof steps: none; this is an existing definition recorded as a Mathlib leaf, so there are no
  hidden proof steps or citations to audit.
- New nodes: none; no child node was created, and consequently there are no new-node statements
  or proof dependencies to check.
- Mathlib leaf: reread `CategoryTheory.mateEquiv` in
  `Mathlib/CategoryTheory/Adjunction/Mates.lean:59-122`; with the four categories, two
  adjunctions, vertical functors, and `theta_sq.hom` substituted, its `toFun` is the unit,
  comparison, and counit composite in this item. The recorded searches and declaration metadata
  are accurate.
- Edge cases: identity and zero functors give the expected identity and zero maps; empty schemes
  and non-cartesian commutative squares remain within the definition, with no invertibility claim.

Changes made in this second reading: appended this source-by-source audit only; the statement,
dependencies, Mathlib attachment, citations, and search records required no repair.
