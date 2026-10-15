## What changed

Proved `exists_derived_adjunction_compatibility` in
`lean/Sheaf/CategoryTheory/DerivedCategory/DerivedAdjunctionCompatibility.lean`, preserving
its complete signature and every original public import. All new helpers are private and proved.

The proof establishes absoluteness from the essential-constancy witnesses, then applies
Mathlib's `CategoryTheory.Adjunction.derived`. For pro-systems it uses the existing, proved
`CategoryTheory.leftDerived_defined_pointwiseKan_bridge`. For ind-systems it proves the dual
fraction/cocone construction locally, including independence of representatives, the colimit
universal property, and preservation by an arbitrary functor. Essential surjectivity and
pointwise Kan-extension uniqueness transfer this to the supplied derived functors. The
representative formula follows from `Adjunction.derivedη_fac_app`, naturality of beta,
and the unit formula for the underived Hom equivalence.

Added proof imports of `Mathlib.Algebra.Homology.DerivedCategory.Fractions`,
`Mathlib.CategoryTheory.Functor.Derived.Adjunction`,
`Mathlib.CategoryTheory.Functor.KanExtension.Preserves`, and
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge`.
Updated only `proof`, `proof_deps`, and `proof_origin` of
`new-derived-adjunction-compatibility` to record this route.

Validation: the unchanged theorem and all helpers compile with no warnings through
`lcompile.py`; `#print axioms exists_derived_adjunction_compatibility` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The new library import passes
`tools/import_direction.py may`. No definitions with proof holes, new axioms, public
helpers, signature changes, or adapted modules were introduced.

## Proved and sorry left

Closed: `exists_derived_adjunction_compatibility`
(node `new-derived-adjunction-compatibility`): 1 of 1 original holes proved.
Added: no holes. Remaining in the delivered module: none. Split off: none.
The axiom audit confirms that the proof does not rely transitively on `sorryAx`.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.
The following is the complete list of project modules removed from this item's
transitive import closure by the change:

- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
  (`lem-pc-pre-derived-adjoint-functors-general`).
- `Sheaf.CategoryTheory.DerivedAdjunctionHomDiagram`
  (`def-pc-derived-adjunction-hom-diagram`).
- `Sheaf.CategoryTheory.DerivedAdjunctionSourceColimit`
  (`lem-pc-derived-adjunction-source-colimit`).
- `Sheaf.CategoryTheory.DerivedAdjunctionTargetColimit`
  (`lem-pc-derived-adjunction-target-colimit`).

These are no longer proof dependencies of this item; other importers may still need them.
The original node's statement-dependency fields are preserved. Both essential-constancy
predicate modules remain public statement dependencies. The proved pointwise pro/Kan bridge
is the sole new project module in this item's transitive import closure.
No UNIT statement or step is bypassed: `sk-thm-picard-duality.realized` contains no node
realized by this item; this is an alternative proof below the UNIT level.

## Where the brief, the DAG or earlier work was wrong

No statement was false or unusable. The old proof plan required assembling the pointwise
pre-derived equivalences, but this is unnecessary: essential constancy supplies the
absoluteness hypotheses for the existing Mathlib derived-adjunction theorem. Earlier searches
correctly observed that Mathlib requires these extra hypotheses; this delivery proves them.
The original theorem docstring is preserved as documentation of its source proof; the updated
DAG and the private helpers describe the implemented alternative route.

Source comparison: [Stacks 05PU](https://stacks.math.columbia.edu/tag/05PU) gives precisely
the retraction/common-stage equations used in both preservation arguments;
[Stacks 05SA](https://stacks.math.columbia.edu/tag/05SA) supplies the denominator-comparison
context. [Stacks 09T5](https://stacks.math.columbia.edu/tag/09T5) is the derived-adjunction
claim. The pointwise bridge and Mathlib constructor were read in full before use.
The sources are not materialized in this shared checkout, so these tags were read on the
Stacks website. The local source library and Mathlib were searched first with rg, LeanFinder,
Loogle, and the prescribed grep search. LeanFinder identified `Adjunction.derived`; the
other searches did not find a direct theorem discharging its absoluteness assumptions.

Edge cases: the split equations supply an actual denominator stage, so no empty indexing
category is silently assumed inhabited. No nonzero object, exact functor, injective/projective
resolution, size equality between categories, or restriction to a bounded subcategory is
used. The zero/identity-functor cases obey the same equations. All category and derived-category
universes in the original signature remain independent and unchanged.

## Second reading by N3

1. **Interface and scope: pass.** I read the entire delivered module and compared it with
   the repository version using `diff`. The complete text from
   `theorem exists_derived_adjunction_compatibility` through its conclusion, before `:= by`,
   is byte-for-byte identical. This includes the six universes, additive abelian-category
   setting, both essential-constancy hypotheses, both supplied comparison transformations,
   their derived-functor properties, and the representative equation for every `M`, `K`,
   and `f`. Every original public import is unchanged. The only added declarations are
   private, proved helpers, including an explicitly constructed inverse-denominator functor.
   There are no adapted modules or statement/definition changes. The existing node differs
   only in `proof`, `proof_deps`, and `proof_origin`.
2. **Proof and axioms: pass.** Fresh single-file compilation and `--all` compilation both
   passed without warnings (about five seconds each). I compiled a fresh scratch copy
   containing `#print axioms` for the public theorem and all seven private helpers; every
   axiom set is exactly `propext`, `Classical.choice`, and `Quot.sound`. A scan of the source found no
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or kernel-check bypass.
   The choices of fraction representatives use Mathlib's proved localization theorem;
   the essential-constancy witnesses are local hypotheses inside proofs. No data is selected
   from an unproved existence theorem. I checked the ind common-refinement orientation,
   cocone naturality, denominator leg formula, retraction-based descent and uniqueness,
   preservation by an arbitrary functor, and the final unit/beta naturality calculation.
3. **Split statements and duplication: pass.** There are no split-off statements, added
   holes, or new nodes. I independently searched with launcher grep and LeanFinder for
   essential-constancy and preservation of filtered colimits, and searched Mathlib and the
   upstream category-theory sources for essentially constant/absolute Kan results.
   The search found Mathlib's eventually-constant diagrams, which require eventual
   invertibility of transition maps; this is stronger than the retraction/factorization
   hypotheses here and does not replace the argument. I read the actual pro/Kan bridge
   statement and proof, the essential-constancy definitions, and Mathlib's derived-adjunction
   constructor and its unit factorization. The supplied split stage rules out an empty
   denominator system without adding an assumption; zero objects and identity functors
   need no exception. Category universes remain independent.
4. **Route and pruning: pass.** The proof first establishes the extra preservation
   hypotheses required by Mathlib's `Adjunction.derived`; it does not assume absoluteness.
   The pro argument uses the already proved bridge. The ind argument constructs the dual
   comma colimit directly. Essential surjectivity and pointwise Kan uniqueness apply to the
   given derived functors, and the formula uses their actual `alpha` and `beta`.
   I read [Stacks 05PU](https://stacks.math.columbia.edu/tag/05PU),
   [05SA](https://stacks.math.columbia.edu/tag/05SA), and
   [09T5](https://stacks.math.columbia.edu/tag/09T5): the split/common-stage equations have
   the stated orientations and 09T5 has the claimed derived adjunction.
   All four added imports are plain proof imports and supply declarations or instances
   used by this proof. A scratch compile removing `KanExtension.Preserves` failed at its
   preservation classes, constructors, and composite derived instances, confirming its use.
   I independently recomputed both transitive project import closures: the four removed
   modules and sole added bridge module are exactly those reported above. The sole old
   proof dependency removed is `lem-pc-pre-derived-adjoint-functors-general`, also listed
   above. The unit `sk-thm-picard-duality` has empty realized statement and step lists;
   this proof bypasses no realized unit node. No global unreachability is claimed.
5. **DAG agreement: pass after documentation repair.** I read the statements of the
   fraction-representation/equality leaves, the pro/Kan bridge, the quasi-isomorphism
   multiplicative-system leaf, and the derived-adjunction leaf. The first two proof steps
   describe the private pro and ind preservation arguments; the third describes their
   transfer to arbitrary Kan extensions; the fourth constructs the derived adjunction.
   I added the missing explicit citation of
   `lem-pc-quasi-isomorphisms-multiplicative-system` in Step 3, since the final specialization
   uses its two calculus instances. The existing derived-adjunction leaf states a counit
   formula, so it alone does not justify the unit calculation in Step 5. I made Step 5
   explicitly identify and apply Mathlib's `derivedη_fac_app`, followed by naturality and
   functoriality, and marked that short calculation elementary. The constructor citation
   remains for the adjunction being computed. `proof_deps` is the union of the steps'
   `uses`, and `proof_origin` describes the implemented route. No node statement changed.

Second-reading changes: repaired these two DAG documentation points and appended this
review. The Lean proof and imports required no repair. Closed one original hole, added
zero holes, split off zero statements: this delivery is a proof, not a decomposition.
