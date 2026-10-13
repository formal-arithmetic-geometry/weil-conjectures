## What changed

Proved `CategoryTheory.localizedHomComplex_nullHomotopy_iff_boundary` in
`Sheaf.Algebra.Homology.LocalizedHomComplexBoundaries`, with its signature and
existing docstring unchanged. Added the proved private additive equivalence
`localizedSectionEquiv` and its proved composition compatibility
`localizedSectionEquiv_map`. These package the definitional comparison between
internal-Hom sections and restricted sheaf-module morphisms once, avoiding
repeated expensive elaboration of restriction wrappers.

The degree-minus-one differential is evaluated using `homComplex_exists`.
A null-homotopy assembles through the evaluated product fan, and joint
injectivity of the degree-zero projections and of the cycle inclusion proves
it is a boundary. Conversely, a boundary gives the component formula for
Mathlib's `Homotopy.nullHomotopicMap'`; `Homotopy.nullHomotopy'` supplies its
null-homotopy. Added proof-only imports of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` for preservation of products
and `Mathlib.Algebra.Category.Grp.EpiMono` for injectivity of a monomorphism.
Updated the existing node's proof and proof origin to describe this Lean argument;
its statement, statement dependencies, and proof dependencies are unchanged.

Searches: LeanFinder found Mathlib's null-homotopy constructors; Loogle checked
`Homotopy.nullHomotopic` (no matching identifier); grep searched the repository
for localized boundary comparisons and Mathlib for product and cycle-inclusion
APIs. No existing localized equivalence supersedes this proof. The unit record
`sk-def-sf-operations` has no realized steps affected by the change.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.localizedHomComplex_nullHomotopy_iff_boundary`
(node `lem-pur-localized-hom-complex-boundaries`). No holes were added or split off.
There are no remaining `sorry`s in the delivery. The private equivalence and
compatibility lemma are fully proved. This is a proof, not a decomposition.
Local single-file compilation passes with no errors or warnings.

## No longer needed

None. No original imports, nodes, or modules were removed. The proof uses the
existing dependency `def-pur-hom-complex`, following the planned route.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. Repeated direct conversions from
internal-Hom sections to restricted sheaf maps caused preliminary versions to
exceed the compilation limit. Packaging that conversion as a proved private
additive equivalence resolved the elaboration cost without changing any
existing definition or statement and without splitting the file.

## Second reading by S4

1. Interface: PASS. Compared the complete delivered module with the repository
   version and checked the existing theorem signature and docstring byte for
   byte: both are unchanged. The only Lean additions are two private, proved
   implementation helpers, two proof-only imports, local elaboration options,
   and the proof replacing the original `sorry`. No definition used by the
   theorem or any other module was changed; no change record is required.
2. Proof: PASS. Independent single-file compilation completed without errors
   or warnings (39.3 s). A scratch copy with `#print axioms
   CategoryTheory.localizedHomComplex_nullHomotopy_iff_boundary` compiled
   (41.7 s) and reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
   The delivered source contains no `sorry`, forbidden declaration form, or
   hollow definition. The private additive equivalence constructs its maps
   explicitly; the section lifted from the product is constructed by its
   universal property, rather than chosen from an unproved existence theorem.
3. Split statements: PASS, none. No new holes, public statements, modules or
   nodes were introduced. Read both helpers: the section equivalence wraps and
   unwraps the same presheaf morphism, and its composition equation is checked
   componentwise. The degree-minus-one sign gives a sum in both directions.
   Zero complexes and zero differentials introduce no extra assumptions, and
   the product uses every integer degree, so unbounded complexes are covered.
4. Route and pruning: PASS. Searched the repository for boundary/homotopy
   comparisons and the upstream internal-Hom restriction API; also ran msearch
   grep with `nullHomotopicMap|homObj.*over|homObj.*equiv`. Mathlib supplies the
   constructors already used in this proof, but no direct equivalence for this
   specified localized section complex. The newer canonical section comparison
   is downstream of this item through RhomIntoKInjectiveLocal, so importing it
   would not give an independent shorter route. The proof needs the existing
   HomComplex dependency, the restriction and homotopy APIs, the abelian-group
   cycle construction, product preservation, and injectivity of monomorphisms.
   Both added imports are correctly proof-only. No original proof dependency
   is unused; `No longer needed: None` is complete. The unit
   `sk-def-sf-operations` has empty realized statement/step lists and is unchanged.
5. DAG: PASS. Compared the node JSON with the repository version: only `proof`
   and `proof_origin` differ. Each proof step matches the Lean argument; the
   proof-dependency union remains exactly `def-pur-hom-complex`. The statement,
   statement dependencies, source, unit, and Lean signature record are unchanged.

Second reading changed only this report, adding the independent checks above.
No repair of the Lean proof or node was needed. Closed one original hole,
`CategoryTheory.localizedHomComplex_nullHomotopy_iff_boundary`; added zero holes,
split off zero statements, and pruned no nodes or modules.
