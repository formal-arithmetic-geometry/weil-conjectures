## What changed

Reduced `AlgebraicGeometry.ProEtale.productExchangeCounitCoordinates` to three specified-map
comparison lemmas, retaining its complete statement. Proved the geometric conjunction from
finite-type/Noetherian stability. Proved both open-counit identities by a single adjunction
Hom equivalence and inverse cancellation. Proved the counit square by mate naturality at
beta inverse, horizontal exchange factorization, inverse cancellation, the second counit
identity and counit naturality. These computations are complete private proofs; none contains
sorry. The new comparison lemmas are strictly smaller parts of original Steps 3--8.

Moved the 23 concrete coordinate instances, definitions and predicates verbatim into
`Sheaf.Paper.ProductExchangeCoordinateDefinitions`, publicly reexported by the original
module, so comparison lemmas can state their equations without an import cycle. No data,
name, signature, attribute or visibility changes. No source-library module is changed.
Change record: `coord/changes/B6-product-exchange-coordinate-definitions.md`.

Validation: all five modules compiled through lcompile.py; after the final associativity
repair the item compiled cleanly in 30.8 seconds with no warnings. No development profiler
options remain. The main signature and the 23 moved declaration blocks were checked
byte-for-byte against the original, and every original public import remains available.
The delivery tool performs the final packet and server preflight checks.

## Proved and sorry left

Closed the one hole in `AlgebraicGeometry.ProEtale.productExchangeCounitCoordinates`
(node `lem-pur-product-exchange-counit-coordinates`) by decomposition, not a net proof.
The delivered item contains zero sorry. Added three holes:

- `AlgebraicGeometry.ProEtale.ProductExchangeCoordinates.productOpenAdjunctionNormalization`
  (`lem-pur-product-open-adjunction-normalization`): identify sectionwise restriction with
  actual exchange, the actual proper/open adjunct and restriction of the open counit.
- `AlgebraicGeometry.ProEtale.ProductExchangeCoordinates.productHorizontalExchangeFactorization`
  (`lem-pur-product-horizontal-exchange-factorization`): horizontal factorization of B0.
- `AlgebraicGeometry.ProEtale.ProductExchangeCoordinates.productCompositionCoordinateComparison`
  (`lem-pur-product-composition-coordinate-comparison`): the compatible-tower comparison
  in the explicit product compactifications, transported to the witnessed object.

Thus one upper hole closed, three lower holes added, net minus two. The coordinate definitions
contain no holes, and no hole is moved into a definition. Geometry and both counit identities
and the counit square have real Lean proofs from the stated normalization equations.

## No longer needed

Removed the unused private `Sheaf.AlgebraicGeometry.ProperStability` import: proper base
change and composition are instances of Mathlib. Removed the direct private
`Sheaf.Paper.RelativeCompactSupportPasting` import from the item: the new horizontal
factorization node records the dependency for its remaining proof. The definitions now publicly import
`Sheaf.Paper.ProEtaleCompositionTowerDefinitions`, because only its constructions are needed;
`ProEtaleCompositionTowerNormalization` is the recorded proof dependency for the remaining
composition comparison. The sorry-only new statements import only what their signatures need.
The original module retains its public tower-normalization import; all other original public
dependencies remain reexported by the definitions module.

No module is withdrawn. No blueprint unit step is bypassed. The following old direct proof
dependencies are no longer direct dependencies of the item, but remain needed by its
coordinate definitions or new comparison lemmas: `def-exchange-projection`,
`def-pc-fibre-product`, `def-weil-open-immersion`, `def-weil-pbc-proetale-operations`,
`def-weil-proper-morphism`, `lem-exc-proetale-derived-open-restriction`,
`lem-pur-relative-compact-support-pasting`, `lem-sf-open-tensor-normalization`,
`lem-sf-proper-open-tensor-compatibility`, `lem-trf-proetale-composition-tower-normalization`,
`lem-weil-derived-direct-image-composition`. `lem-kun-proper-stability`,
`lem-weil-pbc-locally-noetherian-quasi-separated`, `lem-weil-pbc-qc-open-immersion-finite-type`
and `lem-weil-pbc-qcqs-morphism-permanence` are not needed for the delivered geometry proof:
Mathlib stability instances and quasi-compactness of open immersions into locally Noetherian
schemes suffice. This does not assert those modules are unused by the rest of the library.

## Where the brief, the DAG or earlier work was wrong

The original Step 5 says the tensor-compatibility theorem supplies its open-adjoint
normalization. The Lean theorem `properOpenProjectionMate` states a tensor equation;
its docstring explains the desired normalization, but the equality is not a conclusion
of its public signature. Likewise `proEtaleDerivedOpenRestriction` states invertibility
of its intrinsically transported comparison, not equality of the independently defined
fixed-coordinate rho with actual derived exchange. The new normalization statement
isolates exactly those comparisons rather than treating the docstrings as Lean lemmas.

The tower theorem uses a restricted upper compactification, whose scheme is a chosen
pullback. It is not definitionally the explicit product chosen here. Identifying these
compactifications and their canonical comparisons, and transporting along the etale-origin
witness, is genuine remaining work and is recorded in the composition comparison lemma.
The horizontal-pasting theorem likewise uses ordinaryG/mate normalization, which must be
compared with the total-pullback coordinates used by A0/B0/beta.

Searches used leanfinder, loogle, leansearch and Mathlib/project rg. Generic Hom-equivalence
naturality and counit lemmas are enough for the completed categorical assembly; none of
the search results identifies the independently specified geometric comparison arrows.
New statements checked on identity compactifications, empty schemes and zero derived
objects. Every inverted arrow is an open unit, beta or rho; no proper exchange or
proper/open mate is asserted invertible on arbitrary inputs.

## New nodes

`def-pur-product-exchange-coordinate-data` attaches the 23 existing concrete coordinates
to their new module; every moved declaration is unchanged and publicly reexported.

`lem-pur-product-open-adjunction-normalization` isolates original Steps 3 and 5 and the
naturality/open-unit equation of Step 6. Both explicit counit formulas are derived from
these equations by the completed private adjunction proof.

`lem-pur-product-horizontal-exchange-factorization` isolates original Step 4. Its equation
is used with mate naturality and the proved counit identity to prove the square in Step 7.

`lem-pur-product-composition-coordinate-comparison` isolates original Step 8 with an
etale-origin predicate on Q; it does not include geometry or any exchange/counit identity.
The original theorem simply supplies its retained witness and established Noetherian data.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
