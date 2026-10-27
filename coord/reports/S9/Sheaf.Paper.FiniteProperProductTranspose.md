## What changed

Repair of returned delivery `1cd1c0d5045`, passed by C-1cd1c: the landing
failed before merging because the reviewer override used
`S9-finite-proper-product-construction-module.md`. The landing interface
maps the delivered change record to the override name
`S9-finite-proper-product-construction-module.change.md`
(`tools/batch_land.py:fixes`). The change record now explicitly documents
its repository path and accepted override name, preventing that naming
mismatch from being repeated. No reviewer correction file was supplied
with the return, and no mathematical correction was requested. The retained
Lean files were compared with current shared sources: the existing leg
module still differs by exactly its required one-line import adaptation.
The delivery tool rebuilds this packet on current `sheaf-dag`.

Replaced the one sorry of `WeilConjectures.FiniteProperProduct.finiteProperProductTranspose`
by the explicit six-clause argument. The existing ordinary leg-transpose theorem supplies
the first two clauses. Abstract adjunction composition and conjugation calculations give
the two compositor clauses. The tensor normal form supplies the third clause, and
inverse-Hom injectivity, the transport calculation and evaluation symmetry give the last.
The original statement is unchanged.

Extracted the construction declarations, with identical names and bodies, into
`Sheaf.Paper.FiniteProperProductMaps`, publicly reexported from the item. The three
aliases tensor, pull and push now use `def` instead of `abbrev`, with unchanged bodies,
so local irreducibility can prevent expansion of the concrete derived models.
The functors and product maps have explicit result types naming the intended
categories and source/target objects, with the same data bodies; this avoids
repeated comparison of model-specific inferred result types in specializations.
Added names for pairEvaluation, swapStructure and swapPull; these are actual constructions.
The proved objectwiseComparison_naturality and its associated construction expose
the object components of the equality comparison in swapPull. This is the same
canonical comparison, presented so the kernel does not expand concrete derived
functors to compare a natural-transformation cast with its object cast.
Changed the one public construction import in the leg-transpose module to avoid the
cycle introduced by using its existing theorem. This module is held by A5; its signature,
visibility and theorem body are unchanged. The unchanged original would form the cycle
FiniteProperProductTranspose → OrdinaryDerivedProductLegTransposes →
FiniteProperProductTranspose. This is the only forced line in that module.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.FiniteProperProduct.finiteProperProductTranspose`
(node `lem-pur-finite-proper-product-transpose`), by decomposition into named strict
substeps and real Lean adjunction calculations. This is a decomposition, not a proof
without sorry dependencies.

Added three holes:

- `WeilConjectures.FiniteProperProduct.finiteProperCompositorMate`
  (`lem-pur-finite-proper-compositor-mate`): equality of the specified intrinsic
  direct-image compositor with the conjugate pullback compositor.
- `WeilConjectures.FiniteProperProduct.finiteProductNormalForm`
  (`lem-pur-finite-product-normal-form`): tensor evaluation composition for arbitrary
  evaluation arrows, with no direct image or exchange.
- `WeilConjectures.FiniteProperProduct.finiteProductEvaluationSwap`
  (`lem-pur-finite-product-evaluation-swap`): symmetry of arbitrary tensor evaluation
  arrows, with no direct image, exchange, projection or adjunction counits.

The adapted existing theorem
`WeilConjectures.FiniteProperProduct.ordinaryDerivedProductLegTransposes`
(`lem-pur-ordinary-derived-product-leg-transposes`) retains its existing one sorry.
No sorry occurs in a definition or private helper. The item itself has zero holes. The new theorem
`WeilConjectures.FiniteProperProduct.finiteProperTransportTranspose` is proved
without a local sorry, from the specified compositor-mate dependency; its single-file
compile completed in 15.4 seconds.

Validation: `lcompile.py --all` compiled all seven Lean modules with exit code 0.
The original target signature was compared verbatim after whitespace normalization,
and the A5 adaptation was checked to be exactly its one public-import change.

## No longer needed

The target proof does not directly use the fixed-scalar composite or isomorphism
transport theorems. Their concrete scalar presentation differs from the intrinsic
one used in the item. The intrinsic compositor-mate node records the needed
normalization bridge, and the generic triangle calculation proves transport from it.
Thus `lem-pur-ordinary-derived-composite-transpose` and
`lem-pur-ordinary-derived-isomorphism-transport-transpose` are removed from the item's
immediate proof dependencies; the former remains a dependency of the new compositor
node. No withdrawal or source-library declaration removal is requested.

Removed private imports of `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition` and
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage` from the item/construction
extraction where no declaration directly uses them. Their upstream modules and
other consumers remain. No whole module is claimed pruned from the targets' closure. Removed the obsolete
item-level tool_uses entries `lem-pur-proetale-constant-ring-composition`,
`lem-sfb-ringed-derived-monoidal-comparisons` and
`lem-weil-proetale-isomorphism-inverse-image`; none is used by the new upper proof.

## Where the brief, the DAG or earlier work was wrong

The prescribed leg theorem could not be imported directly because its construction
import was the item itself. Factoring the existing construction declarations resolves
this cycle without restating the leg theorem or changing its mathematical content.
The stated fixed-scalar compositor and isomorphism-transport lemmas alone do not
identify the item's transported intrinsic kappa with the intrinsic adjunction mate;
that remaining normalization is isolated as a strict lemma.

Edge checks: arbitrary zero or identity evaluation arrows are permitted in both tensor
lemmas; no arrow is inverted. Empty schemes and zero complexes impose no additional
hypotheses. The swap retains the signed symmetry, so odd shifts are covered without
dropping Koszul signs. The realization and compositor definitions remain the original
canonical constructions. The unit route is unchanged.

## Forced adaptations

`Sheaf.Paper.OrdinaryDerivedProductLegTransposes` is held by A5. Its original
line 18 is `public import Sheaf.Paper.FiniteProperProductTranspose`; the adapted
line imports `Sheaf.Paper.FiniteProperProductMaps` instead. The import-direction checker reports:
`NO: Sheaf.Paper.OrdinaryDerivedProductLegTransposes already reaches
Sheaf.Paper.FiniteProperProductTranspose; importing it from
Sheaf.Paper.FiniteProperProductTranspose closes a cycle`. The original cannot
remain because adding the prescribed leg dependency to the item creates the
import cycle FiniteProperProductTranspose → OrdinaryDerivedProductLegTransposes →
FiniteProperProductTranspose. The adaptation only redirects the construction
import; the complete theorem statement, visibility and existing proof are identical.
The construction names and data it uses are publicly reexported identically.

## New nodes

`def-pur-finite-proper-product-maps` records the extracted actual constructions and
evaluation, swap and objectwise-comparison API. It has no proof hole and adds no
choice of arbitrary data.

`lem-pur-finite-proper-compositor-mate` isolates the intrinsic normalization bridge.
It is one compatibility equality for arbitrary composable morphisms, and does not
assert any product identity. Its docstring records transport through the fixed-scalar
realization and cancellation of the realization units and counits.

`lem-pur-finite-product-normal-form` isolates the canonical tensor calculation for
arbitrary evaluation arrows. Its proof in words records naturality, composition,
bifunctoriality and cancellation of theta's inverse compositor.

`lem-pur-finite-product-evaluation-swap` isolates signed symmetry of arbitrary
evaluation arrows. Its proof in words records monoidal composition and braiding
coherence, projection equations, naturality and involutivity.

Change record: `coord/changes/S9-finite-proper-product-construction-module.md`.

`lem-pur-finite-proper-transport-transpose` records the unit/compositor transport
calculation for arbitrary s and d. Its proof uses abstract conjugation and unit
transposition, equality elimination on c=s;q, and specialization to the recorded
intrinsic functors. It is independent of products.

## Forced adaptations

### Sheaf.Paper.OrdinaryDerivedProductLegTransposes
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
