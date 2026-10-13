## What changed

Proved `AlgebraicGeometry.Scheme.singletonProduct_affine_ring` in
`Sheaf.AlgebraicGeometry.EtaleAffineSingletonProductRing`, with its original statement
and visibility unchanged. The proof realizes the product as a wide pullback and compares
two ring colimits. Private, completely proved constructions establish the indexed tensor
power's colimit property using the existing `PiTensorProduct.liftCommAlgHom` and
`PiTensorProduct.algHom_ext`; no intermediate result is left unproved.

Replaced the public normalization-module import with the statement's actual prerequisites:
`Mathlib.AlgebraicGeometry.Morphisms.Etale` and
`Mathlib.RingTheory.PiTensorProduct`. Proof-only imports are
`Mathlib.CategoryTheory.Limits.Constructions.Over.Products`,
`Mathlib.AlgebraicGeometry.Limits`, and
`WeilConjectures.Mathlib.RingTheory.PiTensorProduct`.
The existing DAG node now records the actual universal-property proof and no proof-node
dependencies. No existing declaration's type or definition changed. The two direct
importers, `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeKernel` and
`Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorSectionsSpan`, independently publicly
import the normalization module, so removing its re-export requires no adaptation.
The import-interface change is recorded in
`coord/changes/singletonProduct_affine_ring_imports.md`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.singletonProduct_affine_ring`
(node `new-etale-affine-singleton-product-ring`). Added zero holes. There are no `sorry`s
in the delivered module or in any added declaration. This is a complete proof, not a
decomposition. All private constructions are proved from Mathlib and the already-proved
source tensor-product homomorphism lemmas.

Local compilation through `lcompile.py` passes without warnings. The delivery dry run
checks the axioms of the delivered declarations. The argument includes the one-factor
case `n = 0`, empty affine schemes, and zero rings; it never assumes a covering,
nonemptiness, faithful flatness, or positive dimension.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization`.
Neither its comparison predicates nor its tensor-section complexes are used by this ring
calculation. Its existing DAG statement-reference field is preserved.

Pruned proof dependency: `lem-weil-pbc-fibre-product-affine-spectra`
(the Mathlib `pullbackSpecIso` route). The binary spectrum calculation, binary induction,
and tensor associativity comparison are unnecessary: the indexed universal property is
proved directly. No planned proof dependency remains. This pruning is for this item's
proof; other targets may still use the removed module or node.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The earlier binary-induction plan is mathematically valid but
unnecessary with Mathlib's affine-limit and global-sections preservation interfaces.
The unit `sk-prop-h2` has no realized statement or step at this node; the unit route is
unchanged.

Searches: LeanFinder returned `pullbackSpecIso` and affine-limit section lemmas, but no
indexed ring comparison. Loogle found no `liftCommAlgHom` because that declaration is in
our source extension; reading `WeilConjectures.Mathlib.RingTheory.PiTensorProduct` found
the needed, already-proved lift and its factor formulas. The prescribed grep search found
no indexed-tensor colimit theorem. Local searches also found the affineness-only wide
pullback argument in `EtaleFiniteAffineCechBasis`; its covering hypothesis is unnecessary
here, so its module is not imported. The original sources were checked at
[Stacks Tag 01I4](https://stacks.math.columbia.edu/tag/01I4) and
[Stacks Tag 01JQ](https://stacks.math.columbia.edu/tag/01JQ).

## Earlier second reading (a previous round; superseded)

1. Compared the sole delivered module against the repository with `diff` and checked
   the complete `singletonProduct_affine_ring` signature byte for byte. Verdict: the
   original scheme, étale objects, morphism, affineness hypotheses, all three algebra
   instances, index `Fin (n + 1)`, linear equivalence, and projection formula are
   unchanged. Only private helpers were added; their variables end before the theorem.
   The public-import change has its change record. The direct importers are
   `EtaleAffineSingletonTensorDegreeKernel` and `EtaleAffineSingletonTensorSectionsSpan`.
   Both independently publicly import the normalization module and compile against the
   delivered module without adaptation.
2. Read all four private constructions and the theorem proof. `tensorCocone` explicitly
   constructs its vertex and maps; cocone compatibility supplies the algebra structure
   for `coconeAlgHom`. `tensorCoconeIsColimit` constructs the desc map via the upstream
   lift, proves both base/factor identities, and proves uniqueness via algebra-hom
   extensionality. The final equivalence comes from two proved colimit properties,
   with the base identity checking scalars and factor identities checking projections.
   No data is selected from an unproved existence result. Local compilation is clean;
   a scratch copy with `#print axioms` for the public theorem reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. There are no
   `sorry`s or prohibited declarations in the delivery. Verdict: a complete proof.
3. No statement was split off, no hole added, and no public intermediate declaration
   introduced. Read the already-proved upstream `liftCommAlgHom`, its factor and pure
   tensor formulas, and Mathlib `algHom_ext`; searched both Lean roots and the indexed
   tensor file for an existing indexed colimit/ring comparison. Verdict: the private
   universal-property argument uses existing tensor APIs without duplicating an open
   result. Its argument also works for an empty finite index; the theorem's one-factor
   case `n = 0` and zero rings impose no extra assumptions.
4. Read Mathlib `Scheme.isAffine_of_isLimit` and `preservesLimit_rightOp_Γ`: each needs
   precisely affine diagram vertices, supplied by `hU` and `hW`. The product becomes
   a finite connected wide pullback, whose forgetful functors preserve its limit.
   Direct indexed tensor universality avoids binary induction and associativity
   identifications. The old `proof_deps` contains only
   `lem-weil-pbc-fibre-product-affine-spectra`, already listed under No longer needed;
   the removed normalization import is listed there too. Read `sk-prop-h2.json`:
   its realized statement and step lists do not contain this node. Verdict: complete
   pruning list and unchanged unit route.
5. Compared the original and delivered node JSON. Only `proof`, `proof_deps`, and
   `proof_origin` changed; the three proof steps match, respectively, the preserved
   geometric cone, the constructed tensor colimit, and the section colimit comparison
   with its scalar/projection identities. No new node is needed. Verdict: DAG agrees
   with Lean, with no remaining planned proof dependency.

Second-reading repair: changed `Over.Products` from `public import` to plain `import`.
A statement-only scratch module compiles without that direct import, proving its
public exposure unnecessary; only the proof uses its cone equivalence. Updated the
import change record and report accordingly. The existing theorem docstring describes
its original valid binary-induction plan rather than the implemented direct argument;
its replacement proof description is recorded above and in the DAG, while the existing
docstring is preserved under the Lean skill's existing-docstring rule.

## Second reading by C1

1. Compared the delivered module with the repository version. The public theorem signature and all existing declarations are byte for byte unchanged; only imports, private helpers, and the theorem proof differ. The import change is recorded in `coord/changes/singletonProduct_affine_ring_imports.md`. Verdict: pass.
2. Compiled the delivered module with `lcompile.py`; it succeeds without errors or warnings. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`. The public theorem uses only the permitted foundational axioms, as checked in the scratch axiom file. Verdict: pass.
3. Searched the library and Mathlib for an existing indexed tensor colimit or equivalent ring comparison. None duplicates the private construction; no statement was split off and no new hole or node was added. The tensor cocone universal property is proved using existing `liftCommAlgHom`, its factor formula, and `algHom_ext`. Verdict: pass.
4. Checked the proof route and pruning. The finite product is handled through the over-product cone equivalence, preservation of limits, affine-limit global sections, and a direct indexed tensor universal property. This covers the one-factor and zero-ring cases. The removed normalization import and old fibre-product proof dependency are listed under `No longer needed`; the unit route remains unchanged. Verdict: pass.
5. Compared the delivered DAG node with the Lean proof. Its three proof steps describe the affine limit, tensor cocone, and global-sections colimit comparison; `proof_deps` is empty because all dependencies are Mathlib or private constructions. Verdict: pass.

Changed only this report section to satisfy the required second-reader record; no Lean or DAG repair was necessary.
