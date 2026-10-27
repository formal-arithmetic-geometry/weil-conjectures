## What changed

Repair of returned head `0a83eddf426`: removed the duplicate private lemmas
`fold_lift_iso` and `fold_sum_unit`. The summand/fold proof now imports
`EtaleProjectionSectionNormalization` with proof-only `import all` and directly uses
its proved private lemmas `etaleLiftSection_iso` and `projection_sum_unit`. Their
signatures were compared with the deleted helpers, and the import-direction check
confirms there is no cycle. Neither public statement nor definition was changed.
The parent node now records the dependency on these existing normalization helpers.

Proved `AlgebraicGeometry.Etale.etaleSheafSumFold` using the existing sum adjunction,
the explicit left Kan-extension/sheafification unit, and the triangle identities.
The summand formula and the fold formula are both checked on arbitrary local sections.

Constructed `AlgebraicGeometry.Etale.etaleSumScalarIso` in the new module
`Sheaf.EtaleCohomology.Purity.Smooth.EtaleScalarSectionNormalization`. This is an actual
isomorphism built by `Adjunction.leftAdjointUniq` from the two composite adjunctions;
its right-adjoint comparison is the specified inverse-image/restriction-of-scalars
isomorphism. It chooses no witness from an existence theorem.

Proved the scalar fold-counit square in the item's private
`foldScalarGeometricComparison_counit`. The generic iterated-mate calculation
`scalarOpenInverseMate` and the ordinary identification `ordinary_reverse_eq` are
proved private helpers reused with private `import all` from `EtaleOpenTensor` and
`EtaleProEtaleScalarMate`. Their holed public theorems are not used. The counit mate
identity and cancellation of the constructed isomorphism prove the square.
Applying `mapHomologicalComplex` gives the cochain equality. The original
`etaleSheafFoldScalar` now combines this proof with the local tensor normalization
statement for the fixed, constructed comparison.

Updated the parent node to describe this argument, and added the local normalization
node. Public signatures and existing definitions are unchanged. The unit route stays: the unit record `sk-lem-sp-reduction` and the current
blueprint exceptional-reduction Charts paragraph were checked; this is the
coefficient-compatible summation input and does not replace the smooth-purity route.
Single-file compilation of the parent succeeded with the new module's sandbox artifact.
The first full import-order check also succeeded (40.0 s for the normalization module,
34.9 s for the parent); the retained additional bridge compiled separately in 24.5 s.
The repaired packet passed the full import-order compile: 45.4 seconds for the
normalization module and 39.3 seconds for the item, exit code 0. The delivery
tool performs the final packet checks.

## Proved and sorry left

Original holes closed (2 of 2):

- `AlgebraicGeometry.Etale.etaleSheafSumFold` is fully proved.
- `AlgebraicGeometry.Etale.etaleSheafFoldScalar` has a complete combining proof.

Holes added (1):

- `AlgebraicGeometry.Etale.etaleSumScalarIso_tensorSections`, node
  `lem-sp-etale-scalar-section-normalization`, is exactly `:= by sorry` in its own
  new module. It states only the two pure-tensor section formulas for the fixed
  canonical comparisons. It asserts neither an existential comparison, the fold
  square, nor the cochain identity. Those parts are constructed/proved in this packet.

Actual packet count: zero sorries in the item; one sorry in the new module.
This is one fully proved original declaration and a decomposition of the other,
with net one hole closed, not two independently completed proofs.

The normalization is a separate local result in the source argument (Stacks 03EL,
0GMW, 03S3/03S4). Attempts established tensor-section naturality, compatibility of
restriction of scalars with the sheaf tensor pairing, and expansion of the scalar
pairing into its unit and right unitor. These three proved private
helpers (`tensor_section_map`, `restrict_tensor_section`, `scalar_tensor_section`)
are retained in the new normalization module, so the next proof can use their
section equations directly. Its private monoidal-comparison import supports them. The remaining work identifies the
scalar-unit equation with the full local bilinear pairing, including the coefficient-unit
comparison. The geometric/restriction comparison bridge is now proved in
`localization_scalar_comparison`, by extending the existing open-restriction proof
to every étale map. This adds no assumption and uses sectionwise unit naturality. The extension uses
proved private `leftUniq_whiskerLeft` and `leftUniq_whiskerRight` from
`EtaleOpenTensorDefs` through a private `import all`; its public open-immersion
theorems are not applied to an arbitrary étale map. The new theorem's docstring
and node give that argument and the exact fixed maps. It is not a renamed copy of the
parent: the adjunction counit calculation is independent of the local formulas.

Edge cases checked mathematically: the comparisons are isomorphisms before any local
normalization assertion; empty U, the identity map, B=0 and nonflat ring maps all obey
the same unit/mate identities. Arbitrary local coefficients are retained in the new
statement, with no finite-ring or compactness hypothesis.

## No longer needed

Deleted the redundant private declarations `fold_lift_iso` and `fold_sum_unit`;
their existing counterparts are imported and used instead. No helper module is
withdrawn.

No module is withdrawn and no global dependency is claimed pruned.

The parent proof no longer directly needs
`Sheaf.SecSmoothPurity.CochainInverseComparison`,
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`, or
`Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness`.
These unused proof imports were removed. The corresponding planned nodes
`lem-pur-independent-inverse-image-tensor-comparison`,
`lem-pc-sites-module-sheafification-bilinear-extension`,
`lem-pc-sites-sheaf-tensor-bilinear-universal`, and
`lem-pc-sites-module-sheafification-bilinear-extension-uniqueness` remain dependencies
of the separate normalization argument, so they are not pruned from the project.
`prop-weil-pbc-inverse-image-modules-exact` is not used by the parent proof: existing
adjunctions and restriction isomorphisms suffice. Its public statement import remains
unchanged. Removed these five unused direct approval entries from the parent node's
`tool_uses`; retained its inverse-image/restriction entry. No approval was added.

The sectionwise bilinear construction is not needed to construct rho or to prove its
fold-counit compatibility: uniqueness of left adjoints and the mate identities do both.
Only identifying the resulting maps on local tensors remains.

## Where the brief, the DAG or earlier work was wrong

The returned delivery redundantly restated two existing private normalization
lemmas. The repair removes both copies and uses the existing declarations, as
requested by the landing check. The normalization module and its genuine separate
local tensor result are retained from the returned packet.

No false statement was found. The planned proof reconstructs the sum adjunction and
uses sheaf tensor uniqueness to prove the fold square. Both steps can be shortened:
the adjunction already exists, and the fold square is a formal identity of mates.
The local tensor formulas still require their substantive compatibility proof.

The sandbox reference clock was reset on launcher resumption: the earlier saved start
was 1792759266, while the resumed `.budget` start is 1792769086.5064635. This packet
preserves the sandbox and earlier proof work; no budget file was edited by this worker.

## New nodes

`lem-sp-etale-scalar-section-normalization` in
`dag/nodes/sec-smooth-purity/lem-sp-etale-scalar-section-normalization.json` attaches
`etaleSumScalarIso` and `etaleSumScalarIso_tensorSections` to
`Sheaf.EtaleCohomology.Purity.Smooth.EtaleScalarSectionNormalization`. The construction
is real data; only the two local section formulas are postponed. Its source, detailed
proof, declared dependencies, all three required kinds of Mathlib search, and edge cases are recorded.
The blueprint ancestor is `det-sp-reduction-exceptional`; its Charts paragraph says
"Each of these commutes with extension of coefficients: summation over fibres is defined
integrally." The new node serves exactly this local scalar/sum computation. A full
blueprint search for `scalar.*section|pure.tensor|fold.*scalar` found no matching node;
the already existing parent remains the unit's fold/scalar result.
The first delivery invocation was refused without pushing by the split-off policy
(46 minutes against the reset reference clock). Work continued on the normalization
bridge; this was a policy rejection, not a tool failure.
No definition/signature repair or change record is needed.

The second delivery preflight found that Loogle and LeanFinder count as one search
kind, so the new node lacked LeanSearch. Ran LeanSearch, recorded its eight results
and their mismatch with this sheaf-level statement, and resubmitted the packet.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
