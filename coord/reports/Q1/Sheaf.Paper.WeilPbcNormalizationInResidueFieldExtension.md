## What changed

Proved `normalization_in_finite_residue_field_extension` in
`lean/Sheaf/Paper/WeilPbcNormalizationInResidueFieldExtension.lean`, preserving its complete
signature and existing docstring. The witnesses are the existing relative normalization,
its integral morphism to X, and its dominant point morphism. Existing proved results give
integrality and normal stalks. Dominance identifies the image point as generic.

The remaining field identification is proved by an internal, fully proved private helper
`finite_residue_extension_integral_quotients`. A finite extension of the residue field is
integral over the affine stalk; Mathlib clears denominators to express each element of K
as a quotient of two elements integral over the affine sections. The normalization sections
isomorphism lifts those elements into the generic stalk, proving the stalk map surjective.
Naturality of residue maps then gives the exact `IsIso (g.residueFieldMap ...)` required.

Updated the existing node's proof, proof dependencies, and proof origin to this route.
No signature, public definition, target, or unit route changed. No new module or node.
The second reading repairs import visibility; its change record is
`coord/changes/normalization_in_finite_residue_field_extension-imports.md`.
The final single-file local compilation is clean; the delivery dry run performs the server
compile, declaration-axiom probe, and preflight.

## Proved and sorry left

Proved the original one of one sorry:
`normalization_in_finite_residue_field_extension`
(node `lem-weil-pbc-normalization-in-residue-field-extension`).
The private helper is also completely proved. No sorry remains in the item or is added
elsewhere. The proof uses only already proved Mathlib and source-library declarations.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.SpecFieldPointResidueField` and the corresponding
node `lem-weil-pbc-spec-field-point-residue-field`; none of its four declarations is used.
The planned nodes `lem-weil-pbc-morphism-into-affine-scheme` and
`lem-weil-pbc-integral-closure-finite-extension-normal` are also removed from this node's
proof dependencies. Their Mathlib modules are available transitively for other purposes,
but the planned affine morphism correspondence and fraction-field calculation are unused.
No assertion is made that other targets cannot independently need these nodes.

Retained the relative-normalization, qcqs-permanence, normal-stalks, scheme-sobriety,
integral-scheme, affine-spectrum, and residue-field dependencies. The normalization module is retained as a plain proof import. Public imports of
`Mathlib.AlgebraicGeometry.Morphisms.Integral` and
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` expose the types used in the unchanged
theorem signature; denominator-clearing declarations are visible through the private
normalization import. An experimental new helper module was removed before delivery;
its proof is now private in the item and creates no downstream work.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool failure was found. The DAG's six-step affine prime-quotient route
is longer than necessary: integral equations over the residue field can first be lifted to
the stalk and then cleared of their affine denominators using
`IsIntegral.exists_multiple_integral_of_isLocalization`. This avoids all four pending
sorries in the imported residue-field module and avoids a separate A/p fraction-field proof.
The unit's statement and realized steps are preserved.

The source TeX files are absent on this machine; Stacks 035F and 09Z6 were read from their
online tag pages. The source's function-field assertion and the node's original proof were
used to check the replacement calculation. The private helper covers zero, arbitrary
characteristic, and non-domain affine rings: only the stalk localization and finite field
extension are used, and its denominator maps to a unit, so the proof does not assume X
integral, reduced, affine, Noetherian, or separated.

## Second reading by Q1

1. Compared the sole delivered Lean module with the repository using `diff`, and compared
   the existing node file field by field. The existing theorem signature and docstring are
   byte for byte unchanged; there are no changed definitions, adapted modules, target
   changes. The import-visibility repair has the change record
   `coord/changes/normalization_in_finite_residue_field_extension-imports.md`. Only the existing node's `proof`, `proof_deps`, and
   `proof_origin` differ. Verdict: pass.
2. Compiled the delivered proof locally, then compiled a scratch copy with `#print axioms`
   for both the main theorem and the private quotient helper. Both use exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The file has no `sorry`, axiom,
   unsafe code, opaque declaration, extern, implemented_by, or hollow definition.
   The normalization witnesses, dominance argument, localization scalar towers, lifting of
   integral sections, and cancellation in the residue-field comparison were read in full.
   Verdict: pass.
3. There are no split-off statements, new public statements, new modules, or new nodes.
   The private helper is fully proved and supplies only the integral quotient calculation,
   not a restatement of the item. Checked zero elements, the trivial extension K=kappa(x),
   arbitrary characteristic, and affine section rings with nilpotents or zero divisors:
   localization is at the point's prime, and its denominator maps to a unit in K, so no
   domain or reducedness assumption on X is hidden. An empty scheme has no x; the chosen
   affine open necessarily contains x. Verdict: pass.
4. Read the upstream normal-stalk theorem and Mathlib's denominator-clearing theorem;
   searched lean/Sheaf and lean/WeilConjectures for normalization/residue-field and finite
   extension variants, and ran a new Lean Finder query about the function field of relative
   normalization. No existing declaration closes the remaining field identification more
   directly. The proof uses the already proved normalization API and Mathlib and requires
   no pending Sheaf lemma. The report lists all three removed old proof dependencies.
   Read `dag/units/sk-thm-p1.json` `realized`: neither this leaf nor the removed dependencies
   realizes a unit statement or step, and the unit route is unchanged. Corrected the
   proof-only normalization import from `public import` to `import`, with public imports
   of Integral and IntegrallyClosed for signature types. The corrected file compiles.
   Verdict: pass after import repair.
5. The node's six revised proof steps describe the actual Lean proof, including both
   scalar towers, denominator clearing, normalizationObjIso, the generic stalk field,
   and the final residue-map comparison. Their uses have exactly the listed proof_deps
   as union. The agent-origin record correctly identifies the replacement argument.
   The node's unchanged historical tool_uses field still mentions the old affine-morphism
   plan; it is outside the stage-3 editable fields and is not an actual proof dependency.
   Verdict: pass.

Changed only import visibility and the explicit public signature imports, and updated this
report accordingly. No proof repair or statement change was needed. The first delivery dry run required
a change record for the narrowed public imports; added the record and checked its two
direct importers, neither of which needs adaptation.
