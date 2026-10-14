## What changed

Proved `AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_section_equiv` from two
independent intermediate statements. The source module's signature and public imports
are unchanged. Added proof imports of `ExteriorSheafAffineUnit` and
`SelfTorConormalExteriorSectionModel` and updated the item's DAG proof route.
The proof obtains conormal quasi-coherence from `affine_conormal_sections.{u, u}`,
uses affineness of the inverse image, inverts the canonical exterior sheafification
unit, and composes with the algebraic exterior-to-affine-model equivalence.
The wedge identity follows by `LinearEquiv.symm_apply_apply` and the second lemma's
formula. Restricting to the over-site identity requires no extra isomorphism.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_selfTor_conormal_wedge_chart_section_equiv`
(node `new-t2-self-tor-conormal-wedge-chart-section-equiv`). No sorry remains in the
item module.

Added exactly two holes:

- `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_affine_unit_bijective`
  (node `new-q1-exterior-sheaf-affine-unit-bijective`).
- `AlgebraicGeometry.exists_selfTor_conormal_exterior_section_model`
  (node `new-q1-self-tor-conormal-exterior-section-model`).

This is a decomposition, not an unconditional proof: one hole closed, two added,
net -1 before any subsequent work on those modules. Each added hole is a public
named theorem with a complete proof in words and a matching node. The first handles
only exterior sheafification and is independent of closed immersions and T(M).
The second handles the actual algebraic exterior module of conormal sections and
never mentions the exterior sheaf. Neither is the original statement relabelled.
No definition, existing signature, target, or visibility was changed.

## No longer needed

None. The original public imports define the statement's objects and are preserved.
`AffineConormalSections` supplies quasi-coherence in the proof. Its section formula
remains an input of the new algebraic model statement. The original
`new-t2-self-tor-affine-section` dependency is now indirect through that statement;
it is still needed, so this is not pruning. The unit's realized statement and steps
were not bypassed or modified.

## Where the brief, the DAG or earlier work was wrong

The node's single proof step bundles two geometric identifications not supplied by
its dependency statements: exterior sheafification on an affine quasi-coherent
chart, and the algebraic exterior comparison with the particular affine model.
`affine_conormal_sections` supplies degree-one coordinates and quasi-coherence,
not either of these identifications. The original result is not disputed.

Searches: LeanFinder found tilde, ModuleCat exterior functors, and algebraic
cotangent/tensor equivalences, but no theorem for these exact section maps.
Loogle returned no exterior/localization or cotangent/exterior match. Mathlib and
both library roots were searched with rg, and DAG/blueprint searches found no
exact intermediate theorem. LeanSearch returned Internal Server Error for both
queries; no mathematical verdict is inferred from that outage.

Sources were read at Stacks Tags 01I6, 01I8, 01IA, 01I9, 01R3, and 0096. The new
lemmas impose neither regularity nor local freeness. Edge cases were checked
mathematically: n=0 is the canonical ring/empty-wedge identification; n=1 is the
conormal section comparison; zero ideal gives zero positive exterior powers;
empty inverse-image charts have zero section rings and zero modules; arbitrary
rank and non-finitely-generated modules are permitted by localization of exterior
powers and the affine quasi-coherent equivalence.

A read-only process-status check while waiting for the dry run exposed an N4
process repeatedly copying its sandbox's `RawModuleScalarCoefficientUnshifted`
compiled artifacts into the shared compiled library during its own dry run. This
appears to bypass the landing/build contract of AGENTS.md section 3. It is outside
this item's files; the maintainer should investigate that process and restore the
shared build if needed. Q1 wrote only its assigned sandbox and ran the authorized
delivery dry-run tool.

## New nodes

`new-q1-exterior-sheaf-affine-unit-bijective` is the bijectivity of the canonical
exterior sheafification unit on any affine open of a quasi-coherent module. Its
module is `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit`, and its proof
follows Stacks 01I8(2) and 01IA using principal-open localization and the affine
tilde unit. This is the exterior/sheafification part of the original calculation.

`new-q1-self-tor-conormal-exterior-section-model` identifies the algebraic exterior
of N(V) with the affine model's sections, with the precise pullback-unit wedge
formula. Its module is `Sheaf.AlgebraicGeometry.SelfTorConormalExteriorSectionModel`.
It follows 01R3(2), 01I9(1), and the tilde and pullback unit calculations. It is the
conormal and affine-model part, independent of exterior sheafification.

No change records or forced adaptations are needed.

## Second reading by Q1

1. **Unchanged statements.** I compared the delivered item module byte-for-byte with the repository version outside its proof and verified that the theorem signature and all existing declarations are unchanged. The two added theorem statements are new split nodes only; no target statement or definition changed. Verdict: pass.

2. **Proof and axioms.** I compiled all three delivered modules with `lcompile.py --all`; they compile without errors or warnings. The item theorem has no `sorry`; the only remaining holes are the two named split theorems listed above, each with a docstring proof plan and matching DAG node. No forbidden declarations or hollow definitions occur. Verdict: pass, conditional on the two documented split nodes.

3. **New statements.** I checked the edge cases recorded in the report (degree zero, degree one, zero ideal, empty chart) and checked that both split statements are strictly smaller parts of the original argument: one is the affine exterior sheafification unit, and the other is the algebraic conormal exterior/model comparison. They are not restatements of the item and no duplicate declaration was found in the library or Mathlib searches. Verdict: pass.

4. **Pruning and route.** The proof uses the affine conormal quasi-coherence result, the exterior affine-unit node, and the algebraic model node. The composition preserves the unit's realized route and uses no bypass imports; no existing import is unused. Verdict: pass; no pruning is available.

5. **DAG agreement.** The item node's proof and `proof_deps` match the composition in Lean, and each new node records its exact module, declaration, statement, source, proof plan, and split status. Verdict: pass.

I changed only this report by adding this second-reading section. No Lean source, statement, definition, node, or import was changed during the second reading.
