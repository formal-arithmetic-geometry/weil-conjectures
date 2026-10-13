## What changed

Proved `AlgebraicGeometry.Scheme.affine_perfect_sheafification_scalar` with its original
signature and public imports unchanged. Two fully proved private helpers compute scalar
multiplication on tilde sections and identify the transported coefficient. The theorem
combines them by extensionality of module-sheaf morphisms.

The tilde calculation uses the fully faithful functor's mapping equation, the canonical
section-module isomorphism, and induction on localized fractions. The coefficient
calculation uses naturality of open-immersion ring maps, `isoSpec_hom_appTop`, and the
explicit over-equivalence. This implements the node's recorded proof route.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.affine_perfect_sheafification_scalar`
(node `lem-sc-affine-sheafification-scalar`).

No holes remain, and no holes were added or split off. Both private helpers
`AlgebraicGeometry.Scheme.tilde_scalar_sections` and
`AlgebraicGeometry.Scheme.affine_scalar_coefficient` are proved.

The consolidated module compiles without warnings. A compiler probe reports only
`propext`, `Classical.choice`, and `Quot.sound` for the original theorem.

## No longer needed

None of the original imports, nodes, or modules are pruned. The proof needs both original
public imports for its statement and definitions. Temporary intermediate modules were
consolidated into private proved helpers; no new modules, imports, or nodes remain in
the delivery.

## Where the brief, the DAG or earlier work was wrong

None. The original statement and its recorded route are preserved. Empty opens and the
zero ring need no exclusions: the component proof is pointwise and its localization
calculation uses no nonzero assumptions.

## Second reading by X3

1. Compared the delivered module with the repository version. The theorem signature and both
   public imports are byte-for-byte unchanged; only the proof and its private helpers differ.
   Verdict: pass.
2. Compiled the module with `lcompile.py`; it has no errors, warnings, forbidden declarations,
   or `sorry`. Axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the two private helper statements against the existing library and DAG, including
   the zero-ring and empty-open cases. They are true, strictly intermediate, and introduce no
   split-off statements or nodes. Verdict: pass.
4. Read the proof downward from the target. It uses the recorded affine sheafification route,
   with the localized-fraction calculation and coefficient transport, and retains both imports;
   no shorter applicable upstream result was found. Verdict: pass.
5. Compared the DAG node's statement, proof route, and dependencies with the Lean declaration;
   the unit route and `realized` obligations remain unchanged. Verdict: pass.

No code, node, import, or statement changes were needed in this second reading.
