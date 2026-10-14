## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isColimit_invertible_symmetricAlgebra_cofan`
in `Sheaf.AlgebraicGeometry.InvertibleSymmetricAlgebraCoproduct`, preserving its complete
signature and all existing public imports. Added proof-only imports of
`Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`,
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`, and
`Mathlib.Topology.Sheaves.SheafCondition.Sites`.

The proof establishes additive generation on affine sections by symmetric-algebra induction,
then independence of tensor components by polynomial coefficients on framed affine
neighbourhoods. It constructs extensions by inverting the affine finite-sum maps, proves
restriction compatibility, extends the additive maps from the affine basis, checks global
linearity and factorization locally, and supplies coproduct uniqueness by sheaf separation.
The DAG copy now records these five steps and the basis-morphism Mathlib leaf.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.isColimit_invertible_symmetricAlgebra_cofan`
(node `lem-sc-invertible-symmetric-algebra-coproduct`).
No holes remain in the module, no holes were added, and no statements were split off.
This is a proof, not a decomposition. All local auxiliary facts are fully proved inside
the existing theorem. The resumed worker rechecked the complete inherited proof: single-file compilation
passed without warnings in 11.9 seconds. `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The theorem's signature is unchanged. The
unique extension is chosen only after both existence and uniqueness are proved.
The original theorem docstring is preserved; the implemented affine-basis route is recorded here
and in the node's proof steps.

## No longer needed

No existing imports, nodes, or modules were pruned: all original dependencies remain used.
The original symmetric-algebra universal-property node supplies the symmetric-algebra API,
and the free-module polynomial node supplies `SymmetricAlgebra.equivMvPolynomial`.
No quasi-coherent symmetric-algebra construction, sheaf coproduct computation on arbitrary
opens, affine tilde equivalence, or new extension/gluing node is needed. The attempted new
extension and injectivity modules were completed and folded into the target proof; neither
is part of the delivery. A redundant new import of `Mathlib.Algebra.DirectSum.Module` was
removed after compilation confirmed the API is already available. The second reader also
removed the redundant added proof import `Mathlib.Algebra.MvPolynomial.Equiv`; a complete
scratch copy compiles without it. No old proof dependency is unused.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid, but its sheafification/gluing step can use Mathlib's proved
`TopCat.Sheaf.restrictHomEquivHom` and `extend_hom_app` directly. There is no assumption
that intersections of affine opens are affine: all compatibility is checked on the full
affine basis, and sheaf separation covers arbitrary opens by affine subopens.
`Scheme.Modules.IsInvertible` and `SheafOfModules.IsInvertible` are distinct classes;
the proved comparison in `ProjectionFormula` is explicitly used to obtain local frames.

The previous attempt checked the source online at Stacks Tags 01CF, 01CG, 01LA and 09MS because the cited
literature files are absent on this read-only machine. The proof preserves the direct-sum
algebra route. Degree zero, the zero ring and empty opens impose no nontriviality condition;
polynomial coefficient identities and sheaf separation apply to them unchanged. No global
finite-support description of sections is used. The unit realization is unchanged.


## Second reading by Q3

1. **Interface: pass.** Compared the sole delivered module with the repository file.
   The complete existing theorem signature is byte-for-byte identical. There are no
   new declarations or definitions, no changed visibility, and no change records or
   forced adaptations. Existing public imports are preserved.
2. **Proof: pass.** Independently compiled the complete module without errors or
   warnings (13.1 seconds), then compiled an exact scratch copy with `#print axioms`.
   The theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`. Scanned
   the delivered source: no `sorry`, forbidden declarations, or hidden definition holes.
   The affine equivalences invert proved bijections; the final chosen extension is
   uniquely determined by the proved factorization and uniqueness.
3. **Split statements: pass (none).** No holes or split statements were added. Read
   all local facts: additive generation, uniqueness, framed polynomial independence,
   restriction to framed neighbourhoods, and extension from the affine basis are fully
   proved. Degree zero uses the unit equivalence; zero rings need no nontriviality;
   empty opens are covered by sheaf separation. No arbitrary unproved witness is used.
4. **Route and pruning: pass.** Searched Mathlib independently with the recorded
   query `isColimit.*[Ss]ymmetric|[Ss]ymmetric.*[Cc]ofan|tensorPow.*coproduct` and
   searched both library roots; no existing replacement theorem was found. Checked
   the direct use of symmetric-algebra induction, polynomial coefficients, and
   Mathlib's proved basis-extension API. Every old proof dependency is still used.
   The three remaining added imports supply the polynomial equivalence, invertibility
   comparison, and affine-basis extension. The unit `sk-thm-curveestimate` realizes
   `thm-sc-proper-cohomology`; this subordinate proof changes none of its realized
   nodes or steps. No existing module is pruned.
5. **DAG: pass.** Only `proof`, `proof_deps`, and `proof_origin` differ. Matched the
   five recorded steps to `hgen`, `hext`, `hinj`, `hexists`, and the final cofan
   construction. The dependency list is precisely the union of the steps' `uses`;
   the added basis-morphism dependency is an existing Mathlib leaf carrying
   `restrictHomEquivHom` and `extend_hom_app`. No new node is delivered.

Second-reading changes: removed the redundant added import
`Mathlib.Algebra.MvPolynomial.Equiv` after compiling a copy without it, restored the
existing theorem docstring, and corrected this report accordingly. The mathematical
proof is unchanged. Holes closed: one,
`AlgebraicGeometry.Scheme.Modules.isColimit_invertible_symmetricAlgebra_cofan`;
holes added: zero; split off: zero.
