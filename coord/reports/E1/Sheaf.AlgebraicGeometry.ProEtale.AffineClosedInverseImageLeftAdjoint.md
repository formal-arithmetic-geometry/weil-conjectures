## What changed

Proved `AlgebraicGeometry.Scheme.exists_affineClosedInverseImageLeftAdjoint` in
`lean/Sheaf/AlgebraicGeometry/ProEtale/AffineClosedInverseImageLeftAdjoint.lean`, with
its original statement and public imports unchanged.

For a quotient immersion, restrict the target to its affine ind-etale basis while
retaining the full source site. Sheafification adjunction and universe-lifted Yoneda
represent evaluation at the lifted object. Both clauses of the existing inverse-image
evaluation theorem identify this representation with inverse-image evaluation on a
weakly contractible basis object. The existing covering theorem and lower-shriek
criterion then supply the extra left adjoint.

Private proved helpers transport the criterion through `ULiftHom`, establish finite-limit
preservation of the ordinary inverse image through the existing `AsSmall` models, and
transport the quotient case to every affine closed immersion using
`IsClosedImmersion.Spec_iff`, direct-image composition, and uniqueness of left adjoints.
The only added proof import is
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`, for the existing
direct-image equivalence of a scheme isomorphism. The import-direction check passed.
The copied DAG node now records this actual route and its direct proof dependencies.
No interface, definition, target signature, or other module was changed.

Validation: the complete module compiles without warnings through `lcompile.py` after
import pruning. The final compile took 2.5 seconds. No new assumptions or admitted
intermediate statements were introduced. Quotient ideals are unrestricted; the proof
also covers the zero ideal, unit ideal, zero ring, and empty schemes. The covering
argument accepts empty covering families and uses no nonemptiness assumption.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_affineClosedInverseImageLeftAdjoint`
(node `lem-weil-pbc-affine-closed-inverse-image-left-adjoint`).

Proved all private helpers: `CategoryTheory.coveringCriterion`,
`AlgebraicGeometry.Scheme.inverseImage_finite`,
`AlgebraicGeometry.Scheme.AffineProEt.quotient_corepresentable`,
`AlgebraicGeometry.Scheme.inverseImageIso_isEquivalence`,
`AlgebraicGeometry.Scheme.reduce_to_quotient`, and
`AlgebraicGeometry.Scheme.quotientInverseImage_isRightAdjoint`.
The two private natural-isomorphism definitions have complete constructions.

No `sorry` remains in the item. Holes added: none. Split off: none.
The proof uses the existing declarations
`affine_closed_inverseImage_evaluation`, `exists_weaklyContractible_cover`, and
`exists_leftAdjoint_of_covering_corepresentable_evaluations`, whose proofs remain
separate existing items.

## No longer needed

Removed these redundant direct proof imports:

- `Mathlib.CategoryTheory.Yoneda`
- `Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
- `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`

The proof's four remaining private imports provide all required declarations and
instances. The other three imports are the unchanged public statement imports.
The direct proof dependency
`lem-weil-pbc-affine-closed-site-functor-properties` is unnecessary here: its theorem
is used by the separately stated evaluation theorem, not applied again in this proof.
It therefore remains a transitive dependency; no global pruning of that node or its
module is claimed. All other original proof-dependency nodes remain needed.

Restriction to the source affine basis, its chosen quasi-inverse, and their transport
isomorphisms are unnecessary: representing sheaves can be formed on the full source
site. This changes no blueprint unit statement or realized unit step. No entire
existing module is claimed to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan omitted the explicit passage from
arbitrary affine closed immersions to the quotient presentations accepted by the
geometric inputs. The proof now supplies this passage.

The generic lower-shriek criterion has `SmallCategory` arguments, while the original
sites have objects in universe `u+1` and morphisms in universe `u`. The private
`ULiftHom` transport resolves this without changing the criterion. Similarly, finite
limit preservation of the constructed ordinary inverse image is not available by a
single existing instance at the original universes; the private small-model argument
proves it. These are implementation details of the original categorical argument.

## Second reading by E1

Independent second reader; did not write the proof.

1. **Interface: PASS.** Compared the entire delivered Lean module with the repository
   using `diff`. The only existing declaration's signature is byte-for-byte identical
   up to `:=`; its docstring and all three public imports are also identical. The
   additions are private proved helpers and two private constructed natural
   isomorphisms. No other Lean module, definition, or target was changed, and no
   interface change record is needed.
2. **Proof and axioms: PASS.** Independently compiled the delivered file through
   `lcompile.py` without warnings or errors (5.0 seconds). Compiled a scratch copy
   with `#print axioms` for the main theorem and all eight private declarations
   (2.8 seconds). Only `propext`, `Classical.choice`, `Quot.sound`, and the permitted
   transitive `sorryAx` occur. In particular, finite-limit preservation, evaluation
   corepresentability, composition, isomorphism invariance, and affine quotient
   reduction use only the three permitted axioms. The file contains no `sorry` or
   forbidden primitive. The representing object is explicitly sheafification of
   lifted Yoneda, and both natural isomorphisms have constructed components; no
   arbitrary object is extracted from an unproved existence theorem.
3. **Split statements and edge cases: PASS.** No statements or holes were split off.
   Read the existing evaluation, covering, and lower-shriek criterion statements
   against their actual applications. Evaluation uses both clauses and the natural
   sheafification unit. Quotient reduction imposes no condition on the ideal, so
   the zero ideal, unit ideal, zero ring, and empty source are included. The cover
   transport works with empty families and introduces no inhabitedness assumption.
4. **Route and pruning: PASS.** Read the proof from the final adjoint witness through
   quotient reduction, the covering criterion, and corepresentable evaluations.
   Checked the `ULiftHom` transport of topology, covers, and adjunctions, and the
   `AsSmall` proof of finite-limit preservation. Repeated searches in `lean/`,
   Mathlib grep, and LeanFinder with evaluation/representability wording; no
   existing theorem supplied a shorter replacement. The proof already applies
   Mathlib adjoint uniqueness and Yoneda directly. The six removed proof imports
   and sole removed old proof dependency are all recorded above. Inspected
   `dag/units/sk-thm-properbasechange.json`: no realized unit statement or step is
   bypassed; the affine basis, evaluation, and covering-criterion route is retained.
   No whole-module pruning is claimed.
5. **DAG: PASS.** The node changes only `proof`, `proof_deps`, and `proof_origin`.
   Its five steps agree with the Lean proof, and `proof_deps` is exactly the union
   of the steps' `uses`. The removed direct site-functor-properties dependency is
   still reached through evaluation. The added closed-immersion dependency records
   the explicit `IsClosedImmersion.Spec_iff` reduction. There are no new nodes.

Second reading changed only this report by adding these review findings. No Lean
or node repair was necessary. One original hole closed; zero holes added; zero
split off. Existing open dependencies are not claimed as fully proved here.
