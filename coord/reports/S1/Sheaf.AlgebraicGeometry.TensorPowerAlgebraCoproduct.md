## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.TensorPowerAlgebraCoproduct` by a complete
Lean reduction using the existing `exists_quasiCoherentSymmetricAlgebra`, the proved
invertible-to-quasi-coherent instance, and two new statements. All added imports in the
item are private proof imports. The original statement and visibility are unchanged.

`CommAlgebraSheafTensorPowerMaps` is fully proved. Its private helpers explicitly construct
the structure map and the bilinear multiplication map through the module sheafification
adjunction, then recursively construct the tensor-power maps. Local frames prove
three-factor extensionality, and induction proves the multiplication identity. The
multiplication helper is irreducible with a proved elementary-tensor API to prevent
expensive unfolding. There is no definition containing sorry or choosing arbitrary data
from an unproved existence theorem.

`InvertibleSymmetricAlgebraCoproduct` isolates the remaining module coproduct universal
property for an already supplied algebra, degree-one map, and multiplicative homogeneous
maps. Its affine symmetric-algebra hypothesis is exactly the clause supplied by the
existing symmetric-algebra theorem. Both new modules have corresponding new DAG nodes;
the original node's proof and proof dependencies follow the delivered reduction.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_tensorPowerAlgebraCoproduct`
(node `lem-sc-tensor-power-algebra-coproduct`), by reduction to the existing symmetric
algebra theorem and one newly holed coproduct comparison. This is a decomposition, not
an unconditional proof of the original theorem. Closed original holes: 1; new holes: 1.

Fully proved the new
`AlgebraicGeometry.Scheme.Modules.exists_commAlgebraSheaf_tensorPower_maps`
(node `lem-sc-algebra-sheaf-tensor-power-maps`) and every private helper of its module.
Its construction, degree-zero, degree-one and multiplication properties have no sorry.

The only sorry added or left in this delivery is
`AlgebraicGeometry.Scheme.Modules.isColimit_invertible_symmetricAlgebra_cofan`
(node `lem-sc-invertible-symmetric-algebra-coproduct`). Its proof is exactly `by sorry`;
its docstring explains the local polynomial universal maps, overlap compatibility,
sheafification and global uniqueness. The imported existing theorem
`AlgebraicGeometry.exists_quasiCoherentSymmetricAlgebra` remains sorry outside this
delivery. No other existing module is changed.

Compilation: all three delivered modules compile through lcompile.py. The final delivery
check also runs the maintainer's axiom probe. Standard axioms only are used by the fully
proved tensor-power extension; the original reduction still depends on the named holes.

## No longer needed

No imports were removed: the four original public imports are needed by the unchanged
statement. No existing module is asserted to be globally unreachable or pruned.

The separate local polynomial-algebra gluing construction in step 1 of the original
node is unnecessary here: the existing symmetric-algebra theorem supplies the algebra.
The original `def-pur-sheaf-tensor-product` proof dependency is no longer directly used
by the item; tensor construction and coherence are handled in the new proved module
using the source library's tensor product. Its conceptual statement dependency remains.
The other old proof dependency removed from the item is
`def-weil-pbc-comm-algebra-sheaf`: the item no longer constructs an algebra directly.
It remains a statement dependency, and its module stays publicly imported. These two
removed direct edges are not claims that either definition is globally unreachable.
No new algebra-gluing lemma, no equality of infinite coproduct sections with a global
direct sum, and no tensor-algebra commutativity lemma is needed by the delivered proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature error was found. The DAG's proof plan did not name the
existing symmetric-algebra construction as a reusable dependency. Its affine comparison
is enough to supply the local polynomial algebra used in the plan. The unit's realized
statement and steps are untouched.

LeanSearch returned Internal Server Error for both new-node searches; this is recorded
as unavailable, not as a negative result. LeanFinder, local source search, and the
whole-DAG/blueprint search found no duplicate of either new statement. The local
literature checkout lacks modules.tex, coherent.tex and schemes.tex, so the cited
Stacks sections 01CF, 01LA and 09MS were checked on the official Stacks website.
The expanded proofs are recorded as agent-written refinements of those sections.

Edge cases: the extension proof covers degree zero, the zero target algebra, zero
sections and the empty open. Empty schemes use the empty local-frame cover, where
sheaf separation still applies. The remaining coproduct statement uses sheafification
and locally finite polynomial expansions rather than a false global section formula.

## New nodes

`lem-sc-algebra-sheaf-tensor-power-maps`, in
`dag/nodes/sec-curve-estimates/lem-sc-algebra-sheaf-tensor-power-maps.json`, records the
fully proved extension of a map from an invertible module into any commutative algebra
sheaf. Its module is `Sheaf.AlgebraicGeometry.CommAlgebraSheafTensorPowerMaps`.

`lem-sc-invertible-symmetric-algebra-coproduct`, in
`dag/nodes/sec-curve-estimates/lem-sc-invertible-symmetric-algebra-coproduct.json`, records
the remaining homogeneous module coproduct comparison, in module
`Sheaf.AlgebraicGeometry.InvertibleSymmetricAlgebraCoproduct`. This is strictly the
universal-property part of the original construction: the algebra, maps, affine
comparisons and multiplication are hypotheses, not conclusions of this lemma.

No change record is needed: existing signatures, definitions and visibility are
unchanged, and there are no forced adaptations.


## Second reading by S1

1. **Interface: pass.** Read all three delivered modules and diffed the item against
   the repository file. The only edits to that existing module are four plain imports
   and the replacement of `sorry` by its three-line reduction. Its theorem signature,
   docstring, visibility, definitions and original public imports are byte-for-byte
   unchanged. There are no adapted existing modules or interface change records.

2. **Kernel proof and data: pass, with the declared open comparison.** Recompiled all
   three modules in import order with lcompile.py: no errors or warnings. Independently
   compiled scratch copies with `#print axioms` for every declaration, including all
   eight private helpers of CommAlgebraSheafTensorPowerMaps. Each helper and
   `exists_commAlgebraSheaf_tensorPower_maps` uses only propext, Classical.choice and
   Quot.sound. The item and `isColimit_invertible_symmetricAlgebra_cofan` also use
   sorryAx, as reported. The latter is the only delivered sorry, in a named public
   theorem with a matching node and a complete proof docstring. No forbidden declaration
   or hollow definition occurs. The explicit algebraUnit, presheafProduct,
   sectionProduct and algebraPowers constructions choose no arbitrary data from an
   unproved existence theorem. The item eliminates the existing existential symmetric
   algebra theorem only inside a proof of an existential proposition.

3. **New statements and smaller cases: pass.** Read Stacks 01CF (tensor algebra,
   symmetric quotient and sheafification), 01LA (9), and 09MS (the direct-sum algebra),
   and compared both new node statements clause by clause with their Lean signatures.
   The power-map theorem allows an arbitrary B and j; its unit, right-unitor and product
   conditions follow from the explicit construction. Read the zero and successor
   cases of hmap, including the equality transports and associator direction. Read
   tensorSection_ext through the sheafification adjunction and the local-frame argument
   in tensorSection_ext_three. The comparison theorem assumes B, j, b and the affine
   algebra comparisons already exist; it proves only their module coproduct property,
   so it is strictly smaller than the original existence-and-multiplication theorem.
   On an affine frame open the hypotheses force b_d(e^d) = T^d inductively, including
   b_0(1) = 1. Structure and degree-one compatibility determine the comparisons on
   smaller affine opens. Finite polynomial expansions define maps into an arbitrary
   module sheaf; uniqueness on an affine basis gives compatibility and gluing. No
   quasi-coherence of that target module, affine intersections, or global finite-support
   formula is assumed. Checked degree zero, degree one, the trivial line over a field,
   zero coefficients, the zero target algebra for the power-map construction, and the
   empty scheme/open. The remaining comparison is not a few-minute consequence of an
   available sheaf coproduct API, so it remains explicitly open.

   Independently searched with msearch.py LeanFinder for "A sheaf symmetric algebra of
   a locally free rank one module is the direct sum of its homogeneous tensor powers"
   and Loogle for "SymmetricAlgebra.ι". These returned ring-module symmetric algebras,
   symmetric powers, the free module-sheaf inclusions, and the symmetric algebra lift
   and uniqueness lemmas, with no sheaf-level comparison theorem. Additional rg searches
   in lean/Sheaf, lean/WeilConjectures, the upstream module directory and Mathlib's
   symmetric-algebra sources found no duplicate of either new theorem. In particular
   equivMvPolynomial proves the local polynomial identification, not the global cofan
   comparison. The pre-existing QuasiCoherentSymmetricAlgebra theorem supplies exactly
   hAffine; it does not supply the coproduct conclusion.

4. **Route and pruning: pass after report correction.** The item first reuses the
   existing symmetric-algebra construction and the proved invertible-to-quasi-coherent
   instance, then the fully proved tensor-power construction, then only the remaining
   coproduct comparison. All four added imports are proof imports. The public imports
   of the new modules provide symbols in their signatures; their ProjectionFormula
   import is private and supplies the invertibility comparison used in the proof.
   The original proof dependencies removed directly from the item's node are exactly
   def-pur-sheaf-tensor-product and def-weil-pbc-comm-algebra-sheaf; both remain conceptual
   statement dependencies and no module is claimed pruned. Checked
   dag/units/sk-thm-curveestimate.json: its realized statement is thm-sc-proper-cohomology,
   with no realized step replaced here, and the unit record is untouched.
   lem-weil-pbc-quasi-coherent-symmetric-algebra (unit sk-thm-p1) is reused as a generic
   algebra-construction tool. It preserves the local symmetric/polynomial-algebra route
   of this item; the maintainer should record this cross-unit tool use if required.

5. **DAG: pass.** Compared the existing node with the repository JSON: only proof,
   proof_deps and proof_origin changed. Its three steps respectively cite the existing
   symmetric-algebra theorem and invertibility definition, the new proved extension,
   and the new open comparison. Their dependency union is exact. Both new nodes carry
   the full Lean statements, source and proof, search records, blueprint provenance,
   chapter/unit and worker metadata. The open comparison cites the symmetric universal
   property and the existing free-module polynomial theorem for the precise two local
   algebra facts its argument uses. No statement or target definition changes.

Changes by the second reader: completed the No longer needed inventory with
`def-weil-pbc-comm-algebra-sheaf`, made the cross-unit generic-tool use explicit, and
added this independent review and axiom evidence. No Lean or DAG repair was needed.
The delivery remains a decomposition: one original hole closed, one lower hole added;
net hole reduction zero. Temporary axiom probes were removed before delivery.
