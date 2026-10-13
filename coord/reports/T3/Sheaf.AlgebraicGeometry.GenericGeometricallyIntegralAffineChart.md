## What changed

Replaced the proof of `AlgebraicGeometry.exists_generic_geometrically_integral_affine_chart`
with a complete Lean proof from two strictly separate algebraic results. The signature and all
existing public imports stay identical. Added proof-only imports of
`Sheaf.AlgebraicGeometry.CommonGenericHypersurfaceAffineOpen` and
`Sheaf.AlgebraicGeometry.GenericHypersurfaceGeometricIrreducibilitySpread`.

The first intermediate theorem constructs a concrete polynomial quotient hypersurface and a
common affine open with nonempty generic fibre, and makes no special-fibre assertion.
The second treats only a polynomial quotient hypersurface and has no arbitrary family or common
open as input. The original theorem combines them: the flat locally finitely presented open
subfamily has open image, and intersecting this image with the hypersurface's good base open
ensures nonempty fibres. A pullback of the comparison open immersion transfers geometric
irreducibility using Mathlib. This proves the geometric and categorical glue rather than
repackaging the original existential conclusion.

Updated the original node's proof route to match these two imports and the proved glue.
Added one node and one module for each intermediate theorem. No definition, existing statement,
visibility, target, or module belonging to another holder was changed.

All three delivered modules compile through lcompile.py in import order. The canonical
hypersurface uses the real term Spec(A[t_1,...,t_n]/(P)) and its coefficient ring morphism;
no data definition chooses a witness from an unproved existence theorem.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.exists_generic_geometrically_integral_affine_chart`
(node `lem-sbc-generic-geometrically-integral-affine-chart`). Its proof body has no sorry.

Added exactly two named holes, each in its own new module:

- `AlgebraicGeometry.exists_common_generic_hypersurface_affine_open`
  (`lem-sbc-common-generic-hypersurface-affine-open`), in
  `Sheaf.AlgebraicGeometry.CommonGenericHypersurfaceAffineOpen`.
- `AlgebraicGeometry.exists_open_generic_hypersurface_geometric_irreducibility`
  (`lem-sbc-generic-hypersurface-geometric-irreducibility-spread`), in
  `Sheaf.AlgebraicGeometry.GenericHypersurfaceGeometricIrreducibilitySpread`.

This is a decomposition: one upper hole closed, two strictly partial lower holes added,
net minus one hole closed in the import closure. It is not a sorry-free proof of the result.
No other holes remain in the delivered files. The new docstrings and nodes give the sources
and full proofs in words, including the edge cases.

## No longer needed

No imports, nodes, or modules are pruned. The original node had no named proof dependencies.
Its four algebraic/geometric plan steps are realized by the two new modules and the proved
Mathlib glue. A density-spreading lemma is unnecessary for this theorem: it concerns only the
open subfamily, not the rest of X's fibres. No such density module was imported or removed.
The original final proposal to choose another affine base neighbourhood and restrict W is
unnecessary: W is already affine, and only the base open U needs to be intersected with its
open image. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The module's node has four non-elementary proof steps but empty uses lists and empty
proof_deps. There are no pre-existing named statements supplying these steps, so the brief's
least-delivery route requires new intermediate modules rather than existing imports.
The recorded blueprint ancestor command does not resolve the created node; the new nodes retain
the explicit existing ancestor `sbc-lem-slicing` and extend its existing via chain.

Read Stacks Tags 0559, 0557, and 0552 online. The common-open citation is Tag 0552 (Lemma 29.51.7).
In Tag 0557 the displayed factor indexing includes zero degrees, but monic zero-degree factors
are units and must be excluded from the obstruction algebras: our proof uses only positive
factor-degree pairs. This avoids claiming the algebra for a trivial factorization is zero.

Checked the following edge cases mathematically before stating the new theorems. Empty generic
source is excluded by geometric irreducibility. A purely transcendental extension, including
relative dimension zero, has a linear hypersurface model with one extra variable. For the
spreading theorem, P = 0 gives affine space and the whole base; a nonzero constant is excluded
by nonemptiness of the generic fibre. If there are no variables, geometric integrality forces
P = 0. After making P monic, degree one has no positive factor-degree pairs, so the empty
product is 1. No Noetherian hypothesis or global nonemptiness of special fibres is assumed
for the common-open theorem. The polynomial specialization theorem applies to the explicit
hypersurface, never to an arbitrary finite presentation.

Searches: LeanSearch was unavailable (HTTP Internal Server Error); this is recorded as
unavailable. LeanFinder returned affine/integral-scheme facts and polynomial Gauss-lemma facts,
none supplying the requested common-open or specialization theorem. Loogle did not recognize
the unqualified geometric-irreducibility name. Mathlib grep found no exact match, and direct
searches of both Lean roots and the blueprint found no independent theorem for these two
algebraic steps. The tempting general generic-irreducibility-shrink theorem imports a theorem
that uses this item, so using it here would be circular. Mathlib directly supplies the open-image,
fibre nonemptiness, pullback-open-immersion, and geometric-irreducibility-transfer glue.

## New nodes

`lem-sbc-common-generic-hypersurface-affine-open`: constructs the common open and a concrete
hypersurface model, with geometrically integral generic fibre. Source: Tag 0559's first proof,
separating transcendence basis and common-open construction, and Tag 0552. Its proof does not
spread polynomial irreducibility or assert any property of special fibres.

`lem-sbc-generic-hypersurface-geometric-irreducibility-spread`: specializes Tag 0557 to an
explicit polynomial quotient family, using generic geometric reducedness to obtain an
absolutely irreducible equation. It handles the zero polynomial separately. It does not
construct an affine open in an arbitrary source. Both nodes carry the actual logged searches,
the unchanged chapter/unit, and the original explicit blueprint ancestor. No change record is
needed because existing statements and definitions stay identical.

## Second reading by T3

1. **Interface: pass.** Read the full diff against the repository. The existing
   declaration's signature and docstring are byte for byte unchanged; the only
   module edits are two plain proof imports and the proof body. No existing
   definition, public import, visibility, or other module changes. No change
   record is needed.
2. **Proof and trust: pass as a decomposition.** Independently compiled all three
   modules in import order through lcompile.py, without errors or warnings. A
   scratch module printed axioms for all three declarations: only propext,
   Classical.choice, Quot.sound, and sorryAx. The latter is expected from the two
   explicitly reported named holes. There are no additional sorry occurrences,
   forbidden declarations, or hollow definitions. The pullback comparison is
   over the residue field; fibreHomeo supplies nonemptiness, and the singleton
   residue-field spectrum supplies the surjectivity needed by Mathlib's
   open-immersion geometric-irreducibility instance.
3. **Split statements: pass.** Read both signatures, docstring arguments, and
   nodes, and checked Stacks Tags [0559](https://stacks.math.columbia.edu/tag/0559),
   [0552](https://stacks.math.columbia.edu/tag/0552), and
   [0557](https://stacks.math.columbia.edu/tag/0557). The first constructs a
   common nonempty generic open with a concrete hypersurface and has no
   special-fibre claim; the second only spreads the explicit hypersurface.
   Neither restates the target. Checked empty source, purely transcendental
   function field, relative dimension zero, zero polynomial, constant polynomial,
   no variables, and degree one. Monic degree-zero factors are units, so using
   only positive factor-degree pairs is correct. The base localization in the
   first argument ensures its hypersurface comparison is between domains.
   Independent msearch queries used birational principal opens (LeanFinder),
   `MvPolynomial, Irreducible` (Loogle), and factor specialization/localization
   and birational opens (grep); direct rg searched both Lean roots and Mathlib.
   These found component results, not replacements for either whole lemma.
   Neither algebraic hole can be closed in a few minutes from those results.
4. **Route and pruning: pass.** The proof realizes the original algebraic model,
   common-open, polynomial-specialization, and open-image steps, with no density
   assertion about the rest of X. The old proof_deps list was empty, so there
   are no abandoned dependency nodes to list. All retained imports support the
   signatures or the proof; the new imports are plain. Read
   dag/units/sk-prop-normal-form.json: its statement and route are untouched, and
   no realized node is bypassed. Its realized arrays were already empty; this
   delivery does not claim to complete that unit's realization records.
5. **Records: pass.** Mechanically compared every node's lean.statement with
   its theorem signature, checked required new-node fields, and checked that
   proof_deps equals the union of proof-step uses. The existing node changes
   only proof, proof_deps, and proof_origin. New nodes retain its chapter, unit,
   and blueprint ancestry. The report correctly counts one original hole
   closed and two added, a decomposition with net minus one hole closed.

**Second-reader changes:** appended this independent review and its search and
axiom evidence. No Lean or node repair was needed. Removed the scratch axiom
probe after checking it; it is not part of the delivery.
