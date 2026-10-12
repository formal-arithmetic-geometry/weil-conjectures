## What changed

Proved `AlgebraicGeometry.Scheme.Modules.H.baseChange_mayerVietoris` in
`Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyMayerVietoris` without changing
its signature or existing docstring. The proof obtains the original R-linear row
and the pulled-back S-linear row before tensoring, tensors the original maps,
and transports the middle term through `TensorProduct.prodRight`. Mathlib's
`Module.Flat.lTensor_exact` and `lTensor_preserves_injective_linearMap` prove
upper-row exactness and initial injectivity. The other row is retained. Tensor
extensionality proves the restriction and boundary squares; transport through
the product equivalence and tensor induction prove the difference square.

Added the proof-only imports of
`Sheaf.AlgebraicGeometry.Cohomology.CohomologyMayerVietorisInverseImage` and
`Mathlib.LinearAlgebra.TensorProduct.Prod`. Updated the item's node proof,
proof dependencies and proof origin to match the compiled argument.

## Proved and sorry left

Proved the item's sole original sorry:
`AlgebraicGeometry.Scheme.Modules.H.baseChange_mayerVietoris`
(node `lem-pc-flat-cohomology-mayer-vietoris`). No sorry remains in the item.

One new sorry remains, as the complete proof of the public theorem
`AlgebraicGeometry.Scheme.Modules.H.baseChangeLinear_mayerVietoris`
(node `lem-pc-cohomology-mayer-vietoris-inverse-image`), in the new module
`Sheaf.AlgebraicGeometry.Cohomology.CohomologyMayerVietorisInverseImage`.
This is the geometric comparison BEFORE tensoring, for arbitrary commutative
algebras and arbitrary modules. It assumes neither flatness nor quasi-coherence.
It contains no tensor row or scalar-extension compatibility. Those are constructed
and proved in the original item, so the reduction is not a renaming of the item.

Both modules compile locally, without warnings, through the prescribed compiler.
The delivery dry run performs the remaining checks.

## No longer needed

Removed the direct proof import `Sheaf.Topology.ModuleMayerVietoris` from the item;
it belongs to the geometric step and is imported by the new module instead.
Removed `lem-sc-mayer-vietoris-ringed-space` from the item's DIRECT proof
dependencies, replacing it with the new inverse-image comparison node.
No node or module is globally pruned: the ringed-space Mayer--Vietoris result
remains needed by the new node. Flat tensor exactness and the comparison
definition remain needed. All original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically appropriate, but its available
ringed-space Mayer--Vietoris statement uses derived module sections, whereas
`HOver` and `H.baseChangeLinear` use Ext in abelian sheaves. That statement alone
does not supply a commuting diagram for the latter construction, particularly
its connecting square. This bridge is now named explicitly in the new node.
The existing étale Mayer--Vietoris pullback theorem concerns a different site;
the existing derived base-change Mayer--Vietoris theorem requires quasi-compactness
and quasi-separatedness not assumed here. Neither was imported as a substitute.

Read Stacks Tags 01EB and 02KH. Tag 01EB constructs the sequence and asserts
coefficient naturality; Tag 02KH suggests the Mayer--Vietoris alternative.
The inverse-image naturality argument is expanded by the agent in the new node
and docstring rather than falsely attributed to an explicit source assertion.
LeanFinder and Mathlib source searches found the free-sheaf Mayer--Vietoris
construction and flat tensor exactness, but no complete inverse-image comparison.
LeanSearch was unavailable (HTTP Internal Server Error), recorded as unavailable.
Blueprint searches for Mayer--Vietoris and 01EB returned no duplicate blueprint
statement. The ancestor helper returned None for this module-created node;
the new node therefore inherits the explicit ancestor recorded in the item's
existing blueprint field, with the item prepended to its via list.

The new statement was checked against the empty scheme, an empty member of the
cover, U = V = X, degree zero, and a nonflat algebra. The two cohomology rows
remain exact in these cases; the unextended comparison needs no flatness.
No compactness, separatedness or comparison bijectivity is used. The unit's
Mayer--Vietoris route is preserved; no unit statement or step is bypassed.

## New nodes

`lem-pc-cohomology-mayer-vietoris-inverse-image`, in
`dag/nodes/sec-picard-framework/lem-pc-cohomology-mayer-vietoris-inverse-image.json`,
states the original and pulled-back exact rows and their compatibility with
`H.baseChangeLinear` before extending scalars. Its new module is
`lean/Sheaf/AlgebraicGeometry/Cohomology/CohomologyMayerVietorisInverseImage.lean`.
Its proof docstring explains free-sheaf inverse image, the coefficient map,
Ext functoriality and the Yoneda boundary. The node has the actual three kinds
of search, source, proof plan, signature and inherited blueprint provenance.
There are no definition or statement changes and no change records.

## Second reading by E2

1. Compared the delivered item with the repository by `diff` and checked the
   entire existing theorem signature byte for byte. The only changes are its
   proof and two private imports replacing the old private import. Its docstring,
   hypotheses (including flatness and quasi-coherence), six existential maps,
   both initial injections, both exact rows and three squares are unchanged.
   No definition, target or existing statement changes; no change record is needed.

2. Compiled both modules in import order with the prescribed local compiler:
   no errors or warnings (2.5 s and 6.9 s). Read every proof branch: flat tensor
   exactness gives the three consecutive pairs; the product equivalence transports
   the middle object, using its inverse, surjectivity and injectivity in the
   appropriate branches. The restriction and boundary squares reduce on pure
   tensors to scalar multiples of the unextended squares. The difference square
   additionally uses surjectivity of the product equivalence and tensor induction.
   There is one named `sorry`, exactly the reported new theorem, and no forbidden
   declaration or hollow definition. The axiom scratch check is recorded below.

3. Read the new theorem and its node clause by clause. Its original row is
   R-linear and untensored; its pulled-back row is S-linear; its vertical maps
   are the existing `H.baseChangeLinear`, not newly chosen comparisons. Read their
   definition: exact abelian inverse image, the constant-sheaf isomorphism, and
   the coefficient map adjoint to the module-pullback unit. The argument needs
   no exactness of module pullback, so the absence of flatness in this new
   theorem is legitimate. Likewise it needs no quasi-coherence or compactness.
   Inverse image of the free abelian sheaf of an open represents sections on
   the preimage open by adjunction. Its inclusion maps have the same signs;
   exact inverse image preserves the short exact sequence and its Ext class.
   Ext composition then gives the boundary square, and the pullback composition
   isomorphisms identify the displayed base-changed open terms. This explains
   the bridge not supplied by the derived-module-cohomology dependency alone.
   Read Stacks 01EB (arbitrary module, two-open cover, coefficient naturality)
   and 02KH (the Mayer--Vietoris alternative); the latter's qcqs assumptions are
   for bijectivity, not for this construction. The agent-expanded inverse-image
   step is explicitly identified as such, rather than claimed to be in 01EB.
   Checked the empty scheme, an empty cover member (cover forces the other to be
   top), U = V = top (diagonal and difference, zero boundary), degree zero, and
   nonflat S. None contradicts the rows or the three squares. The new theorem
   is a geometric part of the argument: it contains no tensor exactness or
   tensor/product transport. The item's 58-line proof performs those remaining
   steps, so this is not a renaming of the original item.

   Independently searched with LeanFinder for preservation of Yoneda connecting
   maps under exact functors, and with grep for connecting/Ext-composition
   naturality, as well as `rg` through both library roots and DAG nodes. Read
   Mathlib's SheafCohomology/MayerVietoris (the boundary is `extClass.precomp`,
   `sequence_exact` is an Ext result) and Ext/Map (`mapExactFunctor_comp`). These
   support the argument but do not give the displayed geometric identifications.
   Read the existing derived base-change Mayer--Vietoris theorem: it assumes
   qcqs and compact opens and uses another cohomology construction. The existing
   etale results use another site. No duplicate complete comparison was found;
   the remaining bridge cannot be closed in a few minutes from these interfaces.

4. The proof follows the top-down route and genuinely closes its scalar-extension
   part. All new proof imports are private. The original public imports support
   statement types/instances; none was converted or removed. The complete old
   direct dependency list loses only `lem-sc-mayer-vietoris-ringed-space`; this
   is explicitly listed under No longer needed, and is still an indirect
   dependency of the geometric bridge, so no global pruning is claimed. The
   unit `sk-thm-picard-rr` has empty realized statement and step lists; this
   delivery alters neither them nor the unit route and keeps the same
   Mayer--Vietoris induction below its existing flat-base-change ancestor.

5. Read both node JSON files against the Lean. The item's three steps match,
   respectively, obtaining the unextended rows, tensor exactness/product transport,
   and extending the three squares. Their uses have union equal to proof_deps.
   The new node has the full untensored statement, the same chapter and unit,
   source and agent proof origin, three recorded searches (one unavailable),
   created/blueprint/lean records, and a signature matching its new module.
   No fields beyond the permitted proof fields of the existing node are changed.
   The report distinguishes the direct dependency removal from global pruning.

Changes by this second reader: appended this independent review and search
findings. No Lean or node repair was necessary; the one geometric statement
remains explicitly open rather than being reported as axiom-free progress.

Axiom scratch check: `#print axioms` for both
`AlgebraicGeometry.Scheme.Modules.H.baseChange_mayerVietoris` and
`AlgebraicGeometry.Scheme.Modules.H.baseChangeLinear_mayerVietoris` reports
exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The scratch
copy compiled in 6.5 s. The latter axiom is the explicitly reported open bridge.
