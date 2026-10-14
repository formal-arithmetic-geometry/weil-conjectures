## What changed

Repair of return cfdb205fd: made every scheme, morphism and arbitrary algebra binder
of the private `inverseRestrict_smul` explicit, and expanded its scalar-action signature
using `B.right` and `B.hom`. The similarly printed private helper in
`AffineModuleTensorBaseChange` instead fixes its algebra to `f_* O_U` and its structure
map to `f.c`. It cannot be applied to the arbitrary algebra in this theorem, and it is
private. The helpers have different elaborated types; the original local notation hid
that difference from the textual duplicate checker. This implements the return's
explicit-binder remedy without changing any public signature or importing the affine
module. The complete existing proof is retained.

Proved `AlgebraicGeometry.Scheme.Modules.exists_algebraTensorPullbackComparison`
without changing its signature or its existing docstring. The only Lean module changed is
`Sheaf.AlgebraicGeometry.AlgebraTensorPullbackComparison`.

The algebra is constructed as the commutative-ring-sheaf pushout of the inverse-image
structure morphism and `tensorPullbackRingMap`, then pushed forward. The coefficient
map is constructed from the ring inverse-image unit; the pushout equation proves it
commutes with structure morphisms. Private proved helpers identify inverse image after
scalar restriction and the induced scalar-extension isomorphism. Existing
`SheafOfModules.sheafTensorPushoutCancellation` and
`SheafOfModules.inverseImageRegularExtension` give the module comparison and its unit
formula. `Adjunction.leftAdjointUniq` transfers that formula to the supplied adjunction.
No algebra data are chosen from an unproved existence theorem.

Added proof-only imports of `TensorPullbackAdjunction`, `SheafTensorPushoutCancellation`,
`InverseImageRegularExtension`, `InverseImageOperationExt`, and the existing ring/sheaf colimit and pushout interfaces supplied by those imports. The three original public imports stay necessary for the statement.
Updated the existing node's proof, proof dependencies and proof origin to the actual argument.
The required scope-command change record is
`coord/changes/algebra-tensor-pullback-comparison-proof-scopes.md`.
It records the unchanged public signature and all downstream modules; none needs adaptation.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_algebraTensorPullbackComparison`
(node `lem-sc-algebra-tensor-pullback-comparison`).

No holes remain in the delivered module; no holes or new modules were added. The private
canonical comparison and all private helpers have complete proofs. This is a proof, not a
decomposition. Existing imported declarations supply the tensor pushout comparison,
regular extension and inverse-image operation extensionality.

## No longer needed

No original imports removed and no planned dependency pruned. The second reading removed
three redundant added proof imports: `Mathlib.CategoryTheory.Sites.Limits`,
`Mathlib.Algebra.Category.Ring.Colimits`, and
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`; their declarations and
instances are already available through the necessary imported interfaces. This removes
redundant direct imports, not modules from the target import closure. The original tensor-product,
algebra-sheaf and adjunction nodes remain used, directly or through their existing interfaces.
No new nodes are needed. `AffineModuleTensorBaseChange` and
`PushoutRegularModuleComparison` were considered but not imported: their statements fix
the source algebra to a structure algebra, whereas this theorem allows arbitrary algebra
sheaves. Their public lower-level interfaces suffice.

## Where the brief, the DAG or earlier work was wrong

The first delivery used identical local notation in the general scalar-action helper
and the specialized affine helper. The textual duplicate check ignored the different
section binders and notation expansions. Explicit binders and expanded types now expose
the mathematical difference. Neither helper is a duplicate of the other's type.

The DAG's steps 1 and 2 named definitions and the module adjunction but did not expose
an algebra base-change comparison. The missing comparison is available through the existing
sheaf tensor pushout cancellation and inverse-image regular extension interfaces; these are
now recorded as actual proof dependencies. No statement correction was required.

Read Stacks `sheaves.tex`, `definition-pushforward` (0095),
`lemma-adjoint-pullback-pushforward-modules` (0096), and `lemma-pullback-module` (008X).
The source text was retrieved into the sandbox scratchpad because the repository's literature
copy is absent on this machine. The proof uses universal properties and balanced tensor
identities and assumes neither flatness nor nonemptiness; zero algebra and empty open
cases use the same maps. This is below the unit level and changes no realized unit step.

The existing pushout cancellation and regular-extension nodes belong to the proper-base-change
chapter and are used here as sheaf-level tools. They do not replace any realized curve-estimate
unit statement or step. The inverse-image operation extensionality node is used in the same way
as an existing tool for the scalar-action comparison.


## Earlier second reading (a previous round; superseded)

1. Compared the sole delivered module against the repository with `diff`, and checked
   the public theorem signature byte for byte. Verdict: unchanged signature, docstring,
   definitions and public imports; all new declarations are private. The existing scope
   command record covers the additional opens and local section notation. No other
   module is adapted.
2. Compiled the delivered source and a scratch copy with `#print axioms` appended.
   Verdict: clean compilation within 60 seconds; the theorem depends only on `propext`,
   `Classical.choice`, and `Quot.sound`. There is no `sorry`, forbidden declaration,
   or hollow definition. The algebra is the actual ring-sheaf pushout, not an arbitrary
   witness of an unproved existence theorem. The choices of scalar structures and
   comparison isomorphisms come from proved upstream interfaces; the resulting theorem
   has no `sorryAx` dependency.
3. No statements were split off and no holes were added. Read the inverse-image action
   extensionality, regular-extension and tensor-pushout interfaces used by the proof.
   Verdict: the action comparison and unit equations are precisely the required ones.
   Balanced tensor and universal-property calculations include zero rings, zero modules
   and empty opens without additional assumptions. Independent LeanFinder search for
   algebra-sheaf base change found module pullbacks and restriction interfaces, not a
   replacement theorem; Loogle confirmed the left-adjoint uniqueness and unit formula
   already used. Local searches found no shorter existing inverse-restriction comparison.
4. Read the proof from the public theorem down through the canonical comparison and
   its private helpers. Verdict: it constructs the algebra, composes the existing tensor
   and regular-extension isomorphisms, checks the unit on sections, and transports to
   the supplied adjunction. No duplicated target is left as an unproved helper. Removed
   the three redundant added Mathlib imports and verified the reduced import set by
   compilation and an axiom probe. All original proof dependencies remain needed,
   including the tensor construction indirectly through its existing interfaces.
   `dag/units/sk-thm-curveestimate.json` realizes `thm-sc-proper-cohomology` as its
   statement; this subordinate comparison bypasses no realized unit statement or step.
5. Compared the old and delivered node records. Verdict: only `proof`, `proof_deps`,
   and `proof_origin` change, and the steps describe the Lean argument. Restored
   `def-pur-sheaf-tensor-product` to step 3 and `proof_deps`, because the argument uses
   the tensor construction through cancellation and regular extension. No new nodes,
   statement changes or changes to the unit are required.

Second reading changed only redundant added proof imports, the missing indirect tensor
proof dependency, and this report. The complete original proof is retained.

## Second reading by S1

1. Compared the delivered Lean module and node against the repository using `diff`
   and separately compared the existing public theorem signature byte for byte.
   Verdict: the signature, docstring, public imports and existing definitions are
   unchanged. Four added imports are proof-only; every added declaration is private.
   The scope-command change record describes the additional opens and local notation.
2. Read all proofs and constructions; compiled the sole module locally (20.0 seconds).
   A fresh scratch copy compiled in 20.7 seconds and printed exactly
   `propext`, `Classical.choice`, and `Quot.sound` for the public theorem. No `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by` or `extern` occurs in the source. The algebra
   is constructed from a categorical pushout. Inverse scalar actions are uniquely
   determined by restriction and unit compatibility; adjunctions and comparison
   isomorphisms are obtained from proved interfaces. No arbitrary algebra witness
   is taken from an unproved existence theorem. Verdict: genuine proof, no new holes.
3. There are no split-off statements or new nodes. Checked the exact imported
   pushout-cancellation inverse-unit formula and regular-extension normalization.
   They compose in the directions used, and require neither nonzero rings nor
   nonempty spaces. Independent LeanFinder search for inverse-image algebra
   underlying-module base change returned scalar restriction and module pullback
   interfaces, no replacement comparison. Local searches confirm the affine helper
   fixes its algebra to the structure direct image, whereas this explicit helper
   allows arbitrary B. The analogous change-of-rings helpers elsewhere are private.
   Verdict: no unjustified split or accessible duplicate.
4. Read from the public adjunction transport down to the constructed pushout and
   scalar-action proof. The canonical helper is fully proved, rather than a renamed
   open target. Each added import supplies a comparison actually used. All original
   proof dependencies remain used, including tensor construction through the imported
   interfaces; no original dependency is pruned. Checked the curve-estimate unit's
   `realized` statement and empty step list: this subordinate comparison bypasses
   none of them. Verdict: route retained and pruning report complete.
5. Node diff changes only `proof`, `proof_deps`, and `proof_origin`. Its four steps
   match the constructed algebra, inverse restriction, tensor/regular comparison,
   and adjunction transport. Dependencies are exactly the union of the recorded
   uses. Verdict: Lean and DAG agree; no new node or unit edit needed.

This second reading changes only this report; the explicit-binder repair and
complete Lean proof are retained.
