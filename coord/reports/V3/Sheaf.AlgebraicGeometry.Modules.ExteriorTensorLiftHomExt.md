## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exteriorTensor_lift_hom_ext` in
`Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt`, preserving its signature
and both existing public imports. Added proof-only imports for preservation of
finite colimits by the underlying abelian-sheaf functor and abelian/epi-mono
instances. The local-surjectivity API is already available through existing imports. Added five fully proved private helpers: restriction of
wedges, local span induction for exterior sheaves, tensor section extensionality,
restriction of tensor sections, and simultaneous local lifts of a finite family.

The proof uses local generation, without local freeness or local splittings.
Updated the existing node's proof, proof_deps, and proof_origin to describe the
actual Lean argument. The unit record has no realized nodes to bypass; the
Riemann–Roch determinant route remains intact. Single-file compilation through
lcompile.py passed without warnings. The finite intersection includes U, so the
empty family (s = 0) gives U itself. Span induction also covers degree zero,
zero modules, and empty opens.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_lift_hom_ext`
(node `lem-sc-exterior-tensor-lift-hom-ext`).

No sorry remains in the delivered module. Added 0 holes and split off 0 statements.
All private helpers are proved. This closes the item's hole, not all imported
construction holes: `exteriorSheafRestriction_existsUnique` and
`exteriorSheafRestriction_laws` in the existing `ExteriorSheaf` module remain
upstream obligations, as permitted by stage 3. No definitions or existing public
signatures were changed, and no other module was adapted.

## No longer needed

Removed the redundant added proof-only import
`Mathlib.Topology.Sheaves.LocallySurjective`; its API is already available through
existing imports. Both original public imports are required by the statement. The original
node had no proof dependencies or named auxiliary modules to prune. Local splitting
and exterior-power basis results mentioned in its old plan are unnecessary; no
specific nodes were named there. The degree-zero isomorphism
`exteriorSheaf_zero_iso` is not used by this proof, but its module remains required
for the exterior-sheaf definitions. No library module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The previous DAG step proposed constructing a map from local splittings and bases.
This is an extensionality statement for arbitrary module sheaves and an arbitrary
epimorphism, so no such splitting or basis hypothesis is available or necessary.
The declaration's existing docstring had the appropriate local-generation proof;
the Lean proof now implements it, using the tensor sheafification adjunction for
the final step. The recorded blueprint source file is absent from this machine's
literature checkout; the statement and proof in its existing module/node were read.
No source statement was changed and no new unproved statement was introduced.


## Second reading by V3

1. Compared the sole delivered Lean module and existing node with the repository
   using `diff`. The entire signature of `exteriorTensor_lift_hom_ext`, from its
   declaration name through `φ = ψ`, is byte-for-byte identical. Its docstring and
   both public imports are unchanged. There are no definition changes, adaptations,
   change records, or new public declarations. Verdict: unchanged interface.

2. Independently compiled the file using `lcompile.py` without errors or warnings.
   Read all five private helpers and the target proof. No `sorry`, axiom, unsafe,
   opaque, implemented_by, or extern declaration occurs in the delivery. A scratch
   copy with `#print axioms` for every helper and the target showed only `propext`,
   `Classical.choice`, `Quot.sound`, and (for the exterior helpers and target)
   `sorryAx`. The latter comes from the existing exterior-presheaf construction
   obligations, not an added hole. `exteriorSheafRestriction` chooses from an
   existence-and-uniqueness statement characterizing the map on spanning wedges;
   it does not choose arbitrary data from mere existence. Verdict: the item's hole
   is closed relative to its existing dependencies, with zero new holes.

3. No statement was split off and no new node was added. Checked the private helper
   arguments: the common neighborhood is `U ⊓ ⨅ i, V i`, so `s = 0` gives `U`;
   no positivity of `r` or `s` is needed by `ιMulti_span`. Empty opens are covered
   by sheaf separatedness, and zero modules require no freeness or rank hypothesis.
   The epi-to-local-surjectivity step applies to the underlying abelian sheaf,
   whose epi follows from preservation of finite colimits. Verdict: the reductions
   are true with exactly the hypotheses supplied.

4. Searched the upstream checkout and `lean/Sheaf` for exterior/tensor
   extensionality and generation, and ran LeanFinder with the distinct query
   "Equality of morphisms of sheaves of modules can be checked on locally generating
   elementary tensor sections". Its hits were general component extensionality and
   generating-section data, not a replacement for the argument here. Read the
   tensor-section definitions and restriction/bilinearity lemmas, the exterior
   sheaf construction, and Mathlib's epi/local-surjectivity theorem. The proof uses
   those existing APIs directly: local lifts give equality on arbitrary wedges,
   two span-and-sheafification inductions give equality on arbitrary factor
   sections, and the tensor sheafification adjunction reduces morphism equality
   to elementary tensors. No basis or local splitting is used. The unit
   `sk-thm-picard-rr.json` has empty realized lists; its determinant-additivity step
   is retained. Tested deletion of each added import: only
   `Mathlib.Topology.Sheaves.LocallySurjective` was redundant. Removed it; the
   other deletions fail respectively on the mapped epi, balanced abelian sheaf,
   or functorial surjective/injective factorization instance. Both original
   public imports remain. Verdict: route retained and imports pruned.

5. Read the delivered node's four proof steps and
   `def-sc-sheaf-exterior-power`. The wedge-restriction step uses the unique
   restriction characterization that node states; the subsequent steps match
   `finite_local_lifts`, `exterior_section_induction`, and `tensor_section_ext`.
   `proof_deps` is exactly the union of the recorded uses, namely
   `def-sc-sheaf-exterior-power`; the original dependency list was empty, so no
   old dependency node is omitted from the pruning report. `proof_origin` names
   V3 and the explicit local-generation argument. The blueprint source file is
   absent locally, as the first report states; this reading checked the existing
   node, preserved theorem/docstring, and unit record rather than claiming to
   have read that missing file. Verdict: DAG agrees with the delivered proof.

Second reading changed only the redundant proof-only import and the report.
No mathematical proof, public signature, definition, or node needed repair.
