## What changed

The unchanged declaration `AlgebraicGeometry.affine_pseudoCoherent_principal_model`
now applies `AlgebraicGeometry.affine_pseudoCoherent_principal_sheaf_model` to obtain
a finite-free module complex and an isomorphism of its associated-sheaf derived
complex with that of the localized input. It then uses
`exists_affineQCohDerivedEquivalence`, its comparison natural isomorphism, and
`Functor.preimageIso` for the fully faithful composite of the equivalence and the
quasi-coherent full-subcategory inclusion to reflect that isomorphism to modules.
The standard derived category on Spec(A_f) supplies the new lemma's auxiliary
instance without adding a hypothesis to the existing theorem.

Replaced the undelivered Witness module/node with
`Sheaf.AlgebraicGeometry.AffinePseudoCoherentPrincipalSheafModel` and node
`lem-pc-affine-pseudo-coherent-principal-sheaf-model`. All newly added imports used
only for proofs are plain imports. No existing statement, visibility, definition,
or public import changed. No change record or forced adaptation is required.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.affine_pseudoCoherent_principal_model`
(node `lem-pc-affine-pseudo-coherent-principal-model`), 1 of 1 original holes.
Hole added: `AlgebraicGeometry.affine_pseudoCoherent_principal_sheaf_model`
(node `lem-pc-affine-pseudo-coherent-principal-sheaf-model`), the finite-free
construction and sheaf-derived comparison. This is a decomposition: one closed,
one added, net zero holes. The target still depends on `sorryAx`, both from this
construction and potentially from the existing comparison theorem. It is not an
axiom-free completion. No other holes are added, and no data is chosen in a
definition from an unproved existence theorem.

## No longer needed

Removed direct proof imports `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`
and `Sheaf.AlgebraicGeometry.DerivedCategory` from the item. The former remains a
proof import of the construction module; the latter is available through existing
public statement imports and is explicitly imported for the new statement.
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` remains a proof import.

Every old proof dependency absent from the item's new direct proof_deps:
`def-pc-derived-category`, `lem-sc-derived-open-restriction-adjunction-exact`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`lem-weil-pbc-spec-module-tilde-sections`. The three comparison facts remain in
the construction node's proof_deps; the derived-category definition remains in
statement dependencies. No original module is pruned from the import closure.
The proposed witness restatement and its node are removed before delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker's witness had exactly the original hypotheses and the original
conclusion unfolded from `DerivedCategory.IsPseudoCoherent`. Unfolding, obtaining,
and repackaging the same existential was not a reduction. Its report also claimed
no imports had been removed, although the diff removed three. Both faults are
repaired. The remaining hole stops before derived reflection; that step is now
proved using the already stated comparison theorem, rather than postponed under
another name. The construction itself requires further formal work and cannot be
closed merely by applying the ordinary tilde adjunction or its sections formula.

## New nodes

`lem-pc-affine-pseudo-coherent-principal-sheaf-model` states only the construction
of finite free terms and differentials and the isomorphism after sheafification
on Spec(A_f). Its docstring explains restriction, transport, termwise lifting,
zero terms above the bound, natural principal-open localization, and composition
of the sheaf-derived isomorphism. Its source is the local comparison in
[Stacks Tag 08E7](https://stacks.math.columbia.edu/tag/08E7); reflection is excluded.
Fresh leanfinder, loogle, and grep searches are logged in searches.jsonl.
The additional LeanSearch query returned HTTP 500 and is recorded as unavailable.
No change record is needed for replacing an undelivered new declaration.

## Second reading by S1

1. PASS after repair. Compared the item with the repository using diff and
   checked that its existing declaration signature is byte-for-byte unchanged.
   No existing definition, visibility, or public import changed. The additional
   module and theorem were absent from the repository. All changes are confined
   to the sandbox; no source-repository git command was run directly.
2. PASS with the explicitly reported open construction. Compiled both modules
   locally in import order through lcompile.py with no errors or warnings.
   There is exactly one `sorry`, the named construction theorem, and no `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definition. A scratch
   copy with `#print axioms` checks both declarations; allowed standard axioms and
   `sorryAx` are the only dependencies. The delivery tool repeats its axiom probe.
3. PASS after replacing the invalid restatement. Read the definition of ring
   pseudo-coherence and the affine equivalence statement. The new construction
   produces an isomorphism of sheaf-derived objects, and the actual proof reflects
   it using the equivalence. The construction omits the unnecessary module-derived
   category instance. Checked empty D(f)/zero ring, f a unit, zero ranks, zero
   complex, and negative upper bounds in the mathematical proof. The new theorem
   has a complete docstring and a matching node. Fresh searches with different
   wording and rg on the library and upstream AlgebraicGeometry sources found no
   existing full construction theorem;
   Mathlib's preimageIso supplies the final reflection without a new hole.
4. PASS. The shortest available reflection route is the existing affine derived
   equivalence followed by full faithfulness; no new reflection lemma is stated.
   Proof-only imports are plain imports, and direct pruning is exhaustively
   recorded above. Read dag/units/sk-thm-picard-duality.json: its realized statement
   and step arrays are empty, and this item is below the unit level. No unit route
   is replaced or changed, and the planned affine comparison is explicitly used.
5. PASS. The existing node now records construction and reflection separately,
   with proof_deps exactly the facts those steps use. The new node records the
   remaining construction, its actual signature, complete hypotheses, source,
   searches, creation metadata, unit/chapter, blueprint origin, and dependency
   union. Its statement dependencies do not cite the parent, avoiding a cycle.

Changes by the second reader: removed the definitional witness restatement;
replaced it with the strictly partial sheaf-model construction; proved reflection
through the existing affine derived equivalence; removed a superfluous instance
from the new statement; repaired imports, both nodes, and this report.
