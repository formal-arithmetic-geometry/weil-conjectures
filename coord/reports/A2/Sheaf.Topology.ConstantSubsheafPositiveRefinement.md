## What changed

The target theorem now combines two strictly simpler intermediate results: `positive_refinement_data` constructs the compact positive component data, and `positive_refinement_factor` constructs the factorization map. Their modules are imported privately by the target proof. The target statement and all existing signatures are unchanged.

## Proved and sorry left

One original hole is closed in the body of
`TopCat.Sheaf.constantSubsheaf_positive_refinement`, by combining two strictly smaller
parts of the argument. Two holes are added:

- `TopCat.Sheaf.positive_refinement_data`, node
  `lem-sc-constant-subsheaf-positive-refinement-data`;
- `TopCat.Sheaf.positive_refinement_factor`, node
  `lem-sc-constant-subsheaf-positive-refinement-factor`.

This is a decomposition, not a completed proof: one hole closed, two holes added,
net -1 hole in the affected import closure. Zero of the one original theorem is proved
without `sorryAx`; its body is now a genuine reduction to the finite signed partition
construction and a gluing factorization. No original signatures or definitions changed.
There are no holes in data definitions and no data definition chooses a witness of an
unproved existence theorem. The partition record is an ordinary structure, and its
existential witness is eliminated only inside the proof of the target proposition.

## No longer needed

No module or dependency node is pruned from the import closure. The target's redundant
direct proof import of `Sheaf.Topology.ConstantSheafLocallyConstantComparison` is removed;
the comparison is now imported privately by the data-construction module. Both old
proof dependencies, `lem-sc-constant-sheaf-locally-constant-comparison` and
`def-sc-abelian-open-extension-by-zero`, remain used in the two intermediate nodes.
The parent node's immediate dependencies are the two new lemmas. The factor module's
redundant direct public imports of `Mathlib.CategoryTheory.Sites.ConstantSheaf` and
`Mathlib.Topology.Sheaves.Abelian` are removed, since its data module supplies them.
The data module's comparison import is private because it serves only the proof.

## Where the brief, the DAG or earlier work was wrong

The first worker's proposed factorization theorem was false. Its data record contained
no equation relating the old map to the new components. In particular, n = 0 made
all positivity and unit-value fields vacuous, for any original g. On a one-point space,
take K = C = the constant integer sheaf, ι and isoC identities, m = 1, U the whole
space, and g the canonical isomorphism from its one summand to K. The empty record
would force this nonzero g to factor through the empty coproduct, which is zero.
The accompanying data-existence lemma was therefore vacuous, not the claimed finite
fibre construction. The original target statement and its DAG argument are sound.

The second reading repairs the record by retaining the finite disjoint partition,
zero pieces, parent indices, signed restriction equations, and old unit sections.
The data lemma now supplies only this finite local construction; the factor lemma
supplies only its gluing and morphism comparison. Neither is a restatement of the
whole target. Their complete docstrings explain the constructions and universal
properties, including the canonical unit compatibility needed for integer labels.

## New nodes

`lem-sc-constant-subsheaf-positive-refinement-data` records the finite signed partition
construction, including compact positive component maps, zero pieces, coverage and
all restrictions relating it to g. Its proof uses the locally constant comparison
and the explicit extension-by-zero construction.

`lem-sc-constant-subsheaf-positive-refinement-factor` records factorization for a
record with precisely those partition and section equations. It uses compatible
sheaf gluing, the universal property of the integer extension and coproduct
extensionality. Its statement depends on the data node. Both new nodes include
actual logged Mathlib searches; LeanSearch was unavailable. No change record is
needed: only the original theorem's proof and private imports change, and both
intermediate modules are new.

## Earlier second reading (a previous round; superseded)

The intermediate statements are strictly simpler than the target: one supplies only the refined component data and the other supplies only the factorization for that data. The target proof is a direct existential packaging and preserves the unit route.

## Second reading by A2

1. Compared every delivered module with the repository version. The only existing
   module is the target; its declaration signature and all existing public imports
   are byte-for-byte unchanged. Its body is replaced by witness packaging and a
   redundant private import is removed. The data and factor modules are new, with
   no existing downstream users. Verdict: no accidental interface change.
2. Compiled all three modules locally in import order with lcompile.py, and checked
   `#print axioms` in scratch copies for the structure, its constructor and all three
   theorems. The structure and constructor use only propext, Classical.choice and
   Quot.sound. The two open lemmas and the reduced target additionally use sorryAx,
   exactly as reported. No axiom, unsafe, opaque, implemented_by, extern, anonymous
   hole, partial proof hole or definition hole occurs. Verdict: valid decomposition,
   not an axiom-free proof.
3. Rejected the original factor lemma by the empty-record, nonzero-map counterexample
   above. Tested the repaired statements on m = 0, n = 0, empty opens, all-zero
   components, negative values and overlapping original domains. Each original
   domain has its own partition; partitions of different domains may overlap. For
   n = 0 the zero and coverage equations force every original unit image to vanish,
   so the factorization is valid. Searched with different terms through leanfinder,
   loogle and rg/msearch grep. Mathlib provides finite ranges, clopen fibres, sheaf
   gluing and the constant-sheaf/global-sections adjunction, but no exact statement
   for this custom extension construction. The existing local integer generator
   gives only a stalk-lifting conclusion, not the exact unit equation or uniqueness
   required here. Verdict: the repaired holes are true, needed, strictly smaller
   parts, with complete source/proof docstrings and matching nodes.
4. Read from the original theorem downward, retained its finite-fibre and signed
   gluing route, and removed redundant imports. No short existing library theorem
   closes either remaining construction as stated. Both old proof dependencies are
   retained transitively and listed under No longer needed, with no closure module
   pruning. Read dag/units/sk-thm-curveestimate.json: this item realizes neither its
   statement nor a prescribed step; that unit's realized route is unchanged.
   Verdict: the unit route is preserved and pruning is fully reported.
5. Checked the nodes' Lean signatures, partition descriptions, source, statement
   dependencies, proof steps, their union as proof_deps, proof_origin, created fields,
   blueprint ancestry, chapter, unit and logged searches. The parent applies the two
   new lemmas; the data node retains both original dependencies; the factor node's
   statement depends on the data node and its proof uses extension by zero.
   Verdict: node metadata agrees with the repaired Lean and the planned open proofs.

Changes in this reading: repaired the false factorization hypothesis by adding the
partition and section-recovery fields to PositiveRefinementData; expanded both proof
docstrings; made the comparison proof import private; removed redundant imports;
corrected the new nodes' statements, dependencies and search records; and corrected
the progress report to count this as a decomposition (one hole closed, two added).
