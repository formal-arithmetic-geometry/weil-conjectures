## What changed

Replaced the sorry in AlgebraicGeometry.koszulOpenHom_chain_evaluation by a complete
Lean reduction. The existing principal-unit theorem proves invertibility of the restricted
augmentation. With v its inverse, the given equation forces ψ = v ≫ R(Q(t)).
Naturality of evaluation reduces the requested class to the identity of the Koszul tail;
postcomposition naturality of the explicit class then gives the formula for t.
No existing signature, definition or visibility changes.

## Proved and sorry left

Closed: AlgebraicGeometry.koszulOpenHom_chain_evaluation (one original hole).
Added two holes, making this a decomposition rather than a completed independent proof:

- AlgebraicGeometry.koszulOpenHom_identity_evaluation, node
  lem-sc-koszul-open-hom-identity-evaluation. Natural Hom equivalences with normalization
  only on the identity of the fixed Koszul tails.
- AlgebraicGeometry.koszulOpenHom_chain_class_naturality, node
  lem-sc-koszul-open-hom-chain-class-naturality. Functoriality of the explicitly constructed
  stage-to-derived-sections class, without any evaluation equivalence or augmentation.

The item itself contains no sorry. Both remaining holes are public named theorems in
separate modules, with source and complete proofs in words. No data was chosen from a
new existence theorem in a definition. No private hole or new axiom was introduced.
The existing principal-unit theorem is used as a dependency, as intended in stage 3.

## No longer needed

Removed the direct proof-only import of
Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology from the item. It remains
needed by the identity-normalization subproblem, so its module is not globally pruned.
The theorem koszulOpenHom_chain_representatives is not used: its module stays as a
public import because its concrete class definitions occur in the unchanged statement.
The direct proof route no longer needs a general coefficient-level fraction calculation;
it needs that calculation only for identity maps, then functoriality. No existing module
is globally pruned, and no unit statement or step is bypassed (the unit's realized lists
are empty). Definition dependencies remain available through the public statement imports.
Explicit accounting for the old proof_deps: def-sc-koszul-open-system remains a direct
proof dependency (the basic-open identification). The other old direct dependencies,
lem-pc-derived-structure-sheaf-hom-hypercohomology,
def-sc-koszul-cech-comparison-construction, and
lem-sc-koszul-open-hom-chain-representatives, are no longer theorem dependencies of the
combining proof. Hypercohomology is retained in the identity subproblem's proof plan;
comparison construction and chain representatives remain definition/signature dependencies
through the public import, and the new lemmas use their concrete constructions.
Thus none of these modules is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's single chain-evaluation step concealed two independent tasks: normalization
on the Koszul identity and postcomposition naturality of the specified stage class.
The generic hypercohomology theorem asserts an existential natural equivalence, without
fixing its normalization, so its statement alone does not give the explicit Koszul formula.
This delivery makes that missing normalization explicit instead of applying an arbitrary
equivalence to the fraction class. The source was checked at Stacks Tags 08D1, 08DD,
and 09M1 online; local Stacks source files are absent on this machine. Edge cases checked
for both new statements: r=0 (empty cover), zero ring, zero complexes, zero chain maps;
naturality also works for non-quasi-coherent complexes because it uses linearity and
resolution comparison, not acyclicity. No mathematical source or target error found.

LeanFinder, Loogle and Mathlib grep searches ran through msearch.py and are recorded in
searches.jsonl. They found generic exact functor and tilde ingredients, no exact normalized
identity or explicit-class theorem. LeanSearch returned Internal Server Error, recorded
as unavailable. Blueprint searches for Koszul, Koszul identity and Koszul functorial
found no duplicate of either new statement. No agents were started.

## New nodes

lem-sc-koszul-open-hom-identity-evaluation:
lean/Sheaf/AlgebraicGeometry/KoszulOpenHomIdentityEvaluation.lean. Specializes the hard
fraction/sign normalization to identity chain maps, and supplies the natural equivalences.
It does not assert the original formula for arbitrary F and t.

lem-sc-koszul-open-hom-chain-class-naturality:
lean/Sheaf/AlgebraicGeometry/KoszulOpenHomChainClassNaturality.lean. States functoriality
of the explicitly specified class for arbitrary coefficient maps. It neither constructs
Hom equivalences nor identifies a class with the inverse of an augmentation.

Both nodes retain the item's chapter, unit and nearest blueprint ancestor. The item's
proof_deps and proof_origin follow the actual combining proof. No change records needed.

## Second reading by Q2

1. Compared the delivered item with the repository using diff and checked the original
   theorem signature byte for byte: identical. Only proof, scoped elaboration options,
   and proof-only imports changed. No existing definition or visibility changed; there
   are no interface change records or forced adaptations.
2. Compiled all three modules in dependency order with lcompile.py: clean (3.1, 6.8,
   29.8 seconds). The item contains no sorry; the two new modules each contain exactly
   the reported public theorem hole. No axiom, unsafe, opaque, implemented_by, extern,
   or hollow definition was added. The scratch #print axioms check and delivery probe
   verify only the standard axioms and sorryAx from the reported open dependencies.
3. Read both new statements, docstrings, nodes, and the constructions of StageClass,
   koszulCechCocone, and principalCechDerivedComparison. Verdict: true proper parts of
   the argument, not a restatement. Identity normalization only concerns fixed Koszul
   tails; class naturality concerns postcomposition and asserts no Hom equivalence.
   For r=0 and the zero ring U is empty and the groups vanish. For r=1 and f invertible,
   the identity formula is division by f^(e+1), with sign +1. For zero maps and zero
   complexes naturality reduces to zero; at e=0 the exponent is 1, never 0. Arbitrary
   coefficient complexes are allowed for naturality: invertibility on intersections
   gives uniqueness of the explicit fractions, and resolution comparison is natural.
   Checked Stacks 08D1, 08DD, 09M1 online. Fresh LeanFinder, Loogle, Mathlib grep and
   repository searches with postcomposition/cocycle/adjunction terminology found
   generic ingredients, no duplicate of either split-off statement. In particular,
   koszulChain_restriction_formula only gives an equivalence separately for each F,
   not a family natural in every derived arrow, so it cannot replace normalization.
4. Read the combining proof from the top: augmentation invertibility, cancellation,
   identity normalization, and postcomposition naturality. No shorter available route
   closes either remaining task in a few minutes; generic hypercohomology does not fix
   normalization. The public import is necessary for the unchanged signature, and the
   new proof-only imports supply the used lemmas. The identity subproblem's imports
   record its remaining proof plan. The unit sk-thm-picard-duality realized lists are
   empty, and no realized unit node or step has been bypassed. Corrected the report's
   explicit accounting of all old proof_deps; no module is globally pruned.
5. Checked each recorded Lean statement against its module, and each proof_deps against
   the union of proof-step uses: exact matches. The existing node changes only the
   stage-3-owned route fields; new nodes have source, docstring proof, searches,
   provenance, blueprint, chapter/unit, and Lean records. Added fresh independent search
   evidence to the new nodes and corrected the naturality node's copied origin note.

Second reading changes: report dependency accounting and review section; independent
search records and naturality proof_origin note. Lean proofs and signatures retained.
This remains a decomposition: one hole closed, two added (net minus one), not a
completed independent proof or a claim of positive ledger progress.
