## What changed

Closed `AlgebraicGeometry.SingleComplexBaseChange.exists_localizedComparison_quasiIso_square`
without changing its statement or public imports. Added proof imports of
`Sheaf.Algebra.Homology.ModuleStalkExact` and the new proved module
`Sheaf.Algebra.Homology.BaseDerivedTensorModelQuasiIsoComparison`.

Two new, fully proved algebraic helper modules separate ordinary counit naturality from
localization by the extension/restriction adjunction. The ordinary theorem constructs the
cohomology isomorphism using uniqueness of universal left-derived functors, proves its
E-linearity by tensor induction, and proves comparison compatibility by the counit and
homology naturality equations. The localized theorem proves the termwise localization
square on generators and transposes the ordinary square. The item proves stalk
quasi-isomorphism preservation and tensorStalkIso naturality, then composes the squares.

All three modules compile locally without warnings. No definition or existing interface
changed. Only the authorized sandbox was edited manually; the dry-run delivery tool
prepares its temporary commit according to the brief.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_localizedComparison_quasiIso_square`
(node `lem-pc-localized-comparison-quasiiso-square`).

Also proved:
- `ModuleCat.exists_baseDerivedTensorModel_quasiIso_ordinary_comparison`
  (`lem-pc-base-derived-tensor-model-quasiiso-ordinary-comparison`).
- `ModuleCat.exists_baseDerivedTensorModel_quasiIso_comparison`
  (`lem-pc-base-derived-tensor-model-quasiiso-comparison`).
- Private tensor-linear lifting and tensorStalkIso naturality helpers.

No sorry remains in any delivered module. Holes added: 0. Split off: 0.
The item still depends on existing model and scheme-pullback constructions; this does
not assert that all previously imported dependencies are free of sorry.

## No longer needed

None. No original imports were removed, and every original proof dependency is still used.
The proof needs no K-flatness of P or G, no invertibility of ordinary tensor pullback,
and no new resolution theorem. Both new modules are used by the proof. The unit's
recorded realization is unchanged; its statement and route were not bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original plan was correct but lacked a reusable theorem
expressing naturality for the model interface. This delivery proves that theorem, including
its action-linearity and counit equations, rather than leaving a new assumption.

The local literature directory contained only indices, so source text was fetched read-only
from the Stacks Project repository into the sandbox scratchpad. Read More on Algebra
`lemma-derived-base-change` (06Y6), and perfect.tex `equation-bc` and
`lemma-single-complex-base-change-condition` (0DJ8). The model-coordinate details are an
agent-written proof from the model's universal property, not a verbatim Stacks proof.
LeanSearch returned Internal Server Error, recorded as unavailable. LeanFinder and Mathlib
source searches found generic tools but no exact model-level statement.

Edge cases: s may be the identity, zero complexes are allowed, any degree is allowed,
and no flatness of B or D is required. The constructed e is an isomorphism because
restriction is exact and the derived functor preserves the resulting isomorphism.
Ordinary extension is never asserted to preserve quasi-isomorphisms; only its natural
map occurs on the target side of the square. Different model choices are accounted for
by universal left-derived uniqueness and the model action equations.

## New nodes

`lem-pc-base-derived-tensor-model-quasiiso-ordinary-comparison`, in
`dag/nodes/sec-picard-framework/`: the fully proved ordinary comparison square for
arbitrary A-module cochain complexes, a quasi-isomorphism, and two base-derived tensor
cohomology models. Its module is
`Sheaf.Algebra.Homology.BaseDerivedTensorModelQuasiIsoOrdinaryComparison`.

`lem-pc-base-derived-tensor-model-quasiiso-comparison`, in
`dag/nodes/sec-picard-framework/`: the fully proved localized comparison square obtained
by transposing the ordinary square. Its module is
`Sheaf.Algebra.Homology.BaseDerivedTensorModelQuasiIsoComparison`.

The original node's proof, proof_deps and proof_origin now record the actual proof.
No change record is necessary: existing signatures, definitions and visibility are unchanged.

## Second reading by Q3

1. PASS: compared the item's complete diff with the repository. The only existing
   declaration keeps its signature byte for byte, and its docstring and public import
   are unchanged. The additions are a private proved naturality helper, two proof-only
   imports, and the completed proof. Both other modules are new. No definition or
   target statement changes; no change record or forced adaptation is needed.
2. PASS: independently compiled all three modules in import order with lcompile.py;
   no errors or warnings. Searched all delivered Lean for sorry and forbidden trust
   mechanisms: none. Scratch copies with #print axioms show exactly propext,
   Classical.choice and Quot.sound for both new public theorems. The scheme theorem
   additionally reaches sorryAx through existing imported constructions; this delivery
   adds no holes and does not claim to close those dependencies. The model transport
   constructs its isomorphism from universal derived-functor uniqueness, not from an
   unproved arbitrary existence witness. The chosen stalk isomorphism used in the
   private helper has its components fixed by the existing specification.
3. PASS: there are no split-off statements left unproved. Read both new theorem
   statements and proofs: the ordinary square is proved from the model fields, and
   the localized square is proved by the scalar adjunction and generator equations.
   Neither assumes tensoring preserves the given quasi-isomorphism. Identity maps,
   zero complexes, arbitrary degrees, and nonflat scalar extensions cause no extra
   assumptions. Repeated searches with different wording: LeanFinder for counit
   compatible universal-derived-functor isomorphisms returned generic leftDerivedNatIso
   tools; Loogle did not recognize Functor.leftDerivedUnique; rg over both library
   roots found generic uniqueness applications but no existing model-level square.
   The upstream exact-functor comparison requires exactness of scalar extension and
   cannot replace this proof for arbitrary B. Both new nodes include sources, proof
   steps, searches and matching Lean records.
4. PASS: read the proof from the original theorem down through localized transport
   and ordinary transport. The ordinary proof uses Mathlib's universal uniqueness,
   homology naturality and tensor induction; the localized proof uses the ordinary
   result and adjunction. Every import supplies signature data or a used proof.
   All three old proof dependencies remain used, so No longer needed is complete.
   Read dag/units/sk-thm-picard-semicon.json: realized is unchanged, and this delivery
   changes only the representative-independence argument below its unit route.
5. PASS: diffed the existing node; only proof, proof_deps and proof_origin change.
   Its steps match stalk exactness, model transport, tensorStalkIso naturality and
   composition of homology squares. Read both new nodes against the Lean: their
   ordinary and localized squares, hypotheses and dependency unions agree.

Second reading changed only this report, recording the independent checks and the
remaining imported sorryAx explicitly. No Lean or DAG repair was necessary.
