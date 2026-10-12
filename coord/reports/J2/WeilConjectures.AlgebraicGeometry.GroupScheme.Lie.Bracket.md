## What changed

Changed only proofs in
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket`.

- `AlgebraicGeometry.GrpObj.commutator_mem_mixedPoints`: precomposition is a group
  homomorphism. On the epsilon axis the delta point becomes the identity, and on the
  delta axis the epsilon point becomes the identity. The two cross-axis identities
  follow from the existing naturality theorems for dual-number projection and inclusion.
  Group cancellation then makes both restrictions of the commutator the identity.
- `AlgebraicGeometry.GrpObj.infPointsMap_infBracket`: apply the injectivity of the
  existing mixed-point equivalence. Its value on a bracket is the commutator.
  Postcomposition by a group homomorphism preserves multiplication and inverses,
  while associativity commutes postcomposition with the mixed-parameter map.
- `AlgebraicGeometry.GrpObj.infBracket_mem_range_infPointsMap`: take the mixed
  commutator lift supplied by the range hypothesis. Cancel the monomorphism on each
  axis to show that this lift is a mixed point of the subgroup. Apply the inverse
  mixed-point equivalence, then its injectivity in the ambient group, to identify
  the image of the resulting infinitesimal point with the required bracket.

Added the proved private helper `AlgebraicGeometry.GrpObj.mixedEquiv_infBracket`,
which exposes the inverse-equivalence cancellation used by the two latter proofs.
All signatures, definitions, public imports, and existing docstrings are preserved.
The sandbox file compiles without warnings through the prescribed lcompile.py wrapper.
No new dependencies or statements with sorry are introduced.

## Proved and sorry left

Closed three of the original nine sorry occurrences:

- `AlgebraicGeometry.GrpObj.commutator_mem_mixedPoints`.
- `AlgebraicGeometry.GrpObj.infPointsMap_infBracket`.
- `AlgebraicGeometry.GrpObj.infBracket_mem_range_infPointsMap`.

The following original holes remain untouched (six sorry occurrences):

- `AlgebraicGeometry.GrpObj.toMixed_bijective` (one occurrence).
- `AlgebraicGeometry.GrpObj.instLieRingLie` (textual declaration name
  `instance instance : LieRing (Lie G)`): its `add_lie`, `lie_add`, `lie_self`,
  and `leibniz_lie` fields (four occurrences).
- `AlgebraicGeometry.GrpObj.instLieAlgebraLie` (textual declaration name
  `instance instance : LieAlgebra Γ(S, ⊤) (Lie G)`): its `lie_smul` field (one occurrence).

The Lie construction belongs to the existing `def-wf-lie-algebra-derivation` node
and unit `sk-d-tangent`; the subgroup bracket inclusion is used in the Lie-inclusion
step of `lem-ag-closure-commutators`, unit `sk-i-restriction`. Their existing Lean
Audit records name the open declarations in this module, rather than assigning a
separate node to each declaration. No holes were added or split off.

The new proofs still depend on the original `toMixed_bijective` hole through
`mixedEquiv`. They close the three local holes without claiming that the transitive
axioms of these declarations are now sorry-free.

## No longer needed

None. No imports were removed or added. All three public imports supply existing
statements, definitions, or already proved arguments in this module. No unit route
is bypassed, and no node or module is claimed to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

The nodes found by searching for this module mention it in their `lean_audit` open
lists; their actual `lean.module` records refer to other modules. There is therefore
no declaration-specific numbered DAG proof for the three elementary obligations
proved here. Their existing docstrings do supply the arguments: restriction to
axes, naturality of the commutator, and cancellation through a monomorphism.
Those arguments are now implemented directly in Lean, using only existing APIs.

Searches through msearch.py used Lean Finder, Loogle, and Mathlib grep. No direct
Mathlib group-scheme bracket theorem was found. Loogle located `MonoidHom.map_mul`;
local source inspection supplied `MonObj.comp_mul`, `GrpObj.comp_inv`,
`MonObj.mul_comp`, `GrpObj.inv_comp`, and dual-number naturality. The untouched
source checkout still has the same nine holes as the initial module.

## Second reading by J2

1. Compared the complete delivered module with the repository using `diff -u`.
   Verdict: all existing declaration signatures, definitions, docstrings and
   imports are byte-for-byte unchanged. Only three proof bodies changed; the
   new private helper is equivalence inverse cancellation, with a complete proof.
   No change record is needed.
2. Read every proof, and compiled the file through `lcompile.py`: no errors or
   warnings. Verdict: the three proofs are valid. No new sorry, axiom, unsafe,
   opaque, implemented_by or extern was introduced, and no definition contains
   sorry. A scratch copy with `#print axioms` checked the three closed theorems
   and `mixedEquiv`: only the standard axioms and the pre-existing `sorryAx`
   dependencies occur. The existing equivalence is determined by the concrete
   map `toMixed` and its bijectivity theorem; it is not an arbitrary existence
   witness. Six original sorry occurrences remain as listed above.
3. There are no split-off statements or new nodes. Verdict: no restatement or
   decomposition was introduced. The private helper is exactly
   `Equiv.apply_symm_apply`. Checked the trivial-group and identity-homomorphism
   cases of the arguments: restrictions and commutators reduce to the identity,
   and cancellation uses precisely the stated monomorphism hypothesis.
4. Searched the library and upstream source for mixed commutators, `toMixed`,
   bracket functoriality and range inclusion; inspected existing dual-number
   axis calculations and categorical group APIs. Verdict: no shorter proved
   group-scheme result replaces these arguments; the upstream module has the
   original holes. The proof uses elementary existing APIs directly. All three
   public imports support existing signatures or definitions, none was added,
   and no old proof-dependency import or node was dropped. Read the `realized`
   fields and routes of `sk-d-tangent` and `sk-i-restriction`: neither is bypassed.
5. Inspected the relevant nodes' `lean`, `lean_audit`, `proof`, `proof_deps`, and
   `proof_origin`. Verdict: no node has this module as its primary `lean.module`;
   the elementary obligations occur in audit records of the existing Lie and
   commutator nodes. Their higher-level routes and dependency sets are unchanged,
   so no node edit is warranted for these local proofs. The first report correctly
   distinguishes local hole closure from transitive sorry-free proofs.

Changes by the second reader: added this review and explicit axiom verification.
No Lean repair was necessary; the proofs were retained unchanged.
