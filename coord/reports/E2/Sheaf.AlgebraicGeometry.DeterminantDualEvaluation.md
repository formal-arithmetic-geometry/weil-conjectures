## What changed

Replaced the sorry in `AlgebraicGeometry.determinant_dual_evaluation` by a complete
Lean reduction. The original signature and public imports are unchanged. The proof
constructs the split complex `Z → M → M`, with `Z` the free sheaf on the empty type,
and proves that Z is zero using its coproduct universal property. The existing
`Scheme.Modules.determinant_shortExact` applied with ranks `0,d,d` supplies the
invertibility of `exteriorSheaf M d`. Only its invertibility clause is used.

Added the proof imports `WeilConjectures.AlgebraicGeometry.Modules.Dual`,
`Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact`, and
`Sheaf.AlgebraicGeometry.DeterminantExteriorDualIso`. The new module states the
strict intermediate comparison `AlgebraicGeometry.exteriorSheaf_dual_iso`.
Tensoring that comparison with the identity and composing the braiding with the
already proved `Scheme.Modules.nonempty_tensorObj_dual_iso_unit` completes the
original conclusion. Updated the original node's proof, proof_deps and proof_origin.

Both delivered modules compile without warnings through lcompile.py. The import
cycle checker permits both existing proof imports. No existing statement,
definition, universe, binder, or public import changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.determinant_dual_evaluation`
(node `lem-sc-determinant-dual-evaluation`), the sole original hole.
No sorry remains in the item's module.

Added: `AlgebraicGeometry.exteriorSheaf_dual_iso`
(node `lem-sc-determinant-dual-evaluation-dual-identification`), in
`Sheaf.AlgebraicGeometry.DeterminantExteriorDualIso`.
Its proof is exactly `by sorry`, with a source and a complete local finite-free,
restriction-compatible, gluing proof in its docstring and node.

This is a decomposition, not an unconditional proof: one original hole closed,
one new hole added. The already existing `Scheme.Modules.determinant_shortExact`
remains unproved in its own module and is an intended next dependency, not a new
hole of this delivery. The invertible-sheaf evaluation is already proved.

Edge cases of the new comparison were checked mathematically: degree zero uses
empty wedges and the dual of the structure sheaf; degree one is ordinary sheaf
duality; on a free rank-d sheaf the top dual wedge evaluates the top wedge to one;
zero section rings have zero modules on both sides; on the empty scheme the
module category is trivial. There is no field, domain, nonempty-scheme, or
nontrivial-ring hypothesis.

## No longer needed

Removed direct proof imports:
- `Mathlib.LinearAlgebra.ExteriorPower.Pairing`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`;
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.

The original module no longer directly uses the ring-level pairing node
`lem-sc-exterior-power-dual-pairing`; it is needed by the new comparison's plan,
so it is not pruned from the overall argument. The tensor product definition
`def-pur-sheaf-tensor-product` remains needed through the actual monoidal
structure; its wrapper `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
is unnecessary to this proof. The locally-free wrapper is already available
through statement imports. No claim is made that these modules are globally
unreachable: other targets or imports may still reach them. The original
finite-local-freeness, internal-Hom and exterior-sheaf definition nodes are
still needed. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's ring-level exterior pairing does not directly produce an isomorphism
of the current sheafified exterior powers. The missing step is comparison with
internal sheaf duality, now isolated precisely in the new statement. It is
strictly less than the item's tensor-inverse conclusion, which also needs
invertibility and evaluation, supplied by separate existing theorems.

The source's finite-free exterior basis theorem and determinant pairing are
useful locally, but scalar restriction and sheafification comparisons remain
nontrivial. No false statement was found. Stacks Tag 0BRT was read online because
this machine's literature checkout contains lists but no duality.tex.
Its last paragraph states the determinant inversion being expanded here.
Source: https://stacks.math.columbia.edu/tag/0BRT .

`determinant_shortExact` is used as a generic tool lemma to extract determinant
invertibility, rather than to change the duality unit's route. The unit
`sk-thm-picard-duality` has no realized node or step for this item. The original
ordinary determinant evaluation remains the theorem needed above.

## New nodes

`lem-sc-determinant-dual-evaluation-dual-identification` states the ordinary
isomorphism from the top exterior sheaf of the internal dual to the internal
dual of the top exterior sheaf. Its new module has one public theorem and one
sorry. Its node supplies the complete local-to-global proof, dependencies,
three available kinds of search plus the recorded LeanSearch outage, source,
and verbatim Lean signature. The whole blueprint was searched for determinant
duality and determinant invertibility; no duplicate blueprint node was found.
No change record is needed because existing signatures and definitions are unchanged.


## Second reading by E2

1. Compared the delivered determinant module with the repository using diff. The existing
   signature is byte-for-byte unchanged, including universes, binders, and conclusion. All
   existing public imports are unchanged. The additional module is new, with precisely the
   declaration recorded in its node. Verdict: pass; no change record is required.

2. Compiled both modules in import order using lcompile.py --all, with no errors or warnings.
   Also compiled scratch copies with #print axioms for both declarations: each uses only
   propext, Classical.choice, Quot.sound, and sorryAx from the documented open dependencies.
   There is no sorry in the item's proof; the only delivered sorry is the named comparison
   theorem. No forbidden declaration, hollow definition, or arbitrary existence-based data
   construction was introduced. Verdict: pass as a decomposition, not an unconditional proof.

3. Checked the new comparison in degrees zero and one, on free sheaves of rank d, over zero
   section rings, and on the empty scheme. The local basis pairing and its restriction
   compatibility prove the exact stated comparison without extra hypotheses. The comparison
   omits the target's invertibility and tensor evaluation steps, which the final proof supplies
   separately, so it is a strictly smaller intermediate statement, not a restatement. Read
   Stacks Tag 0BRT online and inspected the actual exterior-sheaf and internal-dual definitions.
   Independently searched leanfinder for sheaf internal Hom commuting with exterior powers,
   loogle for ModuleCat.exteriorPower, and grep for homObj/dual with exteriorPower/exteriorSheaf;
   searched lean/Sheaf and lean/WeilConjectures with those words too. No existing sheaf-level
   comparison closes this hole in a few minutes. Verdict: pass.

4. Read the proof from the top down. Its split complex really is short exact: the free sheaf
   on the empty type is zero by the coproduct universal property, and its second arrow is
   identity. determinant_shortExact gives invertibility with ranks 0,d,d; the comparison,
   tensoring, braiding, and the proved invertible-sheaf evaluation give exactly the target.
   The three removed direct proof imports are unused; all new proof-only imports are plain
   import. The public Mayer--Vietoris import is needed for moduleRings in the signature.
   All old proof dependencies omitted from the updated list are accounted for: the pairing
   moves to the comparison, while the Hom and exterior definitions remain statement
   dependencies and are also dependencies of that comparison. No globally unreachable module
   is claimed. The unit sk-thm-picard-duality has empty realized statement/step lists, and this
   reduction bypasses no realized unit step. Verdict: pass.

5. Compared the existing node's proof steps, their dependency union, and proof_origin with
   the actual Lean proof. Checked the new node's source, self-contained statement, proof,
   dependency union, searches, created fields, chapter/unit, blueprint origin, and verbatim
   Lean record. They agree with the delivery. The report names the original hole closed and
   the new hole added, accurately recording zero net holes closed by this decomposition.
   Verdict: pass.

Second reading changed only this report: no Lean code, import, signature, definition, or DAG
field needed repair. Scratch axiom probes were removed before delivery.
