## What changed

Replaced the sole hole in `Sheaf.RingTheory.DvrTameTensorFactorRamificationBound` with
an explicit auxiliary-root construction and two ramification tower calculations.
The original theorem's signature and all public imports are unchanged. Added proof
imports of `Mathlib.RingTheory.Flat.TorsionFree`,
`Sheaf.RingTheory.DvrAbhyankarNormalizedFactor`, and
`Sheaf.RingTheory.DvrNormalizedTensorFactorLift`.

The proof chooses t=r/gcd(r,n), proves its positivity and r | n*t, and constructs
A1=AdjoinRoot(X^t-pi). From the existing root-DVR theorem it proves both maximal-ideal
power identities and computes e(A1/A)=t by the localization length formula. The
factor-lifting lemma supplies a compatible finite normalization S1 and Q1 over Q;
the index-one Abhyankar lemma gives e(Q1/A1)=1. Mathlib's tower identities yield
e(Q1/A)=t and e(Q/A) | t, proving the bound.

## Proved and sorry left

Closed: `RingTheory.dvr_tame_tensor_factor_ramificationIdx_le`
(node `lem-sbc-dvr-tame-tensor-factor-ramification-bound`). No sorry remains in the
item's module. This is a decomposition: one upper hole closed, two lower holes added.

Added and left with their complete proof outlines:

- `RingTheory.dvr_abhyankar_normalized_factor_ramificationIdx_eq_one`
  (`lem-sbc-dvr-abhyankar-normalized-factor-index-one`), the sufficiently divisible
  base-index case of Abhyankar, with no partially ramified quantitative conclusion.
- `RingTheory.dvr_normalized_tensor_factor_lift`
  (`lem-sbc-dvr-normalized-tensor-factor-lift`), existence of a compatible normalized
  tensor factor and closed prime above the original one after finite DVR extension.
  It has no tame hypotheses and no numerical ramification conclusion.

Both new statements were checked on the identity base extension. The root construction
also handles t=1 (in particular r=1 or r | n); positivity excludes t=0. The lifting
statement permits inseparable A1/A: finiteness of S1 follows from separability of
E/Frac(B), not separability of Frac(A1)/Frac(A). No arbitrary data are defined by choosing
a witness from either new theorem: the root algebra is an explicit AdjoinRoot and
all existential witnesses are eliminated only inside the proof of the original theorem.

## No longer needed

Removed the direct proof import `Mathlib.RingTheory.DedekindDomain.IntegralClosure`.
The node `lem-weil-pbc-noetherian-normal-separable-integral-closure-finite` is no
longer a direct dependency of the bound; it is retained below the new factor-lifting
node, which needs it. No planned Sheaf module or node becomes globally unnecessary.
The existing uniformizer-root module and node remain used. All original public
imports remain unchanged to preserve the importer-visible interface.

## Where the brief, the DAG or earlier work was wrong

The original DAG steps 1 and 4 had no named declarations for the normalized-factor
lifting or the Abhyankar index-one step. The root-DVR theorem alone does not supply
either. These are now explicit independent work items; the main theorem supplies the
root maximal-ideal calculations, localization length argument and tower glue in Lean.
The unit route is retained. LeanSearch was unavailable (Internal Server Error);
LeanFinder, Loogle and grep were run and found general tower, flatness and lying-over
lemmas, but no existing declaration for either complete intermediate statement.

## New nodes

`lem-sbc-dvr-abhyankar-normalized-factor-index-one` in
`lean/Sheaf/RingTheory/DvrAbhyankarNormalizedFactor.lean` isolates 0BRM and 09E7 for
normalized factors when the tame indices divide the base index. Its statement is
independent of the auxiliary exponent and of the bound r/gcd(r,n).

`lem-sbc-dvr-normalized-tensor-factor-lift` in
`lean/Sheaf/RingTheory/DvrNormalizedTensorFactorLift.lean` isolates the 09EM construction,
032L finiteness, lying over, and torsion-free flatness. It constructs the compatible
algebra maps and prime used by both towers; it asserts no tame index bound.

No existing statement, definition, signature or visibility was changed, and no
forced adaptations or change records are needed.


## Second reading by H2

1. **Interface: PASS.** Diffed the item against the repository. Its complete existing
   theorem signature is byte for byte identical, including all hypotheses, let-bound
   algebra structures and the numerical conclusion. The original public imports are
   unchanged. Only its proof and proof imports change; the other two modules are new.
   There are no changed definitions, forced adaptations or change records. Checked
   the relevant change-record directory for concurrent interface changes.

2. **Kernel and holes: PASS as a decomposition.** Compiled all three modules in
   import order using lcompile.py, with no errors or warnings. In scratch copies,
   printed the axioms of each of the three declarations: each has only propext,
   Classical.choice, Quot.sound and sorryAx. The item's theorem has no sorry;
   the two new named theorems are the only delivered holes. No axiom, unsafe,
   opaque, implemented_by, extern or holed definition occurs. The explicit AdjoinRoot
   construction supplies the auxiliary ring; existential factor-lifting witnesses are
   eliminated inside a proposition proof and never define public data. The root-DVR
   theorem itself is already proved in the repository. Thus one old hole is replaced
   by two strictly smaller holes: this is not an axiom-free proof or net hole reduction.

3. **New statements and sources: PASS.** Independently read Stacks
   [0BRM](https://stacks.math.columbia.edu/tag/0BRM),
   [09EM](https://stacks.math.columbia.edu/tag/09EM),
   [09E7](https://stacks.math.columbia.edu/tag/09E7) and
   [032L](https://stacks.math.columbia.edu/tag/032L).
   In the index-one lemma, the injection into the field tensor quotient forces
   B -> A to be injective. Finite normal A is the normalization in Frac(A), and
   the closed localization of C is tame: both the index and residue inseparable
   degree are prime to the residue characteristic. Divisibility by n is precisely
   the hypothesis needed for 0BRM. This lemma isolates the index-one case; it does
   not assert the general r/gcd(r,n) conclusion or construct the auxiliary ring.
   The lifting lemma is independent of tameness and numerical indices. Separability
   of F/Frac(A) makes F tensor Frac(A1) a nonempty product of fields even when
   Frac(A1)/Frac(A) is inseparable. Each factor is separable over Frac(A1), so
   032L gives finiteness. The integral product normalization contains S injectively;
   lying over supplies Q1, and torsion freedom over the Dedekind domain S gives
   flatness. An A-algebra map i is injective here because S is integral over A
   and its prime kernel contracts to zero in A, so incomparability applies.
   Tested the identity extension A1=A (choose P1=P, i=id, Q1=Q), E=Frac(B),
   r=1, n=1 and r dividing n. Positivity excludes zero exponents. In equal
   characteristic p, a purely inseparable finite DVR base extension is also
   covered by the lifting argument. Each hole has a sourced docstring proof and
   matching node. Independent LeanFinder, Loogle and Mathlib grep searches used
   different queries from the first reader; searched both repository Lean roots
   and the upstream source. No existing complete lemma was found. The existing
   maximal-ideal and unramified modules depend on this bound, so using them here
   would be circular; they also impose a unit base index, unlike the new lemma.

4. **Route and pruning: PASS.** Read the original proof plan, all direct dependency
   declarations, the Mathlib tower/divisibility formulas and the unit's realized
   record. The root relation and localization quotient length prove e(A1/A)=t;
   the two flat towers then prove e(Q/A) divides t. The route through the trait
   case of sk-prop-input-spreading is retained; its realized slots are empty and
   no realized unit node is bypassed. The old root-algebra dependency remains used.
   The only removed old dependency is the finite-separable-normalization node,
   now needed below factor lifting; the No longer needed section records it.
   There is no globally pruned Sheaf module. Removed one redundant direct public
   import of Mathlib.RingTheory.Localization.AtPrime.Basic from the new
   DvrAbhyankarNormalizedFactor module: ramification already imports it, and
   the new signature needs no separate direct import. This changes no old interface.

5. **DAG agreement: PASS.** Checked every delivered lean.statement against its
   actual declaration text, and each proof_deps against the union of the proof
   steps' uses. The updated parent plan follows the actual root construction,
   factor lift, index-one application and Mathlib towers. Its proof_origin identifies
   this assembly. New nodes carry source, complete statements and stmt_deps,
   proof steps, proof_origin, recorded searches, status, created, blueprint,
   chapter, unit and Lean records. Both new statements are strictly parts of the
   argument; neither renames the original bound.

Second reading changed only the redundant direct import in the new index-one
module and this report. No proof repair or additional hole closure was justified
by the checks; the two substantive intermediate lemmas remain separate work items.
