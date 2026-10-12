## What changed

Repaired E1 from reviewer X-4e23d, head 4e23d6ef3, review point 4.
Added `[Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})]` immediately after `[Fact ℓ.Prime]`
in `AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`.
Removed the obsolete STATEMENT-DISPUTED comment: the corrected hypothesis excludes
the reported counterexample. The existing proof hole remains; this is a signature
correction, not a proof completion.

The only external caller is in
`Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction`.
Compiled its unchanged source together with the repaired source module in import
order. Lean automatically supplies the finite quotient for `ULift (ZMod r)`;
no adaptation of its public statement, proof or imports is required. The sandbox
includes its unchanged source for this combined validation; it contributes no diff.

Updated the normalization node's Lean record with the corrected signature. Its
prime-field statement already has finite coefficients, so its statement and
proof route, and `dag/units/sk-thm-p1.json`, remain unchanged. No target changes.

Signature change record (old/new signatures and every declaration user):
`coord/changes/AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite.md`.

## Proved and sorry left

Holes closed: none (0 of 1). Holes added: none. Split-off statements: none.
The only hole remaining in the item is
`AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`
(node `lemma-weil-pbc-curve-normalization-constant`), now with its corrected
finite-quotient hypothesis. Changing this signature is not counted as proving it.

The already landed
`AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar`
still uses the existing `AlgebraicGeometry.normalization_mono_properties` hole.
No axiom-free completion is claimed. The unchanged caller module has no local
sorry; no definition data, axiom, or new theorem hole is introduced.

## No longer needed

No library import, node, module or proof dependency is pruned by this repair.
The original worker's proposed duplicate NormalizationComparisonCokernel module
and lem-pbc-a2-normalization-comparison-cokernel node remain excluded, superseded
by the already landed stronger normalization_mono_properties interface.
They were never library pruning in this delivery.

## Where the brief, the DAG or earlier work was wrong

The former coefficient-general transfer signature omitted finiteness of Λ/ℓΛ.
Finitely generated Λ-module stalks need not be finite as abelian groups. The
reviewer's requested correction restores the hypothesis already present in the
normalization exact-sequence theorem and agrees with the finite prime-field
blueprint statement. The old report's claim that no signature correction was
being made is superseded by this repair.

A concrete mathematical counterexample is as follows. Let k be algebraically
closed of characteristic 3, let Lambda = F_3[t], and let X be the projective
nodal rational cubic with affine equation y^2 = x^2(x + 1). Its node is (0,0),
its point at infinity is smooth, and its normalization nu:P^1_k -> X is finite,
surjective, and smooth over k. Let V be the complement of the node, where nu
is an isomorphism. Let U be X minus the smooth point at infinity. Its inverse
image U-prime is P^1 minus one point. Take ell = 3, so Lambda/ell Lambda = Lambda.
These data satisfy every geometric hypothesis of the disputed theorem.

Put A = j_!Lambda and B-prime = j-prime_!Lambda. Artin-Schreier and
H^1(P^1,O) = 0 give H^0(P^1,F_3) = F_3 and H^q(P^1,F_3) = 0 for q > 0.
The underlying additive group of Lambda is the direct sum of copies of F_3;
filtered-colimit continuity extends this calculation to Lambda. The
open-closed sequence for the removed smooth point identifies the restriction
H^0(P^1,Lambda) -> H^0(point,Lambda) with the identity. Consequently
H^q(P^1,B-prime) = 0 for every q, over k and after every algebraically closed
extension. Thus C1, C3, C4, C5, C6 and C7 for B-prime hold; C2 is conditional
on the false hypothesis that P^1 is affine. For C8, each proper nonempty open
of P^1 is affine, and its restriction of B-prime has zero H^2 by the same
open-closed sequence and characteristic-3 affine vanishing. Empty opens also
have zero H^2. Hence all eight assertions in the hypothesis H hold.

In the finite normalization comparison, the cokernel Q is a skyscraper at
the node: its stalk is (Lambda x Lambda)/diagonal(Lambda), isomorphic to Lambda.
Elsewhere the comparison is an isomorphism, including at the removed smooth
point where both stalks vanish. Finite direct image preserves cohomology, so
H^q(X,nu_*B-prime) = 0 for all q. The exact sequence
0 -> A -> nu_*B-prime -> Q -> 0 then gives H^1(X,A) = Lambda. The curve X is
proper and A is constructible (its stalks are zero or the rank-one
Lambda-module Lambda), but H^1(X,A) is infinite. Therefore its C5 is false,
contradicting the conclusion. This is a natural-language counterexample,
not a Lean-formalized construction of the cubic.

The repaired hypothesis excludes this counterexample because Λ/(3) = F_3[t]
is infinite. It permits the zero coefficient quotient, empty schemes, empty
opens, and the actual finite prime-field coefficients. The theorem is still
unproved; the correction alone is not evidence for its remaining proof.

## Earlier second reading (a previous round; superseded)

The prior second reading identified the omitted finite-coefficient hypothesis
and validated the natural-language nodal counterexample against C1 through C8.
This repair addresses its review point 4 as instructed by reviewer X-4e23d.
The following is the repair worker's validation of that correction; no new
independent reader was spawned.

1. Compared old and new signatures: the only binder change is the requested
   `[Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})]`. All targets, definitions, other
   signatures, imports and proof bodies are unchanged. Removed the now-obsolete
   dispute comment. The blueprint already concerns finite prime-field sheaves.
2. Searched all Lean sources and ran downstream.py with the declaration name:
   the sole external caller is reducedConstantLowerShriekAssertions_of_reduction_data
   in ReducedConstantLowerShriekReduction.lean. Its coefficient ring is the
   finite `ULift (ZMod r)`; its quotient is finite by existing instances. Compiled
   both modules in import order against the corrected theorem: both pass,
   without warnings. No additional hypothesis is added to the caller.
3. Checked the record of every declaration user, with verbatim old/new
   signatures, in the required coord/changes file. Its status is open pending
   the maintainer's global build. The node's Lean signature is updated; its
   mathematical statement, dependencies and unit route stay intact.
4. The counterexample uses an infinite quotient and is excluded. Finite
   prime-field, zero-quotient, empty-open and empty-scheme cases remain allowed.
   The single existing sorry remains and no proof completion is claimed.
5. The delivery dry run checks compilation and axiom probes. No push is
   authorized by this worker brief; delivery is left for the second reader.


## Second reading by A2

Independent second reader, 2026-10-12. This delivery is a statement repair,
not a proof completion or decomposition.

1. Compared both delivered Lean modules byte for byte with the repository.
   The sole Lean difference is the declared finite-quotient instance in
   `AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`.
   The required change record gives the verbatim old/new signatures and the
   only external caller. All definitions, targets, other declaration signatures,
   proof bodies and imports are unchanged. The earlier dispute-comment removal
   mentioned above belongs to an earlier repair round; it is not a difference
   against this repository version. Verdict: the signature repair is explicit,
   and nothing else visible to users changed accidentally.
2. Compiled the two modules together using lcompile in import order: both pass
   without warnings (31.2 s and 9.6 s). The item has precisely its one named
   theorem hole; the unchanged caller has none. Scanned both sources for
   forbidden declarations and attributes: none. A fresh scratch copy probes all
   nine public theorems of the item with `#print axioms`; the delivery also runs
   the maintainer's exhaustive constant probe. Imported open theorems can still
   contribute `sorryAx`; no axiom-free completion is claimed. No definition
   contains a hole or newly chooses an arbitrary witness from an open theorem.
   Verdict: valid incomplete repair, with zero holes closed and zero added.
3. There are no new or split-off statements or nodes. Checked the repaired
   hypothesis against the preceding normalization comparison theorem and
   `normalization_mono_properties`, which already require this same finite
   quotient. The documented infinite F_3[t] nodal example is excluded, while
   finite prime-field coefficients, the zero quotient and empty schemes/opens
   remain permitted. The normalization exact sequence with a finite-support
   finite-stalk cokernel supplies the stated mathematical transfer route;
   finiteness is essential for C4/C5. Verdict: justified correction of an
   overgeneralized intermediate statement, with its proof still open.
4. Read the complete item and the relevant normalization, finite-pushforward
   and downstream reduction interfaces. Searched the curve modules using
   normalization, cokernel and finite lower-shriek terminology. There is no new
   duplicate lemma to remove. No proof route was replaced, and all imports
   and old proof dependencies remain; `## No longer needed` correctly claims
   no pruning. All proof-only imports in the item are plain imports; its public
   imports provide the assertion and functor interfaces used by signatures.
   `dag/units/sk-thm-p1.json` and its realized route are unchanged. Verdict:
   no pruning or unit bypass is claimed by this repair.
5. Compared the delivered node with the repository node. Only its Lean record
   changes, documenting the repaired signature and the still-open theorem;
   its mathematical prime-field statement, proof plan, proof_deps and
   proof_origin are unchanged. Checked that the new recorded signature matches
   the Lean source and that no new node fields are required. Verdict: node and
   Lean agree about the interface repair and the absence of a completed proof.

Second reading changed only this independent review report. The existing Lean
repair and change record are retained. Delivery dry run and delivery are run
by this reader as requested.
