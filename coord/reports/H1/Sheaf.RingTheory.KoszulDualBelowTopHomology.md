## What changed

Proved the body of `ExteriorAlgebra.koszulDual_isZero_homology_below_top`, with its
signature and visibility unchanged. Added proof-only imports of
`Sheaf.RingTheory.KoszulComplementaryEquivalences` and
`Mathlib.LinearAlgebra.ExteriorPower.Basis`. The new module states the
regularity-free signed complementary term equivalences and the commuting differential
squares. The main proof transports individual cocycles and boundaries using those
squares and Koszul regularity, then uses Mathlib's elementwise exactness criterion.
It handles degree zero separately by proving the term of degree r+1 is zero from
its empty exterior basis. Updated the item's DAG proof to match this argument.

The source read was Stacks `duality.tex`, proof of `lemma-regular-immersion-ext`,
Tag 0BQZ, specifically its complementary contraction map and the discussion of
commuting or anticommuting differentials. The unit record
`sk-thm-picard-duality` has no realized statement or step assigned to this node;
this refines the same local computation below the unit level.

## Proved and sorry left

Closed the one original hole:
`ExteriorAlgebra.koszulDual_isZero_homology_below_top`
(node `lem-sc-koszul-dual-below-top-homology`). There is no sorry in its module.

Added one hole:
`ExteriorAlgebra.exists_koszul_complementary_equivalences`
(node `lem-sc-koszul-complementary-equivalences`), in the new module
`Sheaf.RingTheory.KoszulComplementaryEquivalences`.
Its proof is exactly `by sorry`; its docstring and node spell out the wedge
coefficient pairing and the explicit sign correction T_j=(-1)^j T'_j.

This is a decomposition: one upper hole closed, one lower hole added, net zero.
The new statement assumes no regularity and concludes no homology vanishing;
it isolates the original plan's construction and differential compatibility.
The Lean proof of exactness from those data is complete, including the previously
unformalized zero-degree edge. No data definition chooses an arbitrary witness
from the new existence theorem; the witness is used only inside a theorem proof.

Both delivered modules compiled. Edge cases checked mathematically: r=0 has
only the evaluation equivalence and no commuting squares; r=1 gives e_0=1,
e_1=-1 and signed differential -f; f=0 gives zero differentials with the same
invertible wedge maps; characteristic two has all signs equal to one; the zero
ring has all terms zero. For n=0 the actual Lean proof uses the empty basis of
wedge^(r+1), rather than a nonexistent negative-degree equivalence.

## No longer needed

The planned proof dependency `lem-sc-exterior-power-dual-pairing` is no longer
needed by this route, including the new node: `exteriorPower.pairingDual` compares
an exterior power of a dual with the dual of the same-degree exterior power.
The complementary wedge coefficient pairing instead follows directly from the
finite exterior basis. Removed that node from the item's proof dependencies.

No existing imports were removed. The basis and the two complex definitions and
regularity remain needed. No library module is claimed to become unreachable:
Mathlib's Pairing module is still reached through ExteriorPower.Basis. The new
node records the graded Koszul derivation it uses. No unit statement or realized
unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The two cited Mathlib leaves do not already state the signed complementary
isomorphisms. In particular, the canonical `pairingDual` map is not the needed
complementary-degree pairing or differential square. The mathematical plan is
sound, but this algebraic step requires a new interface. It is now separated from
the exactness argument; no existing statement or definition was changed.

LeanFinder returned exterior universal properties and pairingDual but no signed
Koszul comparison; Loogle found no HomologicalComplex.homologyIso; grep found no
Koszul theory in Mathlib and no existing complementary-equivalence node in the
library/DAG or the ten blueprint Koszul search hits. LeanSearch returned Internal
Server Error, recorded as unavailable with no mathematical conclusion drawn.

## New nodes

`lem-sc-koszul-complementary-equivalences` states invertible maps between each
signed dual term in degrees 0 through r and the complementary Koszul term,
together with their differential compatibility. Source: the complementary
contraction argument in Tag 0BQZ, expanded using the existing finite exterior
basis and graded Koszul derivation. Three search kinds are recorded in the node.
Its proof in words explicitly derives the anticommutation and corrects the sign.
The only new module is `lean/Sheaf/RingTheory/KoszulComplementaryEquivalences.lean`.
No change record or forced adaptation is needed.

## Second reading by H1

1. **Interface comparison: pass.** Read both delivered Lean modules whole and
   compared `KoszulDualBelowTopHomology.lean` with the repository using `diff -u`.
   The existing theorem's signature, visibility, docstrings and all original
   imports are byte-for-byte unchanged. Only its proof and two plain proof-only
   imports were added. `KoszulComplementaryEquivalences.lean` is new, contains
   one theorem and no definitions, and publicly imports `KoszulDualComplex`
   because its statement uses both complex definitions. There are no forced
   adaptations or interface changes and no applicable change record was found.

2. **Lean and axioms: pass as a decomposition.** Independently compiled both
   modules in import order using `lcompile.py --all`; both compiled without
   errors or warnings. Scanned both complete files: the original theorem has
   no `sorry`; the only remaining `sorry` is exactly the named new theorem
   `ExteriorAlgebra.exists_koszul_complementary_equivalences`. No forbidden
   declaration or implementation escape occurs and there is no hollow data.
   A scratch module importing the compiled delivery printed axioms for both
   declarations: precisely `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx`. Thus the original proof body is closed conditionally on the new
   algebraic statement; this is not an axiom-free proof of the original target.
   Its existential witness is eliminated inside a proposition proof, never
   chosen to define public data.

3. **The split statement: pass.** Read Stacks `duality.tex`,
   `lemma-regular-immersion-ext` (Tag 0BQZ), especially the complementary
   contraction map and its commuting/anticommuting differential discussion.
   Read the actual signed dual boundary, Koszul boundary and graded derivation
   declarations. The new statement quantifies over arbitrary commutative A,
   all finite r and f, with no regularity assumption. It asserts only
   complementary term equivalences and the squares in degrees j<r, with
   exactly the degrees the proof consumes. It does not restate homology
   vanishing. Its docstring gives a complete construction from the ordered
   exterior bases, not a claim that exactness transports without explanation.
   Explicitly, the coefficient pairing gives
   P_j(dx,y)=(-1)^j P_(j+1)(x,dy); the signed precomposition then gives
   T'_(j+1) delta_j = -d T'_j, corrected by T_j=(-1)^j T'_j.
   For r=1 the two maps are evaluation and negative evaluation and the
   differential is -f. For r=2, T_0(1)=e_0 wedge e_1,
   T_1(e_0^*)=-e_1, T_1(e_1^*)=e_0, T_2(e_top^*)=1;
   both squares commute. Independently checked all 321 individual f_i
   coefficients on dual basis wedges for r=0 through 6. These are integral
   sign identities, so characteristic two is included. For r=0 there is only
   evaluation and no square; for f=0 all differentials vanish; the zero ring
   needs no exception. None of these checks assumes nontriviality of A.
   A few-minute closure of this hole is not available: formalizing its basis
   complement maps and graded pairing is the remaining algebraic work.

   Independently searched with the different phrase "Hodge star finite
   exterior algebra contraction transpose wedge complementary degree"
   (LeanFinder), `"contractLeft"` (Loogle), and Hodge/complementary-pairing
   terminology (msearch grep and direct rg in both source roots and Mathlib).
   LeanFinder gives contraction anticommutation and the same-degree
   `pairingDual_ιMulti_ιMulti`, not these degreewise equivalences. Read
   Mathlib `ExteriorPower/Pairing.lean` and `ExteriorPower/Basis.lean`;
   `pairingDual` has a different source and supplies no complementary square.
   Repository hits in the conormal comparison and regular-sequence dual
   modules use or describe the vanishing argument, not an available theorem
   constructing these equivalences. The new node is needed and not duplicate.

4. **Reduction, imports and pruning: pass.** In positive dual degree n the
   proof uses exactness at the strictly positive Koszul degree r-n, takes a
   boundary preimage, and uses the preceding square and injectivity to pull
   it back. At n=0 it uses exactness at r>0 and proves the incoming term
   wedge^(r+1) A^r zero from its empty basis index type; it never calls a
   negative-degree equivalence. Read Mathlib's basis and exactness criteria;
   the basis argument works without a nontrivial-ring hypothesis and the
   natural-number subtractions include n=r-1. Each import is used: the two
   original public imports supply the unchanged signature, the new plain
   imports supply e/he and the empty exterior basis. No shorter existing
   comparison theorem was found. The only old proof dependency removed is
   `lem-sc-exterior-power-dual-pairing`, fully listed above; no existing Lean
   import or unreachable library module is claimed pruned. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement is empty and
   its sole realized step is empty. This local algebraic reduction preserves
   the unit and chapter routes.

5. **DAG correspondence: pass.** Compared the existing JSON with the
   repository: only `proof`, `proof_deps`, and `proof_origin` differ. The
   three steps record precisely the equivalence theorem, positive-degree
   elementwise transport and the zero-degree empty-basis argument. Read the
   new JSON whole, its verbatim Lean signature, source, searches, provenance,
   blueprint ancestry, chapter/unit and created/lean records. Its dependency
   union equals the uses in its proof steps. Checked the cited exterior-basis
   node (a Mathlib leaf) and differential node against their actual statements:
   they supply the finite bases, vanishing above rank and graded Leibniz rule
   used in the construction. The new node assumes no Koszul regularity and
   cites no node depending on the item, so this reduction is not circular.

**Changes by the second reader:** added this independent review and recorded
additional searches in the sandbox search log; no Lean or node repair was
needed. Original hole closed: `koszulDual_isZero_homology_below_top` (one).
New hole added: `exists_koszul_complementary_equivalences` (one). Net zero,
with a completed exactness reduction; no additional holes closed in review.
