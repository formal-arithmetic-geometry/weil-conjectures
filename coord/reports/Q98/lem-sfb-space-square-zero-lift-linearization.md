## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-square-zero-lift-linearization.json`: statement split into six proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: seven step/node entries, each quoting a verbatim portion of the current cited statement.

Attachments: none. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for square-zero lifts and derivations found no project declaration stating the arbitrary-algebraic-space correspondence with its naturality clauses. Existing square-zero and differential declarations concern rings or schemes and do not supply the whole item.

WANTED: none.

The item was unsplit, and the sandbox initially contained only search records and dispatcher brief markers. I copied the current item, retained its statement, source, provenance, inherited blueprint fields and previous Mathlib searches, and added the completed proof and current recorded searches. No Lean was written, compiled or built, and no repository or launcher file was changed.

No mathematical statement correction was required. The imported proof was empty; a reference to the action-by-derivations lemma alone would have hidden the algebraic-space reconstruction and the differential pullback comparison. These are now explicit citations to existing nodes. The sign convention is consistently difference `b sharp - a sharp`, with inverse `a sharp + D`; it follows the actual construction in the proof of Stacks 04D0.

The inherited `blueprint.from.node` is null, and `blueprint_refs.py ancestor` reports None. I retained this rather than inventing an ancestor. I read the current blueprint in `literature/blueprint/latest/`, including `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and the direct-image proof. Its proof (3) concerns compactification; this item is the inherited infinitesimal supporting input below that route, not a new replacement of it. Whole-blueprint searches for derivation, square zero, and thickening found no node stating the item. The DAG's unit record still carries older text; I did not change it.

Nothing remains unfinished in this one-level split. Its cited inputs already exist and their independent proofs remain their own tasks.

## Not duplicates

No new nodes were created. The existing `lem-sfb-space-infinitesimal-lift-pseudotorsor` requires local finite presentation and already depends on this item, so it cannot prove the present unrestricted statement. The group-space kernel node also depends on this item and concerns a group law. Existing `lem-sfb-space-square-zero-ringed-realization` provides the more primitive reconstruction of ring-sheaf maps and is cited directly, rather than duplicated by a new lifting lemma. Existing inverse-image differentials and sheaf universal-differentials nodes are likewise reused.

## Review by Q98

I read Stacks `spaces-more-morphisms.tex` at Tags 0618 (lemma-difference-derivation), 0619 (equation-D), and 04D0 (lemma-action-by-derivations), including the surrounding common-etale-topos convention and the full proof of 05ZN (lemma-first-order-thickening-maps). I also read `sites-modules.tex` at the universal-module construction and Tags 08TP, 08TQ and 03D7. There are no new nodes needing separate source verification.

Step 1 uses the statement of `lem-sfb-space-first-order-ringed-description` for the equivalence of small etale sites and the exact square-zero ring extension. It uses the maps clause of `lem-sfb-space-square-zero-ringed-realization` for the bijection between compatible ring-sheaf maps and morphisms of thickenings. I opened both node statements: the latter allows different source and target and a fixed map between their reductions, whereas the final maps clause of the former only treats the same reduction. Using the former alone for reconstruction would have been C4; the delivered step cites the stronger existing statement. The substitutions are source `T_0 in T`, target `X in X`, base `S`, and reduced map `a_0`. The zero target ideal satisfies all hypotheses. No finiteness, flatness, affineness or smoothness of X or T is needed. The quotient action on J is written out and uses J squared equal to zero.

Step 2 takes no external lemma: it expands `(alpha(x)+D(x))(alpha(y)+D(y))`, kills the quadratic term in J, and checks additivity and vanishing on the base. It obtains the sheaf identity through restriction-compatible operations, not by assuming every section of a quotient has a global lift. This is an elementary calculation on arbitrary local sections.

Step 3 uses `lem-trf-topos-inverse-image-differentials` exactly for its comparison carrying the universal derivation to the inverse-image universal derivation. It uses `lem-trf-sheafified-module-differentials-cokernel` for its stated representing universal property on sheaves, not merely the ring version. It uses `lem-weil-pbc-ringed-topoi-module-adjunction` for tensor pullback; the step writes the forward formula `t tensor omega maps to t ell(omega)` and its inverse. All the rings are commutative sheaves on the common small etale topos, and J is a module through the reduced structural map. I declared these three off-unit citations as generic tools in `split_report.tool_uses`; they do not change the unit's geometric route.

Step 4 checks that alpha plus D is unital, multiplicative and over S, then applies exactly the same maps clause of the realization node used in step 1. This is the reconstruction input used by Stacks 04D0 via 05ZN, and the new argument does not assume a morphism of ringed topoi automatically comes from a space morphism. The uniqueness in that node is used again in step 5 to identify the reconstructed lift with the original one. The other inverse identity and the value at the origin are elementary subtraction and the two correspondences of step 3.

Step 6 writes the equality for the composite ring maps after pulling u sharp to T_0; this avoids comparing maps on different sites. Precomposition gives a relative derivation because u is over S. The pointwise formulas prove additivity, scalar compatibility for global sections of O_T0, the identity rule and the composite rule. Injectivity of the representing correspondence then gives the claimed identities on Hom modules. No extra naturality theorem is being silently invoked.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the actual files. There is no new statement-only node, no elementary node, no restatement of a clause used as its own proof, and no circular use of the lift pseudo-torsor or group kernel. I traversed statement and proof dependencies of all five cited nodes and found no path back to the item. Every non-elementary step has exactly the needed existing statements, and every cited statement is open in the verbatim citation table. Every step is under 1000 characters, so there is no long step hiding a separate lemma.

For small cases, if J=0, the realization uniqueness gives the singleton lift set and the zero Hom module. For an empty test scheme both sets are singletons. For X=S there are no nonzero relative derivations, and the structure map is the unique S-lift. For an affine line with T=Spec(k[epsilon]/epsilon squared), a lift is the original coordinate plus c epsilon, matching the displayed difference with a positive sign. The same calculation works for a nonfree ideal and never uses a basis or finite presentation. Nonaffine T is handled globally by the sheaf realization statement, not by an unjustified affine reduction. An arbitrary morphism u, including the identity and a composite, obeys exactly the chain-rule calculation in step 6.

The recorded search commands returned `derivationToSquareZeroEquivLift` (Mathlib/RingTheory/Derivation/ToSquareZero.lean:116), `KaehlerDifferential.linearMapEquivDerivation` (Mathlib/RingTheory/Kaehler/Basic.lean:327), and related derivation formulas. I read those source declarations. They classify algebra homomorphisms of rings, and neither their statement nor a one-line specialization proves the algebraic-space realization used here. The second semantic phrasing returned formally unramified schemes and presheaf universal differentials, also insufficient. The item remains a split statement, with the useful general tools already present in the DAG.
