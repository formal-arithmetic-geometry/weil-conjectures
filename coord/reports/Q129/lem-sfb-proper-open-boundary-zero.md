# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-open-boundary-zero.json: repaired split, identical statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-open-complement-square.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-open-extension-zero-constructible-finite-tor.json: statement, unsplit, no Mathlib match.

## Attachments

None. Searching WeilConjectures for the blueprint tag and proper/open-boundary terminology found no project declaration stating the item. Sheaf/Paper/ProperOpenBoundaryZero.lean:116 states it but has sorry at line 136. It is not a finished attachment. No Lean files were written and no compiler, Lake or build command was run.

## WANTED

None; all sources used are present.

## Repair of the return

The sandbox initially contained only dispatcher marker files, with no report, nodes or searches.jsonl. I copied the current repository node and retained its statement, metadata, earlier searches and all six proof steps below. The requested correction is a genuine re-split: two independent new nodes are unsplit, with empty proof/proof_deps and null proof_origin. The complementary-square node carries old steps 1 and 2 (1307 characters of argument); the preservation node carries old step 3 (1293 characters). Neither states the parent's proper-pushforward vanishing. The parent only assembles them with the three existing coefficient-specific proper-base-change results and preservation of zero, and its proof is below 3000 characters.

## Sources and searches

Item and both new nodes: current main-20261015 blueprint, sec-six-functors-basics/sk-thm-sf-comp-composition/det-sf-comp-composition-interchange.proof.md, proof (3), read in full. The preceding proof (1) explains the inverse-image open; here it is already the stipulated fibre product, so no density is needed. The chapter record and sk-thm-sf-comp-composition unit record were read; the latter retains an older master placement under sec-smooth-purity, but this repair follows the node's current source and inherited chapter/unit without changing either.

For the complement-square node I read Stacks 01JY (schemes-lemma-base-change-immersion), 01K5 (schemes-lemma-quasi-compact-preserved-base-change), 01QR (morphisms-lemma-base-change-closed-immersion), 01W4 (morphisms-lemma-base-change-proper), 01W5 (morphisms-lemma-closed-immersion-proper), and 01T3 (morphisms-lemma-composition-finite-type), plus proetale.tex, lemma-ses-associated-to-open (09AH) and lemma-open-immersion (09BN), at their actual source labels. The condensed-module/derived lift is the statement of lem-sfb-condensed-support-derived-localization; I do not claim Stacks itself states that lift.

For preservation I read sk-prop-proper-image-localizing-open.proof.md, paragraphs Constructibility and Finite Tor amplitude, together with det-lem-int-tensor-projection.proof.md, Open immersions and Derived version. The retained argument below uses the explicit tensor interval calculation rather than the blanket Dctf=Dbc assertion in the older open proof. I opened det-def-sfb-constructible-local-model and both constructibility definitions: finite constant scalar models imply locally finitely presented models, not conversely. General condensed coefficients suffice: sk-def-sfb-module-pushforward-pullback explicitly says its constructions are for general Lambda and alpha_f is invertible; inverse image of abelian sheaves is exact, and extension of scalars along this isomorphism is exact. This supplies the exact restriction needed for the general-coefficient version of the old Tor calculation.

DAG searches covered all dag/nodes by complement-square, open extension, finite Tor, interval and constructibility keywords; relevant statements were opened, not only titles. tools/blueprint_refs.py ancestor identifies det-sf-comp-composition-interchange; its via list for both new nodes is [lem-sfb-proper-open-boundary-zero]. Whole-blueprint searches included extension by zero + Tor amplitude and closed complement + condensed, as well as broader open/Tor and complement/proper searches. WeilConjectures and Sheaf/Paper were searched by the same concepts. LeanFinder was run twice per new node with distinct phrasings, with Loogle, source grep and LeanSearch as logged in searches.jsonl. LeanSearch returned HTTP rate-limit errors and is recorded unavailable. LeanFinder's geometry hits concern coborders/ordinary scheme modules; its preservation hits concern condensed category constructors and AB axioms. Loogle's closed-immersion/proper equivalence supplies only a geometric component, not the node's mixed derived restriction. No hit states either complete node. Original item searches were read and retained; the item statement has not changed.

## Not duplicates

- lem-sfb-proper-open-complement-square vs lem-sfb-condensed-support-derived-localization: the existing node assumes complementary immersions; the new node constructs/identifies them after base change and proves all standing scheme and properness hypotheses before its mixed vanishing conclusion.
- lem-sfb-proper-open-complement-square vs lem-weil-pbc-proper-fp-permanence: permanence alone does not identify the complementary open or state derived condensed-module restriction vanishing.
- lem-sfb-proper-open-complement-square vs lem-sfb-proper-open-boundary-zero: no proper derived pushforward occurs in the new conclusion; it is the geometric/support input to the parent's subsequent coefficient-specific base-change calculation.
- lem-sfb-open-extension-zero-constructible-finite-tor vs det-proper-image-localizing-open: the existing node assumes admissible coefficients and states membership in Dctf without specified bounds; the new node applies to every commutative condensed ring and preserves independently specified cohomological and Tor intervals, with the ring-object constructibility comparison. Its assertion contains no localizing-closure extension.
- lem-sfb-open-extension-zero-constructible-finite-tor vs lem-sfb-dc-open-lower-shriek-preserves: the latter only gives ring-object locally-finitely-presented constructibility and no constant scalar models or Tor bounds.
- lem-sfb-open-extension-zero-constructible-finite-tor vs lem-sf-open-extension-zero-constant-model-constructible: the existing node treats individual sheaves and their strata; the new node treats derived complexes and every tensor test for the given Tor interval.
- lem-sfb-open-extension-zero-constructible-finite-tor vs sk-lem-sf-open-ctf: that node uses completed integral/raw rational/common-stage coefficient categories over the algebraic closure of a finite field; the new one uses ordinary module-object derived categories for any condensed ring over any positive-characteristic field different from ell.
- lem-sfb-open-extension-zero-constructible-finite-tor vs det-ctf-finite-proper-localizing and lem-trf-open-ctf: their open-extension assertions concern finite discrete coefficients only.

## Complete retained argument and handoff

These are the returned proof texts verbatim, with their original citations. They are report material, not proof steps or proof sketches in the new statement-only nodes. Future workers can recover every original argument and its precise responsibility.

### Original step 1 — lem-sfb-proper-open-complement-square

Put $T=W\times_{\overline Y}Z$, with projections $a:T\to W$ and $r_Z:T\to Z$. Base change of the closed immersion $c$ makes $a$ a closed immersion; its underlying closed subset is $r^{-1}(|Z|)$, whose complement is exactly $U=r^{-1}(Y)$. The morphism $j$ is an open immersion by base change of $i$, and is quasi-compact by quasi-compact base change. Base change of properness makes $r_Z$ proper. The closed immersions $c$ and $a$ are proper, hence separated and of finite type; composition with the structure morphisms of $\overline Y$ and $W$ shows that $Z$ and $T$ are separated finite-type $k$-schemes. Thus the square $(a,r_Z,r,c)$ is a proper base-change square inside the standing setting. The scheme $T$ need not be reduced: only its closed underlying subset, complementary to $U$, is used.

Uses: lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-open-immersion-base-change, lem-pc-quasi-compact-base-change, lem-weil-pbc-proper-fp-permanence, lem-sfb-finite-type-composition-base-change.

### Original step 2 — lem-sfb-proper-open-complement-square

Apply the mixed-restriction vanishing $i^*j_!=0$ of [lem-sfb-condensed-support-derived-localization] to the complementary immersions $a:T\hookrightarrow W$ and $j:U\hookrightarrow W$. Its quasi-compactness hypothesis holds by step 1. Its coefficients are arbitrary commutative condensed rings, and its derived categories are ordinary unbounded module-object categories, as here. Consequently $a^*j_!A\simeq0$ in $D(T_{\mathrm{pro\acute et}},\Lambda)$, without any further boundedness or reducedness assumption.

Uses: lem-sfb-condensed-support-derived-localization.

### Original step 3 — lem-sfb-open-extension-zero-constructible-finite-tor

Set $K=j_!A$. Constructibility: since $j_!$ is exact and applied termwise, $H^q(K)\cong j_!H^q(A)$ for every $q$ [lem-weil-pbc-exact-functor-complex-cohomology], so $K$ is bounded with the bounds of $A$. Each $H^q(A)$ is constructible in the finite-constant-local-model sense of [sk-def-sfb-constructible], hence so is $j_!H^q(A)$ by [lem-sf-open-extension-zero-constant-model-constructible] (strata of $U$ together with the reduced complement, zero model on the complement). Thus $K\in\Dbc(W,\Lambda)$ in the sense used by $\Dctf$. A finite constant local model is locally finitely presented [det-def-sfb-constructible-local-model], on the same strata, so $K$ is also bounded constructible in the ring-object sense of [sk-def-sfb-bounded-constructible] used by the rational base-change node. Tor amplitude: choose a finite Tor interval $[u,v]$ for $A$. For any sheaf $N$ of $\Lambda_W$-modules, the open-immersion derived projection formula gives
$$K\otimes^{\mathbf L}_{\Lambda_W}N\simeq j_!\bigl(A\otimes^{\mathbf L}_{\Lambda_U}j^*N\bigr).$$
The cartesian-coefficient assertion makes $j^*$ exact, so $j^*N$ is again a sheaf in degree zero. The inner tensor therefore has cohomology only in $[u,v]$, and by exactness of $j_!$ again so does its extension by zero. Thus $K\in\Dctf(W,\Lambda)$.

Uses: lem-weil-pbc-exact-functor-complex-cohomology, lem-sf-open-extension-zero-constant-model-constructible, det-def-sfb-constructible-local-model, sk-def-sfb-bounded-constructible, lem-sfb-open-immersion-derived-tensor-projection, sk-prop-sfb-cartesian-coefficients, def-sfb-module-open-lower-shriek, sk-def-sfb-constructible.

### Original step 4 — parent assembly

Suppose $\Lambda$ is a finite commutative ring killed by a power of $\ell$. Apply clause (2) of [det-thm-sfb-proper-base-change-finite] to $r:W\to\overline Y$, $g=c$, $g'=a$, and $p'=r_Z$. Properness and the standing scheme hypotheses hold by step 1, and $K=j_!A$ lies in $\Dctf(W,\Lambda)$ by step 3. It follows that
$$c^*Rr_*j_!A\simeq R(r_Z)_*a^*j_!A.$$
Both sides are objects of the ordinary unbounded module-object derived category on $Z$.

Uses: det-thm-sfb-proper-base-change-finite.

### Original step 5 — parent assembly

For $\Lambda=\mathcal O_E$ use clause (3) of [det-thm-sfb-proper-base-change-integral] on the same square and $K=j_!A\in\Dbc(W,\mathcal O_E)$ from step 3. This also covers $\mathbf Z_\ell$ by taking $E=\mathbf Q_\ell$, whose valuation ring is $\mathbf Z_\ell$. For $\Lambda=E$ or $\overline{\mathbf Q}_\ell$, use clause (3) of [det-thm-sfb-proper-base-change-rational], again on that square and bounded constructible $K$. The case $\mathbf Q_\ell$ is $E=\mathbf Q_\ell$. These cases and step 4 exhaust the admissible list in [sk-def-localizing-closure]. The algebraic-closure coefficient is throughout the finite-subextension condensed ring fixed in the statement. We obtain in every case
$$c^*Rr_*j_!A\simeq R(r_Z)_*a^*j_!A.$$
Only bounded constructible inputs to these theorems are used, with no assertion on a localizing closure.

Uses: det-thm-sfb-proper-base-change-integral, det-thm-sfb-proper-base-change-rational, sk-def-localizing-closure.

### Original step 6 — parent assembly

Substitute $a^*j_!A\simeq0$ from step 2 into the isomorphism of step 4 or 5. The derived adjunction $r_Z^*\dashv R(r_Z)_*$ implies $R(r_Z)_*0\simeq0$: for every $B$, its adjunction identifies $\operatorname{Hom}(B,R(r_Z)_*0)$ with the singleton $\operatorname{Hom}(r_Z^*B,0)$, so $R(r_Z)_*0$ is terminal and hence isomorphic to the zero object. Thus $c^*Rr_*j_!A\simeq0$, as claimed.

Uses: sk-def-sfb-module-derived-pushpull.

## Review by Q129

I read proof (3) in the current blueprint and the actual statements cited in every parent step. The corrected split keeps exactly the original target object, coefficient convention and finite-Tor bounded-constructible hypothesis. Step 1 now uses the new complement-square statement for the standing schemes, proper base-changed map, complementary immersions and the actual derived isomorphism a^*j_!A=0. The closed complement in the item is reduced, which is stronger than the new node needs; the fibre product T is not assumed reduced. Step 2 uses the new preservation statement for both constructibility meanings and finite Tor amplitude, with no equation of those meanings. The open is a morphism of the standing k-schemes and Lambda is a commutative condensed ring, so the generalized node applies.

Step 3 takes precisely clause (2) of det-thm-sfb-proper-base-change-finite; its finite ring is killed by a power of ell, r is proper and K is Dctf by step 2. Step 4 takes clause (3) of the integral and rational nodes and the full admissible list from sk-def-localizing-closure. Their input K is bounded constructible in both relevant senses; taking E=Q_ell covers Z_ell and Q_ell. The algebraic-closure case retains the finite-subextension ring fixed in the item. I opened the three original blueprint statement files and checked that these are their base-change clauses, not their output-finiteness clauses. These three nodes are retained generic tools from the parent's existing split_report.tool_uses: they give the specific base-change isomorphisms; the composition unit supplies no replacement.

Step 5 uses the derived adjunction stated, not just a name for pushforward, in sk-def-sfb-module-derived-pushpull. Its Hom calculation proves right-adjoint preservation of the terminal zero object directly, so no unrecorded zero-preservation theorem is hidden. Every parent citation has a verbatim statement quote in citations.json. None of the new nodes depends on the parent. The new statements introduce all schemes, morphisms, coefficients, categories and intervals and cite their definition nodes. They have no proof steps, proof dependencies or construction sketch. Their source is the actual blueprint calculation being refined; the auxiliary Stacks labels above are not replaced by changing section numbers.

For the geometric node I checked U empty, U=W, r the identity, empty W, and nonreduced base-change fibres: only underlying complementary closed subsets are asserted, and the mixed restriction is zero in all those cases. For the preservation node I checked zero A, empty U, j identity, disjoint cohomological and Tor intervals, zero coefficient ring, finite rings of nonzero global dimension, and arbitrary nonadmissible condensed rings. No global-dimension claim or derived-completeness condition enters; exact open extension preserves the chosen interval by the projection formula for each degree-zero test module. Arbitrary condensed coefficients in this node are intentional: the old proof needs only exact restriction, exact open extension and the open projection isomorphism, all available for pulled-back general condensed rings. This is why the admissible-only localizing theorem is not a duplicate.

The repair addresses the human return by moving 2600 characters of genuine argument into two separately claimable obligations of comparable original size, while preserving all 4259 original characters above. I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the files and sources. There is no statement dispute, SGA citation, route replacement, Lean edit or compiler invocation. No mathematical work requested by the return is left unfinished; the new nodes are deliberately statement-only for parallel workers.

## Validation

The required deliver.py --no-push completed successfully: preflight passed at d374246b37e (OK, not pushed). I then corrected a report-only tag transcription: lemma-open-immersion is 09BN, whereas 09AC is lemma-compute-i-star. The source label and mathematics were already correct. A final dry run validates that report correction before pushing.
