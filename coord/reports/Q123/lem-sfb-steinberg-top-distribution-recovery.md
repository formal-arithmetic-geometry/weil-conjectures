# Q123 stage-1 report: lem-sfb-steinberg-top-distribution-recovery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-steinberg-top-distribution-recovery.json — item, unchanged statement, five-step split.
- dag/nodes/sec-six-functors-basics/lem-sfb-frobenius-adjacent-borel-reflection.json — new statement-only lemma, unsplit; no Mathlib match.
- citations.json — ten verbatim quotations covering every step/node citation pair.
- searches.jsonl — ten actual msearch.py calls, five for the new lemma and five additional searches for the item.

One new node, zero Mathlib leaves. No unit, Lean, repository or launcher file was edited.

## Attachments

None. Project searches for the exact item tag and for Steinberg, baby Verma, hyperalgebra, Harish-Chandra, Frobenius-kernel and highest-vector terminology found no matching declaration. The Steinberg hits are Lang–Steinberg results about semilinear Frobenius. No compiler was run.

## Wanted literature

WANTED: Jantzen, Representations of Algebraic Groups (2003), II.3.18 and the finite-kernel intertwining/distribution material of II.9, for lem-sfb-steinberg-top-distribution-recovery and lem-sfb-frobenius-adjacent-borel-reflection. The item already marks this book missing. It was not inspected.

I read local Milne, Algebraic Groups, printed pp.422–423 (20.37–20.41, SL2 root maps), pp.428–430 (21.11, rank-one maps, coroots and reflections) and pp.610–613 (C.10–C.22, roots and bases). These supply geometric inputs, not the new finite-kernel module assertion. The assembled proof is explicitly agent-written and the new node remains unsplit.

## What changed and what was wrong

The item had a complete statement and no proof. Its arbitrary ordering of noncommuting root factors needs justification. The proof now constructs a simple-wall sequence, recovers its vectors in reverse order, and only then uses the existing distribution-socle statement to compare products in arbitrary orders.

No statement dispute was found; the statement is unchanged. Positive roots are those of Lie(B); the initial distribution-module vector has character +(q-1)rho. Characters and coroot coordinates are integral lattice data, including in characteristic 2.

The ancestor command returns blueprint.from.node = None for this inherited agent-created chain. I retained the existing item's from.node and via and used that exact ancestor result for the new node, prepending the item to via. Its place identifies the local calculation. Searches of the entire blueprint for Steinberg, highest vector, divided powers, adjacent Borel and top distributions found no equivalent statement. Broad Frobenius/Borel hits were also inspected. I read the latest blueprint unit at sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof, especially clause (3); no chapter/unit route was changed.

## Not duplicates

lem-sfb-frobenius-adjacent-borel-reflection vs lem-sfb-reductive-rank-one-reflections: the existing node constructs rank-one groups and reflections, with no finite-kernel highest-vector operation.

lem-sfb-frobenius-adjacent-borel-reflection vs lem-sfb-sl2-divided-straightening: the existing identity is in a Q-algebra with factorial denominators; it does not state a positive-characteristic distribution identity or the full adjacent-Borel eigencharacter.

lem-sfb-frobenius-adjacent-borel-reflection vs lem-sfb-frobenius-kernel-induced-dual-pbw: PBW/evaluation duality gives no invertible simple-wall operation or reflected highest-vector equation.

lem-sfb-frobenius-adjacent-borel-reflection vs lem-sfb-unipotent-frobenius-distribution-socle: the socle statement concerns one unipotent algebra, not opposite-root operators on arbitrary modules.

lem-sfb-frobenius-adjacent-borel-reflection vs lem-sfb-steinberg-top-distribution-recovery: the new lemma concerns one simple root in any module with one prescribed coroot coordinate, not a product over all roots or the Steinberg induced module. The item still carries the gallery, character bookkeeping, induction, reversal, and arbitrary-order comparison.

Before creating the node I searched its intended id, adjacent-Borel/simple-reflection/highest-vector terminology and the II.3.18 source context in the DAG and ran blueprint_refs.py searches. The rank-one straightening, root-string triangularity, root normalization, mixed commutation, rho/Weyl, PBW and socle statements were opened. None states the new lemma. There is no Stacks tag for this representation-theoretic input; none was invented.

## Review by Q123

I checked the item against its statement, the infinitesimal-simplicity parent and the PBW and socle siblings. This stays on the infinitesimal route: no global induced-module simplicity, dimension formula or Weyl filtration is used. Jantzen is absent; the Milne geometric sources above were read and the finite-kernel argument is marked agent-written. The new node independently introduces the field, group, torus, Borels, roots, pairing, kernels, distribution multiplication, characters, parameters and arbitrary module; it contains no proof or proof sketch.

Step 1 now explicitly specializes the current PBW statement to eta=lambda and the given opposite Borel. I checked that the prescribed B-character restricts to lambda and is trivial on its unipotent radical, and that the current statement defines exactly M and v. The finite-kernel and nonzero-vector assertions apply to these same objects. A new verbatim excerpt quotes the one-dimensional module and balanced tensor product, alongside the finite/nonzero quotations. The highest-vector equation is written with the module action b dot 1, making the balancing computation explicit. The empty-root case still takes c=1.

Step 2 cites the Borel-pair statement for its integral simple-root base with sign-coherent coefficients, and the new local lemma for the adjacent positive system and reflection formula. If all current simple roots were original-negative, their nonnegative sums would be original-negative, so a nonempty original-positive intersection contains a current simple root. Each crossing removes precisely that root. The half-sum changes by minus this root; comparing with the reflection formula gives coroot coordinate 1. These are equalities in the rational character space, with integrality retained by subtraction from the given rho. During self-review I moved the local lemma's geometric positive-root clause before all module/weight hypotheses: using it to construct the gallery must not assume the weight condition that the construction subsequently proves.

Step 3 uses the full conclusion of the local lemma, including the C'_r distribution eigencharacter, not just Lie algebra invariance. Its integer pairing q-1 is supplied by step 2 at every stage. It accepts an arbitrary A-module, so M needs no global S-action. The parameters are those of the item, and the character shift equals mu_{j+1}. The base is step 1 and both assertions of the induction are explicit.

Step 4 multiplies the recovery equations already obtained. The rightmost positive factor is beta_N and acts first on u_N, whose last-applied negative factor is also beta_N. Thus the equations reverse the process one at a time without commuting root factors. This step is elementary.

Step 5 uses the socle node's statement, which explicitly permits any enumeration, gives a nonzero top product spanning the annihilator of the augmentation ideal, and also includes the negative roots of every opposite Borel. Thus the two positive products span one line, and the two negative products span another. Their proportionality factors a,b are nonzero. Their equations hold in A under the distribution inclusions; solving the explicit scalar equation gives c=(ab)^(-1) product(kappa_j), a unit. No compatibility with operator ordering or root normalization is left implicit.

I tested the new statement with w=0 and V=0, for rank-one SL2 and at p=2. In Sym^(q-1)(F^2), coefficient extraction takes X^(q-1) to Y^(q-1) and back, with binomial(q-1,q-1)=1. Independent root-parameter scaling gives nonzero (q-1)st-power factors. Coefficients were checked for p=2,3,5 and r=1,2,3. The empty root system has no simple-root instance of the new lemma and is handled in step 1. An independent finite root-coordinate computation in A2, B2 and G2 verified 3,4,6 crossings, respectively, without repeated original-positive roots. These test signs and bookkeeping, not the general lemma's proof.

For the next worker on the unsplit node, the intended local argument is a rank-one Gauss/SL2 calculation. The common non-simple-root radical is normalized by the negative simple-root group, so its distribution augmentation also kills the lowered vector. Negative simple-root distributions kill their own top divided power on the finite kernel. Torus distributions shift the character by -(q-1)alpha. Opposite top powers have coefficient binomial(q-1,q-1)=1 for compatible parameters, and arbitrary parameter scaling changes it by a unit. This outline belongs in this report, not in the statement-only node.

I checked delivery-errors B–E against the actual files and sources. The new statement introduces its objects and defines or cites its notions; TeX has one logical backslash. All five new-node searches and five new item searches were actually run and read, including a second semantic phrasing; the LieModule chains, characteristic-zero sl2 strings and root-reflection hits do not state these finite-kernel results. No Mathlib leaf is asserted. All non-split-owned item fields are preserved. Each step's citations have verbatim statement quotes, not assertions borrowed from a cited proof. No generic off-unit tool is used. A dependency traversal found no return path to the item. No non-elementary step exceeds 2000 characters; the longest is 1474. The separate local module subclaim is a new node, while the item's counting, balancing, induction and scalar manipulations are explicit.

The server review_split check passed. The first delivery dry run required a longer PBW citation excerpt; I extended that verbatim quote to include the adjacent all-primes sentence. I also wrote out why reflection permutes the other current-positive roots, directly from their sign-coherent simple coordinates. The full dry run is repeated after these repairs.

## Unfinished work

The item's assembly split is complete. The new supporting node is intentionally unsplit and joins the stage-1 queue; it is not claimed proved. Jantzen remains WANTED.


## Repair of returned delivery 03ab8021401

The return has one point: landing refused the reviewed head because the statement of lem-sfb-frobenius-kernel-induced-dual-pbw changed. I compared the retained returned delivery with the current live item, which is still unsplit: its statement, statement dependencies and all non-split-owned fields agree. The split now starts from the current live JSON and overlays only the permitted split fields. The new supporting node and the actual search log are retained; no new search question or statement change calls for repeating the searches.

The old PBW definition said $f(xb)=\widetilde\eta(b)f(x)$ “after every commutative F-algebra extension.” The current definition explicitly requires the equality for every commutative $F$-algebra $D$, $x\in L_r(D)$ and $b\in P_r(D)$. I reread its complete current statement. This clarifies the covariance quantifiers; it does not change its algebra $A$, Borel distribution algebra, one-dimensional module, balanced tensor product, finite kernels or nonzero highest vector. Step 1 uses precisely those last assertions, not the construction of the rational function module or its evaluation duality. I nevertheless expanded the proof to check the full specialization and added its verbatim module-definition excerpt to citations.json. This is a proof/citation repair, not an unchanged re-push.

I also reread the current statements of lem-sfb-reductive-borel-pair-structure and lem-sfb-unipotent-frobenius-distribution-socle, plus the retained new lem-sfb-frobenius-adjacent-borel-reflection. The socle node has since been split and reviewed, but its statement still supplies arbitrary enumeration, nonzero top product, the annihilator line and the negative-root version. The Borel-pair statement still supplies the same sign-coherent simple-root coordinates. All ten citation excerpts were checked verbatim against the current statements. The single-wall node remains absent from main and is still the one new statement-only node. The item statement is unchanged, all steps are below 2000 characters, and the earlier small-case checks remain relevant because neither the item nor the supporting statement changed.

The updated PBW statement SHA-256 read for this repair is 2d651655c925b13524221dc811bfc9e00b20ff7bc21696ac88f95c998572ce41. The required delivery dry run is performed again on the current DAG before pushing.
