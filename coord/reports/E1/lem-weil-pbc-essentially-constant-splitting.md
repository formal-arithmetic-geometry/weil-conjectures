# Stage 1 delivery: `lem-weil-pbc-essentially-constant-splitting`

## 1. Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-essentially-constant-splitting.json`: split the forward implication of Stacks 070C into four complete steps. No new nodes.

## 2. Attachments

None.

## 3. Wanted

None.

## 4. Problems found

- The source proof says only that setting `Z_j = Ker(A_j -> A)` works. The imported helper node had no proof. The delivery writes out the omitted retraction, direct-sum existence and uniqueness, transition compatibility, and eventual-zero calculations.
- The configured source and Mathlib checkout paths in `SETUP.md` are absent on this machine. I read the same pinned Stacks source from `/home/ubuntu/weil-conjectures-sheaf-F2/literature/stacks-project/` and searched the available Mathlib tree at `/home/ubuntu/SHEAF/project-20261007/lean/.lake/packages/mathlib/Mathlib/`.
- Fetching `origin/sheaf-dag` failed because the SSH remote rejected this machine's key. The dedicated worktree is based on the existing local `origin/sheaf-dag` at `c9874496631db122143674288f3327d3648e95b3`.

## 5. Unfinished

None.

## Review by E1

I read Homology Lemma 070C and Categories Definitions 05PU and 05PV. The item specializes the source's abelian-category assertion to abelian groups and states the same retraction, compatible cone, and eventual factorization data as the cited essential-constancy definition. Step 1 derives $p_j\pi_j=1$ using cone compatibility. Step 2 writes the unique image-plus-kernel decomposition elementwise. Step 3 checks both transition identities and restriction to the kernels. Step 4 applies clause (b) of the definition to make a later kernel transition zero. The two cited definition nodes state all non-elementary input; the remaining calculations are elementary group homomorphism identities. I checked the constant system ($Z_j=0$) and an eventually zero system ($X=0$) as edge cases. There is no new node, cycle, changed hypothesis, or route departure. The delivery has only the item and report in one commit; no correction was sent back.
