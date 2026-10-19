# Stage-1 delivery: lem-per-prime-field-tensor-devissage

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-prime-field-tensor-devissage.json: item, split into eight proof steps; statement unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-algebra-external-tensor-filtration.json: statement, unsplit; no Mathlib match. ILO XVII 7.4.7 for an arbitrary finite-dimensional algebra over F_ell.
- dag/nodes/sec-deligne-laumon-a1/lem-per-constructible-finite-monodromy-filtration.json: statement, unsplit; no Mathlib match. Geometric filtration by extensions from finite-cover-trivialized stratum sheaves, before any tensor-factor argument.
- dag/nodes/sec-deligne-laumon-a1/lem-per-galois-cover-module-descent.json: statement, unsplit; no Mathlib match. Arbitrary-coefficient module descent on one connected finite Galois cover, with exactness and mixed tensor comparison.
- citations.json contains a verbatim statement for every cited node in every step. report.md and searches.jsonl accompany the delivery. The local dag-index.json and ilo.txt are reading aids only.

## Attachments

None. Read-only searches of WeilConjectures/ in slopmaster2 and upstream master for the blueprint tag, prime-field terminology, tensor devissage and 7.4.6 found no project declaration giving this statement. Searches of the pertinent SixFunctors and RepresentationTheory files likewise found no candidate for the new nodes. Master sorry declarations are not treated as completed proofs.

## WANTED

None. The ILO PDF and relevant Stacks source are present.

## Corrections and scope

The imported item was a statement-only node, not an existing completed split. Its statement, source, statement dependencies, creation record and blueprint ancestry are retained. Its proof is the prime-field specialization of ILO XVII 7.4.1, proved using 7.4.2 and 7.4.7 through the reductions in 7.4.6. Finitely generated N suffices: 7.4.6 and 7.4.7 explicitly produce modules of finite type, even though the formulation of 7.4.1 allows arbitrary N.

There is no statement dispute. No invertibility of ell on X, finite underlying set of A, perfection of N, or descent of every A-object to F_ell is added. The group algebra used in the application of 7.4.7 is B=F_ell[G], so A tensor B=A[G]. The PDF's sentence immediately before 7.4.7 prints B=A[K]; this cannot literally be its finite base-coefficient algebra when A is infinite, and is read as the evident group-algebra specialization just written. This is a correction to that application's notation, not a change to the theorem.

The chapter and unit are unchanged. The item's existing ancestry identifies the coefficient-extension argument inside Artin–Gabber duality. This is an infrastructure split under that ancestry, not a replacement for the unit's Fourier/perverse argument. All cross-unit proof tools are explicitly justified in split_report.tool_uses.

## Existing-node and blueprint searches

I searched the whole DAG (20,638 records in the local read-only index) by statements, titles, ILO section numbers, finite group, monodromy, Galois partition, finite filtration, tensor products, constructibility and descent. I ran blueprint_refs.py ancestor for the item and searches for tensor filtration, finite group, finite-dimensional algebra, monodromy, Galois descent, unipotent, tensor simple, torsor trivialized, finite etale descent and constructible filtration. No blueprint node states any new lemma. The finite-field continuous-representation nodes and finite-ring torsor nodes have narrower coefficient hypotheses. Existing generic Serre, global stratification, finite presentation, geometric stalk, tensor stalk, short-exact triangle and good-truncation nodes are used directly rather than recreated.

Mathlib searches were all made with msearch.py and their actual returned summaries are recorded. Each new node has leansearch, leanfinder, loogle and source grep; second semantic phrasings were read. The algebra searches find Module.Finite.tensorProduct, Module.Finite.base_change, semisimple module decompositions and Artin–Wedderburn infrastructure. None states the external-factor filtration for arbitrary Noetherian A. The geometry searches find etale topologies and sheaf finite-generation infrastructure, not directed monodromy filtrations. The descent searches find finite Galois categories and equivalences arising from site comparisons, not arbitrary-coefficient module descent on a fixed scheme torsor with the stated tensor comparison. I did not claim that these general tools are absent; I claim they do not themselves state any new node or a one-line specialization of it.

## Not duplicates

lem-per-finite-algebra-external-tensor-filtration vs lem-per-prime-field-tensor-devissage: this is a theorem about modules over arbitrary finite-dimensional noncommutative algebras, with no schemes or derived category. The item proves thick generation by combining its filtration with geometric descent, stratum extensions and truncations; it does not merely apply a renamed generation theorem.

lem-per-constructible-finite-monodromy-filtration vs lem-per-prime-field-tensor-devissage: the new node gives only geometric stratum/monodromy filtration; it has no external tensor factors or derived-generation conclusion.

lem-per-constructible-finite-monodromy-filtration vs det-lem-coefficient-heart-filtration: the existing node is for E or Qlbar in the pro-etale lisse coefficient framework and supplies a filtration into lisse sheaves. The new node concerns arbitrary Noetherian F_ell-algebras on the ordinary etale site and supplies further finite-cover-trivialized quotients, with no rationalization.

lem-per-constructible-finite-monodromy-filtration vs lem-fin-constructible-devissage: the latter has finite coefficients and a finite-type-over-a-field base. It does not cover the arbitrary Noetherian scheme and arbitrary Noetherian F_ell-algebra here.

lem-per-galois-cover-module-descent vs lem-weil-pbc-finite-ring-torsor-module-descent: the existing node assumes a finite coefficient ring and asserts essential realization only. The new node permits arbitrary rings and states an exact equivalence and mixed tensor comparison; its arbitrary-ring clause is necessary for A.

lem-per-galois-cover-module-descent vs cor-galois-lisse-representations: the existing finite-coefficient clause assumes a finite ring; its other clauses concern adic coefficients. The new statement is about sheaves trivialized by one supplied finite cover with arbitrary ordinary discrete coefficients.

lem-per-galois-cover-module-descent vs lem-pod-lisse-tensor-and-scalar-extension: only the existing node's constant-stalk clause has arbitrary rings; its tensor and scalar clauses assume finite rings. The new node needs mixed tensors with an arbitrary Noetherian A-module and a finite-field representation on the supplied cover.

No new node carries a Stacks tag shared with an existing node: the new source statements are from ILO, with specific proposition/lemma numbers. Stacks tags for existing tools remain in proof sources and are not used in lieu of node citations.

## Review by NK

I read the ILO PDF, printed pages 301–308, especially 7.2.3–7.2.7 (including the warning that local constancy alone need not mean a fundamental-group local system), 7.3.1–7.3.6, 7.4.1–7.4.2 and 7.4.5–7.4.7, together with the proof of 7.4.1. For the algebra node I checked the noncommutative finite algebra, finite-type module and direct-summand conclusions of 7.4.7. For the geometry node I followed the directed-partition filtration and then the unipotence filtration to finite-group local systems; it does not assert that the original locally constant sheaf on a singular stratum has finite monodromy. For the descent node I read the equivalence in 7.2.3 and its finite quotient application in 7.4.6; on the given connected cover arbitrary constant modules have their usual maps, and the descent operations give the exactness and tensor statement. These are supporting statements left unsplit, not proofs hidden inside their statements.

For Step 1 I opened both discrete-Noetherian constructibility nodes and checked that one states weak Serre closure and the other compares affine-local with global finite stratification on a Noetherian scheme. I added the existing finite-module finite-presentation node rather than silently identify the coefficient conventions. The derived long-exact node says exactly the exact sequence used to express cone cohomology as a kernel/cokernel extension. A retract's cohomology is explicitly the image of an idempotent; no claim that arbitrary subsheaves are constructible is needed.

For Step 2 I checked the ordinary tensor-stalk theorem, stalk exactness and stalk isomorphism detection. Their statements do not require finite underlying coefficient sets. The basis-splitting argument is written out, giving K-flatness and the cohomology calculation. The constant-stalk clause of lem-pod-lisse-tensor-and-scalar-extension is used only in its explicitly arbitrary-ring form: its finite-ring tensor and scalar-extension clauses are not applied to A. On the lisse cover the finite-dimensional F_ell stalk has a basis, producing N^d and a stalkwise isomorphism to the local tensor model. The argument works when N is not A-flat and when N has infinite dimension as an F_ell-vector space.

For Step 3 the new geometric filtration explicitly provides the locally closed factorization, constant-on-cover finite-type quotients and constructibility. The cited short-exact triangle node concerns any abelian category, so it applies to A-module sheaves. Step 4 uses the new descent node for the precise exact equivalence and tensor identity it states, and the algebra node for the filtration, not any unstated construction in their proofs. B=F_ell[G] is finite-dimensional because G is finite; M is finite over A tensor B because it is already finite over A. A simple B-module is finite-dimensional by the explicitly written cyclic quotient of B, so its associated F_ell sheaf has the finite type required by the generators.

For Step 5 I opened the ordinary open-extension exactness and finite pushforward stalk nodes. The latter is for abelian sheaves and finite morphisms; a closed immersion is finite and has one geometric fibre point on its image and none off it. Module exactness follows from the same underlying abelian sequence, since the maps preserve A. I did not cite the similarly named closed-pushforward stalk node for structure-sheaf modules on the Zariski site. The short stalk calculation proves the needed exactness instead. Retracts remain retracts under any additive functor.

For Step 6 the open stalk node and finite stalk formula give the two values of extension from the chosen factorization. The F_ell sheaf F_0 has an explicit stratification including the two complementary pieces. The mixed coefficient map is described on sections/extension-by-zero presheaves, and its stalks are computed explicitly; hence this is a routine stalk argument, not an uncited arbitrary-A projection formula. I checked the arbitrary-module hypotheses in the tensor-stalk theorem. Step 7 uses only the earlier finite filtrations, the stated short-exact-to-triangle theorem and the defining closures of T. Step 8 uses exactly the existing truncation cohomology and distinguished truncation triangle statements. The lower starting truncation is acyclic; the final upper truncation is quasi-isomorphic to K, so there is no unbounded induction or appeal to infinite sums.

I tested X empty, the zero ring A (all modules zero), E=0, N=0, the trivial group, ell dividing the group order, nonsemisimple finite group algebras, infinite A such as F_ell[t], a non-A-flat module such as A/(t), and a single-degree or zero complex. The algebra lemma does not assert semisimplicity or split the whole representation into tensor products: only filtration quotients are retracts. No inverse of |G| is used. I checked that the three new statements are smaller tools rather than clauses of the generation conclusion; no new node is elementary and no Mathlib match was relabelled unsplit. Every new statement introduces its own objects and definition dependencies. New nodes contain no proof or proof dependencies. Every citation has an actual verbatim statement in citations.json. All eight steps have an explicit elementary flag, all are under 2,000 characters, and the proof dependency set equals their citation union. No prohibited source or SGA route is used.

## Unfinished work

None in the one-level split. The three new supporting nodes intentionally remain statement-only unsplit items, for later workers.
