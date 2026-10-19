# Worker report: lem-wf-fibre-functor-basepoint-transport

## Files written

- `dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-fibre-functor-basepoint-transport.json`: statement, split into ten steps; statement unchanged; not a Mathlib leaf.
- `dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-exact-finite-gsets-forgetful.json`: new statement-only dependency, Stacks 0BMV, unsplit; no Mathlib match.
- Sandbox `citations.json`: verbatim statement quotations for every proof-step dependency. `searches.jsonl` is the actual msearch log. `write_split.py` regenerates the sandbox files and is not a delivery file.

## Attachments

None. I searched all of `WeilConjectures/` in the read-only slopmaster2 checkout for the item id, basepoint names, fibre-functor terminology and the relevant path declarations. Finite-cover path constructions exist in FundamentalGroup/FrobeniusElement.lean, Restriction.lean and FrobeniusTransport.lean; none states all of the item's finite-module and integral/rational/algebraic-adic clauses.

The project declaration `CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor`, in `WeilConjectures/Mathlib/CategoryTheory/Galois/Prorepresentability.lean:138`, is not in Mathlib. I read its surrounding variables (lines 38-39 and 83) and proof (138-146), and its record in `local/sorry_map_slopmaster2_7d675a26.jsonl.gz`: `s=false`, `ts=false`. It states an isomorphism between two functors already satisfying Mathlib's FiberFunctor axioms on a GaloisCategory. It does not state the new 0BMV lemma for an arbitrary topological group and a merely exact finite-valued functor: in particular, conservativity is not a hypothesis of 0BMV but is an extra input to that project theorem. Converting those hypotheses requires a mathematical argument, so neither an exact attachment nor a one-line Mathlib leaf is claimed. It also does not cover the item's adic assertions.

## WANTED

None. Stacks `pione.tex` and `sites-modules.tex`, Deligne Weil II, and the current blueprint are present locally.

## Problems found and corrections

The item was unsplit. Its statement agrees with its intended sources and requires no correction. The connected-scheme hypotheses suffice for the finite assertions; Noetherianity, separatedness and invertibility of ell are used only for the stipulated adic category. I retained that distinction. I also retained the finite-ring assertion for noncommutative rings.

The current main-20261015 ancestor `def-wf-fundamental-representation` asks for stalk transport and change of base point but does not supply the construction. I expanded these without changing the affine-geometry unit or its route. The new generic dependency isolates the exact-functor uniqueness result actually used by Stacks' proof; all coefficient transport calculations remain in the item.

## Not duplicates

The whole-DAG searches for `0BMV`, `second-fundamental-functor`, two fibre functors and the proposed id found no existing statement of 0BMV. Whole-blueprint searches with `blueprint_refs.py` for `0BMV`, `fibre functor`, `Galois category`, `exact functor`, `forgetful` and `change of base` found no equivalent blueprint node.

- lem-wf-exact-finite-gsets-forgetful vs lem-wf-fibre-functor-basepoint-transport: the new lemma concerns any exact finite-valued functor on finite continuous actions of an arbitrary topological group; the item constructs geometric stalk transport and proves topological, module, coefficient, adic and action compatibilities. The new lemma has no schemes, stalks or adic assertions.
- lem-wf-exact-finite-gsets-forgetful vs thm-galois-fundamental: the existing theorem classifies finite sheaves by the automorphism group of one geometric fibre functor; it does not identify a second exact functor with the forgetful functor.
- lem-wf-exact-finite-gsets-forgetful vs lem-real-lisse-path-fibres: that node concerns paths and rational lisse sheaves on a smooth separated finite-type scheme over an algebraic closure of a finite field, together with a pro-etale comparison; it does not state the abstract exact-functor lemma. Its scheme hypotheses are also stronger than those of this item's finite assertions.

## Review by NF

I read Stacks 0BMV (`pione-lemma-second-fundamental-functor`, pione.tex:280-349), 0BN5 (`pione-lemma-functoriality-galois`, 672-703), and 0BND (`pione-theorem-fundamental-group`, 1217-1255). The new statement is exactly the statement of 0BMV, with the finite continuous action category and its maps spelled out and “exact” tied to the existing definition. In particular G need not be profinite and H is not assumed conservative. It carries no proof, sketch, or proof dependencies. I read Deligne Weil II (0.1), printed p.144, and (1.1.1) b)-d), printed pp.146-147 (PDF pages 9 and 11-12), checking the Noetherian separated ell-invertible convention, compatible inverse systems, rationalized Hom modules and the coefficient 2-colimit. The transport compatibilities are an explicit agent argument based on those constructions, so `proof_origin.by` is `agent`.

For steps 1-2 I opened the statements of thm-galois-fundamental, thm-galois-lc-etale, lem-fet-galois-category, def-galois-category and lem-galois-equivalence-preserves-limits. They respectively supply the equivalence with finite continuous pi_y-sets, its compatibility with the finite-cover fibre, the Galois axioms for each geometric point, exactness/finite values, and preservation by an inverse equivalence. Thus H=F_z Q has precisely the hypotheses of the new lemma. The counit has the required direction QB -> id, so the formula really gives F_y -> F_z. No change-of-base-point clause was silently taken from thm-galois-fundamental: its statement does not include that clause.

For step 3 I read def-galois-fibre-functor's induced product topology over a small skeleton. Every target evaluation is a finite discrete conjugation of one source evaluation; continuity and inverse continuity follow directly. The change-of-path multiplication was checked in order: a=t't^{-1} lies in pi_z, not pi_y, and c_{t'}=Int(a)c_t.

For step 4 I read cor-galois-lisse-representations(1): its action is evaluation on the underlying finite locally constant set sheaf, exactly what this step uses. Projections force the product comparison for t, so addition and scalar multiplications give linearity without assuming t is a monoidal natural transformation. Naturality applies to set maps as well as linear maps.

For step 5 I read lem-pod-lisse-tensor-and-scalar-extension(3), including lissity and its stated map b tensor germ(x) -> germ(b tensor x). I checked its source's ringed-topos tensor formula in Stacks 03EL (`sites-modules-lemma-tensor-product-pullback`, sites-modules.tex:3649) and the locally constant tensor statement 093V (`lemma-tensor-product-locally-constant`, :8610). The step proves the path comparison on every pure tensor by the underlying set-sheaf map i_b and then additivity. This avoids an incorrect requirement that i_b be A-linear when rings are noncommutative. The compatibility for composites is checked on c tensor (b tensor x).

For step 6 I read def-pod-lisse-l-adic-sheaves(1) and def-pod-lisse-adic-fibre-functors(1): they give compatible-family morphisms and the actual inverse-limit fibre maps. The transition map is a set-sheaf map across the two coefficient levels, so the same t commutes with it. The inverse is coordinatewise t^{-1}; O_E-linearity reduces to every finite coefficient ring. There is no assertion that a geometric stalk commutes with an arbitrary inverse limit of sheaves.

For step 7 I read def-pod-lisse-l-adic-sheaves(3) and the “at every level” coefficient-extension assertion in cor-galois-lisse-representations(2). The scalar-extended object has exactly the prescribed index n=ceil(m/e). The canonical fibre comparisons are provided by that cited statement; the new equality for paths is proved by projecting to every level m and evaluating on pure tensors. No unramifiedness, flatness of a coefficient quotient, or unjustified interchange of tensor and inverse limit is assumed.

For steps 8-9 I read the rational and algebraic fibre functors in def-pod-lisse-adic-fibre-functors(2)-(3), and Hom rationalization and common-field Hom colimits in def-pod-lisse-l-adic-sheaves(2),(4). Naturality is first checked for tensors a tensor u, then their finite sums; algebraic morphisms are represented at a common finite field. Compatibility after further extension makes their induced equality well-defined on the Hom colimit. This is the supplied coefficient route, not a filtered colimit of finite-coefficient stalks.

For step 10 I reopened both clauses of cor-galois-lisse-representations. Its integral action is built from finite evaluations, and the rational and algebraic actions are their scalar extensions. Evaluation of t g t^{-1} and t'=a t gives the two finite equalities with the correct source and target; coordinatewise limits and tensoring preserve them. This proves both adic formulas, not merely existence of abstract isomorphic representations.

Small cases: a separably closed field gives trivial fundamental group and the usual identification of constant stalks; y=z and the identity path give identity maps; t'=t gives a=1; the empty finite sheaf and zero module yield their unique maps; a zero ring is harmless. The new lemma includes G trivial and finite G, and H=U, as well as topological groups with no nontrivial finite quotients (only trivial finite actions). No empty scheme with chosen geometric points exists, so that is not an omitted case. Integral zero and torsion systems, E=L, a ramified extension and a change of integral model via rational isomorphism are all covered by the formulas. I verified every cited hypothesis at its first application.

Against delivery-errors B-E: the new node is self-contained and statement-only; its one source tag has no existing duplicate; every search recorded was really run with msearch and the hits were read. In particular Mathlib Prorepresentability.lean:382-385 only makes endomorphisms of one fibre functor invertible, and Equivalence.lean:40-60 gives classification, not the new uniqueness statement. Both natural-language phrasings and Loogle returned no matching declaration. No new definition or hollow construction is introduced. All steps are below 1000 characters, so no non-elementary step exceeds the 2000-character threshold. The only substantial abstract lemma was extracted as 0BMV. The other steps explicitly calculate from cited definitions and statements, rather than hiding a comparison behind the word “transport”. All citation quotes were copied verbatim from the actual node statements. Off-unit tools are declared in split_report.tool_uses; definitions and Mathlib/closed nodes are generic notions/tools. No unit statement or realization is edited, and no other worker's node is edited.

## Unfinished work

The new 0BMV dependency remains unsplit as required for a one-level stage-1 delivery. No Lean was written and no compiler, Lake, or build command was run. Delivery validation is performed by the required server checks and dry run.
