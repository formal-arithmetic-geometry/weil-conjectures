# Stage-1 delivery: lem-sfb-triangular-quotient-section-conjugacy

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-triangular-quotient-section-conjugacy.json — statement item, now split; unchanged statement and statement dependencies; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-diagonal-additive-crossed-vanishing.json — one new statement-only, unsplit lemma; no Mathlib match.
- citations.json — one verbatim statement extract for every node citation in every proof step.

One new node, zero Mathlib leaves. Searches are recorded verbatim from the commands in searches.jsonl; all four services answered. The existing item's searches are retained and the new item searches appended.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint id and for triangular group sections, trigonalizable groups and conjugacy found no declaration stating the item. GroupScheme/GeneralLinear/ClosedSubgroup.lean has general matrix-group constructions, not this conjugacy theorem. Mathlib's GroupExtension.IsConj (Defs.lean:317) defines the desired relation and Basic.lean:188--200 proves its equivalence-relation properties; none supplies the existence theorem. Its conjAct is an action construction, not vanishing of crossed homomorphisms. Thus these are not attachments or Mathlib leaves.

## WANTED

None. The entire argument uses the available Milne Algebraic Groups PDF and existing DAG statements. No SGA source was used.

## Source error already repaired in the live statement

The live item already assumes that D is smooth, faithfully following Milne Summary 16.29(b), printed p.334. Its statement is preserved without any further correction. Milne Theorem 16.27(a), p.333, omits that assumption in the stated generality. Over an algebraically closed field F of characteristic p, consider J inside B_2 consisting on every algebra of matrices [[t,x],[0,1]] with t^p=1 and x^p=0. Then V=alpha_p and D=mu_p. The two homomorphism sections are t -> [[t,0],[0,1]] and t -> [[t,1-t],[0,1]], since 1-tu=(1-t)+t(1-u). They are distinct as scheme morphisms, whereas V(F)=0. They cannot be conjugate by a kernel rational point. The existing smoothness assumption excludes this example. This is a warning about the cited theorem's scope, not a dispute of the current item.

## Not duplicates

lem-sfb-smooth-diagonal-additive-crossed-vanishing vs lem-sfb-additive-subgroup-diagonalizable-extension-splitting: the existing statement produces one section of an extension, with D allowed nonsmooth; the new statement says that every regular scalar crossed homomorphism into a closed additive subgroup is principal when D is smooth. Splitting an extension does not imply conjugacy of its sections, as the preceding alpha_p-by-mu_p example shows. The new node is the one-dimensional commutative coefficient input, not the original noncommutative triangular-group assertion or a clause renamed as a lemma.

I searched the entire DAG for crossed homomorphisms, principal cocycles, diagonalizable groups, the relevant Milne places and additive-subgroup lemmas; the existing coordinate filtration, homomorphism factorization and closed-torus-subgroup nodes were reused. Whole-blueprint searches with tools/blueprint_refs.py for crossed, crossed homomorphism, conjugacy sections, trigonalizable, unitriangular, diagonalizable and additive subgroup found no equivalent blueprint statement. The ancestor command reports blueprint.from.node=None for the inherited lineage. I retained that value and extended its exact via list and supporting place for the new node. The current latest blueprint's ctf-stability unit, direct-images proof (3), and chapter were read; the inherited supporting algebraic-group route is unchanged, and no chapter/unit file was edited.

## Review by Q14

I read Milne Theorem 16.21 and its coordinate-filtration proof on printed p.330, the proof of Theorem 16.27(a) on p.333, and Summary 16.29 on p.334 for the item. I read Proposition 15.3 and its prime-to-characteristic torsion averaging proof on p.303 for the new additive crossed-homomorphism node, along with Example 15.1 on pp.302--303. The new node extends the proposition from a commutative unipotent group variety to a possibly nonsmooth closed additive subgroup N in exactly the situation where smooth D makes this legitimate: D is reduced, so f factors through N_red; over the algebraically closed (hence perfect) field N_red is a smooth commutative unipotent group. The scalar action restricts to N_red because D times N_red is reduced. Apply 15.3 to this action, and negate its principal element to get our sign a-chi(d)a. Since N_red(F)=N(F), the resulting element has exactly the required membership. This argument is source material for the future split of the statement-only node, not a proof embedded in its statement.

For step 1 I opened lem-sfb-algebraic-group-homomorphism-factorization: its statement really gives the represented fppf quotient by the scheme-theoretic kernel, a closed image and a faithfully flat finitely presented factor. I checked the kernel of the diagonal map is V on all algebras. I also opened lem-sfb-split-torus-subgroups-diagonalizable, which explicitly identifies any closed subgroup of the split torus with Spec F[M]. The base is algebraically closed as required. We identify its image with the given D by the representing property; no unproved assertion about only rational points is used.

For step 2 I opened lem-sfb-unitriangular-coordinate-filtration. It states the exact ordering of coordinates, normality under B_n, the scheme-theoretic kernels, and the scalar conjugation formula used in our proof. I checked its restriction to J and its intersections V_r. Applying the factorization node to each restricted coordinate map supplies N_r and its quotient map; it does not assume that restriction is onto all of G_a. The scalar action on the closed image is checked after locally lifting its points, with the defining-equation descent argument written out. Thus N_r may be finite, infinitesimal, disconnected, or trivial.

For step 3 I read lem-weil-pbc-closed-point-residue-field-base. It says a closed point of any scheme locally of finite type over an algebraically closed field has that field as residue field. The quotient factorization gives nonempty fibres, and the displayed affine coordinate quotient proves these fibres are finite type before this lemma is applied. Selecting a maximal ideal of their nonzero coordinate ring gives the needed closed point. No smoothness, separability of the quotient kernel or surjectivity on rational points is silently assumed. This generic residue-field tool is declared in split_report.tool_uses because it is off-unit.

Step 4 cites no external result: substituting h=c s_1 into h(dd') and cancelling s_1(dd') writes the full cocycle identity as a natural identity on every algebra. The factorization through V is its defining kernel equation.

For step 5 I checked the new lemma's statement line by line against its use. D is smooth by hypothesis and diagonalizable by step 1; N_r is the actual closed additive image and scalar stable by step 2; f_r is a morphism, with its crossed identity deduced using the cited filtration's exact conjugation formula. Its conclusion gives an element a in N_r(F), not merely an ambient additive scalar. Step 3 lifts it to v in V_{r-1}(F). I checked the sign: conjugating h by v^{-1} changes its additive defect to -a+f_r+chi(d)a=0. The product order w_r=w_{r-1}v is correct. This explicitly gives both the induction hypothesis and its base and step; no nonabelian H^1 vanishing is cited without proof. Step 6 then terminates at V_m=1 and reverses this conjugation to get exactly s_2=Int(w_m)s_1.

I tested n=1, V=1, D=1, repeated filtration terms N_r=0, positive characteristic infinitesimal N_r=alpha_p, and smooth disconnected diagonal quotients such as mu_l with l prime to the characteristic. None requires J or V to be smooth or connected. In the infinitesimal additive case a morphism from smooth D factors through the trivial reduction, consistent with the new lemma. I separately checked that removing smoothness on D fails by the explicit counterexample above.

Against delivery-errors B--E, the new node introduces all its own objects, cites their actual definitions, contains no proof or proof dependencies, has logged searches in two phrasings, and is strictly smaller than the item. I read the returned Mathlib hits in LowDegree.lean:489--540 and Hilbert90.lean:84--95: the former defines abstract cocycles and coboundaries, while the latter proves a theorem for Galois actions on field units, so neither is a match for the new algebraic-group statement. Each proof citation has a verbatim statement extract in citations.json. No proof step exceeds 2000 characters; none hides a further comparison lemma. All unchanged metadata from the item is retained. No Lean, build, compiler, repository write or unapproved source was used.

## Unfinished work

The new statement-only node is intentionally left unsplit, as required by a one-level stage-1 delivery. No part of the item's natural-language proof remains unfinished. Required server dry run and direct push are performed with the delivery tool after this report.
