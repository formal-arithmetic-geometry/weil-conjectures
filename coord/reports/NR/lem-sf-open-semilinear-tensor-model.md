# Stage-1 report: lem-sf-open-semilinear-tensor-model

## Files written

- dag/nodes/sec-six-functors/lem-sf-open-semilinear-tensor-model.json: statement, split; seven proof steps. Mathlib: no match after two semantic phrasings, Loogle, LeanSearch and source grep, recorded from searches.jsonl.
- citations.json: verbatim cited statements for every step/node pair.
- report.md: this report.

No new DAG nodes and no Mathlib leaves. Only sandbox files were written. No Lean, compiler, Lake, repository git command, or other agent was used.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, semilinear systems, extensionByZero, jShriek and KFlat did not find a project declaration stating all the clauses. Existing finite-coefficient or etale open-extension declarations do not state the varying-ring simultaneous comparison, so are not attachments.

## WANTED

None. The Stacks source and the relevant blueprint proof are available locally. The live node's main-20261017 blueprint path is not installed under that spelling; I read the corresponding main-20261015/sk-thm-sf-package/fix-prop-coherence.proof.md and the live unit and ancestor node records. Their tensor/evaluation/adjunction route is the same route used here.

## Audit of the item and route

The imported item is true as stated, and its statement and statement dependencies are unchanged. Its proof was empty. Its completeness and normalization terminology merely fixes context; the construction itself never uses completeness, normalized inputs, or quasi-compactness. It is important that the comparison lives over B_n, with semilinear transitions, before restriction to the completed ring. I did not substitute the scalar-restricted constant-tower comparison for that stronger assertion.

I read Stacks sites-modules.tex Tag 0E8I (lemma-j-shriek-and-tensor), including the five adjunction/Hom equivalences, and sites-cohomology.tex Tag 0GL1 (lemma-j-shriek-and-tensor). The latter leaves chain-level details omitted. I supplied those details and the coefficient squares as an agent refinement, recorded with proof_origin.by=agent. I also read the extension-presheaf adjunction in sites-modules.tex (lemma-extension-by-zero) and the tensor/sheafification construction around Tag 0GMW (lemma-sheafification-tensor), and the K-flat localization passage, Tags 06YS, 06YT, 06YU and 0G7D. No SGA source is used.

The blueprint ancestor search gives fix-prop-coherence. The existing from.place already identifies its sentence about tensor reassociation, evaluation, units and counits, through the integral open reduction and compactification realization nodes. I retained it. Whole-blueprint searches for open tensor, tensor comparison, semilinear, and extension by zero found no blueprint node stating this simultaneous representative assertion; same_as stays empty. The chapter and sk-thm-sf-compatibility route are respected. This item is not the unit statement, so no unit realization fields were changed.

## Not duplicates

No new nodes were created. In particular, lem-sf-ringed-open-total-tensor-kflat already supplies the generic K-flat preservation theorem, and lem-weil-pbc-ringed-slice-extension-tensor already states the ordinary isomorphism. The former is cited as a generic tool; the generator formula and its inverse are written out instead of assuming the latter's existence statement specifies them. lem-cbc-ringed-open-strict-reduction concerns a scalar-restricted adic tower; I did not create another such node or cite it for the before-restriction semilinear claim. The etale open-tensor nodes use a different site/coefficient setting and are not used for arbitrary completed ring sheaves on the pro-etale site.

## Review by NR

I reviewed the seven steps against delivery-errors B through E with the source and cited statements open. The source for the item is 0E8I/0GL1; there are no new node sources to check. The proof does not push a clause into a new node, and each step is shorter than 2000 characters.

Step 1 uses the site-localization theorem exactly for its equivalence with the slice, and the extension-presheaf definition exactly for its summands and restrictions. The two bilinear-sheafification statements explicitly give existence and uniqueness for presheaf pairings into a sheaf. Their hypotheses hold with O already a commutative ring sheaf, P_G a presheaf, and H a sheaf regarded as a presheaf. Balancing uses the equality O_U(V,f)=O(V), not flatness of a coefficient map. The tensor definition identifies the sheafified tensor. This constructs the actual map on generators rather than using a derived isomorphism as an underived construction.

Step 2 uses the exact slice adjunction and the ordinary restriction/tensor theorem. The latter explicitly gives the pure-tensor formula on every slice object. I expanded the adjunction explicitly: sum the component map over P_G(V) and sheafify, with inverse restriction to each summand. This sends x to its own extension summand; transposing the indicated pairing therefore gives [x tensor a] mapping to [x] tensor a. I checked both inverse identities: the first is checked on original extension-presheaf/tensor generators using uniqueness of bilinear extension; for the second the adjunction reduces the equality to the unit map out of G tensor j^*H. This avoids treating an unspecified natural isomorphism as generator normalized.

Step 3 uses the left-adjoint colimit theorem with the small discrete index {(a,b) in Z^2 : a+b=d}. It gives exactly the canonical direct-sum comparison needed here. The total tensor definition supplies the two differential components and the sign (-1)^a. Both functors are additive, so the sign is unchanged. I checked separately the d_Q and d_F terms and then their sum; there is no convergence argument or infinite sum into one fixed summand.

Step 4 invokes the flatness definition as exactness of tensor, and exact restriction and extension from the slice-adjunction theorem. Thus flat terms follow from a composite of three exact functors. The existing generic total-tensor/K-flat theorem explicitly allows an arbitrary commutative ring sheaf, unbounded complexes and a K-flat resolution, exactly our hypotheses. Its statement, not a construction hidden in its proof, gives K-flat preservation and preservation of the representative quasi-isomorphism. Its off-unit use is declared in split_report.tool_uses along with the other generic tools.

Step 5 is elementary from the maps already constructed: I computed B_n-linearity, both quotient-transition paths, chain-map naturality and both scalar-unit augmentation paths. Restriction commutes with the quotient ring maps and preserves 1. The semilinear-sections node states componentwise exactness and the ordinary system category, so a commuting component family is genuinely a system morphism. Commuting inverses follow by multiplying the squares by the component inverses. This step never infers equality from evaluations of derived maps.

Step 6 uses the reduction-evaluation calculus for exactly its asserted computation on one flat-term K-flat representative, the semilinear-sections statement for exact termwise open extension, the tensor-descent statement for the equivalence from localized flat-term K-flat complexes, and the localization universal property for natural-transformation descent and uniqueness. I checked the coefficient categories on both model functors: both land in D(S_X). Step 4 supplies the permitted representative for the source. Thus change of representative and arbitrary derived morphisms are handled by localization, not by choosing unrelated levelwise arrows.

Step 7 uses precisely the inverse-transpose characterization in open-tensor-normalization. The inverse constructed in step 2 has that characterization, hence its localization is the canonical derived map. The semilinear-sections statement specifies actual system constructions on ordinary derived categories, exact open extension, tensor and evaluation; these are the same constructions used before localization here. All squares are proved there before passing to coefficients or evaluating. I checked that no claim of faithfulness of derived evaluation enters.

I tested j equal to the identity (the formula is the tensor identity), U empty (both sides are zero), Q=0, degree-zero Q and F (the ordinary map), negative and odd degree a (the same sign occurs on both sides), unbounded Q and F (only two outgoing differential terms per summand), n=m (identity quotient), and m>n>r (both coefficient paths apply the same composite quotient). Non-flat B_m to B_n is allowed because the strict representative squares use ordinary coefficient maps and the source K-flat representative computes derived reduction. I also checked arbitrary nonconstant O, so no stalk-flatness or constant-ring shortcut was used. No statement correction was necessary.

## Unfinished work

None in this stage-1 split. The statement-only dependencies already in the DAG remain work for their own items.
