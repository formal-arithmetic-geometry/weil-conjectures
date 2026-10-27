# Stage-1 repair: Q40

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-invertible-finite-set-section.json`: existing statement unchanged; four-step assembly, two new dependencies.
- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-finite-point-scalar-separation.json`: statement, unsplit; no exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-invertible-section-fibre-correction.json`: statement, unsplit; no exact Mathlib match.
- `citations.json`: one verbatim statement quotation for each proof-step citation.

## Attachments

None. The project search by blueprint tag and concept found no finished declaration of the item in WeilConjectures. `lean/Sheaf/AlgebraicGeometry/AffineInvertibleFiniteSetSection.lean:62` states it exactly with arbitrary finite E, but its proof at line 70 is `sorry`. No Lean was written and no compiler or Lake command was run.

## WANTED

None. The sources needed here are present.

## What was wrong and the requested repair

The returned head's proof has six steps totalling 3627 characters. The return requests at least two comparable independent statement-only nodes, rather than a shortened rendition of the same argument. The sandbox actually contained only dispatcher dotfiles at the start, without nodes, report or search log; I copied the current read-only repository item and preserved all of its metadata, statement, source and recorded searches. The current repository version supplies the returned six-step proof verbatim. There was no retained divergent sandbox branch to rebase. The required delivery tool builds on the current server head and preserves maintainer fields.

The scalar-separation node carries old steps 1 and 5 (1560 characters): the affine coordinate and stalk dictionary, scalar residue criterion, specialization/prime-inclusion check, choices of a_x, finite product, and its two residue conclusions. The fibre-correction node carries old step 2, the correction data in step 4, and step 6 (1474 characters): affine global generation, one section nonzero at z, zero/nonzero residue arithmetic and preservation of the old fibre values. These are separate arguments with different inputs. The correction takes an already supplied f and s, permits arbitrary F and says nothing about constructing f or avoiding an arbitrary finite E; the separator concerns only scalar functions and has no line bundle. Neither restates the item. Old step 3 (593 characters) remains the parent's finite-set induction and comparable-points branch. Empty F, the early return when s(z) is nonzero, and the zero initial section are retained explicitly.

The extracted arguments are comparable in size. Both nodes are deliberately unsplit, with empty proof and proof_deps and null proof_origin, to allow other workers to split them independently. In particular the correction node includes the affine existence of a nonzero section in one fibre, not just the elementary formula s+ft. The detailed retained proof below supplies all old arguments without concealing them in a shorter summary.

## Sources and searches

Read Stacks Properties Tag 0F20, `properties-lemma-quasi-affine-invertible-nonvanishing-section`, properties.tex 5327–5383: base case global generation; induction removes a generalization; the remaining case adds a section zero at the earlier points. The affine product construction is the retained explicit version of this step. Read Schemes Tag 01HV, `schemes-lemma-spec-sheaves`, especially clauses (1),(6),(7), and Tag 01IB, `schemes-lemma-equivalence-quasi-coherent`. Read Modules Tag 01CY, `modules-lemma-s-open`, and Divisors Tag 0BUT, `divisors-lemma-finite-trivialize-invertible-upstairs`, for how the finite-fibre assertion is used.

DAG search by 0F20 and statement concepts, whole-blueprint searches via blueprint_refs.py for 0F20, nonvanishing, nonvanishing-section, separating, finite-set and correction, and project searches found no replacement for either extracted assertion. The inherited nearest blueprint ancestor is null, as blueprint_refs.py ancestor reports; the inherited place and via chain are retained, and the new nodes prepend the current item to that chain. This is an auxiliary algebraic geometry input beneath the fixed six-functor unit, not a different unit route. No SGA source was used.

All new-node Mathlib queries were run with msearch.py and read, including second semantic phrasings. The actual records are in searches.jsonl and copied by exact tool/query text to each new node. Read `AlgebraicGeometry.Scheme.evaluation_eq_zero_iff_notMem_basicOpen` and `evaluation_ne_zero_iff_mem_basicOpen` at Mathlib/AlgebraicGeometry/ResidueField.lean:107,111: these are criteria for a given scalar, not its existence with finitely many zero constraints. Read `Ideal.IsPrime.prod_mem_iff` and `Ideal.IsPrime.inf_le'` at Mathlib/RingTheory/Ideal/Operations.lean:1028,1038: these give algebraic ingredients but not the scheme statement without spectrum, specialization and residue identifications. Read Module.Invertible.exists_finset_free_localization at PicardGroup.lean:380 and exists_linearEquiv_ideal at :901: local freeness and ideal representation do not give the correction for an arbitrary invertible sheaf. The local tilde fraction descriptions in the second search do not give the global correction either. No match was promoted without statement agreement.

## Not duplicates

lem-sfb-affine-finite-point-scalar-separation vs lem-sfb-affine-invertible-finite-set-section: the new lemma prescribes zeros on F and a nonzero scalar value at z outside all closures; the item asserts only a line-bundle section nonzero on a finite set. Neither the item nor a clause of it gives these vanishing constraints.
lem-sfb-affine-invertible-section-fibre-correction vs lem-sfb-affine-invertible-finite-set-section: the new lemma takes already chosen s and f, preserves every old residue value and requires s(z)=0 and f(z) nonzero; it is a one-point correction and does not construct the scalar or perform the finite-set induction.
lem-sfb-affine-finite-point-scalar-separation vs lem-sfb-affine-invertible-section-fibre-correction: the separator constructs the scalar; the correction takes that scalar as input and constructs a line-bundle section. They have distinct hypotheses and conclusions and can be proved independently.

## Review by Q40

I read the old proof against the full induction in 0F20, and checked the two extracted statements against the exact arguments allocated to them above. The new separator assumes exactly the one-sided specialization exclusion used to choose a_x in p_x minus p_z; it requires no pairwise incomparability inside F. The new correction assumes f is supplied and uses affineness only for global generation. It requires neither finiteness nor closedness of F. The zero value of s at z and the nonzero scalar f(z) suffice for its conclusion. Taking the product over an empty set is 1.

For the parent's step 1 I checked strong induction is on all smaller finite subsets with X,L fixed, so both removals qualify; the empty case uses 0. Step 2 cites only lem-weil-pbc-nonvanishing-section-trivializes. I opened it and read the clause saying Y_s is open with precisely the residue-nonzero definition; an open containing the specialization y contains its generalization x, in the required direction. Step 3 cites the new scalar-separation statement: F is finite and no x in F specializes to z, which is exactly z not in closure{x}. Step 4 cites the correction statement: X is affine, L invertible, s(z)=0, f vanishes on F and f(z) is nonzero, so every hypothesis is present. Its residue equality v(x)=s(x), together with induction, proves all the earlier nonvanishings; its other conclusion supplies z. citations.json quotes those actual statements, not their proofs.

I also reopened every node used by the retained arguments: def-weil-affine-spectrum gives the spectrum/global-ring dictionary; lem-weil-pbc-affine-open-stalk-localization clause (c), with U=X, identifies the scalar germ with localization; def-sc-invertible-module explicitly includes quasi-coherence; lem-weil-pbc-affine-algebra-module-generators applies to the identity O_X-algebra and M=L on U=X and says global generating sections exist; lem-sc-global-generation-nonvanishing-cover says these sections cover X by their nonzero residue loci. Thus the proposed correction proof does not assume a global trivialization. These facts now belong to the work assigned to the unsplit children, rather than uncited hidden facts in the parent. Only the openness tool remains directly cited from another unit; its existing accepted generic-tool status is respected.

I tested E empty and X empty (including the zero ring), a singleton, comparable generic/closed points in a DVR, two disconnected affine points, nonclosed incomparable primes in k[u,v], finite residue fields, nonreduced rings, and invertible modules not globally free. In the DVR case, for F containing the closed point and z the generic point, a uniformizer separates them; reversing their roles violates the separator's explicit hypothesis, as it must. If z belongs to F the correction hypotheses on f are inconsistent, so no impossible conclusion is asserted. Over finite residue fields no generic-linear-combination argument is used: nonzero scalar multiplication is invertible even over F_2. Nilpotents cause no problem because residues and prime containment are what enter. No statement dispute or hypothesis change was needed.

I checked delivery-errors B–E: the children have self-contained TeX statements, cited defining notions, exact Stacks tag/label sources, genuine logged searches, no proof sketches or steps, valid ancestry and no closed Lean attachment. Every parent step uses only the precise statement cited, with all inputs checked above. The new statements do not depend on the parent and introduce no cycle; neither duplicates a clause of it. No non-elementary parent step exceeds 2000 characters and the total assembly is below 3000. This repairs the numbered return by spreading two full arguments, rather than deleting work. The full old proof is retained below as a handoff of the extracted arguments.

## Retained returned-head proof and exact allocation

### Old step 1: lem-sfb-affine-finite-point-scalar-separation

Put $A=\Gamma(X,\mathcal O_X)$ and identify the affine scheme $X$ with $\operatorname{Spec}A$ [def-weil-affine-spectrum]. Write $\mathfrak p_x$ for the prime corresponding to $x$. The affine stalk-localization statement [lem-weil-pbc-affine-open-stalk-localization], applied with $U=X$, identifies the germ map with $A\to A_{\mathfrak p_x}$. Thus for $a\in A$ its residue $a(x)$ is nonzero exactly when $a\notin\mathfrak p_x$. Explicitly, $a\notin\mathfrak p_x$ gives a unit germ. Conversely, if $a\in\mathfrak p_x$ and its germ were a unit, represent an inverse as $b/c$ with $c\notin\mathfrak p_x$. Equality $ab/c=1$ gives $u(ab-c)=0$ for some $u\notin\mathfrak p_x$, forcing $uc=uab\in\mathfrak p_x$, a contradiction. In a local ring, zero residue is exactly membership in its maximal ideal, equivalently failure to be a unit.

Uses: def-weil-affine-spectrum, lem-weil-pbc-affine-open-stalk-localization. Source: literature/stacks-project/schemes.tex, Tag 01HV, lemma-spec-sheaves (1),(6); affine coordinate preparation for Properties 0F20.

### Old step 2: lem-sfb-affine-invertible-section-fibre-correction

The sheaf $L$ is quasi-coherent by [def-sc-invertible-module]. Apply [lem-weil-pbc-affine-algebra-module-generators] with $S=X$, the algebra sheaf $\mathcal A=\mathcal O_X$ with its identity structure map, the affine open $U=X$, and $M=L$. Restriction of scalars is the identity, so its quasi-coherence hypothesis holds, and $L$ is generated by global sections. Now [lem-sc-global-generation-nonvanishing-cover] gives $X=\bigcup_t X_t$, where $X_t=\{x:t(x)\ne0\}$. Consequently for every point $x$ there is a global section $t$ with $t(x)\ne0$. Here $t(x)$ denotes the class of $t_x$ in $L_x/\mathfrak m_xL_x$.

Uses: def-sc-invertible-module, lem-weil-pbc-affine-algebra-module-generators, lem-sc-global-generation-nonvanishing-cover. Source: literature/stacks-project/properties.tex, Tag 0F20, lemma-quasi-affine-invertible-nonvanishing-section, base case: global generation; in the affine case use Schemes 01IB, lemma-equivalence-quasi-coherent.

### Old step 3: parent induction

Prove the assertion for every finite subset $E$ by strong induction on $|E|$. For $E=\varnothing$ take $s=0$. Each nonvanishing locus $X_s$ is open by [lem-weil-pbc-nonvanishing-section-trivializes]. If distinct $x,y\in E$ satisfy $x\leadsto y$, apply the induction hypothesis to $E\setminus\{x\}$. Its section is nonzero at $y$; every open containing $y$ contains its generalization $x$, by the definition of specialization, so the section is also nonzero at $x$. This handles any pair of comparable points. It remains to handle a nonempty $E$ with no specializations between distinct points.

Uses: lem-weil-pbc-nonvanishing-section-trivializes. Source: literature/stacks-project/properties.tex, Tag 0F20, lemma-quasi-affine-invertible-nonvanishing-section, empty case and induction step removing a generalization; Modules 01CY supplies openness.

### Old step 4: lem-sfb-affine-invertible-section-fibre-correction (data selection stays in the parent)

Choose $z\in E$ and put $F=E\setminus\{z\}$. By induction there is $s\in\Gamma(X,L)$ nonzero at all points of $F$. If $s(z)\ne0$ we are done. Otherwise $s(z)=0$. By step 2 choose $t\in\Gamma(X,L)$ with $t(z)\ne0$. In the case $F=\varnothing$, this already proves the assertion; the same construction below also works with its empty product equal to $1$.

Uses: elementary. Source: literature/stacks-project/properties.tex, Tag 0F20, lemma-quasi-affine-invertible-nonvanishing-section, induction step: the old section and a section nonvanishing at the new point.

### Old step 5: lem-sfb-affine-finite-point-scalar-separation

For each $x\in F$ we have $\mathfrak p_x\not\subseteq\mathfrak p_z$: inclusion would imply $x\leadsto z$. Indeed the Zariski closed sets are $V(I)=\{\mathfrak q:I\subseteq\mathfrak q\}$, so any closed set containing $\mathfrak p_x$ also contains every prime above it. Choose $a_x\in\mathfrak p_x\setminus\mathfrak p_z$ and let $f=\prod_{x\in F}a_x\in A$. For each $x\in F$, one factor lies in $\mathfrak p_x$, hence $f\in\mathfrak p_x$. Every factor is outside the prime $\mathfrak p_z$, hence $f\notin\mathfrak p_z$. The scalar-residue criterion in step 1 therefore gives $f(x)=0$ for $x\in F$ and $f(z)\ne0$. This is the affine separating-function construction in the induction of the source, written directly using prime ideals.

Uses: def-weil-affine-spectrum. Source: literature/stacks-project/properties.tex, Tag 0F20, lemma-quasi-affine-invertible-nonvanishing-section, induction step: choose a section supported away from the closures of the earlier points; the affine separating scalar is the explicit product above.

### Old step 6: lem-sfb-affine-invertible-section-fibre-correction

Set $v=s+ft\in\Gamma(X,L)$. Taking germs and then quotienting by the maximal ideal commutes with addition and scalar multiplication, so $v(x)=s(x)+f(x)t(x)$. For $x\in F$ this is $s(x)\ne0$. At $z$ it is $f(z)t(z)\ne0$: multiplication by a nonzero element of the field $\kappa(z)$ is invertible on the vector space $L_z/\mathfrak m_zL_z$. Thus $v$ is nonzero at every point of $E$. This completes the induction, including arbitrary nonclosed points, and proves precisely the asserted residue-fibre nonvanishing.

Uses: elementary. Source: literature/stacks-project/properties.tex, Tag 0F20, lemma-quasi-affine-invertible-nonvanishing-section, final addition of sections.

## Unfinished work

No part of this stage-1 repair remains unfinished. The two new statements are intentionally unsplit work items; no Lean proof is claimed. Validation and delivery results are recorded after the required tool finishes.
