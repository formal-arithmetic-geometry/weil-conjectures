## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-strict-perfect-local-null-homotopy.json` (statement, split; no Mathlib match), this report, and `citations.json` in the sandbox. The statement and its three statement dependencies are unchanged. The item now has five proof steps and eight distinct proof dependencies. No Lean was written and no compiler was run.

## New nodes

None. There are zero new nodes and zero new Mathlib leaves. In particular, no new copy of Stacks 08FN is needed: the finite-generator lifting argument is two lines of construction from the existing general-site abelian epimorphism criterion. Existing finite-free lifting nodes were also examined, but their more explicit Lean sheafification instances are unnecessary here.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, strictly-perfect terminology, and local/null-homotopy terminology. The AbelianHigherDirectImageFunctorComparison docstring concerns a particular abelian higher-direct-image comparison, and LocalizedHomComplexBoundaries identifies already existing boundaries with homotopies; neither states this result for arbitrary ringed sites, finite-free retract terms and an upper-acyclic, possibly unbounded target. The project's sorry declarations are not attachments.

## Literature and searches

WANTED: none.

Read `literature/stacks-project/sites-cohomology.tex`, definition-strictly-perfect (08FL), lemma-local-lift-map (08FN), and lemma-local-homotopy (08FP), including its proof. The item is exactly assertion (2) with the explicit homotopy equations. Read the abelian epimorphism/local-surjectivity equivalence at sites-modules.tex, lemma-abelian-abelian (03CN)(5), and exact forgetting at lemma-abelian (03DA). Read localization of ringed sites, including the sectionwise restriction rule. The proof expands the finite-support induction using residual cycle maps rather than invoking the homotopy-category exact Hom sequence. Thus the required lifts and their signs are visible in the item itself.

Read the DAG chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md`, `sk-thm-sf-ctf-stability/_section.md`, and the direct-images proof there. This is an auxiliary ringed-site local-homotopy tool in the existing ancestry of direct-images proof (3), not a replacement of the chapter or unit argument. The inherited `blueprint.from.place` is already specific and is retained. Its `from.node` is null; `tools/blueprint_refs.py ancestor` reports None. That ancestry metadata was not rewritten. The server review_split check accepts the split.

Searched the whole DAG for 08FN, 08FP, lemma-local-lift-map, local lifting, and null-homotopy, and searched all imported blueprint nodes with blueprint_refs.py for finite free, projective lift, local homotopy, homotopic to zero, and null-homotopy. In particular, lem-weil-pbc-finite-free-etale-acyclic-homotopy concerns termwise constant finite-free coefficients on the small etale site and a wholly acyclic target, so it does not state this item. The finite-free/retract local lifting nodes in sec-six-functors are existing inputs, not reasons to create another node.

Ran the required msearch command with LeanFinder twice (different phrasings), LeanSearch, Loogle, and grep; all returned successfully. Read the KProjective.lean declarations suggested by the searches, including IsKProjective.homotopyZero and isKProjective_of_projective, and their hypotheses. A finite free sheaf need not be a projective object of the global sheaf category, and partial cohomology vanishing is weaker than acyclicity. Homotopy.nullHomotopy only packages a supplied family. These hits therefore do not give the local existence claimed by the item. The original search records were retained and the newly executed exact queries/results were appended to mathlib_searches; searches.jsonl records this session's calls.

## Problems and unfinished work

The imported item had no proof. No statement error or source error was found, and no hypotheses or conclusions were changed. The proof remains valid without boundedness of K. All mathematical stage-1 work is complete; the dry run and push are the remaining delivery operations. Maintainer-owned records and the repository were not edited.

## Review by Q32

I checked 08FP(2) against every hypothesis of the item: a general ringed site, a slice over U, integer indices, finite support and finite-free direct summands for P, P zero below a, and H^j(K)=0 only for j at least a. No assumption that K is bounded, that the ring sheaf is constant, or that the site has points is used. 08FL is precisely the stated strictly-perfect convention.

Step 1 uses the statement of lem-pur-site-restriction-module-adjunction-exact that restriction is exact, not its extension-by-zero construction. Together with the kernel/image quotient definition in def-weil-abstract-derived-category this preserves the needed cohomology vanishing. def-pur-localized-ringed-site explicitly states sectionwise restriction and relocalization, so finite free modules, retract equations and the successive slice identifications really persist. The preservation of H is just kernels and cokernels under an exact functor, written in the step.

Step 2 uses the actual complex and chain-map definitions in def-weil-abstract-derived-category and the sectionwise kernels in def-weil-sheaf-of-modules-category. I checked the residual calculation d_K(w-hd_P)=0: the next homotopy identity supplies the factor h^{n+2}d_P^{n+1}, and d_P^{n+1}d_P^n=0 kills it. The base has h^{b+1}=0 because P is zero above b. This is an explicit finite induction, not an assumption of a homotopy.

Step 3 uses exactly H^n=ker(d^n)/im(d^{n-1}) from def-weil-abstract-derived-category to obtain the epimorphism onto cycles. Clause (1) of lem-weil-pbc-module-sheaves-colimits-forgetful explicitly preserves cokernels, hence sends that epimorphism to an epimorphism of abelian sheaves. I checked its sheafification hypothesis: ordinary abelian sheaves on the small sites and their slices have the sheafification of def-weil-pbc-sheafification, whose listed value categories include abelian groups. The precise quantified statement of lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective supplies lifts over covering families on every object; it is not merely a definition of epimorphism and it is not restricted to etale sites. This is the only section-lifting theorem used.

Step 4 is the finite-free/retract assembly of those section lifts, not an additional hidden lifting lemma. I checked qi=1 and p_n(si)=r^nqi=r^n. The formula s_W((c_l))=sum c_l(y_l|_W) is linear and natural by the module-sheaf definition, so independently chosen lifts on one covering member do give a sheaf morphism on that member; they need not agree on different members. The site definition explicitly supplies covering pullbacks and composition, so finitely many generator covers have a common covering refinement. The elementary flag covers only this finite assembly, not the local-surjectivity assertion of Step 3.

Step 5 composes a finite number of covering families using the same site axioms. I checked all boundary degrees: below a both terms vanish because the source term is zero, including h^a d_P^{a-1}; above b the chosen components vanish. At the last stage only H^a(K)=0 is used, although h^a takes values in K^{a-1}; there is no assumption about H^{a-1}(K). The zero source and rank-zero retract use the identity cover and zero homotopy. Also checked a single nonzero source degree, gaps in the support, the zero ring, and sites admitting an empty covering; no existence of a point or a global section lift is assumed. Only finitely many target degrees are inspected even if K is unbounded on both sides.

For the B--E audit, there are no new statement-only nodes, duplicate nodes, Mathlib leaves to identify, or renamed clauses of the item. All non-elementary inputs are existing cited statements opened during this review; citations.json has a verbatim supporting quote for every uses entry. The local-ringed-site, general-abelian-epi and exact-forgetful inputs have the right categories and hypotheses. The proof never uses the proof body of another node. Every step is shorter than 2000 characters. No SGA source is used. The exact forgetful functor is declared as a generic tool use in split_report; it is also already Lean-closed. No correction to the mathematical statement was needed during self-review.
