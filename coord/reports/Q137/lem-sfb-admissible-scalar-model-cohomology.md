## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-admissible-scalar-model-cohomology.json`: statement, split; no Mathlib match for the whole result. Seven proof steps reuse existing nodes. Added the definition of Noetherian ring to statement dependencies; the statement is unchanged.
- `citations.json`: twenty verbatim cited-statement quotations, indexed by proof step.
- No new nodes and no new Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the item id, its blueprint tag, admissible scalar, scalar realization, constant-to-continuous and scalar-model cohomology. No declaration there gives the complete item. The existing Sheaf constant-to-continuous theorem supplies only a generic ingredient, already represented in the DAG.

## Wanted sources

None needed for this delivery: it follows the current blueprint local-model paragraph and existing stated tools. The existing local-field node records its own wanted Serre reference; this delivery does not create or reprove that node.

## Findings and corrections

The source's sentence about flat coefficient sheaves needs separate finite, integral and field arguments; a finite ring need not be a field, and integral perfect cohomology need not be projective. The split keeps these distinctions. The algebraic closure coefficient is the finite-subextension condensed ring of its definition, not the ring of all continuous functions without that condition. Flatness over its constant scalar field works for that module sheaf too.

The source of the existing finite-discrete condensed identification names Bhatt–Scholze Proposition 5.3.2. Reading that proposition in the PDF shows that its literal statement is instead the derived étale/pro-étale left-completion equivalence. I did not take a discrete-ring identification from that proposition: the cited existing node itself explicitly states the needed ring identification, and its direct finite-clopen-fibre argument establishes it. This inaccurate bibliographic place is reported here without editing another worker's node.

Mathlib search hits were read: `CondensedMod.LocallyConstant.functor` in `Mathlib/Condensed/Discrete/Module.lean` is for condensed modules over an ordinary scalar ring; its constant-sheaf comparison is not the extension to a non-discrete coefficient ring pulled back to a scheme. `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` at `Mathlib/Algebra/Category/ModuleCat/Descent.lean:42` is ordinary ring-module scalar extension and assumes flatness. Neither states the item. All new Q137 searches were run with msearch.py and are recorded verbatim with their actual results; both semantic phrasings gave related generic APIs, not this statement. Inherited searches have been retained unchanged.

## Unfinished work

None in the one-level split. The reused dependencies keep their own existing status. No Lean was written or compiled, and the repository was read only.

## Not duplicates

No new nodes were created. Whole-DAG statement searches and blueprint_refs searches found the generic tools already present; they are cited instead of duplicated. The item has no matching blueprint statement (`scalar realization`, `perfect cohomology`, `admissible scalar`, and constant-field searches). Its nearest blueprint ancestor is `det-prop-scalar-six-ctf`.

## Review by Q137

I read the chapter and unit records, GOAL.md, the three blueprint-level rules, the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-ctf.proof.md` paragraph (2), and the current detailed pullback-from-point definition and proof. The result is the local scalar-model cohomology claim of that paragraph; it does not replace any unit-level six-functor comparison. No new node needs a source review. I read delivery-errors B–E, including the duplicate merged copy, and checked the following actual applications against the complete cited statements.

Step 1 evaluates the continuous and finite-stage definitions at a singleton. The local-field theorem explicitly assumes finite degree over Q_l and a compatible absolute value; these are exactly the E in this item. It explicitly makes its ring of integers a PID. The PID Noetherian theorem then applies. Finite-ring and field Noetherianity are written as ideal arguments using the cited definition, rather than hidden in a new node. The zero finite ring is allowed.

Step 2 uses the condensed finite-discrete node for the ring-object isomorphism, and the scheme node only for transporting an already supplied monoidal ring identification; the latter's statement does not assert the point identification by itself. The constant-module functor node explicitly states additivity and exactness without finiteness. The tensor unit and its inverse are written in the step and work for arbitrary modules and the zero ring. Finite clopen fibres explain the identification, including the empty profinite set.

Step 3 uses the topological-PID flatness node exactly on O_E. Because its statement expresses internal extension-of-scalars flatness, I included the internal/section-module equivalence before using the ringed-topos flat-module pullback statement. The flat module is pulled back over the inverse image of the *constant* ring, not over the continuous coefficient ring itself. The constant-module inverse-image node identifies both the scalar ring and the action on constant scalars; the coefficient-pullback definition identifies the resulting module with Gamma_W. I checked that the point inverse image is the specified monoidal inverse image, not evaluation or a stalk. The standard sheaf categories on these small sites have the sheafification, local-bijectivity and closed tensor hypotheses required by the generic encoding bridge; universes are enlarged to contain both sites. No flatness of a further coefficient map or geometric finiteness hypothesis is used.

Step 4 cites the *sheaf* constant-field flatness theorem, whose statement covers every module sheaf over a constant field. This is stronger than the ordinary vector-space flatness theorem, which would not on its own prove the assertion for a sheaf. Apply it to Gamma_W as a module over the constant scalar field, for either E or Q_lbar. Its smallness/sheafification assumptions hold on the selected small pro-étale site in the containing coefficient universe. I did not identify this coefficient with a discrete constant field sheaf. In particular no completeness of Q_lbar is assumed.

Step 5 uses the realization definition for additivity and the realization exactness lemma only after its flatness hypothesis has been established. Both statements concern the same sheafified ordinary tensor after constant realization. The finite-ring case was already handled in step 2. Step 6 uses only the first clause of the Noetherian perfect-cohomology node, not its extra PID resolution clause. The complex is a bounded finite-projective representative by hypothesis and R is Noetherian by step 1, so every scalar cohomology module is finitely presented even if torsion. Step 7 cites the exact-functor theorem which explicitly gives a *natural* cohomology comparison induced on cycles and boundaries, rather than inferring naturality from unrelated degreewise isomorphisms. Its inputs are abelian module categories and the established additive exact functor. The local-model definition explicitly allows finitely presented scalar modules, so the identity cover and H^q(Q_0) prove the final clause. The zero module is finitely presented and gives the zero sheaf.

For small cases I checked the empty scheme, finite zero ring, zero complex, degrees outside the finite term interval, a finite non-field ring Z/ell^2, and the two-term integral complex [O_E --pi--> O_E]. In the last case the nonzero cohomology is O_E/pi, so demanding projective cohomology would have been false; this split demands only finite presentation. I checked that no proof step has more than 2000 characters (largest is 915), and no new node merely restates a clause of the item. All non-elementary facts are cited explicitly; every citation in citations.json copies the entire relevant statement verbatim. Off-unit statements are declared as generic tool uses with the mathematical purpose of each, rather than silently changing the route. No statement dispute or change was necessary.
