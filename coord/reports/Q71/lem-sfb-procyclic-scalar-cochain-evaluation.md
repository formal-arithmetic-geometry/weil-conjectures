## Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-procyclic-scalar-cochain-evaluation.json` keeps its statement verbatim and replaces nine proof steps (6972 characters) by five assembly steps (2443 characters). Three new statement-only nodes, all status `unsplit`, with empty proof and proof dependencies:
   - `lem-sfb-continuous-procyclic-low-degree-evaluation`: continuous face/sheaf construction, natural generator evaluation and dense-integer low-degree calculation for any norm field over Q_ell; Mathlib search: no full match.
   - `lem-sfb-banach-translation-difference-split`: Banach translation action, constant kernel, Mahler shift and continuously split difference sequence; Mathlib search: no full match (existing Mahler-coordinate leaf reused in its statement).
   - `lem-sfb-compact-open-coinduced-contraction`: compact-open homogeneous evaluation coordinates and an augmented contracting homotopy, including its derived isomorphism; Mathlib search: no full match.
   Also written: `citations.json`, with a verbatim statement for every citation in every parent step. Search outputs and actual command log are retained in the sandbox. No Lean file, repository file or launcher file was edited; no compiler, Lake or build was run.
2. Attachments: none. The exact project tag has no matching declaration under `lean/WeilConjectures/`; `lean/Sheaf/RepresentationTheory/ProcyclicScalarCochainEvaluation.lean:266` states the existing theorem but ends with `sorry` at line 279. Upstream discrete-module procyclic results do not state the all-continuous norm-coefficient assertion.
3. WANTED: an exact norm-topological source for the parameterwise scalar calculation, especially completion-boundary descent for the original incomplete algebraic closure. This is the existing wanted reference in the returned node and `lem-sfb-parameter-cochain-completion-boundary-descent`, not a new appeal to an unavailable theorem. The new lemmas are agent formulations; Stacks 0DVG defines the cochains only.
4. Return repaired: the old node carried too much work. Its statement has not changed or been weakened. The old arguments are allocated below without dropping any: original steps 1–3 to `lem-sfb-continuous-procyclic-low-degree-evaluation`, original step 5 to `lem-sfb-banach-translation-difference-split`, original step 6 to `lem-sfb-compact-open-coinduced-contraction`, original step 4 to assembly step 2, original step 7 to assembly step 3, original step 8 to assembly step 4, original step 9 to assembly step 5. The three extracted argument blocks have respectively 1979, 998 and 895 characters of the old proof; their self-contained statements have 1628, 1285 and 1714 characters. These are separate tasks, rather than a copy of the entire quasi-isomorphism into one replacement lemma.
5. Not finished in stage 1: the three new proofs are deliberately not supplied, as the human's re-split instruction requires; their statements are ready for separate workers. The incomplete-coefficient boundary descent remains the existing dependency. No new Mathlib leaf is claimed. The original parent proof dependencies now used only by child arguments (module definition, Mahler coordinates and homogeneous-coordinate comparison) disappear from the parent's proof-dependency list; applicable notions remain in its statement dependencies. No DAG nodes are deleted.

## Repair baseline and sources

The sandbox initially contained only `.brief2` through `.brief5`, with no report, searches or node files to retain. I copied the current returned node from the read-only shared repository, retaining every imported, Lean and blueprint field and all original searches. `returned-node.json` retains that baseline; the original nine proof steps are reproduced verbatim below. Delivery builds against current origin and preserves maintainer-owned metadata; no manual git operations are used.

I read AGENTS.md, the worker role, the stage-1 brief and stage document, GOAL.md, SETUP.md's three-level route rules, the item's chapter and unit, and delivery-errors B–E. The new snapshot's direct-images proof paragraph (3) locates the scalar input below open-image stability; it does not itself prove this analytic calculation. The old unit record comes from the older snapshot: I leave its route and realization fields unchanged, since this is not the unit's key node. `blueprint_refs.py ancestor` returns None for the existing creation chain. I retain this null ancestor and via chain and prefix the item in each child's via list. Searches of the whole blueprint for procyclic, continuous cohomology, evaluation generator, translation, coinduced, Mahler and 0DVG found no exact version of the new lemmas.

For all three new statements I read the full old argument in the returned DAG and the identical source docstring, lines 175–264 of the landed scalar-cochain module. For the first and third I also read `literature/stacks-project/etale-cohomology.tex:9007–9055`, whose label is `etale-cohomology-section-continuous-group-cohomology`, Tag 0DVG (verified in tags/tags). That source explicitly warns that topological-coefficient short exact sequences do not automatically give short exact cochains. The second node is based on Mathlib `NumberTheory/Padics/MahlerBasis.lean:337–385`, in particular the actual forward-difference Mahler isometry at 357 and formulas at 382,384; the separate exact-sequence claim is agent-formulated, rather than attributed to that definition.

Each new node has five recorded actual searches: LeanFinder twice with different phrasings, LeanSearch, Loogle, and source grep. Raw hits are stored with their original queries, and all are in searches.jsonl. The first node's Loogle service reported overload, recorded as unavailable rather than as a negative theorem search. Its two semantic services succeeded. I read the character classification in Padics/AddChar.lean:50–133: its characters are multiplicative-valued and completeness-dependent, so they are not the new additive norm-cochain result. For the Banach lemma the hits stop at the existing Mahler isometry; they do not provide its constant kernel, action continuity and split equivariant coefficient sequence. For the contraction I read the actual homogeneous-complex definition in RepresentationTheory/Homological/ContCohomology/Basic.lean:45–125; its recursively defined complex alone does not give this compact-open contraction. The abstract free standard resolution and alternating constant complex returned by the second search are different complexes, requiring a comparison rather than a one-line specialization.

## Review by Q71

For assembly step 1, I opened the new low-degree node and checked that it states the actual U and K differentials, the internal-module sheaf construction, all evaluation formulas, parameter restrictions including empty S, coefficient embeddings, and the explicit cocycle inverse. This is stronger in its coefficient generality than the particular E and Omega setup, but asserts no higher vanishing. A norm field containing Q_ell satisfies its hypotheses for both fields without a completeness assumption. In its retained argument, the congruence-class description makes nonnegative integers dense; equality of continuous functions then uses Hausdorffness, not completeness. Both degrees have zero incoming boundary, and the degree-one additive equation is exactly d^1 f=0. This is a finite construction plus a density lemma for arbitrary norm fields, not a new restatement of the full sheaf quasi-isomorphism. The human's request to distribute every old argument is why this entire coherent block, rather than just its elementary individual identities, is one task.

For assembly step 2, I opened all four cited nodes. `lem-weil-l-adic-extension-complete` supplies precisely completeness of the finite extension with its extending norm; `lem-sfb-normed-field-completion` supplies the complete norm field and isometric field map without assuming Omega complete. Norm identities and the ultrametric inequality pass to the completion by continuity and density. `lem-sfb-compact-function-space-complete` explicitly supplies the supremum topology, normed scalar action, completeness and empty-space norm; pointwise ultrametric inequalities then pass to the supremum. `lem-coef-compact-open-currying` supplies BOTH transpose and evaluation continuity with a locally compact factor. Profinite S and H^q are compact Hausdorff and hence locally compact. Swapping the two product factors and applying its explicit formulas gives the stated function coordinates, intertwining all substitutions in d. I have not silently treated a pointwise family as a continuous norm-valued family.

For assembly step 3, I opened the Banach split node and checked each hypothesis against step 2: complete ultrametric normed Q_ell-space V, including V=0. Its statement gives jointly continuous translations, equivariance of const and Delta, the continuous section T and continuous inverse-to-kernel evaluation. Pointwise postcomposition with T lifts any continuous cochain; pointwise evaluation at zero gives a continuous V-valued kernel inverse. Thus the asserted short exact sequence is in abstract vector-space complexes, even though T is not equivariant. The new coinduced node applies with J=H, k=Q_ell, V as above, and the very same compact-open R (its topology agrees with the supremum topology). It explicitly provides actual continuous primitives in every positive degree, as well as a chain homotopy equivalence and derived isomorphism; the parent is not citing only a per-degree surrogate for a derived identification. `lem-weil-pbc-complex-ses-homology-long-exact` states the exact segment needed for n at least 2. Its abelian-category hypothesis holds for abstract Q_ell-vector spaces. Both exterior degrees n-1 and n are positive. This proves existence of actual primitives by ordinary kernel/image exactness, without topological closure.

For assembly step 4, I reopened `lem-sfb-parameter-cochain-completion-boundary-descent` and read its entire statement. It requires a profinite G, profinite S, closed original cochain of degree n at least 1 and existence of an ACTUAL completed primitive. G=H and n at least 2 qualify, postcomposition with the isometric field embedding commutes with the finite-sum differential, and step 3 supplies that completed primitive. The conclusion is exactly finite jointly surjective parameter-local Omega-valued primitives; it does not assert a global primitive or identify condensed right derived invariants. The other citation, normed-field-completion, supplies the coefficient embedding used here. No new comparison theorem has been invented in this assembly.

For assembly step 5, I opened `def-weil-abstract-derived-category`: it defines cohomology by kernel/image and quasi-isomorphisms by all induced cohomology maps being invertible. Local primitives say exactly that the ordinary sheaf image contains the kernel; the reverse containment is d^2=0 from step 1. The sectionwise low-degree inverse is natural, so it is an inverse on the sheaves. Negative degrees are zero. I checked that the final compatible map is the same explicit epsilon, not an arbitrary quasi-isomorphism between the two objects. The five steps together are under 3000 characters, and none is over 2000.

I checked each new statement against small cases. For the low-degree node S empty gives the zero module and unique function; S a point, F=Q_ell gives precisely continuous additive maps t maps to t a; degrees zero and one have no incoming boundaries. For the Banach node V=0 is allowed, so I stated a norm bound rather than an incorrect claim that the operator norm is always exactly one. Constants have Delta=0, and prefixed-zero Mahler coordinates have tail equal to the original coordinates. No equivariance of T is claimed or used. For the coinduced node J the trivial group gives the unnormalized alternating complex, not falsely zero differentials in all degrees: in degree zero h_1 delta(phi)(x)=phi(x)-phi(0), and in positive degree prefixed-zero deletion gives phi, the other terms cancel in pairs. Empty parameter spaces do not make J empty (a group has an identity). V=0 works. Neither the contraction nor the low-degree node assumes completeness. All original analytic arguments are retained below, with only their allocation changed; none is replaced by a label such as 'standard comparison'.

I checked B–E against the actual JSON: every new node introduces its own objects; each is status unsplit with empty proof/proof_deps/proof_origin; sources distinguish the cochain definition from the new claim; real search outputs include failures as failures; definitions are cited or written explicitly; the item statement is unchanged; its proof-dependency list is exactly the union of uses; all cited statements were read, and citations.json copies them verbatim. New nodes have no dependency on the parent, so there is no cycle. No SGA source or forbidden alternate route is used. The two original generic tool uses for exponential law and abstract long exact sequence, and the completeness input, are preserved in split_report. The source's missing analytic theorem is explicitly marked agent-formulated with a wanted exact reference, not misattributed to Tag 0DVG.

## Not duplicates

lem-sfb-continuous-procyclic-low-degree-evaluation vs def-sc-brauer-scalar-defect: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs def-sc-galois-units-cohomology: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs def-sc-galois-units-two-cocycle-classes: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs def-sc-homogeneous-cochain-evaluation: the existing node assumes discrete coefficients/locally constant cochains and states Concrete evaluation of homogeneous continuous cochains; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-exc-cochains-derived-invariants: the existing node assumes discrete coefficients/locally constant cochains and states Continuous cochains compute derived invariants for discrete profinite modules; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-exc-coinduced-continuous-acyclic: the existing node assumes discrete coefficients/locally constant cochains and states Coinduced discrete modules are acyclic for continuous cochains; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-exc-coinduced-discrete-embedding: the existing node assumes discrete coefficients/locally constant cochains and states Discrete continuous modules embed in coinduced modules; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-exc-coinduced-homotopy-continuous: the existing node assumes discrete coefficients/locally constant cochains and states The coinduced contracting operator is continuous; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-exc-coinduced-homotopy-identity: the existing node assumes discrete coefficients/locally constant cochains and states The coinduced contraction satisfies the homotopy identity; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-exc-continuous-cochains-delta-functor: the existing node assumes discrete coefficients/locally constant cochains and states Continuous cochains form a delta-functor; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-exc-continuous-cochains-invariants-zero: the existing node assumes discrete coefficients/locally constant cochains and states Degree-zero cochains are invariants; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-exc-continuous-cochains-short-exact: the existing node assumes discrete coefficients/locally constant cochains and states Continuous cochains preserve short exact sequences of discrete modules; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-per-finite-quotient-cochain-colimit: the existing node identifies a colimit of finite-quotient cochains with cochains in a discrete finite-ring module; the new result retains norm-topological vector coefficients and asserts low-degree generator evaluation and sheaf compatibility.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-galois-units-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-amplification: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-cocycle: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-cocycle-realization: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-exists: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-faithful: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-faithful-backward: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-faithful-forward: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-lifts: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-scalar-data: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-surjective: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-surjective-crossed-product-realization: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-tensor-split: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-brauer-scalar-defect-unique: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-cocycle-monomial-coefficients: the existing node assumes discrete coefficients/locally constant cochains and states Regular monomial coefficients for a continuous Galois cocycle; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-continuous-cohomology-coefficient-equiv: the existing node assumes discrete coefficients/locally constant cochains and states Equivariant discrete coefficient equivalences preserve continuous cohomology across universes; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-discrete-invariants-continuous-comparison: the existing node assumes discrete coefficients/locally constant cochains and states Derived invariants under an equivalence compute homogeneous continuous cohomology; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-discrete-resolution-continuous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states Invariants of a transported injective resolution compute homogeneous continuous cohomology; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-discrete-resolution-inhomogeneous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states Invariants of a transported resolution compute locally constant inhomogeneous cohomology; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-etale-galois-units-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-etale-stalk-continuous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states For an abelian etale sheaf on Spec K whose geometric stalk identifies equivariantly with a discrete Galois representation M, its sheaf cohomology in every degree is equivalent to continuous cohomology of M.; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-etale-units-h2-forward-embedding: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-etale-units-h2-reverse-embedding: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-etale-units-two-cocycle-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-finite-galois-cocycle-data: the existing node assumes discrete coefficients/locally constant cochains and states Finite quotient data for a prescribed continuous Galois cocycle; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-galois-units-homogeneous-cocycle-descent: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-galois-units-homogeneous-cocycle-equivalence: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-galois-units-homogeneous-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-galois-units-scalar-coboundary: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns norm-field additive scalar procyclic families and low-degree generator evaluation.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-homogeneous-cochain-evaluation-bijective: the existing node assumes discrete coefficients/locally constant cochains and states Bijectivity of cumulative-product cochain evaluation; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-homogeneous-cochain-evaluation-differential: the existing node assumes discrete coefficients/locally constant cochains and states Differential of cumulative-product cochain evaluation; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-homogeneous-inhomogeneous-continuous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states Locally constant inhomogeneous coordinates for homogeneous continuous cochains; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-locally-constant-cochains-acyclic-embedding: the existing node assumes discrete coefficients/locally constant cochains and states Every object embeds in one whose locally constant integer cochain complex is exact; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-locally-constant-cochains-degreewise-exact: the existing node assumes discrete coefficients/locally constant cochains and states Pointwise degreewise exactness of locally constant integer cochains; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-locally-constant-cochains-effaceable: the existing node assumes discrete coefficients/locally constant cochains and states Effaceable locally constant integer cochain delta-functor; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-locally-constant-cochains-exact: the existing node assumes discrete coefficients/locally constant cochains and states The locally constant integer cochain complex is additive and degreewise exact; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-locally-constant-cochains-invariants-zero: the existing node assumes discrete coefficients/locally constant cochains and states Degree-zero locally constant integer cochain homology is naturally invariants; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sc-locally-constant-cochains-structure: the existing node assumes discrete coefficients/locally constant cochains and states Construction of locally constant integer cochains; it does not cover parameterwise generator evaluation with all continuous norm-field scalar maps.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sfb-procyclic-scalar-cochain-evaluation: the parent proves higher sheaf exactness including incomplete Omega; this lemma constructs the complexes and proves only low-degree evaluation for every norm field over Q_ell.

lem-sfb-continuous-procyclic-low-degree-evaluation vs lem-sfb-topological-homogeneous-cochain-coordinates: the existing node changes homogeneous/inhomogeneous coordinates for arbitrary actions; it gives neither parameter sheaf construction nor the dense-generator additive-cocycle classification.

lem-sfb-banach-translation-difference-split vs def-sc-brauer-scalar-defect: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs def-sc-galois-units-cohomology: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs def-sc-galois-units-two-cocycle-classes: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs def-sc-homogeneous-cochain-evaluation: the existing node assumes discrete coefficients/locally constant cochains and states Concrete evaluation of homogeneous continuous cochains; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-exc-cochains-derived-invariants: the existing node assumes discrete coefficients/locally constant cochains and states Continuous cochains compute derived invariants for discrete profinite modules; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-exc-coinduced-continuous-acyclic: the existing node assumes discrete coefficients/locally constant cochains and states Coinduced discrete modules are acyclic for continuous cochains; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-exc-coinduced-discrete-embedding: the existing node assumes discrete coefficients/locally constant cochains and states Discrete continuous modules embed in coinduced modules; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-exc-coinduced-homotopy-continuous: the existing node assumes discrete coefficients/locally constant cochains and states The coinduced contracting operator is continuous; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-exc-coinduced-homotopy-identity: the existing node assumes discrete coefficients/locally constant cochains and states The coinduced contraction satisfies the homotopy identity; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-exc-continuous-cochains-delta-functor: the existing node assumes discrete coefficients/locally constant cochains and states Continuous cochains form a delta-functor; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-exc-continuous-cochains-invariants-zero: the existing node assumes discrete coefficients/locally constant cochains and states Degree-zero cochains are invariants; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-exc-continuous-cochains-short-exact: the existing node assumes discrete coefficients/locally constant cochains and states Continuous cochains preserve short exact sequences of discrete modules; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-per-finite-quotient-cochain-colimit: the existing node identifies a colimit of finite-quotient cochains with cochains in a discrete finite-ring module; the new result retains norm-topological vector coefficients and asserts the split Banach translation-difference sequence.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-galois-units-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-amplification: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-cocycle: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-cocycle-realization: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-exists: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-faithful: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-faithful-backward: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-faithful-forward: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-lifts: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-scalar-data: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-surjective: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-surjective-crossed-product-realization: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-tensor-split: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-brauer-scalar-defect-unique: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-cocycle-monomial-coefficients: the existing node assumes discrete coefficients/locally constant cochains and states Regular monomial coefficients for a continuous Galois cocycle; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-continuous-cohomology-coefficient-equiv: the existing node assumes discrete coefficients/locally constant cochains and states Equivariant discrete coefficient equivalences preserve continuous cohomology across universes; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-discrete-invariants-continuous-comparison: the existing node assumes discrete coefficients/locally constant cochains and states Derived invariants under an equivalence compute homogeneous continuous cohomology; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-discrete-resolution-continuous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states Invariants of a transported injective resolution compute homogeneous continuous cohomology; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-discrete-resolution-inhomogeneous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states Invariants of a transported resolution compute locally constant inhomogeneous cohomology; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-etale-galois-units-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-etale-stalk-continuous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states For an abelian etale sheaf on Spec K whose geometric stalk identifies equivariantly with a discrete Galois representation M, its sheaf cohomology in every degree is equivalent to continuous cohomology of M.; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-etale-units-h2-forward-embedding: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-etale-units-h2-reverse-embedding: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-etale-units-two-cocycle-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-finite-galois-cocycle-data: the existing node assumes discrete coefficients/locally constant cochains and states Finite quotient data for a prescribed continuous Galois cocycle; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-galois-units-homogeneous-cocycle-descent: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-galois-units-homogeneous-cocycle-equivalence: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-galois-units-homogeneous-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-galois-units-scalar-coboundary: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns a Banach Q_ell-valued translation-difference operator and its continuous section.

lem-sfb-banach-translation-difference-split vs lem-sc-homogeneous-cochain-evaluation-bijective: the existing node assumes discrete coefficients/locally constant cochains and states Bijectivity of cumulative-product cochain evaluation; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-homogeneous-cochain-evaluation-differential: the existing node assumes discrete coefficients/locally constant cochains and states Differential of cumulative-product cochain evaluation; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-homogeneous-inhomogeneous-continuous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states Locally constant inhomogeneous coordinates for homogeneous continuous cochains; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-locally-constant-cochains-acyclic-embedding: the existing node assumes discrete coefficients/locally constant cochains and states Every object embeds in one whose locally constant integer cochain complex is exact; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-locally-constant-cochains-degreewise-exact: the existing node assumes discrete coefficients/locally constant cochains and states Pointwise degreewise exactness of locally constant integer cochains; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-locally-constant-cochains-effaceable: the existing node assumes discrete coefficients/locally constant cochains and states Effaceable locally constant integer cochain delta-functor; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-locally-constant-cochains-exact: the existing node assumes discrete coefficients/locally constant cochains and states The locally constant integer cochain complex is additive and degreewise exact; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-locally-constant-cochains-invariants-zero: the existing node assumes discrete coefficients/locally constant cochains and states Degree-zero locally constant integer cochain homology is naturally invariants; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sc-locally-constant-cochains-structure: the existing node assumes discrete coefficients/locally constant cochains and states Construction of locally constant integer cochains; it does not cover the Banach Mahler difference sequence with a continuous linear section.

lem-sfb-banach-translation-difference-split vs lem-sfb-procyclic-scalar-cochain-evaluation: the parent proves a sheaf quasi-isomorphism for E and incomplete Omega; this lemma is a split translation-difference coefficient sequence for an arbitrary Banach Q_ell-space, with no parameter sheaf conclusion.

lem-sfb-banach-translation-difference-split vs lem-sfb-topological-homogeneous-cochain-coordinates: the existing node changes cochain coordinates; it provides no Mahler shift, constant kernel or continuously split difference operator.

lem-sfb-compact-open-coinduced-contraction vs def-sc-brauer-scalar-defect: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs def-sc-galois-units-cohomology: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs def-sc-galois-units-two-cocycle-classes: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs def-sc-homogeneous-cochain-evaluation: the existing node assumes discrete coefficients/locally constant cochains and states Concrete evaluation of homogeneous continuous cochains; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-exc-cochains-derived-invariants: the existing node assumes discrete coefficients/locally constant cochains and states Continuous cochains compute derived invariants for discrete profinite modules; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-exc-coinduced-continuous-acyclic: the existing node assumes discrete coefficients/locally constant cochains and states Coinduced discrete modules are acyclic for continuous cochains; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-exc-coinduced-discrete-embedding: the existing node assumes discrete coefficients/locally constant cochains and states Discrete continuous modules embed in coinduced modules; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-exc-coinduced-homotopy-continuous: the existing node assumes discrete coefficients/locally constant cochains and states The coinduced contracting operator is continuous; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-exc-coinduced-homotopy-identity: the existing node assumes discrete coefficients/locally constant cochains and states The coinduced contraction satisfies the homotopy identity; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-exc-continuous-cochains-delta-functor: the existing node assumes discrete coefficients/locally constant cochains and states Continuous cochains form a delta-functor; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-exc-continuous-cochains-invariants-zero: the existing node assumes discrete coefficients/locally constant cochains and states Degree-zero cochains are invariants; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-exc-continuous-cochains-short-exact: the existing node assumes discrete coefficients/locally constant cochains and states Continuous cochains preserve short exact sequences of discrete modules; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-per-finite-quotient-cochain-colimit: the existing node identifies a colimit of finite-quotient cochains with cochains in a discrete finite-ring module; the new result retains norm-topological vector coefficients and asserts a contraction on compact-open continuous coinduced cochains.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-galois-units-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-amplification: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-cocycle: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-cocycle-realization: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-exists: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-faithful: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-faithful-backward: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-faithful-forward: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-lifts: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-scalar-data: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-surjective: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-surjective-crossed-product-realization: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-tensor-split: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-brauer-scalar-defect-unique: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-cocycle-monomial-coefficients: the existing node assumes discrete coefficients/locally constant cochains and states Regular monomial coefficients for a continuous Galois cocycle; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-continuous-cohomology-coefficient-equiv: the existing node assumes discrete coefficients/locally constant cochains and states Equivariant discrete coefficient equivalences preserve continuous cohomology across universes; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-discrete-invariants-continuous-comparison: the existing node assumes discrete coefficients/locally constant cochains and states Derived invariants under an equivalence compute homogeneous continuous cohomology; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-discrete-resolution-continuous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states Invariants of a transported injective resolution compute homogeneous continuous cohomology; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-discrete-resolution-inhomogeneous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states Invariants of a transported resolution compute locally constant inhomogeneous cohomology; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-etale-galois-units-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-etale-stalk-continuous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states For an abelian etale sheaf on Spec K whose geometric stalk identifies equivariantly with a discrete Galois representation M, its sheaf cohomology in every degree is equivalent to continuous cohomology of M.; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-etale-units-h2-forward-embedding: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-etale-units-h2-reverse-embedding: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-etale-units-two-cocycle-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-finite-galois-cocycle-data: the existing node assumes discrete coefficients/locally constant cochains and states Finite quotient data for a prescribed continuous Galois cocycle; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-galois-units-homogeneous-cocycle-descent: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-galois-units-homogeneous-cocycle-equivalence: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-galois-units-homogeneous-comparison: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-galois-units-scalar-coboundary: the existing node concerns discrete separable-closure units, Brauer classes or their cocycles; the new node concerns actual compact-open C(J,V)-valued cochains and a continuous insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-homogeneous-cochain-evaluation-bijective: the existing node assumes discrete coefficients/locally constant cochains and states Bijectivity of cumulative-product cochain evaluation; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-homogeneous-cochain-evaluation-differential: the existing node assumes discrete coefficients/locally constant cochains and states Differential of cumulative-product cochain evaluation; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-homogeneous-inhomogeneous-continuous-cohomology: the existing node assumes discrete coefficients/locally constant cochains and states Locally constant inhomogeneous coordinates for homogeneous continuous cochains; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-locally-constant-cochains-acyclic-embedding: the existing node assumes discrete coefficients/locally constant cochains and states Every object embeds in one whose locally constant integer cochain complex is exact; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-locally-constant-cochains-degreewise-exact: the existing node assumes discrete coefficients/locally constant cochains and states Pointwise degreewise exactness of locally constant integer cochains; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-locally-constant-cochains-effaceable: the existing node assumes discrete coefficients/locally constant cochains and states Effaceable locally constant integer cochain delta-functor; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-locally-constant-cochains-exact: the existing node assumes discrete coefficients/locally constant cochains and states The locally constant integer cochain complex is additive and degreewise exact; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-locally-constant-cochains-invariants-zero: the existing node assumes discrete coefficients/locally constant cochains and states Degree-zero locally constant integer cochain homology is naturally invariants; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-locally-constant-cochains-structure: the existing node assumes discrete coefficients/locally constant cochains and states Construction of locally constant integer cochains; it does not cover the compact-open C(J,V) topology with arbitrary Hausdorff topological vector coefficients and its derived contraction.

lem-sfb-compact-open-coinduced-contraction vs lem-sfb-procyclic-scalar-cochain-evaluation: the parent concerns trivial scalar coefficients on Z_ell; this lemma contracts compact-open translation coefficients C(J,V) for arbitrary compact abelian J and topological vector V.

lem-sfb-compact-open-coinduced-contraction vs lem-sfb-topological-homogeneous-cochain-coordinates: the existing node changes homogeneous/inhomogeneous coordinates and is reused in the new statement; it does not remove equivariance by evaluation into C(J,V), or give the augmented insertion contraction.

lem-sfb-banach-translation-difference-split vs lem-sfb-banach-mahler-coordinates: the existing node gives only the coordinate isometry (and is cited in the new statement); the new theorem also requires jointly continuous translation, the dense-integer constant-kernel argument and the continuous linear right inverse with equivariant coefficient maps.

lem-sfb-compact-open-coinduced-contraction vs lem-sc-group-coinduced-acyclic: that node assumes discrete ell-primary coefficients and a discrete coinduced module, whereas the new theorem retains the compact-open function topology and all continuous topological vector coefficients, with an explicit chain homotopy and derived isomorphism.

lem-sfb-compact-open-coinduced-contraction vs lem-sfb-internal-homogeneous-functions-injective: that node concerns injectivity of internal Hom objects in condensed equivariant modules, not continuous compact-open function-space cochains or their insertion homotopy.

lem-sfb-compact-open-coinduced-contraction vs lem-sfb-normed-scalar-profinite-hom-acyclic: that node compares an internal derived Hom with an underived scalar function sheaf, whereas this one is an explicit contraction of abstract continuous group cochain complexes.

## Retained arguments and allocation

The following is the full returned proof, verbatim, preserved so that the separate workers have every argument, not a shortened synopsis. The nodes themselves remain statement-only as required. Original steps 1–3 belong to lem-sfb-continuous-procyclic-low-degree-evaluation; step 5 to lem-sfb-banach-translation-difference-split; step 6 to lem-sfb-compact-open-coinduced-contraction. Steps 4,7,8,9 are the preparation, dimension shifting, coefficient descent and sheaf assembly remaining in the parent. For the new contraction the degree-zero identity is also made explicit above and in its statement.

### Original step 1

Each face in $d$ is precomposition by a continuous map, so it acts on all the indicated continuous functions. Composing two faces in the two orders gives the same substitution, with opposite alternating signs; hence $d^{q+1}d^q=0$. The convention $d^0=0$ is the trivial-action degree-zero differential. Functions on $S\times H^q$ form a sheaf in $S$ by [def-sfb-continuous-map-condensed-ring], applied to continuous functions and descent along the product with $H^q$. Scalar multiplication through $S$ commutes with each face, and with restrictions. Thus these are complexes of the internal modules defined in [sk-def-sfb-module-objects].

Uses: def-sfb-continuous-map-condensed-ring, sk-def-sfb-module-objects.

### Original step 2

For $u:S'\to S$ one has $(f\circ(u\times1_H))(s';1)=f(u(s');1)$, and postcomposition by $E\hookrightarrow\Omega$ commutes with evaluation and every finite sum. The identity in degree zero and the zero maps in degrees at least two have the same naturality. Both sides of the cochain-map identity in degree zero are zero because $d^0=0$; in degree one the target differential and $\epsilon^2$ are zero, and higher degrees are zero as well. Evaluation is $C(S,F)$-linear. This proves all the asserted map and compatibility clauses, including the empty parameter.

Uses: .

### Original step 3

In degree zero the cohomology is $C(S,F)$, and $\epsilon^0$ is its identity. A degree-one cocycle satisfies $f(s;x+y)=f(s;x)+f(s;y)$. Put $a(s)=f(s;1)$. Additivity gives $f(s;m)=m a(s)$ for nonnegative integers $m$. Every basic congruence class of $H=\varprojlim_r\mathbf Z/\ell^r\mathbf Z$ contains a nonnegative integer, so these integers are dense. The two continuous functions $t\mapsto f(s;t)$ and $t\mapsto t a(s)$ agree on that dense subset and take values in the Hausdorff norm field $F$, hence agree everywhere. Conversely $f(s;t)=t a(s)$ is jointly continuous and a cocycle for each $a\in C(S,F)$. Since $d^0=0$ there are no degree-one boundaries. Thus evaluation at $1$ is an isomorphism in degrees zero and one already on sections, for both fields, without completeness.

Uses: .

### Original step 4

For the higher degrees first let $B$ be either $E$ or $\widehat\Omega$. The first is complete by [lem-weil-l-adic-extension-complete] and the second by [lem-sfb-normed-field-completion]. The ultrametric inequality extends to the completion by taking limits in the inequality in $\Omega$; the same applies to multiplication by $\mathbf Q_\ell$. For fixed $S$ set $V=C(S,B)$ with the supremum norm. By [lem-sfb-compact-function-space-complete] this is a complete normed $\mathbf Q_\ell$-vector space. Pointwise ultrametricity implies ultrametricity of its supremum norm, and $\|a v\|=|a|_\ell\|v\|$ for $a\in\mathbf Z_\ell$. By [lem-coef-compact-open-currying], all the function spaces in question can be curried as $C(H^q,V)$: the compact-open and supremum topologies coincide here. In particular, continuous families remain continuous in the norm on $V$.

Uses: lem-weil-l-adic-extension-complete, lem-sfb-normed-field-completion, lem-sfb-compact-function-space-complete, lem-coef-compact-open-currying.

### Original step 5

Put $R=C(H,V)$ and let $H$ act by $(t\cdot f)(x)=f(x+t)$. The action is jointly continuous: the evaluation map on compact $H$ is continuous by [lem-coef-compact-open-currying], and currying the continuous map $(t,f,x)\mapsto f(x+t)$ gives the action map. Set $\Delta f(x)=f(x+1)-f(x)$. It commutes with this action. Its kernel is the constant functions, since invariance under $1$ implies invariance under the dense integer subgroup and then under all translations. By [lem-sfb-banach-mahler-coordinates], if $\mathcal Mf=(a_0,a_1,\ldots)$ then $\mathcal M(\Delta f)=(a_1,a_2,\ldots)$, directly from the forward-difference formula. Sending $(a_0,a_1,\ldots)$ to $(0,a_0,a_1,\ldots)$ is a norm-one linear operator on $c_0$. Conjugating it by $\mathcal M$ gives a continuous additive right inverse to $\Delta$. Hence $0\to V\xrightarrow{\mathrm{const}}R\xrightarrow\Delta R\to0$ is exact and splits continuously as a sequence of coefficient spaces. The splitting need not commute with the $H$-action.

Uses: lem-coef-compact-open-currying, lem-sfb-banach-mahler-coordinates.

### Original step 6

Compute the cochains with coefficients in $R$ using [lem-sfb-topological-homogeneous-cochain-coordinates], in additive notation. For a homogeneous equivariant cochain $F:H^{q+1}\to R$ put $\phi(x_0,\ldots,x_q)=F(x_0,\ldots,x_q)(0)$. Equivariance is $F(x_0+t,\ldots,x_q+t)(y)=F(x_0,\ldots,x_q)(y+t)$, so its inverse is $F(x_0,\ldots,x_q)(y)=\phi(x_0+y,\ldots,x_q+y)$. Continuity in both directions follows from [lem-coef-compact-open-currying]. The differential on $\phi\in C(H^{q+1},V)$ is alternating deletion. For $q\geq1$ define $(h_q\phi)(x_0,\ldots,x_{q-1})=\phi(0,x_0,\ldots,x_{q-1})$. In $h_{q+1}\delta\phi$, deletion of the prefixed zero gives $\phi$; every other deletion cancels its counterpart in $\delta h_q\phi$ with the opposite sign. Thus $\delta h_q+h_{q+1}\delta=1$ in positive degrees. These are actual continuous cochains. It follows that $H^q(C^\bullet(H,R))=0$ for $q\geq1$.

Uses: lem-sfb-topological-homogeneous-cochain-coordinates, lem-coef-compact-open-currying.

### Original step 7

Apply continuous $q$-cochains to the coefficient sequence of step 5. Its continuous right inverse makes $C(H^q,R)\xrightarrow\Delta C(H^q,R)$ surjective in every degree. Its kernel is $C(H^q,V)$: the inverse to the constant inclusion is evaluation at $0$, which is continuous. The equivariance of the coefficient maps makes this a degreewise short exact sequence of complexes of abstract $\mathbf Q_\ell$-vector spaces. By [lem-weil-pbc-complex-ses-homology-long-exact], for $n\geq2$ the segment $H^{n-1}(H,R)\to H^n(H,V)\to H^n(H,R)$ is exact. Both outside groups vanish by step 6, so $H^n(H,V)=0$. Under the currying in step 4 this says that every closed element of $C(S\times H^n,B)$ has an actual continuous primitive in $C(S\times H^{n-1},B)$, for $B=E$ and $B=\widehat\Omega$.

Uses: lem-weil-pbc-complex-ses-homology-long-exact.

### Original step 8

For $F=E$, step 7 proves higher exactness on each parameter set. For $F=\Omega$, take any $n\geq2$ and any closed $z\in C(S\times H^n,\Omega)$. Postcomposition with the isometric inclusion $\iota:\Omega\hookrightarrow\widehat\Omega$ gives a continuous closed completed cochain. Step 7 with $B=\widehat\Omega$ provides its completed primitive. Now apply [lem-sfb-parameter-cochain-completion-boundary-descent] with this $G=H$, the original $S$, and this $n$. Its hypotheses are exactly the closedness and existence of a completed primitive just verified. It gives a finite jointly surjective profinite cover $S_a\to S$ and genuine $\Omega$-valued continuous primitives there. No Banach argument has been applied to $\Omega$ itself.

Uses: lem-sfb-parameter-cochain-completion-boundary-descent.

### Original step 9

A section of the kernel sheaf in degree $n\geq2$ is locally in the image sheaf by step 8. Images are always contained in kernels by $d^2=0$, so these sheaves are equal; this is ordinary sheaf image, not its closure. In degrees zero and one the sectionwise inverse in step 3 is natural in $S$ and therefore is an inverse on cohomology sheaves. Negative degrees are zero on both complexes. The definition in [def-weil-abstract-derived-category] now makes $\epsilon$ a quasi-isomorphism. The maps whose cohomology was computed are the explicit maps of step 2, so their parameter and coefficient compatibility is the required compatibility. None of the argument identifies these underived complexes with internal right derived invariants.

Uses: def-weil-abstract-derived-category.


## Landing return repair, 2026-10-22

The return at branch head `b9c5a54d4ca` approved the mathematics but reported that the side-project completion had not been promoted into the live queue DAG. This repair uses the delivery tool to build on current `origin/sheaf-dag`; no git operation or promotion of maintainer-owned status was performed by the worker. The first resumed dry run exited successfully at `33cbc24b69c`. The report and parent split report now explicitly record this rebase and review, so this is not an unchanged re-push.

I compared `returned-node.json` with the current shared-repository parent: all fields agree. The retained split differs from that baseline in its five-step proof, proof dependencies and split report. The three extracted child ids are still absent from the shared repository. Thus none of the approved argument blocks has been superseded there. The released stage-1 repair note dated 2026-10-22 explicitly requires retaining the statement and distributing the old argument into at least two nodes; this delivery retains three.

For this repair I re-read all current cited statements, rather than relying on their prior status. Step 1 still uses the child's actual complex construction, generator evaluation and naturality clauses. Step 2 still has completeness for the finite field and completion, completeness and topology of compact continuous-function spaces, and the exponential-law formulas. Step 3 still uses an actual continuous nonequivariant section and continuous kernel inverse, the compact-open contraction, and the degreewise-short-exact long exact sequence; both outer degrees are positive for n at least two. Step 4 still satisfies the current boundary-descent node's closedness and actual-completed-primitive hypotheses, so its conclusion gives exactly a finite jointly surjective parameter cover with original-coefficient primitives. That node is now split; its current statement, not its proof or status, supplies the same assertion. The current homogeneous-coordinate comparison also remains an actual cochain isomorphism with the formulas used by the contraction child. Step 5 still uses ordinary kernel/image cohomology and the definition of quasi-isomorphism. All eleven entries of citations.json are verbatim parts of the current statements. No hypothesis, coefficient topology, map normalization or conclusion needs changing.

I also re-read the scalar module's source proof and its theorem ending in sorry, the current blueprint paragraph (3), and Stacks Tag 0DVG's explicit warning about nondiscrete exactness. I reused the recorded search results: they distinguish the Mahler coordinate isometry and discrete-coefficient results from the extracted analytic claims. I did not repeat unchanged search questions. Small cases remain as checked under Review by Q71: empty parameter, zero Banach space, trivial group, and incomplete coefficients. The retained assembly is under 3000 characters and every step is under 2000. The final dry run and push follow this report update.


## Current-DAG rebase repair, 2026-10-22

The resumed delivery dry run built `ca5bd2121b5` on the current server base and exited OK before any changes in this attempt. I then compared the retained `returned-node.json` with the current shared parent: they agree in every field. The three extracted child nodes are still absent from the shared DAG. I reconstructed the parent from that current file and applied only the retained split-owned fields, preserving all current maintainer metadata. This is a fresh repaired delivery, not an unchanged re-push of the previous branch.

I re-read every current parent proof citation and every definition or comparison used to state the three new nodes. All eleven citation entries still match the current statements verbatim and cover every step citation exactly. In particular, the current homogeneous-coordinate node states an actual cochain isomorphism as well as its derived isomorphism; the Mahler node states the forward-difference coordinate formula; and completion-boundary descent still assumes an actual completed primitive and concludes finite jointly surjective parameter-local primitives. No changed hypothesis requires altering the statement or the extracted tasks. `current-dependency-statements.json` retains the exact current external statements and their fingerprints for any subsequent rebase audit.

I clarified assembly step 3 to display the actual degreewise short exact sequence of abstract vector-space complexes, with its two copies of continuous R-cochains. Postcomposition with the supplied continuous section proves surjectivity; evaluation at zero gives the continuous kernel inverse; equivariance, rather than equivariance of the section, makes the arrows cochain maps. The exact segment is applied with both exterior degrees positive. The other steps still use the low-degree evaluation statement, Banach function-space completeness and currying, local completion descent, and ordinary kernel/image cohomology exactly as checked under Review by Q71. The statement and all nine original arguments remain intact, with the allocation already recorded above.

For this attempt I reopened the current blueprint paragraph (3), Stacks Tag 0DVG's definition and warning about nondiscrete coefficients, the Mahler isometry and formulas in Mathlib, and the source scalar theorem and its proof docstring. Its theorem still ends in sorry; a fresh search of all of lean/WeilConjectures found no exact scalar theorem or blueprint tag, so there is no attachment. I read the retained search outputs and reused the same logged queries and verdicts because the three mathematical search questions have not changed. The small cases remain valid: empty S gives the zero function module, V=0 satisfies the norm bound, the trivial group has the augmented alternating contraction, and the incomplete field is used only in the low-degree and local-descent portions. No SGA route, new hypothesis, closure of images, or global primitive for incomplete coefficients has been introduced. The final server dry run and push will use these repaired files.
