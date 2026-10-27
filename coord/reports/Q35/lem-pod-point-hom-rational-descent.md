# Worker report — Q35

## Files written

- `dag/nodes/sec-six-functors/lem-pod-point-hom-rational-descent.json`: statement split into five steps; statement and statement dependencies unchanged. No new nodes and no Mathlib leaves.
- `citations.json`: verbatim live statement quotations for every citation in every proof step.
- `searches.jsonl`: actual msearch results; existing item searches retained, with the searches of this worker appended to its Mathlib search record.

## Attachments

None. I searched the entire project source by the blueprint tag and by point/rational/Hom/descent terminology. `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual` in `lean/WeilConjectures/SixFunctors/Etale/Derived/Point.lean:436` gives an étale coefficient dual comparison, but not the specified completed pro-etale point comparison, rational morphism action, or finite-field scalar and common-stage clauses. Its proof therefore does not attach to this item.

## Literature wanted

None. The proof is an agent-written assembly, following the second sentence of the current main-20261015 point-dualizing-complex proof. I read that proof, the source definitions of rationalization and algebraically closed coefficient categories, and Stacks Tag 0A6A (`more-algebra.tex`, `lemma-base-change-RHom`, clause (1) and its preceding canonical-map construction).

## Corrections and reuse

The live item was unsplit and the sandbox had no item or earlier report. Its statement is retained verbatim: no statement dispute or hypothesis repair is needed. The blueprint's phrase that internal Hom at the point is computed over the coefficient ring does not itself prove the rational and common-stage comparison; the five steps supply that assembly, using the already stated integral results. In particular, a new rational-Hom lemma or a new common-stage lemma would duplicate existing inputs or relabel this item's clauses.

DAG searches found `lem-pod-perfect-dual-scalar-calculus`, which already states representative-independent dual base change, derived naturality, localization and the tower equation. I therefore created no separate algebraic lemma. The more general `lem-pc-base-change-rhom-perfect` identifies invertibility of precisely the canonical RHom base-change arrow, rather than just an abstract isomorphism. `lem-weil-point-transformation-coefficient-descent` concerns pullback transformations and does not apply to this contravariant dual comparison; the elementary descent equations are written here instead. Whole-blueprint searches for “point Hom”, “computed over the coefficient”, “perfect-source” and “rational descent” produced no second blueprint statement of this item (the last returns the unrelated zeta rational-descent proposition).

The msearch calls tried two semantic phrasings, LeanSearch, Loogle and source grep. The hits concern ordinary sheaf Hom/sections, generic localization natural isomorphisms, and linear derived functors, not this specified completed-point transformation. I read `CategoryTheory.Localization.liftNatIso` at Mathlib/CategoryTheory/Localization/Predicate.lean:357 and inspected its context; it is a generic localization tool, not a one-line specialization proving the item's scalar squares and common-stage action. No Mathlib match is claimed.

## Tool uses

The split report declares perfect-source RHom base change from the Picard unit as a generic algebraic tool, and the specified sections-scalar comparison and target common-stage category from the coefficient compatibility route. None replaces a step of the six-functor package route. The remaining point comparison statements belong to the item's own unit. Definition citations introduce the actual categories and actions, not additional theorems about them.

## Review by Q35

I read delivery-errors B–E in full and checked the written split against the live statements, rather than relying on their proofs. There are no new nodes, hence no new statement-only, duplicate, missing-definition or Stacks-tag records to validate. The item uses completed coefficient sheaves, raw rationalization and the literal common-stage pair category throughout; it never replaces these by discrete non-torsion étale coefficients or adds an idempotent completion. Each step is shorter than 2000 characters.

Step 1 uses `lem-pod-point-exact-extension-sections` for the exact adjunction and coefficient ring identification; `lem-pod-point-sections-reconstruction` for the actual natural counit; and `lem-pod-point-derived-hom-evaluation` for its natural Hom-complex comparison, with formula h(1 tensor x). These statements supply precisely the claims taken from them. The integral constructibility and finite-projective internal-Hom model are assumptions of this item, not inferred from a definition. Rational internal Hom is the operation defined in `def-weil-derived-pullback-tensor-hom`.

Step 2 uses `lem-pc-base-change-rhom-perfect` with rings O_E and E, first argument c and second argument O_E in degree zero. Perfectness is supplied by the given P; no unproved flatness or boundedness claim about a new resolution is needed. I read Tag 0A6A, whose first clause has exactly these hypotheses. The pure-tensor arrow of `def-pc-perfect-rhom-base-change-map` agrees with the beta of `lem-pod-perfect-dual-scalar-calculus`, and that latter statement explicitly supplies independence of the bounded projective representative, derived naturality and preservation of quasi-isomorphisms under localization. `def-weil-finite-coefficient-point` specifies F_E as sections followed by tensor with E, so the source identification is an instance of the definitions. This checks the actual arrow, not merely existence of an isomorphism.

Step 3 is elementary after the preceding comparisons: for an integral u the two sides agree by the cited naturality; multiply each equation by its scalar a_i and add. The rationalization definition really has Hom tensored with E, and the operation and point-fiber definitions specify the displayed scalar actions. Tensor balancing, not an assumed injective map from integral Hom, proves presentation independence. Precomposition is contravariant and coefficient-linear, not scalar conjugation.

Step 4 uses `lem-pod-point-scalar-hom-evaluation`, whose statement explicitly identifies the sections of the specified internal-Hom scalar arrow with f tensor a mapping x tensor b to f(x)ab and explicitly includes rationalization and identity/tower compatibility. `lem-weil-point-sections-scalar-extension` identifies exactly the rational sections maps and their associators, so an arbitrary replacement scalar isomorphism is not being substituted. The tower clause of `lem-pod-perfect-dual-scalar-calculus` identifies the two ring-map paths O_E to E to L and O_E to O_L to L with the direct O_E to L map. All models used have bounded finite-projective terms; C and its dual have the required constructibility by the item's hypotheses and the specified scalar comparison's domain. This proves the square with its named maps.

Step 5 is the direct elementary calculation in the two category definitions, not an invocation of a missing colimit theorem. `def-weil-algebraically-closed-coefficients` and `def-weil-point-fd-qlbar-category` both explicitly describe representatives and equality after further extension. The internal-Hom and point-evaluation definitions specify the conjugated actions. I checked the variance of a_C A_L(u) a_Cprime inverse and of its module counterpart. Substituting step 4 into step 3 over L gives their naturality equation. Passing to a field where representatives agree proves equality in the colimit, and inverse classes work because both inverse equations already hold at the finite stage. No smallness assumption on a new colimit and no field descent theorem is hidden here.

I tested the zero complex, a single copy of O_E in degree zero, a shift of it, and the two-term complex [O_E --varpi_E--> O_E]. For the latter rationalization is zero and both dual comparisons are the unique isomorphism of zero derived objects. The formula for beta and its evaluation signs agrees on shifts; rational coefficients introduce no new sign. The identity E=L and successive extensions multiply coefficients in the same order on both paths, including ramified extensions. The empty or zero sum of localized morphisms gives the zero naturality equation, and torsion in integral Hom does not affect balancing. All these checks preserve the statement as written.

A local read-only dependency walk encountered a standing cycle far below an original statement dependency (the ring-Hom extension differential nodes). This is not a new edge of this delivery; the server delivery checks determine introduced findings against their baseline. No repository or launcher file was edited, and no Lean or compiler tool was used.

## Unfinished work

None in this one-level split. Existing cited unsplit results remain their own stage-1 items. Delivery validation is recorded below when the required command completes.
