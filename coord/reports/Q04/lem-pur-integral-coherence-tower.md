# Stage-1 re-split of lem-pur-integral-coherence-tower

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-integral-coherence-tower.json`: existing statement, unchanged; five assembly steps (2573 characters) instead of the former six steps (4998 characters).
- `dag/nodes/sec-smooth-purity/lem-pur-quotient-expression-kflat-normalization.json`: statement, status `unsplit`; no Mathlib match. This independently queueable argument constructs simultaneous flat-term K-flat representatives and identifies the actual derived transition-adjoints for finite quotient expressions. It has no proof steps or proof dependencies.
- `citations.json`: one verbatim statement quotation for each node used in each assembly step.

## Attachments

None. The project module `lean/Sheaf/Paper/IntegralCoherenceTower.lean` states `WeilConjectures.IntegralCoherence.integralCoherenceTower` at line 308, but its proof ends in `sorry` at line 331. Searches by the blueprint tag and by quotient/K-flat/normalization notions in `lean/WeilConjectures/` did not give a finished declaration of the item or of the new simultaneous expression result. The existing Lean attachment is preserved, and no Lean file is written or compiled.

## WANTED

None. All sources used here are present in the read clone.

## What was wrong and what changed

This is the human's deliberate 2026-10-21 re-split of an already reviewed item, not a claim that its prior review or Lean attachment was stale. The 2009-character first step carried the model-construction argument separately from the remaining coherence argument. That construction now has its own self-contained theorem, with an explicit expression grammar, coefficient maps and actual transition-adjoints. It is larger than a reformulation of normalizedness: it supplies the flat-term K-flat chain representatives of arbitrary mixed finite expressions and identifies their localization and actual scalar-adjunction representatives. In contrast, the old item's associativity, symmetry, two unit equations, composition, derived-limit transport and coherent reduction remain assembled in the parent.

The item's statement and statement dependencies are byte-for-byte equal as JSON values to the live item read at the start. No target or notion is weakened. No new SGA reference is introduced. The new node inherits `sec-smooth-purity` and `sk-def-purity-conv`; neither chapter nor unit is changed.

The new theorem's assertion is strictly smaller than the item. It contains no tensor-pullback comparison c, no coherence diagrams, no inverse limit, and no assertion about completed operations or their finite reductions. Its additional generality (a finite list of inputs and finite expression syntax) expresses the induction already implicit in the former model-construction step, including units and intermediate tensor/pullback objects. This is not moving the parent theorem to another name.

## Preservation of every former argument

| Former step | Where its work now resides |
|---|---|
| 1: actual quotient transitions, K-flat change of rings, derived adjoint association, identity and cocycle, total tensors, exact constant pullbacks, K-flat pulled models, and normalized tensor/pullback closure | New `lem-pur-quotient-expression-kflat-normalization`; applied in assembly step 1. The full original argument is retained below as a handoff, not silently discarded. |
| 2: insertion comparison, naturality and triple reassociation with total differential | Assembly step 2, using the existing full cochain comparison statement. |
| 3: Koszul symmetry, both action unitors, adjunction-normalized composition | Assembly step 2, using the same existing statement, including its displayed composition equation. |
| 4: compatibility with every quotient transition and strictness before localization | Assembly step 3; coefficient-change equations handle c, and scalar multiplication formulas explicitly check the other structural maps. |
| 5: functorial inverse limit, equality and inverse preservation, identification of vertices and all structural arrows | Assembly step 4, citing the strict-tower derived-limit and coherent substitution statements. |
| 6: coherent counits and recovery of every finite equation, including transitions | Assembly step 5, citing effectivity and substitution. |

### Full extracted argument for the next worker

The following is the former first step, retained verbatim. It is a proof plan for the new unsplit theorem, not a proof included in that theorem's statement:

For each m≥n, the quotient maps B_{Y,m}→B_{Y,n} and their pullbacks to X and Z give the actual transitions of P_m,Q_m,H_m and of the unit systems. Since P,Q,H are K-flat with flat terms over R_Y, termwise change of rings along R_Y→B_{Y,m} gives K-flat complexes P_m,Q_m,H_m of B_{Y,m}-modules with flat terms [lem-pur-kflat-change-of-rings]; the unit complexes B_{W,m}[0] are of this form with P=R_W. Hence derived change of rings along B_{Y,m}→B_{Y,n} is computed termwise on them [lem-pur-derived-change-of-rings], and the transition-adjoint α_{m,n} is the canonical associativity isomorphism (P⊗_{R_Y}B_{Y,m})⊗_{B_{Y,m}}B_{Y,n}≅P⊗_{R_Y}B_{Y,n}, and similarly for Q,H and the units. Associativity of tensor and q_{r,n}=q_{m,n}q_{r,m} give τ_{n,n}=1 and the cocycle identity, so these strict quotient towers, viewed in Tow_{R_Y} through Res_n, are normalized DVR towers. By the K-flat total tensor model [lem-pur-kflat-total-tensor-model], Tot(P_n⊗_{B_{Y,n}}Q_n) (and the triple tensors) are K-flat with flat terms and represent the derived tensor of the levels; by exactness of the pro-etale module inverse image along the constant-ring identification f^{-1}B_{Y,n}≅B_{X,n} [prop-weil-pbc-proetale-constant-exact], the termwise f_n^*P_n and h_n^*f_n^*P_n represent the derived pullbacks, and they are again K-flat with flat terms [lem-weil-pbc-ringed-topos-kflat-pullback], so the total tensors of pulled-back complexes also represent derived tensors [lem-pur-kflat-total-tensor-model]. So the strict towers in the statement are models of the fiberwise derived tensor and system inverse image, and the normalized tensor/pullback closure lemma applies: it identifies the transition-adjoint of a tensor with the tensor of the transition-adjoints after the strong monoidal scalar-extension comparison, and the transition-adjoint after pullback with the pulled-back transition-adjoint. Both are therefore invertible, and the total tensors and termwise pullbacks in the statement are normalized coherent systems.

For the new theorem's finite-expression formulation, induct on the expression grammar stated there. The generator computation is exactly the displayed scalar-adjunction map and its insertion inverse. The zero-input case consists of coefficient units. For each tensor constructor use `lem-pur-kflat-total-tensor-model` for K-flatness, flat terms and the derived representative, and `lem-pur-system-normalized-tensor-closure` for the actual transition-adjoint formula. For each pullback constructor use finite constant-coefficient exactness, `lem-weil-pbc-ringed-topos-kflat-pullback`, and the pullback clause of the same closure statement. Compose the strict transition maps already supplied by the children. All unit and cocycle equalities are identities of the actual quotient maps under these formulas, not unrelated chosen isomorphisms. Successive scalar association can also be cited as `lem-sfb-successive-derived-quotient-normalization`. These are existing nodes to use when that new item is split; this delivery deliberately leaves its proof empty.

## Searches

The actual Mathlib queries and returned names are recorded in the new node and `searches.jsonl`. LeanFinder was run with two distinct phrasings, plus Loogle, LeanSearch, and two source-grep queries through the required `msearch.py` command. All services answered. The first semantic search returned ordinary Noetherian adic-completion flatness and module tensor equivalences, which have no sheaf-complex quotient expressions or actual derived transition-adjoints. The second returned algebra presentation tensor models and module flatness criteria. LeanSearch returned scalar extension for ordinary modules, flat ring maps, and quotient-to-derived-category localization, not the varying-coefficient sheaf construction. Loogle's name fragment KFlat returned only a Lean structure constructor utility. The homological source grep found no KFlat/tower match; the category-theory grep found monoidal products in over categories, where tensor is a categorical pullback. I read those displayed declarations: these concern different objects and provide no exact match or one-line specialization. The new node is consequently unsplit, not a Mathlib leaf.

Before creating the new id I searched the whole DAG for quotient/K-flat/expression and normalization terminology, and read the nearby candidate statements. Blueprint searches included `quotient K-flat`, `normalized tensor`, `integral coherence`, `quotient tensor`, `07A2`, `0G7E`, `flat-term`, and `normalized quotient`; no blueprint node states the new result. The existing normalization, scalar-change, cochain comparison, completed substitution and ambient-operation nodes are reused rather than recreated. The `ancestor` command returned `def-weil-frobenius-coefficient-twists`; the new node records the intermediate ancestry through this item and `lem-pur-derived-pullback-tensor-iso`. The current blueprint coefficient-twists text is only the ancestry location; the actual model/coherence construction is the explicitly agent-formulated refinement of the Stacks constructions and existing split, not a theorem falsely attributed to the current short Frobenius statement.

## Review by Q04

I read delivery-errors B through E against the item, the new statement and their sources. For the item I read Stacks `sites-cohomology.tex`, Tag 07A4 (`lemma-pullback-tensor-product`, proof at lines 3684ff), including the flat-term K-flat total model and its ordinary tensor comparison; and Tag 0941 (`lemma-derived-limit-is-ok`, lines 5067ff), including the K-injective strict-system computation. For the new node I read Tag 0G7E (`lemma-pullback-K-flat`, lines 3508ff), which explicitly requires K-flatness and flat terms and preserves both, and Tag 07A2 (`lemma-tensor-product-K-flat`, lines 3060ff), whose reassociation proof works for unbounded total tensors. I checked their tags against `literature/stacks-project/tags/tags`. I also read the current main-20261015 unit conventions, chapter/unit records, blueprint ancestry text, the live item's full proof, and the attached Lean theorem/docstring. The proof origin remains agent-written: the strict simultaneous normalization is a refinement of these sources, not quoted verbatim as a Stacks theorem.

Assembly step 1 uses exactly the new theorem's conclusions: flat-term K-flat representatives of every finite expression, actual semilinear transitions, the strict identity and cocycle, and invertibility of their actual derived adjoints. The parent supplies its hypotheses with r=3 and inputs P,Q,H; all three schemes have the invertible prime required and both morphisms have the stipulated direction. Units and both tensor parenthesizations belong to the stated grammar. There is no appeal to the future proof of the new node.

Assembly step 2 uses the statement of `lem-pur-cochain-pullback-tensor-coherence`: it explicitly gives the insertion map and multiplication inverse, naturality, reassociation, signed symmetry and action unitors, and the displayed composition law with exactly the adjunction-normalized a_K. I checked its source/target for f:Y-source pullback to X and h:X-source pullback to Z; both sides start at (fh)*Tot(P tensor Q) and end at the tensor of h*f*P and h*f*Q. The coefficient rings are B at the same positive level. No assertion is taken only from that node's proof.

Assembly step 3 uses that node's explicit coefficient-change equations and final strict-quotient sentence for c. I corrected the old broad assertion that all structural arrows were covered by the final sentence alone: the parent's step now explicitly writes the reassociation, signed interchange and multiplication formulas and checks compatibility through q(st)=q(s)q(t). Pullback composition is the inverse-image compositor followed by the scalar-association formula that the cited statement specifies; functorial inverse image and the same product identity give its transition square. The inverse of a strict isomorphism commutes with transitions by multiplying its transition square on both sides by the inverses. These small computations use only the displayed structural formulas, not an uncited general coherence theorem.

Assembly step 4 uses the exact functor Rlim in `lem-weil-pbc-ringed-strict-tower-homotopy-limit`; preservation of equality, identities and composition gives preservation of inverse pairs. I read `lem-pur-completed-operation-tower-substitution` in full: its last paragraph covers finite typed expressions and explicitly identifies the limits of reassociators, action unitors, Koszul symmetry and the pullback compositor, rather than merely identifying endpoint objects. This supplies exactly the conjugations used in step 4.

Assembly step 5 uses the full statement of `lem-coef-normalized-dvr-effectivity`, whose counits are coherent isomorphisms for every normalized tower without boundedness or constructibility. I checked normalizedness comes from step 1 for every vertex. Substitution explicitly says the coherent reduction is the whole system including every quotient transition and that the identifications are natural in input morphisms. Thus naturality of the counits identifies each reduced arrow, and consequently both sides of each equation, not just the objects.

For B1–B9 the new statement introduces all schemes, rings, input complexes, indices, expression constructors, transitions, localization and scalar adjoints; each named notion cites an existing definition or construction. It contains no proof sketch, has empty proof/proof_deps and null proof_origin, and uses ordinary single TeX escapes. Its full statement is not an existing cochain, normalized-closure or ambient-completion theorem: the distinctions are listed below. All new searches are copied from their real log records. The item is not a Mathlib candidate because the attached project theorem is a sheaf-tower/coherence construction with an open proof, and its existing recorded searches remain untouched.

For D1–D5 the new result extracts only the model construction; the finite and integral diagrams remain assembled with the existing independent coherence, substitution and effectivity results. No new node simply states the whole item or an isolated coherence clause. There is no circular derivation: the new theorem's statement dependencies use older ringed tensor/scalar infrastructure and definitions, not this parent. The source's small omitted scalar-transition calculations are explicitly present in assembly step 3 and in the extracted argument above. No remaining non-elementary assembly step exceeds 2000 characters.

For E1–E7 I checked m=n (the adjoint is the tensor unitor and t is identity), r>=m>=n (both scalar associations multiply the same images of coefficients), r=0 (unit-only expressions), zero complexes, and degree-zero complexes. Tensor units are free rank one over their own coefficient rings. For the signed symmetry p=q=0 the sign is 1, and for p=q=1 both quotient routes retain sign -1. Identity scheme maps satisfy the same functorial formulas, including the empty scheme. For ramified E and m>n, the quotient ring map need not be flat: the models are K-flat over the level source ring, so derived reduction is still computed correctly and no quotient flatness was used. Arbitrary unbounded P_i remain allowed because total tensor uses direct sums and the K-flat total-model statement explicitly covers both-sided unbounded complexes. In particular I never assume f^(-1)R_Y=R_X for completed coefficients; only the finite constant-ring identifications enter the pullback adjoint formula. I found no statement dispute or departure from the authorized purity-conventions route.

The old accepted off-route tool_uses field is preserved as maintainer-owned data. The active assembly's generic strict-limit and effectivity tools are also recorded in split_report.tool_uses. The new theorem's proof is intentionally left for a later stage-1 worker, and that worker can use the full extracted argument above with the cited older lemmas.

## Unfinished work

The new statement-only theorem remains to be split and proved. That is the requested parallel-work boundary. This delivery changes no Lean proof; the existing integralCoherenceTower sorry is still present.

## Not duplicates

lem-pur-quotient-expression-kflat-normalization vs lem-pd-module-ringed-topos-derived-comparison: the existing statement concerns Module-object and ringed-topos derived tensor comparison; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-completed-adic-koszul-kflat: the existing statement concerns K-flatness of the actual completed exterior Koszul complexes; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-constant-derived-normalization-universal: the existing statement concerns Constant derived realization preserves universal coefficient arrows; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-derived-scalar-extension-local-systems: the existing statement concerns Coherent localized derived scalar extension and comparison; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-diagram-kflat-replacements: the existing statement concerns Objectwise K-flat replacements in strict diagram categories; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-flat-coefficient-reduction-adjunct: the existing statement concerns Finite scalar comparison preserves derived reduction adjuncts; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: the existing statement concerns Derived pullback computes K-flat tensor representatives; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-normalized-derived-isomorphism-transport: the existing statement concerns Universal normalization and evaluation of source-site local Isom sheaves; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-pulled-reduction-normalization-comparison: compares a fixed pair of pulled reduction towers and successive scalar normalization; the new result supplies all finite tensor/pullback expression models and their actual strict transition-adjoints.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: the existing statement concerns Common quotient reduction of the geometric scalar comparison; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-ringed-pullback-preserves-kflat: the existing statement concerns Ringed pullback kflat; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: the existing statement concerns Canonical tensor comparison unit existence; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: the existing statement concerns Canonical tensor comparison unit uniqueness; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: the existing statement concerns Derived tensor comparison for arbitrary ringed topoi; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-ringed-topos-acyclic-kflat-pullback: the existing statement concerns Ringed-topos pullback in the acyclic K-flat case; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-ringed-topos-kflat-pullback: the existing statement concerns Ringed-topos pullback preserves flat-term K-flat complexes; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution: the existing statement concerns A flat resolution whose ringed-topos pullback is K-flat; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: the existing statement concerns Tensor pullback adjoint to a supplied ringed-topos module direct image; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs def-coef-semilinear-system-models: defines generic system models and representative normalizations; it does not prove existence or normalizedness for the specified mixed quotient expressions.

lem-pur-quotient-expression-kflat-normalization vs lem-pod-point-extension-kflat: the existing statement concerns K-flatness of the point extension of a flat-term module complex; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-sf-open-operation-models: the existing statement concerns Open operation comparisons with fixed tensor models and right square; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-sf-open-pullback-support: the existing statement concerns Derived pullback preserves open support; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-sf-scalar-pullback-composition: the existing statement concerns Composition coherence of normalized scalar/pullback comparisons; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-weil-etale-native-tensor-pullback: the existing statement concerns Native unbounded derived tensor commutes with etale inverse image; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-sfb-constant-module-kflat: the existing statement concerns Constant realization preserves flat-term K-flat complexes; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-sfb-constant-realization-derived-scalar-extension: the existing statement concerns Derived constant realization commutes with derived scalar extension; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-sfb-flat-term-kflat-functor: the existing statement concerns Flat-preserving colimit functors preserve flat-term K-flat complexes; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-sfb-kflat-scalar-comparison-normalization: the existing statement concerns Representative and adjunction normalization of scalar pullback comparison; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-sfb-ringed-site-point-kflat-resolution: the existing statement concerns K-flat resolution with K-flat stalk; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-sfb-scalar-extension-kflat: the existing statement concerns Scalar extension preserves all K-flat sheaf complexes; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-sfb-successive-derived-quotient-normalization: only successive scalar extension and its units are compared; the new result includes strict mixed expression models and their tensor/pullback recursive actual adjoints.

lem-pur-quotient-expression-kflat-normalization vs def-pur-change-of-rings-complex: the existing statement concerns Termwise change of rings of a cochain complex; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs def-pur-derived-constant-pullback-comparison: the existing statement concerns Canonical derived constant-sheaf pullback comparison; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs def-pur-etale-scalar-pullback-iso: the existing statement concerns Canonical derived scalar and pullback isomorphism; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs def-pur-open-coefficient-normalizations: the existing statement concerns Exact-pullback and open-unit coefficient normalizations; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-exc-proetale-constant-support-projection: the existing statement concerns Constant-coefficient projection for compact support; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-fix-tensor-pullback-square: the existing statement concerns Tensor inverse-image comparisons commute around an open square; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-coefficient-pullback-comparison: the existing statement concerns Canonical inverse-image coefficient comparison; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-etale-scalar-pullback-existence: the existing statement concerns Existence of normalized derived scalar/pullback comparison; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-etale-scalar-pullback-uniqueness: the existing statement concerns Uniqueness of normalized derived scalar/pullback comparison; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-integral-ambient-operation-models: compares ambient completion with completed pullback/tensor and their quotient augmentations; the new result proves chain-level K-flat expression models and actual normalized adjoints before any completion.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-integral-operations-well-defined: proves descent under quasi-isomorphisms and independence of resolution of two completed operations; the new result is the pre-completion flat-term K-flat/normalization construction for finite expressions.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-kflat-change-of-rings-independent: the existing statement concerns Change of rings preserves K-flat complexes with flat terms in independent universes; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-kflat-change-of-rings: only K-flatness and flat terms after one ring change are supplied; the new result supplies strict towers, actual transition adjoints and mixed iterated tensor/pullback models.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-kflat-total-tensor-model: only a single total tensor and its reassociation are supplied; the new result constructs the entire quotient-expression tower and identifies the actual derived adjoints at every coefficient transition.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-scalar-tensor-pullback-normalization: the existing statement concerns Scalar/tensor pullback normalization on a K-flat representative; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-varying-ring-tensor-comparison: the existing statement concerns Normalized tensor comparison for one varying-ring inverse image; it does not construct the actual strict quotient towers of every finite mixed expression or identify their derived transition-adjoints as in the new result.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-system-normalized-tensor-closure: closure assumes already normalized derived systems and gives the derived adjoint formulas; it does not construct the actual quotient generator adjoints or supply the simultaneous flat-term K-flat chain representatives of finite mixed expressions.

lem-pur-quotient-expression-kflat-normalization vs lem-coef-normalized-dvr-kflat-reduction-model: the existing result supplies a K-flat representative of one input and comparison of its derived scalar units with its reduction tower; it does not model all mixed tensor/pullback expressions, prove their flat terms or identify their actual recursive adjoints.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-integral-coherence-tower: the parent asserts the four explicit coherence diagrams, strict structural arrows, completed integral equations and coherent reductions; the new result supplies only their input expression models and normalized transitions.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-completed-operation-tower-substitution: substitution assumes normalized input systems and identifies expressions after completed operations and limits; it does not construct the specified quotient chain models from flat-term K-flat integral inputs.

lem-pur-quotient-expression-kflat-normalization vs lem-pur-cochain-pullback-tensor-coherence: the existing result gives ordinary cochain comparison and coherence equations for arbitrary input complexes; it neither proves their K-flatness nor proves that their actual quotient expression towers are normalized derived systems.
