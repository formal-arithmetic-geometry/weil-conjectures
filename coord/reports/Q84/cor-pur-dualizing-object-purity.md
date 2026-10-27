# Q84 repair: cor-pur-dualizing-object-purity

## Files written

- `dag/nodes/sec-smooth-purity/cor-pur-dualizing-object-purity.json`: existing statement unchanged; four-step assembly, 2329 proof-text characters instead of 5406.
- `dag/nodes/sec-smooth-purity/lem-pur-oriented-derived-tensor-transport.json`: statement-only, unsplit. Conditional, parameterized oriented derived-tensor transport, with the specified K-flat even-shift formula, resolution independence, naturality and explicit inverse. No Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-diagonal-affine-trace-site-comparison.json`: statement-only, unsplit. Actual diagonal-defined affine-model trace equals ordered Kummer integration, with the ordinary/pro-etale morphism comparison at arbitrary finite coefficient levels. No Mathlib match.
- `citations.json`: full verbatim statements for each citation, so all displayed typed comparison maps are retained.
- `report.md`, `searches.jsonl`, and sandbox-only research scripts/baseline: evidence and reproducible repair. Only node files and this report are delivery content.

## Attachments

None. I searched `lean/WeilConjectures/` for the item tag and notion, and read `EtaleCohomology/Purity/Smooth/Basic.lean` and `lean/Sheaf/Paper/DualizingObjectPurity.lean`. `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_twistShift` at Basic.lean:255 supplies only an ordinary-etale Nonempty isomorphism with a separated structural base; it does not state the item's full-domain specified pro-etale morphism, normalization and two coherence clauses. The project's exact declaration `WeilConjectures.PurityFiniteSetting.dualizingObjectPurity` is still sorried. Neither is an attachment. The upstream `smoothPurityIso` constructor does not state the new tensor lemma's derived representative identification and general parameterized assertion.

## WANTED

None. No SGA source is used.

## What was wrong and what changed

The return required spreading the 5406-character argument over at least two comparable statement-only tasks, retaining the statement and every old argument, with an assembly of at most 3000 characters. Both new nodes have empty proof/proof_deps and null proof_origin, and status unsplit. Their statements are 1701 and 2683 characters. The new arguments are independently available: tensor transport has arbitrary supplied orientation/tensor data and no smooth geometric existence theorem; the trace comparison concerns affine models and actual site/counit comparisons, without proving general smooth purity or either coherence law. The assembly still constructs the requested geometric map explicitly.

The sandbox initially contained only dispatcher brief markers, no delivered JSON/report/searches. I therefore copied the current shared item as the returned baseline, preserving its 5406-character six-step proof exactly in `returned-baseline.json` and below. All existing source/import/blueprint/update/Lean/review metadata and the statement/stmt_deps were retained. There was no previous sandbox research to discard or repeat. The delivery tool rebases the permitted split fields on current origin and preserves maintainer-owned fields. No git command was run in the shared repository.

An inherited documentation discrepancy remains: the definition node `def-pur-smooth-purity-map` says absolutely separated X,Y, while this item's statement, the diagonal theorem, the exchange definition and the actual Lean constructor use the full finite-type domain with only relative separatedness. This was already recorded by the preceding reviewer. The present proof uses the same three-arrow formula on that full domain; it never infers absolute separatedness. I did not modify the definition node or weaken this item. The old unused tool_uses list is maintainer-owned and was retained; the new split_report has no off-unit tool requests.

## Return-point repair and coverage map

- Old Step 1 (761 characters): all of its K-flat representative, degree-r identification, differential, even-sign and naturality work is the task `lem-pur-oriented-derived-tensor-transport`. Its statement requires the actual comparison, not merely existence of some isomorphism.
- Old Step 2 (655): assembly Step 1 still invokes the existing full-domain diagonal theorem and uses exactly its Pi_f. No additional geometric-orientation node duplicates that theorem, no source-affine chart construction is introduced, and the no-absolute-separatedness check is explicit.
- Old Step 3 (804): the tensor lemma carries the parameterized composite, exact inverse and naturality argument. Assembly Step 1 supplies the *geometric* theta and Pi using their original theorems, writes the actual composite, and identifies the specified smooth purity map. The tensor lemma assumes its orientation and theta; it does not prove their existence, geometric normalization or coherence.
- Old Step 4 (1602): the trace lemma carries the substantive affine-model identification, actual adjunction/site morphisms, t_q h_q=1, arbitrary E,n, no ramification-divisibility assumption, rank zero, and exponent independence. Assembly Step 2 retains the separate general-f trace formula and the point that the fixed orientation/tensor/reassociation introduce no extra scalar. Its model domain remains separated, and this is not used to claim a model theorem over nonseparated bases.
- Old Step 5 (828): assembly Step 3 retains the exact exchange composite, the cancellation e^{-1}e, and the arbitrary-v domain. The existing coherence theorem is retained. No identification with a different right-adjoint mate is asserted.
- Old Step 6 (756): assembly Step 4 retains the exact exceptional-compositor order, source comparison, d+e twist and 2d+2e shift. The existing composition theorem is retained.

The entire old argument appears verbatim at the end of this report. It is supporting proof material for the new tasks, not a proof embedded in an unsplit node. No old mathematical work was removed to satisfy the character bound.

## Sources and searches

I read the main-20261015 corollary statement and proof in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-smooth-purity/`, the chapter and original unit record including its model paragraph, and the current main projection-agreement statement/proof. The new tensor lemma extracts the three-arrow proof's resolution/sign and orientation-substitution work; the new trace lemma extracts the corollary's Kummer-normalization sentence and its model explanation. The sources are blueprint material and the derived comparison is an agent extraction, not a claim that a Stacks tag alone proves smooth purity. The existing site-comparison statement locates its supporting infrastructure at Stacks 09AF (`lemma-jshriek-comparison`), 099R (`section-comparison`) and 0B65 (`lemma-transformation-between-functors-and-adjoints`); those tags are not presented as the statement of the new trace lemma. The tensor conventions are the existing nodes for Stacks 012Z and the K-flat tensor construction, not a new invented tensor product.

Before creation I searched the whole DAG (statements and keywords) and blueprint, including `blueprint_refs.py ancestor cor-pur-dualizing-object-purity` and searches `reassociation`, `normalization`, `tensor orientation`, `shift tensor`, `trace comparison`, `Kummer integration`, `even shift`, `orientation substitution`, `affine model trace`. I read the closest candidates listed under Not duplicates. Both new nodes have the exact corollary ancestor, no via nodes, precise proof locations and same_as=[]. No blueprint node already states either complete technical comparison.

All Mathlib searches were actually run through the specified msearch.py, preserved in searches.jsonl, and read. The tensor node records seven runs including two semantic phrasings, valid CommShift2 Loogle, and two source searches. The initial Loogle pattern additionally mentioned the nonexistent identifier CategoryTheory.NatIso: its unknown-identifier answer is retained, not treated as a successful mathematical absence test; the subsequent CommShift2 query ran successfully. LeanSearch initially returned a rate-limit response for the tensor query and is marked unavailable. LeanFinder and Loogle were available. The trace node records six runs, including two semantic phrasings, Loogle, LeanSearch and two source searches; none states the geometric comparison.

The closest Mathlib hits for tensor transport are the chain-level BifunctorShift comparisons (including `commShiftIso_map₂CochainComplex_hom_app`, BifunctorShift.lean:257, read with the instance at 235) and CommShiftTwo structures. The latter assume a coherent shift structure, and the former concern total complexes. They do not by a one-line specialization give the fixed K-flat *derived* representative comparison, descended at every object, plus the asserted oriented parameterized map and inverse. The upstream derived monoidal Shift module explicitly constructs this localization; it is project source, not a Mathlib leaf. The trace searches return formal etaleness, scheme normalization, ring traces and general adjunction formulas; none concerns the diagonal-defined affine purity morphism. There are zero Mathlib leaves in this delivery.

## Not duplicates

lem-pur-oriented-derived-tensor-transport vs lem-pur-total-tensor-signed-coherence: existing node concerns natural chain isomorphisms for total tensors and their signed identities; new node concerns the specified derived comparison on K-flat representatives together with transport of arbitrary supplied orientation/tensor natural isomorphisms and its inverse. Its future proof should reuse the existing chain theorem.
lem-pur-oriented-derived-tensor-transport vs lem-weil-pbc-derived-tensor-shift-descent: existing node descends coherent shift structures and identifies their restrictions to K-flat tensors; new node fixes the even-degree, degree-zero-sheaf component and the *oriented* parameterized composite and inverse. The existing descent theorem is useful proof material, not a second node for shifts alone.
lem-pur-oriented-derived-tensor-transport vs def-pur-smooth-purity-map: existing node defines a particular geometric map; new node is a theorem about derived representative compatibility, inverse and naturality for arbitrary supplied omega, Pi, theta and parameter category. It neither supplies diagonal purity nor claims the normalization/coherence clauses of this item.
lem-pur-oriented-derived-tensor-transport vs lem-sfb-ringed-derived-monoidal-comparisons: existing theorem concerns monoidality and composition of ringed-topos pullback; new theorem has no ringed-topos morphism and transports given orientations through a derived tensor and even shift.
lem-pur-diagonal-affine-trace-site-comparison vs lem-pur-projection-purity-agreement: existing theorem identifies diagonal gamma with an ordered composite Gamma of affine-line adjuncts; new theorem identifies the *counit composite trace*, its single coefficient-first integration expression and its actual etale/pro-etale comparison for all finite coefficient stages.
lem-pur-diagonal-affine-trace-site-comparison vs lem-pur-vector-integration-site-comparison: existing theorem compares the independently integration-defined maps on the two sites, their traces and adjoint transposes; new theorem identifies those maps with the trace and morphism actually defined from the *diagonal orientation*.
lem-pur-diagonal-affine-trace-site-comparison vs thm-pur-trace-normalization-transitivity: existing statement gives transitivity/general transports and the unit trace on structural geometric affine fibres; new statement identifies actual affine-model morphisms over arbitrary separated finite-type S, for every finite-Tor K and all E,n, with the specified site/source/counit comparisons.
lem-pur-diagonal-affine-trace-site-comparison vs det-sp-trace-basic: existing statement supplies naturality and unit-coefficient affine-fibre normalization using the later transported purity theorem; new statement identifies the earlier diagonal-defined map at arbitrary K and its two-site comparisons without invoking that later theorem.
lem-pur-diagonal-affine-trace-site-comparison vs lem-pur-finite-universal-smooth-trace: existing lemma is a finite-free coefficient-extension comparison at n divisible by the ramification index; new lemma is a site/diagonal-to-integration comparison at every n, without this divisibility.
lem-pur-diagonal-affine-trace-site-comparison vs lem-pur-etale-affine-projection-coefficient-mate: existing lemma compares change-of-coefficient mates on the ordinary site; new lemma compares diagonal and integration definitions and the two sites at one coefficient ring.
lem-pur-diagonal-affine-trace-site-comparison vs lem-pur-tower-trace-purity-comparison: existing lemma concerns integral coefficient towers and scalar rationalization; new lemma stays at finite coefficients and does not assert any completed or rational comparison.

## Review by Q84

I reviewed the return as a mathematical extraction, not a change of theorem. The two tasks are of comparable scope: the first must check the concrete K-flat comparison and its localization/naturality before its formal inverse calculation; the second must check which actual model map is transposed, its coefficient-first source, and how the compact-support/counit/site identifications carry the trace. Both are statement-only because other workers are to prove them. The general categorical construction by itself is short, but it is deliberately joined to the actual derived representative-identification argument of old Step 1 rather than introduced as an elementary standalone inverse-of-composite node.

For assembly Step 1 I opened all five cited statements. The twist definition says M(d)=M tensor^L A_X(d) and places the finite twist in degree zero. The diagonal theorem explicitly has finite-type X,Y in the exceptional-image domain and only relative separatedness; its conclusion supplies exactly omega_f to A_X(d)[2d]. Cohomological smoothness supplies the *canonical* tensor map and its invertibility for the given Dctf K. The new transport statement has precisely the type of the required a_M and three-arrow map, and supplies its inverse/naturality. The purity-map definition specifies the same orientation and arrow order. Parameterizing by Dctf(Y,A) restricts the already natural functors/maps; no tensor formula is asserted for arbitrary unbounded K. The new transport lemma itself only assumes theta for its chosen parameter functors.

For assembly Step 2 I opened the new affine trace statement and the smooth-trace definition. The former gives the actual diagonal map's counit composite and site equations, not merely existence of isomorphic objects or a Kummer class with the right image. Its separatedness is checked because this step invokes it only for affine models over separated S. It applies at all E,n and any annihilating exponent, so the old prohibited restriction e|n does not return. The trace definition explicitly defines the coefficient-valued epsilon composed with Rf_!(gamma), including the unit case. The step claims no extension of the model lemma to a nonseparated base. The fixed Pi in Step 1 is the original canonical diagonal map, so this model normalization is not attributed to a newly constructed chart orientation.

For assembly Step 3 I opened the exchange definition and base-change coherence theorem. The definition displays e' composed with b composed with e^{-1}, and explicitly allows arbitrary v. The coherence theorem has precisely this square. Cancellation is elementary once Step 1 supplies invertibility. The definition's statement also provides the finite-Tor constructible pullback domain, so there is no unrecorded assumption that v is flat or smooth. This is the defined smooth exchange, never a different mate.

For assembly Step 4 I opened the composition theorem. It states gamma_gf equals shifted Lf*gamma_g followed by gamma_f at Rg!K followed by c^{-1}. The source is canonically identified with the (d+e)[2d+2e] twist/shift, and the exceptional compositor has exactly the direction used. This same specified map was constructed in Step 1; no mere-existence purity statement is substituted.

I read the new tensor source (current corollary proof) against its original Steps 1 and 3, and the trace source (current corollary normalization sentence and model paragraph) against old Step 4 and both existing comparison statements. I corrected the old trace prose into a typed claim on actual morphisms, with beta's source explicitly named, and included arbitrary pro-etale K for the trace equality but only etale-origin K=C_SK0 for the displayed C_V(eta^e) formula. No ordinary-site expression is applied to an intrinsic pro-etale K without a witness.

Edge checks: d=0 makes a_M the zero-shift identification and gives the identity model adjunction; M=0 and K=0 give their unique maps; the empty scheme causes no exception; arbitrary n not divisible by e is explicitly allowed; no A-flatness over Z/ell^r is used; nonseparated finite-type X,Y are allowed in Step 1 and the exchange square; the separatedness of S in the trace task is not silently propagated to those X,Y. In the tensor task T need not be flat, since a K-flat resolution in the other variable computes the derived tensor. Evenness is indispensable for the *identity* representative formula; an odd shift has the usual signed comparison and is not included. Pi is independent of the parameter, while theta is assumed natural, so the claimed naturality has exactly its needed hypotheses.

I checked B through E: self-contained objects, definition dependencies, single TeX escaping, explicit provenance, no invented search results, no duplication of existing orientation/coherence theorems, every non-elementary assembly fact cited by statement and covered by citations.json, no off-route proof tool, no extra geometric hypothesis or weakening. Each assembly step is under 2000 characters, and the total is under 3000. Any nontrivial remaining proof work has either an existing node or one of the two new tasks. The baseline statement and its dependencies were checked byte-for-byte unchanged. Mechanical server checks and delivery results are recorded below when completed.

## What is unfinished

No requested stage-1 repair work is intentionally omitted. The two new proof tasks remain unsplit by instruction. No Lean was written and no compiler, Lake, local DAG checker or patched launcher tool was used.

## Required validation

The required server dry run completed successfully on 2026-10-22: `deliver.py Q84 cor-pur-dualizing-object-purity --no-push` printed `OK (not pushed)` at 58b7ca956ce with preflight passed, including the server DAG/split checks. The final report update is validated once more before direct delivery; the push result and final commit are reported by deliver.py. No compiler/build was run.

## Preserved returned proof (verbatim step texts)

### Original Step 1

Put $M=Lf^*K$ and $T=\Lambda_X(d)$. By [def-coefficient-twists-detailed],
$M(d)[2d]=(M\otimes^L T)[2d]$. Compute the tensor using a K-flat
representative $P\to M$ as in [def-weil-derived-tensor]. The degree-$r$
terms of both $(P\otimes T)[2d]$ and $P\otimes T[2d]$ are
$P^{r+2d}\otimes T$; their differential is $d_P\otimes1$ on both sides,
since $T$ is in degree zero and $(-1)^{2d}=1$. These are the total-tensor
and shift conventions of [def-pc-tensor-complex-sheaves] and
[def-weil-abstract-derived-category]. The identity on these terms thus
gives the canonical reassociation
$a_M:M(d)[2d]\xrightarrow{\sim}M\otimes^L T[2d]$.
The calculation is functorial in $P$ and $T$, so is the displayed
identification on derived objects, with no extra scalar or sign.

Uses: def-coefficient-twists-detailed, def-weil-derived-tensor, def-pc-tensor-complex-sheaves, def-weil-abstract-derived-category

### Original Step 2

Apply [thm-pur-diagonal-dualizing-object] to the given $f:X\to Y$. Its statement assumes precisely finite-type $k$-schemes in the exceptional-image domain and a smooth separated morphism of pure relative dimension $d$; it does not assume that $X$ or $Y$ is separated over $k$. It supplies the canonical isomorphism
$$\Pi_f:\omega_f=Rf^!\Lambda_Y\xrightarrow{\sim}\Lambda_X(d)[2d].$$
Use this specified map itself. In particular, no second orientation is constructed on source-affine charts and no equality between two chart constructions is required. The symbol $\Pi_f$ here is exactly the diagonal-purity isomorphism named in [def-pur-smooth-purity-map].

Uses: thm-pur-diagonal-dualizing-object, def-pur-smooth-purity-map

### Original Step 3

Put $M=Lf^*K$. By [thm-pur-cohomological-smoothness], the specified canonical tensor map
$$\phi_{f,K}:M\otimes_A^L\omega_f\xrightarrow{\sim}Rf^!K$$
is an isomorphism for the given smooth separated $f$ and bounded constructible finite-Tor $K$. Define
$$\gamma_{f,K}=\phi_{f,K}\circ(1_M\otimes\Pi_f^{-1})\circ a_M.$$
The arrow $a_M$ is Step 1; the middle arrow uses the inverse of the very map of Step 2. Tensoring the two inverse equations for $\Pi_f$ gives inverse equations for this middle arrow. Thus all three arrows are invertible, and so is their composite. This is exactly the arrow order and the specified orientation in [def-pur-smooth-purity-map]. It is natural in $K$: reassociation is functorial by Step 1, $\Pi_f$ is fixed independently of $K$, and the canonical tensor map is natural in $K$.

Uses: thm-pur-cohomological-smoothness, def-pur-smooth-purity-map

### Original Step 4

For normalization, use a statement about the specified smooth purity maps. On a separated finite-type base $S$, [lem-pur-projection-purity-agreement] states that for $p_d:\mathbf A^d_S\to S$ the map defined using the diagonal orientation equals $\Gamma_{p_d,K}$. The latter is the ordered composite of adjoint transposes of the restricted projective-line Kummer traces, for every $A=A_{E,n}$; for $d=0$ it is $1_K$. Thus the model normalization belongs to the map $\Pi$ used in Step 2, rather than to a separately constructed orientation. The lemma is used only on its stated separated-base model domain, not as a theorem about arbitrary nonseparated bases.

The actual finite-level site comparison [lem-pur-vector-integration-site-comparison] gives $t_q^ph_q^p=1$ for the prescribed Kummer class, identifies the restricted projective-line traces and their integration adjoint transposes on the two sites, and states independence of the annihilating exponent $r$. These statements apply to every $E,n$ and require no divisibility by the ramification index. The reassociation of Step 1 adds no sign, and Step 3 uses the fixed diagonal orientation and fixed tensor transformation, so introduces no new scalar choice. Finally [def-pur-smooth-trace] defines the trace of these very maps by
$$\operatorname{Tr}^{\mathrm{sm}}_{f,K}=\epsilon_{f,K}\circ Rf_!(\gamma_{f,K}).$$
Consequently the twist $d$, shift $2d$, and trace are fixed with the stated Kummer normalization. This uses no property of a new source-affine construction. It also makes no specialization of a result restricted to $E=\mathbf Q_\ell$.

Uses: lem-pur-projection-purity-agreement, lem-pur-vector-integration-site-comparison, def-pur-smooth-trace

### Original Step 5

For a Cartesian square with $f'$ the base change of $f$ and bottom
map $v:Y'\to Y$, put $e=Lu^*\gamma_{f,K}$,
$e'=\gamma_{f',Lv^*K}$, and let $b$ be the canonical pullback-and-twist
identification from the source of $e$ to the source of $e'$. By the
explicit statement of [def-pur-smooth-pullback-exchange],
$\operatorname{Ex}^{!,\mathrm{sm}}=e'\circ b\circ e^{-1}$.
Consequently
$$
\operatorname{Ex}^{!,\mathrm{sm}}\circ Lu^*\gamma_{f,K}
=e'\circ b\circ e^{-1}\circ e=e'\circ b,
$$
which is precisely the square of [thm-pur-smooth-base-change-coherence].
The latter statement applies to arbitrary $v$ between the finite-type
schemes here, with no flatness, smoothness or etaleness condition on
$v$. This is compatibility for the chapter's defined smooth exchange;
it makes no identification with a different right-adjoint mate.

Uses: def-pur-smooth-pullback-exchange, thm-pur-smooth-base-change-coherence

### Original Step 6

Let $g:Y\to Z$ also be smooth separated of pure relative dimension
$e$, with $Z$ in the same scheme domain, and let $K\in D^b_{ctf}(Z,\Lambda)$.
The maps constructed in Step 3 are the smooth purity maps to which
[thm-pur-composition-coherence] applies. Its displayed identity is
$$
\gamma_{gf,K}
=c_{g,f}^{-1}\circ\gamma_{f,Rg^!K}\circ
Lf^*(\gamma_{g,K})(d)[2d],
$$
under its canonical identification of the source with
$L(gf)^*K(d+e)[2d+2e]$. This proves composition compatibility for the
specified maps, with the order of exceptional pullbacks fixed by
$c_{g,f}:R(gf)^!\cong Rf^!Rg^!$. In particular the twists add as $d+e$
and the even shifts add as $2d+2e$; no inference from mere existence of
isomorphisms, or from tensor invertibility alone, is used.

Uses: thm-pur-composition-coherence
