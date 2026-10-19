1. Files written:

- `dag/nodes/sec-six-functors/lem-weil-closed-costalk-duality.json` — item split; no new nodes.
- `citations.json` — verbatim statement quotes for the proof step.

2. Attachments: none.

3. WANTED: none.

4. What was wrong in the imported item/proof: the original middle arrow
`i_*N ⊗ᴸ K ≅ i_*(N ⊗ᴸ i^*K)` was attributed to the definition of the
open–closed recollement and an unstated stalkwise argument. That definition
only names the recollement data; it does not state this projection formula.
I rewrote the chain with `Ri_!` and cited `prop-functor-package`: its proper
coincidence clause identifies `Ri_!` with `Ri_*` for the closed immersion,
and its compact-support projection-formula clause gives the middle
isomorphism. The tensor/Hom and exceptional-adjunction arrows are exactly
what the two cited operation definitions provide. The existing generic node
`lem-trf-exceptional-internal-hom-exchange` was checked and recorded in
`blueprint.same_as`; its finite-coefficient admissible statement is a related
specialization, not an exact replacement for this all-stage item.

5. What I could not finish: nothing. No Lean source declaration with the
item's exact statement was found; no new node was necessary.

## Review by Q43

I read the imported item, its blueprint source/place, the unit and chapter
records, and the operation definitions
`def-weil-derived-pullback-tensor-hom` and
`def-weil-exceptional-inverse-image`, plus `fix-lem-tensor-adjunction` and
`fix-prop-adjunctions`. The two fix nodes provide the tensor–exceptional Hom
exchange and the exceptional adjunction in the exact domains used by the
chain. I also read `prop-functor-package` clause (3), which says proper
direct image agrees with compact-support direct image, and clause (5), which
states the compact-support projection isomorphism with its hypotheses. For
the single proof step I checked each displayed Hom arrow against those
statements: the tensor–exceptional exchange is the specialization of
`fix-lem-tensor-adjunction`, the exceptional transpose uses
`fix-prop-adjunctions`, the middle arrow uses clause (5) after clause (3),
and the final identification uses `ω_Z = Ri^!ω_T`; naturality follows from
the same adjunction maps. I removed the unsupported recollement citation,
added the operation definitions to `stmt_deps`, and declared the three
generic fix/package nodes as off-unit tool uses because they supply the
formal adjunction and projection infrastructure.
Mathlib searches were run for the item: LeanFinder and Loogle returned only
generic category/scheme adjunction declarations, grep found no relevant
Verdier/exceptional-Hom theorem, and LeanSearch was unavailable; these
results are recorded in the delivery search log.

## Not duplicates

lem-weil-closed-costalk-duality vs lem-trf-exceptional-internal-hom-exchange: the existing node is a finite-coefficient admissible-morphism exchange `RHom(c^*M,c^!N) ≅ c^!RHom(M,N)`, while this item is the all-stage closed-immersion Verdier-dual comparison `Ri^!D_TK ≅ D_Zi^*K` and explicitly identifies dualizing objects by `ω_Z = Ri^!ω_T`.

## Second reading by Q43

I independently opened the original blueprint item (order 2125), its unit
`sk-prop-sf-biduality-general`, and the six-functors chapter, from the obtained
blueprint under `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/`.
The shared clone's recorded `literature/blueprint/` path is absent on this
machine. I also opened the actual Stacks TeX under
`/home/ubuntu/weil-launcher-nt/literature/stacks-project/`: proetale.tex Tags
09AA (`lemma-closed-immersion`), 09BM
(`lemma-closed-immersion-complement-retrocompact-exact`), 09AH
(`lemma-ses-associated-to-open`); etale-cohomology.tex Tag 04CA
(`proposition-closed-immersion-pushforward`); sites-cohomology.tex Tags 07A4
(`lemma-pullback-tensor-product`), 08J9 (`lemma-internal-hom`), and 08JA
(`lemma-section-RHom-over-U`). Tags were checked in `tags/tags`. For the cone criterion I also read derived.tex Tags 05RT (`lemma-acyclic`) and 05QR (`lemma-third-object-zero`), and the two recorded Mathlib declarations at HomologySequence.lean lines 88-89 and Pretriangulated.lean lines 388-391.

- Imported statement: the source says an ambient exceptional adjoint, arbitrary test complexes, and no biduality. Verdict: preserve this ambient assertion; make its missing site, coefficient, and object typing explicit as described below.
- First reader's step 1: opened all three cited statements. Verdict: repair. `fix-lem-tensor-adjunction` states a pushforward/internal-Hom isomorphism, not the tensor-Hom adjunction claimed; it requires finite-Tor constructible inputs. `fix-prop-adjunctions` is a constructible adjunction with exceptional admissibility. `fix-prop-projection-formula` requires its second tensor input to be finite-Tor constructible. None justifies the displayed calculation for arbitrary ambient test complexes and unrestricted K. The saved report also still described an earlier citation of `prop-functor-package`, which the saved node no longer used; that package's clause (5) has the same Tor restriction and its dependency on boundary duality makes it unsuitable here.
- Repaired step 1: checked each of the five cited node statements against 09AA, 09BM, 09AH, and 04CA, plus the etale closed-pushforward stalk and exact/conservative stalk statements. Verdict: pass. Pro-etale exactness, closed counit, and the localization sequence use the explicitly quasi-compact complement. Etale exactness uses geometric stalks only on the etale site. All ringed module actions are induced from inverse-image coefficient sheaves; forgetting them reflects exactness. The support argument gives joint detection of zero sheaves on both sites.
- Repaired step 2: checked exact inverse image, the ringed-topos module adjunction, the localization definition, termwise homotopy adjunction, and the unbounded derived pullback/tensor statement. Verdict: pass. The coefficient map is an isomorphism, so module pullback is exact inverse image; both closed functors are exact and their unit/counit descend. Tag 07A4 applies to arbitrary complexes over arbitrary ring sheaves and supplies the tensor comparisons used below. Joint detection on complexes follows degree by degree on cohomology.
- Repaired step 3: checked its projection morphism against the adjunction and tensor comparison already established in step 2. Verdict: elementary. Its closed inverse image is the closed counit/tensor isomorphism; both open inverse images are zero; the cone is acyclic by joint detection. Opened the existing Mathlib leaves `lem-weil-pbc-unbounded-derived-iso-cohomology` and `lem-kun-distinguished-cone-zero`: their exact statements turn that cone into a zero object and make the projection morphism invertible. This supplies the missing projection identity without a new node or a Tor hypothesis.
- Repaired step 4: checked the complete statement of `lem-weil-pbc-ringed-internal-hom-exact-restriction` (08J9) and `lem-pur-rhom-global-sections` (08JA). Verdict: elementary. Apply derived global H-zero to currying, then the global-Hom identification on both sides. These are unbounded ringed-site results, not assertions taken from the operation definition.
- Repaired step 5: matched the six displayed arrows, in order, with the assumed ambient exceptional adjunction, step 4, the inverse projection identity in step 3, the assumed exceptional adjunction, the fixed identification of dualizing objects, and step 4 on Z. Verdict: elementary; every test object is arbitrary in its specified ambient category and no constructibility or Tor hypothesis is inserted.
- Repaired step 6: checked the representing-object maps and both inverse composites directly. Verdict: elementary Yoneda: evaluation at the two identities produces alpha and its inverse. Naturality in the test object proves the inverse equations, and naturality in K proves naturality of alpha. The transposes are the source's evaluation and exceptional counit maps. No local-etale-to-global claim is needed to identify these objects on Z.
- New nodes: none. Verdict: no elementary fact, duplicate, clause of the item, or Mathlib result has been promoted to a new node.
- Existing-node/Mathlib check: searched all DAG statements for closed immersion, projection, tensor/Hom adjunction, and Tag 08J9; read the related `lem-trf-exceptional-internal-hom-exchange` and the unbounded `lem-weil-stratum-ambient-hom`. The latter's statement is a different pushforward/internal-Hom formula: its proof is not cited as a black box. Instead the precise statements it uses for the elementary closed-projection argument were opened and cited here. Independently ran msearch LeanFinder, Loogle, and grep with the more general monoidal-closed vocabulary, recorded verbatim in searches.jsonl. Read Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean lines 78-84 and Closed/Functor.lean's Frobenius mate context: generic closed/cartesian category structure does not provide this sheaf-derived statement or the required projection theorem. Verdict: the item is not a Mathlib leaf; zero new nodes and zero newly declared leaves. Step 3 reuses two existing Mathlib leaves after reading their statements and declaration sources.
- Small cases: K=0 or omega_T=0 makes both sides zero; Z empty gives the zero derived category on Z; i=id gives the identity tensor-Hom identification. Over the one-point field with i=id, the claim is ordinary derived module Hom. Over A=F_ell or A=Z/ell^2 the proof still applies; no finite free/projective resolution, regularity, or finite Tor dimension of arbitrary K is assumed. An n=0 coefficient quotient is the zero ring and also yields zero categories, although the blueprint coefficient conventions use n>=1. Verdict: all these cases pass.

Changes made and reasons:

1. Replaced the single mis-cited Hom-chain paragraph by six steps, including the proof of the closed projection identity and explicit Yoneda inverses. This repairs C1, C3, C4, E1, and E5 while retaining the source's conditional ambient proof route.
2. Named the ambient ringed sites, coefficient identifications, complexes, and adjunction in the statement; recorded the missing quasi-compact-complement condition for pro-etale closed-support operations. The formula, its direction, naturality, and independence of biduality are preserved. The more general ring-sheaf formulation includes all constant finite coefficient rings and ordinary ambient ring-sheaf realizations; no finite-Tor assumption on K or omega_T was added.
3. Removed the three unusable fix-node citations, and the misleading report-style tool_uses list inside split_report; identified the actual off-unit generic tools in split_report and this report for the maintainer to classify. The maintainer's top-level tool_uses field is not edited.
4. Cleared blueprint.same_as: the finite-coefficient admissible internal-Hom exchange is related, but does not state the same theorem. Kept the first worker's `## Review by Q43` and original sections, with this second reading recording the corrections to them.
5. Rebuilt citations.json with exactly one complete verbatim statement per cited node per step, removed stale citations, and appended independently executed searches to the log and node.

## Statement corrected

STATEMENT-DISPUTED: the imported standalone statement leaves K unbound and
specifies neither a coefficient ring nor a site nor the domain of Ri^!.
This is a type-check defect: with the current
`def-weil-exceptional-inverse-image`, Ri^! is a constructible functor,
whereas RHom(K,omega_T) and the source's arbitrary N live in ordinary
ambient categories and need not belong to its domain. For an explicit domain failure at a point, take A=Z/ell^2 and
K=omega_T=Z/ell in degree zero. The periodic free resolution with all
differentials multiplication by ell gives Ext_A^r(Z/ell,Z/ell)=Z/ell
for every r>=0. Thus RHom(K,omega_T) is unbounded and is not in D^b_c,
even though both inputs are bounded constructible. An arbitrary
unbounded test N is also plainly outside D^b_c. Merely saying the adjoint exists does
not select which adjunction is intended. Also, the source's pro-etale
exactness/localization argument uses a quasi-compact open complement:
09BM and 09AH state that hypothesis explicitly; geometric stalks on the
small etale site do not justify the same claim for arbitrary pro-etale
sheaves.

The corrected statement explicitly gives the ambient right-adjoint
bijections and the ordinary ringed-site categories and keeps K and omega_T
arbitrary. On the etale site it imposes no complement condition. On the
pro-etale site it states the quasi-compact-complement hypothesis required
by the source's intended closed-support argument. It is automatic for the
finite-type schemes over a field in the enclosing unit. This is a typing
and context correction, not a claim that the exchange formula itself has
an exhibited counterexample. No structure-morphism ambient adjoint,
constructibility preservation, or biduality is asserted to exist.

Citer audit (no citer edited): `def-weil-boundary-duality-input` and
`cor-weil-boundary-duality-discharge` use finite coefficients on locally
closed pieces of finite-type schemes, so the complement condition holds
and the same conditional ambient comparison remains available. Their
separate identification of the ambient closed right adjoint with the
constructible one is still required, exactly as before.
`thm-a1-curve-perverse-heart` uses the comparison in the common-stage
Q_lbar category. I opened its already cited `thm-coef-qbar-verdier`: its statement gives
Ri^!=D_Z i^* D_T and natural biduality in that common-stage category.
Consequently the exact isomorphism its step 4 uses remains available there
by Ri^!D_TK = D_Z i^*D_TD_TK, followed by D_Z i^* of the inverse biduality
isomorphism, giving D_Z i^*K. That caller already invokes biduality at this
step; its argument does not need the present ambient lemma to supply a
common-stage identification. This is a separate derivation from that
caller's existing theorem, not an identification of a common-stage Q_lbar
category with an ordinary ring-sheaf derived category and not an input to
the present proof. The maintainer should use this precise justification
when that caller is split. No new finiteness restriction is placed on its
complexes.

Off-unit infrastructure requested as tools: the exact ringed inverse-image
and module adjunction statements, termwise adjunction on homotopy
categories, unbounded derived tensor pullback, derived internal-Hom
currying/global-Hom, the etale closed-support/stalk statements, and the
ringed pro-etale open-closed statement are generic operation tools. The
unit supplies no competing statements for them, and using them does not
replace its geometric stratification route or invoke biduality.
