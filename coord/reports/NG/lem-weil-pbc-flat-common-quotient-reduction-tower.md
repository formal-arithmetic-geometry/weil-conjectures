## Worker report

Files written:
- dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-common-quotient-reduction-tower.json: existing item, deliberately re-split, statement unchanged; four assembly steps (2476 characters).
- dag/nodes/sec-proper-base-change/lem-weil-pbc-sheaf-tensor-ideal-quotient.json: new statement, unsplit, no Mathlib match (1610-character statement). No proof or proof dependencies.
- citations.json: verbatim statement quotations for every assembly-step citation.

Attachments: none. Searching lean/WeilConjectures by the item tag and common-quotient terminology found no finished declaration stating the item. The recorded Sheaf.Paper.FlatCommonQuotientReductionTower module was read: nonempty_comparison still ends in sorry. ModuleCat.quotSMulTopCompRestrictScalarsIso is an ordinary-module result, not an arbitrary-site sheaf result.

WANTED: none.

The old statement is retained verbatim, as are all maintainer-owned fields and the previous searches. This is the human-requested re-split of an already reviewed item, not a stale assignment. No source error or statement dispute was found. The problem was the amount of work inside one proof. The new task extracts the actual sheaf tensor-quotient construction, with its local ideal-product kernel, quotient projection, module-map naturality and ideal-inclusion naturality. It does not restate the derived comparison or its strict-tower clause. The old arguments are preserved explicitly below; the item keeps only their assembly from the new lemma and existing resolution/descent tools. No Lean source was written and no compiler was run.

Nothing mathematical is left unfinished at this stage: the new node is intentionally statement-only, available for a separate worker. The parent proof is not an assertion that the new node is already proved.

## Sources and route

I read the current main-20261015 completed-pullback blueprint (order 1329), especially its nth evaluation, displayed derived inverse limit and final completion-map sentence, together with the chapter and sk-thm-properbasechange unit. The extraction supplies the common-quotient finite reduction used on that route; it changes no unit or chapter. blueprint_refs.py ancestor gives def-weil-pbc-completed-pullback, via the existing constant-completion-equivalence node. A new descendant has the item prepended to that via chain. Searches over all blueprint nodes for tensor quotient, quotient, sheaf tensor, F/IF, and the tensor/quotient combination found no blueprint statement equal to the new one.

For the item I read proetale.tex Tag 099L, label section-derived-completion-noetherian: the completed coefficient algebra is flat and identifies finite quotients. I also read sites-cohomology.tex Tags 06YS (lemma-K-flat-resolution), 06YT (lemma-derived-tor-quasi-isomorphism-other-side) and 06YY (lemma-derived-base-change), including the resolution-class construction and its reference to 06XN. These justify the resolving route, not a claim that 099L explicitly states this general strict-tower theorem.

For the new node I read sites-modules.tex Tag 03EK (section-tensor-product): sectionwise presheaf tensor, sheafification, and its bilinear universal property. The formula for quotient modules and the two compatibility squares are an agent-written extraction of the old item, not a quotation of a Stacks theorem under a different tag. The node's source says this. The relevant module/sheafification and tensor definition nodes are explicit statement dependencies. Ideal subsheaves, local ideal-product membership and sheaf quotients are defined in the new statement itself.

The existing generic tools lem-pc-kflat-resolution, lem-pur-derived-change-of-rings and lem-pur-left-derived-from-kflat-class retain their previously declared tool-use explanations. No other unit's route is substituted, and no SGA source is used.

## Argument assigned to the new node

This proof plan is in the report, not in the statement-only node. It is the work the extracted task must carry, rather than a claim that objectwise surjectivity of quotient sheaves holds.

Define the subsheaf IF by local ideal-product membership; restrictions preserve the generating products, and the sheaf property makes local membership stable under coverings. Its quotient is the sheafified cokernel. On presheaf representatives define a(f tensor r-bar)=[rf]. If r changes by i in I, its image changes by if in IF. The bilinear pairing is balanced over R. Quotient coefficient sections can be lifted only locally; refinements give agreement because two lifts differ locally by I. Hence these pairings glue to an S-linear sheaf map. Conversely f maps to f tensor 1 and every local product if maps to f tensor i-bar=0. This kills IF and factors uniquely through the sheaf quotient to b([f])=f tensor 1. The composites ab and ba fix quotient generators [f] and tensor generators f tensor r-bar: r f tensor 1=f tensor r-bar. The sheafification universal property, checked locally, makes them inverse maps of sheaves, not merely a bijection of selected sections. In particular the unit is the quotient map under this isomorphism, so its sheaf kernel is exactly IF and it is an epimorphism.

For an R-linear h, both sides of the module naturality square send f tensor r-bar to [r h(f)]. For I' contained in I, both sides of the quotient square send f tensor the class of r modulo I' to the class of rf modulo IF. Both coefficient-unit composites send f to f tensor 1. Pure-section determination and local lifts prove the two sheaf equalities. This accounts for the old construction, inverse, local-lift qualification, sheaf quotient normalization and both naturalities. No assumption of flatness or of enough points is introduced.

## Review by NG

I checked the delivery against B–E with the cited statements and the sources open. B1/B2: the one new node has empty proof and proof_deps, and introduces its own small site, commutative ring sheaf, ideal sheaves, module sheaves, quotient maps and naturality data. It has no reference to a chosen P, M, B or the objects of another proof. B3–B7: module sheaves, module sheafification, tensor and pure sections cite exactly the four definition nodes that supply them; ideals and the local product submodule are defined inline. TeX is escaped once in JSON. The source uses the checked Stacks tag and label, and expressly describes the agent extraction. B8: Mathlib's tensorQuotEquivQuotSMul at Mathlib/LinearAlgebra/TensorProduct/Quotient.lean:164 has ordinary rings/modules; the sheaf result requires sheafification and local quotient lifts and is not its one-line specialization. I read that definition and its formulas as well as the Quasicoherent presentation hits. B9/B10: the blueprint ancestry is filled, whole-blueprint/DAG searches were made, and the live recorded theorem contains sorry, so attachment does not apply.

Step 1: lem-pc-kflat-resolution actually states the existence of a quasi-isomorphism from one K-flat complex with flat terms, for any cochain complex over a ringed site. lem-weil-pbc-flat-scalar-restriction-kflat actually states both K-flatness after restriction and flatness of the restricted terms, under precisely the assumed flatness of B over R. def-pc-sheaf-restrict-scalars keeps the underlying abelian sheaf. def-weil-sheaf-of-modules-category states sectionwise kernels and sheafified cokernels. Thus the short exactness/cohomology observation needs no assertion that evaluation on sections is exact. The site is small relative to the coefficient universe and unbounded complexes are permitted.

Step 2: the new statement gives the S-linear isomorphism, its inverse formula, projection normalization, and module-map square for every module. It is applied separately over R and B, never to a module without the required structure. The remaining equality (J_n B)F=J_nF is written out on local generators, using the B-module action on F; the reverse inclusion uses 1. Local generation, not a false equality of sectionwise extended ideals, is the reason these are equal subsheaves. The map R/J_n to B/J_n B is the given map induced by phi, so their quotient S_n actions agree. This is a proper extraction: the new task contains no derived category, flat scalar restriction, complex or tower assertion, and is strictly smaller than the item. The item still constructs c_n from two instances of it.

Step 3: def-pc-tensor-complex-sheaves gives the displayed total differential, which reduces to d_P tensor 1 for a degree-zero coefficient. def-weil-pbc-ringed-tensor-section-calculus says exactly that pure sections determine module-sheaf maps and are natural. def-weil-inverse-system defines both transitions and morphisms componentwise. The differential, h-naturality, adjacent transition and cone equations are all displayed; composing adjacent squares covers arbitrary transitions. No compatibility is asserted only after derived localization, and no homotopy-coherent tower is mistaken for a strict one. This step is elementary assembly once the quotient isomorphisms have been supplied.

Step 4: I read both clauses of lem-pur-derived-change-of-rings, not just its title. Clause (1) gives quasi-isomorphism invariance on K-flat complexes; clause (2) gives the specified derived computation on any K-flat resolution. For lem-pur-left-derived-from-kflat-class, condition (1) is the common B-resolution from step 1; condition (2) holds over B by clause (1), and over R by the restriction lemma and that same clause. The maps are natural already on complexes, hence pass to homotopy categories. Its universal derived-pair property carries a natural isomorphism and its inverse to the derived functors; the counit being invertible on the class fixes its value at P. This proves naturality on all derived morphisms and independence of resolution. No definition node is used to supply a theorem about derived functors.

C1/C4: citations.json copies the actual relevant statements verbatim for each use, including the new lemma in step 2. All other non-elementary inputs are the existing resolution, flat restriction, derived change-of-rings and resolving-class nodes. C3: nothing is taken from the construction inside a dependency's proof. D1/D2: the new node is the independent ordinary sheaf quotient theorem; the parent still makes the B/R identification and the strict and derived assembly. It cannot be used alone as the item. The former six-step proof is preserved below so the extraction cannot hide a deleted argument. No assembly step exceeds 2000 characters and the complete assembly is below the requested 3000.

For E and edge cases I checked I=0 (the unit F tensor R is F), I=R (zero quotient ring, zero module), F=0, repeated ideals I'=I (identity transition), I'=0 contained in a general I, and the empty site. None requires a nontrivial ring or enough points. On the singleton site the statement reduces exactly to the Mathlib quotient tensor equivalence and its projection formula. For the parent, R=B and the identity map gives the identity comparison. The flat example Z to Z_p with ideals (p^n) has the required compatible common quotients. No flatness is asserted for S_n; it is the chosen P and Res P that are K-flat. This matters for arbitrary unbounded M. Neither the item nor the new statement assumes Noetherian rings or finitely generated ideals merely because 099L's motivating case has them.

Corrections made in this pass: extracted the local quotient calculation rather than simply shortening it; included both naturality squares, local kernel and quotient projection in the new public statement; kept the explicit B-ideal-product equality, differential, chain naturality, transition and cone formulas in the parent; kept the resolving-class hypotheses and universal normalization explicit. The parent's mathematical statement was not changed.

## Not duplicates

The following comparisons include all current nonmerged nodes whose source carries 03EK, and the closest additional candidates. The shared section tag is a broad tensor section, not evidence of equal statements.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pe-internal-section-tensor-comparison: the existing node concerns Relative tensor and K-flatness under the internal-to-sectionwise module equivalence; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sf-completed-tensor-finite-shift: the existing node concerns Signed right shifts of the strict finite tensor tower; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-zl-pbc-finite-raw-scalar-comparison: the existing node concerns Canonical comparison of normalized and embedding finite-field scalar extension; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-trf-singleton-site-operations: the existing node concerns Punctual ringed-site operations and normalized comparison predicates; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sc-hom-tensor-comparison-natural: the existing node concerns Naturality of the sheaf tensor comparison isomorphism; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sc-hom-tensor-summand-restriction-ext: the existing node concerns Internal Hom maps determined by total tensor summand restrictions; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sc-internal-hom-coproduct-fan: the existing node concerns Internal Hom of a coproduct is a product; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pc-sheaf-modules-tensor-closed: the existing node concerns Sheaves of modules on a site form a symmetric monoidal closed category; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sc-hom-tensor-section-natural: the existing node concerns Naturality of the canonical presheaf-to-sheaf tensor map; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sc-hom-tensor-summand-localized-ext: the existing node concerns Localized pure-tensor extensionality for a sheaf tensor; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pc-sites-sheaf-tensor-bilinear-universal: the existing node concerns Universal property of sheaf tensor product; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sc-internal-hom-product-fan: the existing node concerns Internal Hom preserves integer-indexed product fans; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sc-hom-tensor-reverse-pair: the existing node concerns Reverse currying for one pair of module sheaves; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sfb-scalar-inverse-image-tower-diagram: the existing node concerns Ordinary inverse-image and balanced scalar-tower square; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sfb-proetale-intrinsic-tensor-comparison: the existing node concerns Right-tensor comparison for intrinsic constant-ring realization; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sfb-internal-section-scalar-adjunction: the existing node concerns Scalar adjunction transport between internal and sectionwise module sheaves; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sfb-internal-scalar-extension-section-test: the existing node concerns Internal scalar-extension flatness tested on sectionwise module sheaves; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-sfb-internal-section-total-comparison: the existing node concerns Canonical internal-to-sectionwise total-complex comparison; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-pbc-continuous-module-encoding-scalar-extension: the existing node concerns Scalar extension under the continuous integral and rational module encodings; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-pbc-scalar-localization-complex-colimit: the existing node concerns Ordinary scalar-sequence colimit of complexes; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs adic-unit-exists-data: the existing node concerns Existence of the identity scalar-extension unit map; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-weil-pbc-ringed-tensor-section-calculus: the existing node concerns Section calculus for the actual sheaf tensor and scalar extension; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-pbc-scalar-localization-module-colimit: the existing node concerns Scalar localization as an ordinary module-sheaf colimit; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-pbc-tensor-local-bijection-universes: the existing node concerns Tensoring a local module bijection commutes with sheafification in independent universes; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-w2-inverse-image-change-of-rings-unit-smul: the existing node concerns Scalar compatibility of the inverse-image change-of-rings unit; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-pbc-extension-tensor-comparison: the existing node concerns Restricted scalar extension as a sheaf tensor product; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-pbc-continuous-module-encoding-lattices: the existing node concerns Local freeness and lattice compatibility of the explicit continuous encodings; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-pbc-flat-scalar-restriction-kflat: the existing node concerns Flat scalar restriction preserves K-flat complexes; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-weil-pbc-common-quotient-tower-presentation: the existing node concerns Common-quotient tower presentations and local ideal-product membership; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-pbc-scalar-tensor-comparison-universes: the existing node concerns Scalar-extension tensor associativity on underlying abelian sheaves in independent universes; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-pur-kummer-module-coefficients: the existing node concerns Kummer sheaves with module coefficients and their scalar actions; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-pur-sheaf-tensor-product: the existing node concerns Tensor product of sheaves of modules on a site; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-system-ordinary-tensor-reduction: the existing node concerns Ordinary scalar-adjoint tensor formula for strict systems; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-kun-prime-coefficient-functors: the existing node concerns Punctual tensor source and target functors; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-constant-finite-free-section-basis: the existing node concerns Compatible sectionwise bases of constant coefficient extensions; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-sp-semilinear-constant-ring-operations: the existing node concerns Constant-ring semilinear system operations and normalized evaluation mates; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sp-scalar-extension-dual-local-iso: the existing node concerns Local rank-one scalar extension and dual invertibility; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-kummer-finite-biproducts: the existing node concerns Integral finite-basis cohomology and Kummer exactness; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-kun-prime-coefficient-complexes: the existing node concerns Degree zero complexes and localization; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-proetale-inverse-image-tensor-comparison: the existing node concerns Pure-tensor description and coherence of the pro-etale inverse-image tensor comparison; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-pur-finite-tate-site-comparison: the existing node concerns Finite Tate tensor generators and root-normalized site comparison predicates; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sp-scalar-extension-binary-coherence: the existing node concerns Normalized binary scalar-extension comparisons; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-module-tensor-monoidal-equations: the existing node concerns Associativity and symmetry of the canonical ordinary module tensor comparison; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-kun-prime-coefficient-complexes-input-output: the existing node concerns Ordinary source and target tensor complexes; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-sheaf-scalar-extension-ring-iso: the existing node concerns Scalar extension along an isomorphism of ring sheaves; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-kun-prime-coefficient-constructions: the existing node concerns Canonical quotient coefficient tensor arrow; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-twist-coefficient-comparison: the existing node concerns The canonical coefficient pushout comparison is invertible; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-change-of-rings-tensor-comparison: the existing node concerns Natural comparison of restricted scalar extension and sheaf tensor; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-constant-finite-free-power-iso: the existing node concerns Finite-basis coordinates for constant scalar extension; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-etale-constant-module-tensor: the existing node concerns Constant-coefficient realization commutes naturally with right tensor; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sp-finite-free-scalar-models: the existing node concerns Existence of normalized actual-restriction scalar models; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-kun-prime-coefficient-normalization: the existing node concerns Derived normalization by the quotient tensor map; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-kun-prime-coefficient-iso: the existing node concerns Derived coefficient tensor isomorphism type; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-twist-coefficient-tensor: the existing node concerns Finite integral coefficient extension commutes with sheafwise completion; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-kun-prime-coefficient-term-map: the existing node concerns Degree zero coefficient term map; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-change-of-rings-tensor-cancellation-independent: the existing node concerns Natural tensor cancellation in independent coefficient universes; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-twist-integral-local-models: the existing node concerns Scalar-extension local models of the integral root line; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-kun-prime-coefficient-localization-compatibility: the existing node concerns Localized termwise coefficient compatibility; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-pur-twist-coefficient-rings: the existing node concerns The canonical discrete and completed scalar square of the Tate twist; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-tensor-pushout-action: the existing node concerns A sectionwise scalar pushout acts uniquely on a balanced tensor sheaf; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-sp-scalar-tensor-comparison-data: the existing node concerns Normalized tensor and scalar-extension comparison data; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-inverse-image-tensor-comparison: the existing node concerns The unit-normalized tensor comparison for an isomorphic base change; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-kummer-integral-root-comparison: the existing node concerns Integral basis reduction for the Kummer root sheaf; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-module-tensor-generator-calculus: the existing node concerns Pure tensors and normalized insertion naturality for sheaf modules; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-inverse-image-scalar-comparison: the existing node concerns Inverse image commutes with extension of scalars, with its unit formula; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sp-scalar-extension-dual-evaluation: the existing node concerns Explicit scalar-extension evaluation on internal duals; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-pur-presheaf-tensor-product: the existing node concerns Presheaf tensor product of modules; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-kun-prime-coefficient-termwise-normalization: the existing node concerns Termwise normalization of the quotient tensor arrow; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-compatible-coefficient-tower: the existing node concerns Compatible coefficient maps give a linear strict tensor tower; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-system-cochain-tensor-reduction: the existing node concerns Cochain scalar-adjoint tensor formula for strict systems; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-kun-prime-coefficient-pullbacks: the existing node concerns Canonical coefficient pullback maps; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-point-sections-tensor-shift: the existing node concerns Sections-tensor comparison commutes with shifts; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sp-scalar-extension-dual-tower-core: the existing node concerns Dual comparisons and binary scalar-extension tower squares; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-change-of-rings-tensor-cancellation: the existing node concerns Natural cancellation of scalar extension in sheaf tensors; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-kummer-finite-free-comparison: the existing node concerns Normalized finite free Kummer cohomology comparison; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-pur-inverse-image-tensor-hom-sections: the existing node concerns Tensor, scalar and unit-section conventions for module inverse image; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-etale-constant-module-flat: the existing node concerns Flatness under constant-scalar realization; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-pur-operation-scalar-transport: the existing node concerns Pure-tensor and derived-counit normalized operation scalar transport; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pur-constant-finite-free-products: the existing node concerns Countable products and finite-free constant scalar extension; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-pd-proetale-section-module-functors: the existing node concerns Normalized tensor structures on existing pro-etale section-module functors; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-pd-ringed-direct-image-pairing-lax: the existing node concerns Normalized lax tensor pairing for ringed direct image; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs def-pd-section-module-operations-data: the existing node concerns Existing section-module operations and pure-tensor data; it does not assert the normalized isomorphism F tensor_R (R/I) = F/IF with local ideal-product kernel and both module/ideal naturality squares for arbitrary ring sheaves.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-sfb-integral-tensor-quotient-epimorphism: the existing statement gives only local surjectivity and the epimorphism property of the tensor unit; it supplies neither its ideal-product kernel nor the isomorphism to the actual sheaf quotient or the two naturality squares.

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: this is a geometric derived scalar-insertion comparison for two sites and flat maps; it does not state the ordinary quotient identification for an arbitrary ideal and module on one ringed site (and depends on the present item, so cannot replace it).

lem-weil-pbc-sheaf-tensor-ideal-quotient vs lem-weil-pbc-flat-common-quotient-reduction-tower: the item compares derived tensors over two flat-related coefficient rings with the same quotient and assembles normalized strict towers. The new statement is the ordinary sheaf-module ideal quotient theorem over one arbitrary ring, with no flatness, derived category, complex, or inverse system.

## Prior argument retained and allocation

Former step 1 is assembly step 1, using existing resolution and flat restriction statements. Former step 2 is assigned to the new node. Former step 3's identification of the ideal products and c_n is assembly step 2; the quotient identification it uses is the new node. Former step 4 is assembly step 3 using module naturality from the new node. Former step 5 is assembly step 3 using the new node's ideal-inclusion and unit normalizations and the displayed tensor transition formula. Former step 6 is assembly step 4 using the two existing derived tools. Thus every former argument is either assigned to a separate node (new or already existing) or kept explicitly as an elementary assembly identity.

Former step 1:

Represent $M$ by a $B$-complex $G$. Apply [lem-pc-kflat-resolution] over $B$ to choose one quasi-isomorphism $P\to G$, with $P$ K-flat and all its terms flat over $B$. Flatness of $B$ over $R$ is precisely the hypothesis of [lem-weil-pbc-flat-scalar-restriction-kflat], so $\operatorname{Res}P$ is K-flat over $R$ and has flat $R$-terms. Restriction does not change the underlying abelian sheaves [def-pc-sheaf-restrict-scalars]; kernels and sheafified cokernels are therefore unchanged, so it preserves this quasi-isomorphism. This same $P$ works simultaneously at every level; no compatible choice of separate resolutions is required.

Former step 2:

For a term $F=P^i$, put $Q_n=F/J_nF$, the sheaf quotient by the submodule sheaf locally generated by products $jp$. By the tensor and sheafification universal properties [def-pur-sheaf-tensor-product, def-weil-presheaf-modules-sheafification], the formulas
$$a_n:F\otimes_R S_n\longrightarrow Q_n,\quad p\otimes\bar r\longmapsto[rp],\qquad b_n:Q_n\longrightarrow F\otimes_R S_n,\quad[p]\longmapsto p\otimes1$$
define inverse $S_n$-linear maps. Indeed changing $r$ by $j\in J_n$ changes $rp$ by an element of $J_nF$, while $jp\otimes1=p\otimes\bar j=0$ makes $b_n$ well-defined. The composites fix $[p]$ and $p\otimes\bar r$, respectively, by tensor balancing. These formulas are first defined on presheaf sections and then sheafified; a section of $S_n$ need only lift locally to $R$. Thus no surjectivity on sections, nor enough points of the site, is assumed. The quotient itself is the sheafified cokernel [def-weil-sheaf-of-modules-category].

Former step 3:

Apply the preceding calculation with $B$ and its ideal $J_nB$. Its submodule $(J_nB)F$ equals $J_nF$: locally a generator $(\varphi(j)b)p$ equals $\varphi(j)(bp)$, and the reverse inclusion uses $b=1$. The assumed ring isomorphism $R/J_n\cong B/J_nB$ therefore identifies the second tensor with the very same $S_n$-module $Q_n$. Let
$$c_n:F\otimes_R S_n\xrightarrow{a_n}Q_n\xrightarrow{(a_n^B)^{-1}}F\otimes_B S_n.$$
Then $c_n(p\otimes s)=p\otimes s$, and its inverse has the same formula, checked locally after lifting $s$ to $R$. This also verifies $S_n$-linearity for the stipulated common-quotient structure. Equalities of maps are checked on pure sections by [def-weil-pbc-ringed-tensor-section-calculus].

Former step 4:

Apply $c_n$ in every degree of the fixed $P$. Tensoring with the degree-zero sheaf $S_n$ has differential $d_P\otimes1$ [def-pc-tensor-complex-sheaves]. Both composites in the chain-map square send $p\otimes s$ to $d_P(p)\otimes s$; the same calculation for the inverse proves that $c_n$ is an isomorphism of complexes. More generally, for a $B$-linear chain map $h:P\to P'$ the two naturality composites send $p\otimes s$ to $h(p)\otimes s$. The pure-section determination property [def-weil-pbc-ringed-tensor-section-calculus] makes these equalities actual equalities of sheaf morphisms.

Former step 5:

For $J_{n+1}\subseteq J_n$, write $t_n:S_{n+1}\to S_n$ for the quotient map. The quotient-transition square for $c_{n+1}$ and $c_n$ has both composites
$$p\otimes s\longmapsto p\otimes t_n(s).$$
The compatibility assumed for the common-quotient identifications ensures that the same $t_n$ is used over $R$ and over $B$. Restrict the targets to $R$. The adjacent squares, and hence their composites for all levels, give an isomorphism of strict towers [def-weil-inverse-system], degreewise and compatible with the differentials by step 4. The quotient maps from $P$ are chain maps $p\mapsto p\otimes1$ and satisfy $(1\otimes t_n)(p\otimes1)=p\otimes1$. Finally $c_n(p\otimes1)=p\otimes1$ proves equality of the two strict cones from the constant tower, at every level, rather than only after localization. Pure sections determine these squares [def-weil-pbc-ringed-tensor-section-calculus].

Former step 6:

Use [lem-pur-derived-change-of-rings] for $R\to S_n$ and $B\to S_n$. Step 1 supplies its K-flat models on both sides, so the complexes of step 4 represent $\operatorname{Res}M\otimes_R^L S_n$ and $M\otimes_B^L S_n$ as objects of $D(S_n)$. Their chain isomorphism thus gives the asserted canonical $S_n$-linear derived isomorphism. To check naturality and independence of the chosen resolution, regard both ordinary constructions as functors on $B$-complexes with values in $D(S_n)$. Their comparison is natural by step 4. On the class of K-flat $B$-complexes with flat terms both functors invert quasi-isomorphisms, by flat restriction and [lem-pur-derived-change-of-rings](1); every complex has a resolution in that class by step 1. The universal derived-functor construction [lem-pur-left-derived-from-kflat-class] therefore descends this natural isomorphism uniquely, and its inverse descends as well. This gives naturality for all morphisms of $D(B)$ and the canonical agreement for a different $P$. Step 5 already proves the stronger strict representative assertion, including quotient transitions and cones.
