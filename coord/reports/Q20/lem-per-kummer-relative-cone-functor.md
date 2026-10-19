# Q20: lem-per-kummer-relative-cone-functor

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-relative-cone-functor.json`: statement, split into ten proof steps; no complete Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-exact-comma-injectives.json`: new statement-only auxiliary lemma; unsplit, no complete Mathlib match.
- `citations.json`: verbatim statements backing all 29 proof-step citations. `searches.jsonl` retains the actual search-command records.

One new node, zero new Mathlib leaves. The item is not its unit's key node; no unit or chapter file was changed.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 checkout for the exact item tag, relative cohomology, classifying topoi, Kummer relative cones, coinduction, and the prospective comma lemma. The matches are unrelated Kummer-class constructions, individual mapping-cone uses, or general adjoint/injective infrastructure. No project declaration states all the item. The item has no recorded slopmaster2 declaration to inspect further. No claim of completion is made from upstream master sorries.

## WANTED

None. The source passage and all Stacks ingredients used here are available locally. ILO leaves the relative functor's construction implicit; I supply it as an agent argument, and mark `proof_origin.by = agent`. The new comma lemma is an agent auxiliary construction, not a claim that Stacks 015Z literally states it.

## Findings and corrections

The starting item was statement-only, without a proof. I read ILO Expose XVI, printed pp.247–248, from Lemma 3.4.8 through the paragraph defining the triangulated relative cohomology functor and Lemma 3.4.9. The passage identifies the finite direct-image coefficient sheaves and uses that identification on derived sections. It states that relative cohomology defines a triangulated functor whose values are cones, but does not construct compatible cones. The split supplies that construction in a comma category, rather than claiming that a cone can be chosen functorially in an arbitrary triangulated category.

No mathematical statement dispute was found. I clarified `G/H` as a finite left G-set (H need not be normal), and added the existing constant-sheaf and module-sheaf definition citations. These clarify the same categories; they neither add a hypothesis nor weaken a conclusion. In particular the source's special cyclic/pro-ell situation is not silently imposed on the general finite-slice statement. No purity assertion is imported.

The current blueprint ancestor and its proof were read in `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/`. The item's inherited `blueprint.from` records a historical regular finite-coefficient input through the Kummer-root ancestry; that ancestry is preserved and the new lemma's `via` prepends this item. The current unit and chapter are untouched. Generic homological-algebra and slice statements from other units are declared under `split_report.tool_uses`; none replaces a step of the Fourier/perverse unit.

## Auxiliary lemma: construction checked

For an exact additive L:A→B with additive right adjoint R, form triples (P,N,u:LP→N). Kernels and cokernels are componentwise: exactness of L induces the structural maps on both, and the universal properties are checked in each component. Images and coimages are componentwise too, so their canonical comparison is an isomorphism; this proves abelianness.

The source evaluation e0 has exact left adjoint Delta(P)=(P,LP,id), and target evaluation e1 has exact left adjoint N↦(0,N,0). Hence both evaluations preserve injectives by Stacks 015Z. To obtain enough injectives, their right adjoints are i0(I)=(I,0,0) and i1(J)=(RJ,J,epsilon_J). Since the evaluations are exact, these right adjoints carry injectives to injectives. Choose monomorphisms a:P→I and b:N→J with I,J injective. The pair (a, adjunct(bu)) together with b defines a monomorphism of triples

(P,N,u) → i0(I) ⊕ i1(J) = (I⊕RJ,J,(0,epsilon_J)).

Its P component is monic because its first projection is a; its N component is b. The target is injective, as a finite direct sum of injectives. This proves the claimed enough-injectives assertion without assuming that L preserves injectives or that R is exact. The new node contains only the statement; this verification explains why it is a valid, strictly smaller auxiliary lemma.

I searched the whole DAG for comma/abelian/injective/triple and gluing descriptions, and the whole imported blueprint with `blueprint_refs.py search` for comma, injective comma, gluing, finite covering and relative cohomology. No existing node states this exact-comma result. The same-tag nodes below were opened and compared. The prospective id was also checked against the DAG and project Lean source before creation.

All searches in the new node were run through msearch.py. Two distinct semantic phrasings, LeanSearch, Loogle, and two Mathlib grep queries were read. `CategoryTheory.EnoughInjectives.of_adjunction` and `Injective.injective_of_adjoint` were read in `Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean` (especially the latter around 199 and the former around 336); they give general preservation/transfer ingredients, not the triple category and its abelian structure. `abelianOfAdjunction` was read in `Mathlib/CategoryTheory/Abelian/Transfer.lean`, around 91: it requires a reflective comparison which is not supplied for this comma category. It is not a one-line specialization. Grep found no abelian/injective comma theorem. Individual cone declarations, a triangulated functor induced by an additive functor, and ordinary discrete-group Shapiro returned for the item do not state its relative topos comparison.

## Not duplicates

lem-per-exact-comma-injectives vs lem-sc-field-scalar-restriction-injectives: that node preserves injectivity under restriction from ring sheaves to vector-space sheaves; it constructs no category of triples and gives no enough-injectives theorem for it.

lem-per-exact-comma-injectives vs lem-weil-pbc-injective-abelian-sheaf-injective-presheaf: that node concerns the sheaf-to-presheaf inclusion, not an exact comma category or its evaluations.

lem-per-exact-comma-injectives vs lem-weil-pbc-module-injective-open-cover-cech-acyclic: that node is Cech vanishing on a ringed-space open cover, with no comma-category statement.

lem-per-exact-comma-injectives vs lem-weil-pbc-colimit-of-sites-injective-system: that node embeds a system over a cofiltered collection of sites into a system with injective components; it does not make the exact-comma category abelian or show its injective objects have injective components. Its geometric hypotheses and direction also differ.

lem-per-exact-comma-injectives vs lem-weil-pbc-zariski-open-restriction-injectives: that node handles restriction to a Zariski open of a scheme, not triples for an arbitrary exact left adjoint.

lem-per-exact-comma-injectives vs lem-weil-pbc-equivalence-injective-resolutions: that node transports injectives through an already given equivalence; it neither constructs the comma category nor provides its injective embeddings.

lem-per-exact-comma-injectives vs lem-weil-pbc-module-open-restriction-injectives: that node concerns module restriction and direct image for an open immersion of ringed spaces, not the two evaluations of a comma category.

lem-per-exact-comma-injectives vs lem-weil-pbc-injective-module-injective-presheaf: that node preserves injectives under a module sheaf-to-presheaf inclusion on an etale site, not in the exact-comma construction.

lem-per-exact-comma-injectives vs cohomology-site-equivalence-fixed-degree: that node compares fixed-degree abelian sheaf cohomology under an equivalence of sites; it gives no abelian or injective structure on triples.

lem-per-exact-comma-injectives vs lem-exc-rg-right-adjoint-preserves-injectives: that node states the general adjoint preservation ingredient of 015Z. It supplies neither the componentwise kernels/cokernels nor the adjoints of the two evaluations nor the simultaneous injective embedding required here.

## Review by Q20

I checked B–E with the item, new node, cited statements, ILO text and Stacks text open. In addition to ILO XVI pp.247–248, I read Stacks `homology.tex`, Tag 015Z (`lemma-adjoint-preserve-injectives`); `derived.tex`, Tags 013K (`lemma-injective-resolutions-exist`), 014E (`definition-cone`), 014F (`lemma-functorial-cone`), and the K-injective Hom statement of 070I; `sites.tex`, Tag 0791 (`lemma-localize-topos-site`); and `sites-modules.tex`, Tags 03D7 (`lemma-adjoint-pullback-pushforward-modules`), 04IE (`lemma-localize-ringed-topos`) and 04J4 (`lemma-relocalize-ringed-topos`). ILO is the route, and these are generic tools, not an alternative purity route. No SGA source is used.

Step 1 uses the discrete-module definition only for its objects/actions and the ringed-slice theorem for the actual slice construction. Fiber at H and G×_H(-) give the inverse equivalence explicitly; openness of H checks continuity. I checked that its permutation module uses left cosets and translation, not a quotient group. Step 2 cites precisely left-adjoint preservation of small colimits, which its cited statement provides; applying it to the kernel-pair coequalizer constructs the cover on E. The trivialization over G/N is written explicitly and uses a finite intersection, not an infinite intersection of open subgroups.

Step 3 uses the slice and module-adjunction statements to identify the sheetwise right adjoint. It proves exactness by simultaneous local lifting through the finitely many factors, and proves the comparison by finite-product projections and gluing their unique maps. It does not cite the definition of flatness or assume an unproved cohomology base-change result. Thus the two asserted comparisons are actual sheaf maps. This is a direct finite-product calculation, not a new node repeating a clause of the item.

Step 4 cites the Grothendieck module-sheaf theorem for arbitrary small sites (not just schemes), enough injectives for Grothendieck categories, the actual module adjunction, and the new exact-comma statement. Every hypothesis is present: the coefficient sheaves are commutative constant rings, L is additive exact by the item, and its right adjoint is the module direct image. The new lemma's complete statement explicitly supplies abelianness, enough injectives and preservation by evaluations. No property of L on injectives is smuggled in.

Steps 5 and 6 are elementary matrix calculations from the stated cone differential. I checked the minus sign on the P-part of a cone homotopy, the shift matrix diag(1,-1), and the minus sign on the last summand of the double-cone permutation. The cited homotopy-category theorem says that all distinguished triangles are cone triangles up to isomorphism, exactly what Step 6 uses. These steps construct the functor on homotopies before passing to a derived category.

Step 7 uses the full general-abelian statements of the injective representative and K-injective Hom nodes, not a scheme-specific version. They imply essential surjectivity and full faithfulness on bounded-below complexes of injectives. The homotopy/localization theorem provides exactness, and exact-functor derived factorization explicitly supplies the triangulated graph localization. The remaining finite-sum injectivity follows by lifting the two components using the cited injective definition. This gives F on morphisms, not just objects.

Step 8 uses right-derived computation on injectives only after Step 4 has proved the components injective. I checked the cited K-injective Hom statement is bijectivity of Hom in the derived category, stronger than mere resolution existence. Together with the cited right-adjoint preservation theorem, termwise adjunction identifies w's adjunct as the derived unit corresponding to the identity. This verifies that the arrow is the specified a_K, rather than an arbitrary comparison with the same cohomology. Cone triangles then give the displayed natural triangle.

Step 9 applies the same model on the two slice topoi; smallness follows from the element-site presentation in the cited slice theorem. Right-adjoint preservation of injectives applies because the module pullbacks are exact. Exactness of both direct images is established in Step 3, so their pushed resolutions resolve M and rho* M. The module adjunction gives the literal section identities, and the derived-on-injectives theorem gives the stated derived-section isomorphisms. Step 10 writes the structural chain map through beta, verifies its augmentation represents the identity, and checks its effect on each product projection. This checks compatibility of the canonical arrows on complexes, not just abstract isomorphism of their domains and codomains. The final cone conclusion now follows from the already constructed triangle.

For C4, each citation's statement was opened; `citations.json` copies its exact text without altering hypotheses. For C1, every non-elementary tool is cited. The new lemma is a structural enough-injectives fact, not the relative cone statement or its finite-cover clause. For B1–B9 it is self-contained, statement-only, with every notion introduced or linked, genuine searches, exact ancestry and a precise source qualification. No Mathlib leaf is falsely claimed. All proof steps are under 2000 characters; I also inspected the shorter steps for concealed lemmas, and retained only the explicit fiber, finite-product, adjunction and signed-matrix verifications.

The auxiliary lemma was tested with L=0 (the category becomes A×B), with L=id (the arrow category), and with a nonexact right adjoint R: the proof uses R only on injectives and never assumes it exact. For the item I checked A=0, H=G (both finite covers are identities), G=1 (ordinary relative global sections), and rho=id (the functor is zero up to isomorphism). A nonnormal subgroup of S3 still gives the correct left-coset permutation module and finite trivialization; no argument requires normal H. Complexes may start in any integer degree: the cone lowers the bound at most by one, with no uniform bound on group cohomology required. During review I corrected prime notation in the generated TeX and made the existing coefficient definitions explicit. No source error or false extra hypothesis remained.

## Unfinished work

The new exact-comma lemma is intentionally unsplit, as required for a one-level stage-1 delivery. No Lean was written and no compiler, Lake, local preflight, or local DAG/review checker was run. Required dry-run and delivery results follow below.
