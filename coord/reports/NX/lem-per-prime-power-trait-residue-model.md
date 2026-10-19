# Worker report: lem-per-prime-power-trait-residue-model

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-prime-power-trait-residue-model.json: statement, split; no Mathlib match. Fourteen proof steps over Lambda = Z/ell^n, with the original statement and source fields unchanged.
- citations.json: one verbatim statement quotation for each node citation in each proof step.
- report.md: this report.

New nodes: none. New Mathlib leaves: none. Existing Mathlib leaves used: lem-exc-rg-right-adjoint-preserves-injectives, lem-sp-grothendieck-enough-injectives and lem-sc-bounded-below-injective-resolution-existence.

The retained sandbox contained the unchanged item, searches.jsonl, search-results.json, run_searches.py and the ILO text, but no report or split. No delivery process was running on resumption. The retained searches were read and reused; no search service request was repeated. The initial inherited item search records are preserved and the additional logged item searches are appended verbatim. Auxiliary searches from the earlier attempt remain in the log; the corresponding proposed nodes are already in the current DAG and were not recreated.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 source for the full item tag, tame inertia, augmentation ideal and the trait notions. The hits concern Hopf-algebra augmentation ideals or a Frobenius argument, not this three-part trait theorem. No declaration supplies all clauses. No Lean was written and no compiler or build tool was run.

## WANTED

None: the proof follows the available ILO Expose XVII, sections 1.2.1–1.2.3, printed pp. 259–262.

## Corrections and comparison with existing material

The item statement is unchanged. Its existing fields, blueprint ancestry and inherited searches are retained. The current repository item and the initial sandbox copy were identical. The current blueprint main-20261015 ancestor and the chapter/unit were read; the trait construction is a generic input below the potential-dualizing interface used in the ancestor's dimension-normalized duality step. It does not replace the unit's Fourier argument or alter either upper blueprint level. The item is not the key node of its unit, so no unit record is changed.

The current DAG contains a reviewed F_ell sibling, lem-per-trait-residue-model. Its proof is useful material, not a proof of the prime-power assertion by specialization. I checked its argument against ILO and adapted the finite-level calculations to q = ell^n. In particular N_(q*d) projects to q*N_d = 0, not ell*N_d; the injectivity extension uses B_(q*d), and the finite geometric sums depend on the exponent modulo q*d. The last step uses a free rank-one Lambda-module, not a one-dimensional vector space. This avoids silently assuming n = 1.

The source proof of Proposition 1.2.2.1 names H^1 immediately before discussing surjectivity onto the last term of a complex placed in degrees 0,1,2. In these degrees that surjectivity is the H^2 calculation. The delivery separately proves both H^1 and H^2 vanish. It also gives the extension argument at finite discrete quotients, rather than treating the compact completed group algebra as an object of the discrete-module category. These are clarifications of the proof, with no statement correction.

## Not duplicates

No new nodes are created. The existing lem-per-trait-tame-algebra and lem-per-trait-sheaf-gluing are reused directly: their statements allow the present trait and arbitrary commutative coefficient ring, respectively. Whole-DAG searches for the item, tame inertia, completed group algebra, natural homotopy and the source tags 0BUB/03QO, plus blueprint_refs.py searches for tame and residue, found the existing F_ell sibling and these inputs. The sibling has Lambda = F_ell; this item has Lambda = Z/ell^n for every n >= 1. It cannot be cited to deduce the latter. The two excellent-trait nodes require extra excellence/residue hypotheses and are not used instead of the more general tame input.

The retained logged searches for the item used LeanFinder with two natural-language phrasings, Loogle on augmentation/profinite, LeanSearch on etale cohomology over prime-power coefficients, and grep on tame/wild inertia and augmentation ideals. Hits include perfectoid/PreTilt material, henselian and etale ring maps, residue-field maps, and Ideal.IsAugmentation. The source of Mathlib/RingTheory/Ideal/IsAugmentation.lean was read: it defines a complement to the scalar submodule and gives a scalar-restriction equivalence, not freeness of this completed group-algebra ideal or the trait residue comparison. No hit states the item or gives it by one-line specialization. No Mathlib searches are invented for existing cited nodes.

## Review by NX

I read ILO Expose XVII pp. 259–262: the opening tame exact sequence, Definition 1.2.1.1, the exercise Proposition 1.2.1.2, the sheaf-arrow description and Proposition 1.2.2.1 with its proof, and the construction and proof of Lemma 1.2.3.2. The source allows Z/N coefficients with residue characteristic invertible; N = ell^n therefore satisfies precisely the stated hypotheses. I opened each cited DAG node and compared its statement with the step using it. The two geometric inputs already give the arbitrary strictly henselian DVR and arbitrary coefficient ring required here. There are no new-node statements to review.

Step 1 uses the full statement of lem-per-trait-tame-algebra for the canonical quotient, pro-p kernel, procyclicity and cyclic finite quotients; it does not infer those from a definition of inertia. No excellence or algebraically closed residue-field hypothesis is added.

Step 2 is the explicit finite cyclic coefficient calculation from the source's exercise. It proves both the kernel and image statements over Lambda, constructs inverse-limit preimages using level q*d, proves independence of the chosen lift and compatibility, and proves injectivity using the same norm projection. It uses no separate lemma about completed group rings and works when d = 1. This is one coefficient calculation, not a clause moved to a new node.

Step 3 uses lem-per-trait-sheaf-gluing for exact stalks, the H-equivariant specialization and its invariant image. The averaging formula is written explicitly, including refinement, conjugation and invariant lifts. The denominator is a p-power unit modulo ell^n; if p = 1 the kernel is trivial and averaging is the identity. Step 2 then identifies Hom_A(I,-) with the underlying module. This checks that F is a complex and is degreewise exact.

Step 4 uses the gluing statement's actual category of triples to check the exact left adjoint V -> (0,V,0). The Mathlib leaf lem-exc-rg-right-adjoint-preserves-injectives states exactly that a right adjoint to a mono-preserving left adjoint preserves injective objects, in arbitrary categories. Its second application is to inflation and S-invariants, with the adjunction checked by factoring maps through invariants. Thus N = V^S is injective in discrete G-modules; injectivity is never asserted in the compact module category.

Step 5 uses the gluing statement's Gamma(T,M) = W and Gamma(eta,M) = V^H, and def-pur-etale-derived-supported-sections for their kernel. H^1 vanishes by an explicit extension along the displayed monomorphism of triples. Step 6 proves H^2 vanishes by extending the well-defined map (1-z)B_(q*d) -> N. The annihilator computation is exactly Step 2; q*N_d*x = 0 holds because q*Lambda = 0, including n > 1. Both extension objects are discrete.

Step 7 cites the general category theorem lem-weil-pbc-module-sheaves-grothendieck-abelian, the Mathlib leaf asserting enough injectives, and the Mathlib leaf asserting bounded-below injective replacement. Their hypotheses are a scheme, a commutative coefficient ring, and an abelian category with enough injectives: all have just been verified. The two cited derived/support definitions identify which derived functor is computed. The off-unit module-sheaf theorem is declared as a generic tool use in split_report.tool_uses, since no theorem of this unit supplies the category input. No maintainer-owned tool_uses field is added.

Step 8 writes the finite-filtration/row elimination arguments that pass from sheaves to bounded-below complexes; it does not just say “totalization preserves”. Only three horizontal degrees occur. The quasi-isomorphism comparison is natural through injective replacements, and supported sections are computed exactly as the cited definition prescribes.

Step 9 factors continuous additive maps through G/qG = mu_q, not through mu_ell. This both gives the correct prime-power twist and verifies exactness of the twist functor. The map has only the degree-two target component, so its cochain-map condition and naturality follow directly from Steps 2–3. No equivariance is imposed on Hom_cont(G,N).

Step 10 uses the gluing statement for the maps of triples reducing natural homotopies to closed stalk zero, then the H-equivariant averaging projector reduces to discrete G-modules. Step 11 proves the natural-operation identification directly by evaluating on finite regular representations and the maps sending 1 to a vector. Step 12 writes the change-of-generator coordinates, with alpha reduced modulo q in Lambda^times, and identifies the homotopy equation (1-sigma)h = 1-g. Step 13 explicitly extends geometric sums through their period q*d, giving epsilon(u) = alpha modulo q and then the unique solution using Step 2. This proves uniqueness of the family of natural homotopies; it does not falsely assert uniqueness for a fixed isolated module.

Step 14 checks the total homotopy signs, localization at quasi-isomorphisms using def-weil-pbc-derived-categories, and the rank-one evaluation isomorphism in a basis. The K-flat definition in def-kun-derived-tensor shows that tensor with this free module already computes derived tensor. The statements of def-asd-finite-etale-tate-sheaf and lem-asd-etale-finite-twist-pullback give precisely the signed twists and canonical inverse-image/evaluation compatibilities. Their coefficient-integer and invertibility hypotheses hold with m = q. None of these citations is used for a result appearing only in its proof. Every citation has a verbatim quotation in citations.json.

I checked B–E of delivery-errors.md: no new auxiliary statement restates a clause; all non-elementary inputs are the cited statements; no new definition or imported statement is changed; the proof is TeX with single backslashes after JSON parsing. No step is longer than 2000 characters (the longest is Step 14, 1567 characters), and each longer calculation is one direct argument, not an unrecorded standard comparison.

Small cases: n = 1 recovers the reviewed sibling; n = 2 requires q, and the displayed q*d calculation gives the correct zero norm projection. For the constant sheaf, F = [Lambda -> Lambda -> Lambda] with first differential the identity and second zero, so only degree-two cohomology remains, of rank one, as expected. For a closed-supported sheaf F = [W,0,0] and the residue is zero. For j_!V the closed stalk is zero, matching the homotopy reduction. Checked d = 1, ell = 2, p = 1, zero modules and nontrivial tame action; no field division is used except inversion of units (p-group orders and generator exponents), and natural homotopy uniqueness uses injectivity of 1-sigma on A, not on an individual module.

Nothing remains mathematically unfinished. Server checks and the required dry-run/push results are recorded by the delivery tool.
