# Q07: lem-sf-weil-lisse-biduality

## Files written

- `dag/nodes/sec-six-functors/lem-sf-weil-lisse-biduality.json`: the item, now split into six steps. No new nodes and no new Mathlib leaves.
- `citations.json`: twelve verbatim statement witnesses, one for each step/node citation.
- `report.md`: this report. `prepare.py` is a sandbox-only reproducible writer, not a repository change. `searches.jsonl` is the search command's log.

## Attachments

None. The exact upstream declaration is `AlgebraicGeometry.WeilSheaf.nonempty_iso_dual_dual`, `lean/WeilConjectures/WeilSheaf/VerdierDual.lean:229-231`, whose proof is `sorry`. Searches of `lean/WeilConjectures` for the item tag, biduality, dual-dual, IsLisse, and this declaration found no completed declaration giving the whole item. The scheme-module theorem with the same last name is for invertible structure-sheaf modules; the Artin–Schreier double-dual theorem is a specialization. Neither attaches this item.

## WANTED

None. The sources needed for this local calculation are available.

## Source error / statement clarified

STATEMENT-DISPUTED: the imported theorem's mathematical conclusion is correct, but its annotations do not type its full scheme domain. It permits an arbitrary k₀-scheme, while `def-pod-lisse-l-adic-sheaves` starts with a Noetherian separated scheme and `def-weil-weil-sheaf-complex` introduces finite-type schemes and common-stage derived coefficient categories. For example, the countable disjoint union of Spec k₀ is an allowed scheme in the actual Lean theorem, and its adic coefficient unit is lisse, but this scheme is not Noetherian or of finite type, so those annotated definitions cannot be instantiated. The irrelevant sentence introducing WC(X) also imposes an unused derived-category convention.

I replaced those annotations with the literal native degree-zero convention read in the library: modules over the sheaf R of locally finite continuous Q̄ℓ-valued functions, locally finite free for the pro-etale topology, with a Frobenius fixed-pair structure. The functions have locally finite-dimensional Qℓ-span, exactly as `locallyFiniteFunctions` specifies; R is not silently replaced with a discrete constant sheaf. The dual is the native internal Hom into R, with inverse Weil structure in its first argument. The arbitrary-X hypothesis and existential isomorphism conclusion are retained. No separatedness, finite type, smoothness, global rank bound, or invariant integral lattice was added. The `lean` record is untouched.

The source and blueprint are followed in their finite-free/locality argument. The current main-20261015 proof is under `sec-six-functors-basics`, whereas the inherited item source records the master path under `sec-six-functors`. Both proof texts were read and agree on the relevant calculation. The item is not the unit's key statement; no unit or chapter record is changed. The maintainer's existing blueprint ancestor `lem-a1-local-boundary-duality` is preserved. The ancestor command prints None because created.item was seeded as null; I did not invent another ancestry chain.

## Searches and reuse

I searched the whole DAG and blueprint by biduality, double dual, finite projective, local module isomorphism, and the relevant source tags. `lem-sf-hom-finite-projective` and `lem-pod-finite-projective-tensor-hom` give ordinary coefficient biduality in their separated finite-type settings; they do not give this arbitrary-scheme native Weil assertion. The general sheaf-Hom and locality nodes below already supply the reusable ingredients. No supporting finite-free bidual lemma was created: its basis calculation belongs in this item's proof.

The command-run Mathlib queries are recorded exactly in `mathlib_searches` and `searches.jsonl`. LeanFinder and LeanSearch found module reflexivity, finite free sheaf transport, isocrystals, and closed-category evaluation naturality, rather than the stated pro-etale Weil result. Loogle's first pattern returned zero hits with an unknown-identifier diagnostic for the project-only name CategoryTheory.Mod.ihom; this diagnostic is preserved, and I did not treat it as a successful absence search. The second substring pattern `"bidual"` returned no hits. A second LeanFinder phrasing asked about closed-monoidal naturality. The source grep queried bidual/dual_dual/reflexive in CategoryTheory and returned equivalence/reflexive-pair material, not this sheaf theorem. The module-level hits do not identify this adic sheaf category or its specified Weil dual, so the item is not a Mathlib leaf. The three pre-existing maintainer search records are retained as inherited records; the appended records are the calls made by Q07.

## Not duplicates

No new nodes. The item is already a maintainer-created node. The finite-projective sf/pod nodes are related but have narrower geometric hypotheses and no assertion about the particular native Weil structures on an arbitrary k₀-scheme, so they are not listed as same_as.

## Review by Q07

I read the item source in the master blueprint and the corresponding current main-20261015 statement and proof; Stacks `sites-modules.tex` at Tags 03EM (lemma-internal-hom), 0E8H (lemma-internal-hom-restriction), and 03EO (lemma-internal-hom-adjoint-tensor); `sites-cohomology.tex` Tag 08JJ (lemma-dual-perfect-complex), especially the degree-zero evaluation calculation; and `sites.tex` Tag 04TQ (lemma-glue-maps). For the actual meaning of the theorem I read native `ConstantSheaf.lean`, `Ring.lean`, `Module.lean`, `Constructible.lean`, `InternalHom.lean`, and `Hom.lean` under SixFunctors/ProEtale/Adic, plus WeilSheaf `Category.lean`, `Dual.lean`, and `VerdierDual.lean`. There are no new nodes whose sources require an additional review. No SGA route is used.

Step 1 uses the statement of `def-weil-sheaf-of-modules-category` for sectionwise action/linearity, `def-pur-sheaf-hom` for slice-Hom, and `lem-pc-sheaf-modules-tensor-closed` for the actual adjunction, not merely its fully faithful or definitional consequences. I checked that R is commutative and that its constant Q̄ℓ-scalars make an R-module map automatically Q̄ℓ-linear. The native action is the sheafified tensor action representing those same bilinear maps; the adjunction comparison is fixed by currying, so it preserves evaluation. This is an ordinary module statement and needs no derived comparison, scalar-localization equivalence, or global projectivity.

Step 2 uses exactly the slice formula in `def-pur-sheaf-hom`. I wrote the component of evaluation on every V→U, checked restriction compatibility and R-linearity, and checked naturality by evaluating at a functional. The restriction identity is an identity of iterated slices, not an unsupported Hom/pullback theorem for arbitrary morphisms. I corrected a draft tag: internal-Hom restriction is 0E8H, not 03EN.

Step 3 uses the same Hom definition and clause (1) of each of `lem-weil-proetale-weakly-etale-localization` and `lem-sfb-proetale-object-inverse-image-restriction`. I opened both nodes. The first actually identifies the sites for a weakly etale site object; the second explicitly includes abelian sheaves in its inverse-image/restriction comparison. Each covering member is such a site object. I use neither node's constant-ring module clause for the adic ring R: on a further object V the adic coefficient identification is directly equality of the locally finite function rings. This verifies that Lean's native pullback trivializations give the literal slice trivializations used in the basis computation. The displayed sum supplies both inverse identities, and also proves that the dual is locally finite free. Thus no node is cited merely for a definition when an isomorphism theorem is needed.

Step 4 uses the actual conclusion of `lem-sfb-sheaf-cover-local-isomorphism` and the small-skeleton convention of `def-weil-size-convention`. I checked its covering condition for every object V by base-changing the chosen covering and enlarging the resulting sieve. The theorem applies to the underlying abelian sheaves. The inverse's R-linearity is then proved by cancellation, rather than assumed from an unrelated constant-coefficient theorem. This works without points of the topos or geometric-stalk conservativity.

Step 5 uses `def-pur-sheaf-hom` for reindexing Hom under the automorphism and `def-weil-endofunctor-fixed-pair-category` for the exact morphism equation. The formula for b is the formula of `dualStr`, not an arbitrary dual structure. The formula for c applies that same definition again. I checked the types: μ takes TM to TR, bμ takes M to R, and c applies the coefficient map s only after evaluating the reindexed double dual. The equation tested against bμ proves the fixed-pair square because b is invertible. It does not assume an invariant trivializing cover or confuse geometric Frobenius with absolute Frobenius.

Step 6 uses the same fixed-pair definition, which explicitly says the forgetful functor is faithful. The cancellation equation for the inverse has the correct direction a T(h)=h c. Its two inverse identities hold as underlying module maps and hence as Weil maps. This produces precisely Nonempty (P ≅ (P.dual hP).dual hP.dual).

I tested zero rank, the empty scheme, ranks varying between infinitely many components, and a rank-one Weil sheaf with scalar eigenvalue α: the first dual has eigenvalue α⁻¹ and the second α, so evaluation intertwines the actual structures. There is no division by a rank or any characteristic restriction in the basis argument. I checked B–E of delivery-errors against the resulting files: no new statement-only/proof mixing, no new duplicate or clause-as-node, no off-hypothesis theorem application, no reliance on another node's proof, and no circular citation. All cited statements were reopened and the twelve quotes verified verbatim. Each proof step is under 2000 characters. The ordinary basis, evaluation, and cancellation calculations are written out instead of hidden behind named new lemmas.

The four generic tool uses are declared only in split_report.tool_uses for maintainer review: the ringed-site closed adjunction, covering conservativity, site localization, and the abelian inverse-image/restriction computation. They support the source's local finite-free route; they do not replace a step by a different geometric route. No top-level approval field is written.

## Unfinished work and checks

No unfinished mathematical part at stage 1. No Lean files were written and no compiler, Lake, or library build was run. The server review_split check passed on the initial six-step version; the final dry run below validates the version with explicit native-cover/slice citations and the corrected Stacks tag.
