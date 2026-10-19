## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-flat-finite-module-presentation.json`: repaired split item.
- `def-trf-valuation-ring`: definition/Mathlib leaf for the valuation-ring hypothesis.
- `lem-trf-valuation-finite-type-module-presentation`: statement-only Stacks input, no Mathlib match.
- `lem-trf-finitely-presented-over-subring`: statement-only Stacks input, no Mathlib match.
- `lem-trf-flat-module-torsionfree-domain`: Mathlib leaf by `Module.Flat.torsion_eq_bot` and `Submodule.isTorsionFree_iff_torsion_eq_bot`.
- `lem-trf-module-submodule-localization`: Mathlib leaf by `Submodule.localized'gi` and `GaloisInsertion.l_u_eq`.
- `lem-trf-localization-preserves-finite-presentation`: Mathlib leaf `instFinitePresentationLocalizationLocalizedModule` at `Mathlib/Algebra/Module/FinitePresentation.lean:361-364`.
- `citations.json`: verbatim citations for every item proof use.

## Attachments

No existing Lean declaration states the item. No new node has a closed slopmaster2 declaration.

## WANTED

None.

## Not duplicates

- `def-trf-valuation-ring` vs `def-sc-discrete-valuation-ring`: the new definition allows arbitrary value groups and gives the valuation-ring fraction-field criterion; the existing node is only the discrete valuation-ring notion with principal maximal ideal and nonfield condition.
- `lem-trf-valuation-finite-type-module-presentation` vs `lem-trf-valuation-flat-finite-module-presentation`: the former assumes a finite type algebra and proves the finite-presentation result used inside the latter; the item allows essentially finite type and a local map.
- `lem-trf-flat-module-torsionfree-domain` vs `lem-trf-valuation-torsionfree-flat`: the new Mathlib leaf is flat over a domain implies torsion-free, while the existing node is torsion-free over a valuation ring implies flat.
- `lem-trf-module-submodule-localization` vs `lem-weil-pbc-localization-module-exact`: the former identifies submodules of a localized module with localizations of inverse images; the latter states exactness of localization.
- `lem-trf-localization-preserves-finite-presentation` vs `lem-pc-affine-tensor-cohomology-localization-square`: the existing node is a cohomological tensor square, not module finite presentation under localization.

## Review by Q109

I reread the item source, More on Algebra Lemma Tag 0GSE (lemma-valuation-ring-flat-essentially-finite-type), part (2), lines 6005--6044, including its polynomial-localization reduction and the exact sequence argument, and the preceding finite-type valuation lemma Tag 053E, lines 5967--6001. The item statement retains the source's valuation-ring, local essentially-finite-type, finite-module, and A-flat hypotheses and B-finite-presentation conclusion. I added `def-trf-valuation-ring` and checked its source against Algebra Definition Tag 00I9 and Lemma Tag 00IB; its Mathlib match is `ValuationRing` together with `ValuationRing.TFAE`. I added that definition and the existing flatness definition to `stmt_deps`, so the two notions used in the statement are explicitly defined.

Step 1 uses the statements of `def-weil-pbc-essentially-finite-type-algebra` and `def-weil-pbc-finite-type-algebra`: they provide the finite-type algebra, its polynomial presentation, and the localization data. I checked that the inverse image of the local maximal ideal is the prime q and that every denominator outside q maps to a unit, making the map from P_q to B surjective. Step 2 now says only that a finite surjection P_q^r -> M is chosen and K is its kernel; it no longer asserts a finite presentation before it has been proved (the returned E3 fault). The cited `lem-trf-module-submodule-localization` statement says exactly that the inverse image L localizes to K, which gives the injection N=P^r/L into M. Step 3 uses the newly cited valuation-ring definition and flatness definition, then `lem-trf-flat-module-torsionfree-domain` for flat over the domain implies torsion-free, `lem-trf-valuation-torsionfree-flat` for torsion-free over a valuation ring implies A-flat, and `lem-trf-valuation-finite-type-module-presentation` for finite presentation over P. The finite P-module claim follows directly because N is a quotient of P^r. Step 4 uses `lem-trf-localization-preserves-finite-presentation`, whose Mathlib source was corrected to lines 361--364, and `lem-weil-pbc-localization-module-exact` to identify N_q with M; `lem-trf-finitely-presented-over-subring` then transfers finite presentation across the finite-type map P_q -> B. Every quoted node statement was opened and copied verbatim into `citations.json`.

For the five existing new nodes I added the required `lean_audit` records with both master and slopmaster2 states `none`; the item also carries the same explicit audit record. I reread each new node's source and searches: Tag 053E for the finite-type valuation presentation, Tag 0561 for finite presentation over a finite-type subring, Tag 0539/Mathlib for flat torsion-freeness, Tag 00CU/Mathlib for localization of submodules, and the Mathlib finite-presentation localization instance. The three Mathlib source locations and line numbers were checked directly; in particular the localization instance is at lines 361--364, not 574. I searched the whole DAG and blueprint for duplicate statements before retaining the listed nodes. Small cases checked include M=0, A a field (a valuation ring), and localization at the unit submonoid; all clauses reduce correctly. No source error or hidden long lemma remains.

## Repairs to returned review

- E3: Step 2 chooses a finite surjection and kernel, not a finite presentation.
- B3: added and cited the self-contained valuation-ring definition node.
- B3: added `def-weil-pbc-flat-ring-map` to the item statement dependencies and Step 3 citations.
- B6: corrected the localization Mathlib match to `FinitePresentation.lean:361-364`.
- Added `lean_audit` records to all five new dependency nodes (and the item).
- `lem-trf-flat-module-torsionfree-domain` vs `lem-weil-pbc-pid-torsion-free-module-flat`: the existing node assumes a PID and proves torsion-free implies flat; this node proves flat implies torsion-free for every domain.
- `lem-trf-flat-module-torsionfree-domain` vs `lem-sbc-punctured-dvr-normalization-stalk-domain`: the existing node proves a normalization stalk is a domain, not a module torsion criterion.
- `lem-trf-flat-module-torsionfree-domain` vs `lem-sbc-punctured-dvr-normalization-stalk-torsion-free-injective`: the existing node proves injectivity of one normalization stalk map under DVR hypotheses, not flat implies torsion-free.
- `lem-trf-flat-module-torsionfree-domain` vs `lem-sbc-punctured-dvr-normalization-stalk-torsion-free`: the existing node is a geometric normalization-stalk torsion-free result, not the general algebraic implication.
- `lem-trf-flat-module-torsionfree-domain` vs `lem-sbc-root-normalization-generic-stalk-flat`: the existing node is a geometric flatness conclusion for a normalization stalk, not flat implies torsion-free.
- `lem-trf-flat-module-torsionfree-domain` vs `lem-weil-pbc-adic-tor-flat-cohomology`: the existing node concerns an adic Tor/cohomology module, not the domain torsion criterion.
- `lem-trf-flat-module-torsionfree-domain` vs `lem-trf-valuation-separable-closure-extension`: the existing node concerns faithful flatness of valuation extensions, not flat implies torsion-free.
- `lem-trf-localization-preserves-finite-presentation` vs `lem-pc-affine-tensor-localization-flat`: the existing node states flatness after tensor localization, not finite presentation preservation.
- `lem-trf-localization-preserves-finite-presentation` vs `lem-pc-affine-tensor-target-flat-extension`: the existing node states target flatness after extension, not finite presentation localization.
- `lem-trf-localization-preserves-finite-presentation` vs `lem-pc-localization-restriction-kflat`: the existing node concerns K-flat restriction, not finitely presented ordinary modules.
- `lem-trf-localization-preserves-finite-presentation` vs `new-lem-pc-complex-localization-unit-kernel`: the existing node concerns a derived-complex localization unit/kernel, not module finite presentation.
- `lem-trf-localization-preserves-finite-presentation` vs `lem-weil-pbc-affine-intersection-quotients-stalk`: the existing node identifies affine intersection quotient stalks, not finite presentation preservation.
- `lem-trf-localization-preserves-finite-presentation` vs `lem-weil-pbc-localization-finite-gl-dim`: the existing node concerns finite global dimension after localization, not module finite presentation.
- `lem-trf-localization-preserves-finite-presentation` vs `lem-weil-pbc-localization-ideal-kernel-generators`: the existing node concerns generators of a localized ideal kernel, not arbitrary finitely presented modules.

## Repair verification (2026-10-18)

The returned review's B3/G1/F3/F5 points are now represented in the files themselves: `def-trf-valuation-ring` is a self-contained valuation-ring definition with its normal-domain and fraction-field dependencies; `lem-trf-module-submodule-localization` carries the module-localization definition dependency; the item and Step 3 explicitly carry `def-weil-pbc-flat-ring-map`; and every delivered node (the item plus all six new nodes) has explicit `lean_audit.master` and `lean_audit.slopmaster2` records with state `none`. I reran the required item LeanSearch query and appended its exact result to the item's `mathlib_searches`; the query returned only generic finite-presentation declarations, so the item remains without a Mathlib match. The server `check_dag` and `review_split` checks both pass, and the final stage-1 preflight dry run passes.
