# Stage-1 report: lem-sfb-steinberg-infinitesimal-induced-simple

Group Q86; 2026-10-24; direct delivery, with the self-review required by the brief.

## Files written

All node files are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `lem-sfb-steinberg-infinitesimal-induced-simple.json`: item, statement, split. The statement is unchanged. Four steps prove simplicity of the actual regular-function module through its distribution-module dual.
- `lem-sfb-frobenius-kernel-induced-dual-pbw.json`: new statement, unsplit, no Mathlib match. General-character evaluation duality between actual infinitesimal induction and a balanced distribution tensor module, with negative-unipotent freeness.
- `lem-sfb-unipotent-frobenius-distribution-socle.json`: new statement, unsplit, no Mathlib match. Higher-kernel PBW basis, nilpotent augmentation and its explicitly identified one-dimensional left annihilator.
- `lem-sfb-steinberg-top-distribution-recovery.json`: new statement, unsplit, no Mathlib match. A specific product of positive-root distributions takes the top negative-root vector back to a nonzero multiple of the generator.
- `citations.json`: one verbatim statement quotation for each cited node of each proof step.
- `searches.jsonl`, `search-plan.json`, `search-results.json`: actual search log, queries grouped by intended node, and complete outputs for reuse. Sandbox-only scripts prepare the JSON and run the searches; they are not project changes.

There are three new nodes and zero Mathlib leaves. No Lean, compiler, Lake, repository write, launcher edit, or sub-agent was used.

## Attachments

None. Searches by the exact blueprint tag and by Steinberg, baby Verma, Frobenius kernel and infinitesimal induction in `lean/WeilConjectures/` found no declaration of this assertion. Lang--Steinberg for semilinear vector spaces and Artin--Schreier Frobenius kernels are different assertions. No upstream sorry declaration is treated as a proof.

## Wanted literature and source provenance

WANTED: Jens Carsten Jantzen, *Representations of Algebraic Groups*, second edition, Part I distribution/finite-group/Frobenius-kernel chapters I.7--I.9, and Part II.3.18 and II.9.1, for the item and all three new nodes. No local copy was found in the named literature directory. In particular I did not read the claimed book proof or invent a quotation from it.

I read the primary corroboration already named by the item: Masaharu Kaneda, *On the Frobenius morphism of flag schemes*, Pacific J. Math. 163 (1994), Section 2.5, equations (4)--(9), printed pp.322--323, https://msp.org/pjm/1994/163-2/pjm-v163-n2-p07-s.pdf . It defines infinitesimal induction, records its duality and socle structure, and states the Steinberg simplicity result, referring to Jantzen II.3.18. It does not supply the exact evaluation-dual identification or top-root computation stated here. Those inputs are explicitly agent-formulated statement-only nodes, not alleged transcriptions from Kaneda or from the unavailable book. The assembly proof is marked `proof_origin.by = agent`.

The new nodes' source places say precisely this, and do not claim an inspected theorem number for the top-product identity. There is no applicable Stacks tag for these reductive-group representation assertions; I have not substituted a tag for a book result. No SGA source is used.

I also read the current blueprint unit and its direct-images proof (3) under `literature/blueprint/latest/`, and the chapter/unit DAG records. These give the higher-level direct-image route and the provenance of this supporting algebraic-group input. They do not themselves contain an infinitesimal representation proof. The item's inherited `blueprint.from.node` is null; `blueprint_refs.py ancestor` confirms that null ancestor. I retained it and extended the existing place/via chain for the three new nodes. Whole-blueprint searches for Steinberg, infinitesimal induced, distribution, socle, Verma and PBW found no duplicate; the one Steinberg hit is the unrelated semilinear Lang theorem. A broader induced search was also read for relevant hits.

## What needed repair or expansion

The live item was statement-only, with no sandbox split/report/search log from an earlier attempt. I copied it and preserved its statement, provenance, original recorded searches and all other inherited fields. No statement dispute or change was needed.

The source specifies the infinitesimal route, before global induced dimensions, Kempf vanishing and Weyl filtrations. The split follows that constraint. In particular it does not cite the global Steinberg irreducibility, restricted Weyl-module freeness, or the item's parent, each of which risks a dependency cycle or the wrong route.

A sign check is essential: the functions satisfy right transformation by the positive character and carry inverse left translation. In the contragredient, evaluation at the identity transforms by the positive character, so the tensor generator has weight +(q-1)rho. There is no missing negative sign or modular-character assumption in that identification. The antipode is displayed in the evaluation formula and in the annihilator argument.

I initially considered citing the kernel-socle statement to choose root parametrizations. That statement assumes them. In the final step 1 I instead cite and quote the actual existing parametrization theorem, together with the pair-structure theorem's assertion that a semisimple group is reductive. This repairs the potential C4 gap.

## Mathlib searches

For each of the item and the three intended new nodes I ran the prescribed `msearch.py Q86 lem-sfb-steinberg-infinitesimal-induced-simple` command with LeanFinder, Loogle, grep and LeanSearch, and a second LeanFinder phrasing. All twenty invocations completed; their outputs were read and retained. Each JSON record uses the exact tool/query string and corresponding logged response metadata. All searches were available in this run. The item's inherited searches are retained, followed by the new ones.

The meaningful hits include abstract-group `Representation.dual` (Basic.lean:678), `Representation.IsIrreducible` and its group-algebra correspondence (Irreducible.lean:29--35), finite-index abstract-group induction/coinduction (FiniteIndex.lean:105--121 and following), ordinary tensor-dual equivalences, Lie-module weight-chain endpoints (Weights/Chain.lean:255--275), and commutative divided-power ideal structures (DividedPowers/RatAlgebra.lean). I opened the relevant source sections. None is a one-line specialization to representations detected by the coordinate coalgebra of a nonreduced Frobenius kernel. In particular, equality on F-points cannot replace that coaction. The socle grep hits were only `assocLeft` substrings in Holor.lean. No matching leaf was missed among these outputs.

## Not duplicates

lem-sfb-frobenius-kernel-induced-dual-pbw vs lem-sfb-steinberg-infinitesimal-restriction-injective: the existing assertion embeds global section functions into the infinitesimal function space at one weight; the new assertion identifies the latter's dual with a tensor-induced distribution module for every character. Neither statement supplies the other.

lem-sfb-frobenius-kernel-induced-dual-pbw vs lem-sfb-steinberg-weyl-restricted-freeness: the existing assertion concerns the dual of a global flag section module at r=1; the new one concerns actual infinitesimal functions for arbitrary characters and r, and includes evaluation duality. It makes no claim of global section-module freeness.

lem-sfb-unipotent-frobenius-distribution-socle vs lem-sfb-unipotent-restricted-enveloping-augmentation: the existing assertion is about a height-one restricted enveloping algebra and gives nilpotence/dimension; the new assertion is about every Frobenius kernel and identifies the annihilator by a specified top divided-power product. For r>1 it cannot be obtained by simply putting a larger prime in the old assertion.

lem-sfb-unipotent-frobenius-distribution-socle vs lem-sfb-restricted-pbw-top-pairing: the existing assertion gives the height-one restricted-enveloping PBW pairing and a highest torus-weight line; it does not state the higher-kernel algebra or its left augmentation annihilator. The overlap at height one is intentional, and the new statement is needed at arbitrary r.

lem-sfb-unipotent-frobenius-distribution-socle vs lem-sfb-finite-hopf-frobenius-form: the latter concerns a commutative Hopf algebra and an unspecified Frobenius form. The former concerns a generally noncommutative distribution algebra, nilpotent augmentation, and a specified root-distribution integral. Applying the old commutative theorem to this algebra is invalid.

lem-sfb-steinberg-top-distribution-recovery vs lem-sfb-restricted-pbw-top-pairing: the existing pairing is internal to one unipotent restricted enveloping algebra at height one; the new identity uses both opposite radicals acting on a specified tensor-induced module at every height. The old statement does not assert the identity.

lem-sfb-steinberg-top-distribution-recovery vs lem-sfb-steinberg-infinitesimal-induced-simple: the new assertion is one explicit operator calculation in the dual tensor model; it does not assert simplicity, rationality, nonvanishing of the function space, or classification of submodules. Steps 2--4 carry that argument.

lem-sfb-frobenius-kernel-induced-dual-pbw vs lem-sfb-steinberg-infinitesimal-induced-simple: identification/freeness holds for arbitrary characters and does not imply irreducibility; at the zero character a nontrivial kernel gives an elementary counterexample to such an implication. The special top-operator calculation is a separate essential input.

lem-sfb-unipotent-frobenius-distribution-socle vs lem-sfb-steinberg-infinitesimal-induced-simple: a unipotent kernel distribution algebra has a one-dimensional socle for every induced character, including reducible baby Vermas. It says nothing about whether that socle generates the whole S_r-module.

The general-character duality, the unipotent algebra structure, and the particular scalar calculation are distinct lemmas, not the item's clauses renamed. All three new nodes have empty proof/proof_deps and no proof hidden in their statements.

## Review by Q86

I checked delivery-errors B--E against the files and the sources, including the complete repeated B--E sections. For the item the source actually read is Kaneda 2.5, plus the current blueprint unit/direct-images proof for the route. For each new node I inspected the potentially overlapping DAG statements named above and the reported Mathlib candidates. The book is absent, so each new source explicitly records an agent formulation and the precise material wanted; I do not sign off an unread book proof as read. The supporting statements are independently meaningful and smaller than the item.

Step 1 uses three exact statements. The pair-structure node explicitly says a semisimple group is reductive; this verifies the reductivity hypothesis of the root-parametrization node. That node gives root subgroups isomorphic to the additive group for every root, so parametrizations exist on both signs. The new dual/PBW node supplies an opposite Borel, rational left translation on the actual functions, dimension q^N, the evaluation isomorphism, and negative-radical freeness. Its field, characteristic, simple-connectedness, torus/Borel and character hypotheses are exactly those in the item. Raising the supplied B-character to q-1 gives the required character, with no choice of a new character. The resulting function equation is literally the item's function equation.

Step 2 uses only the statement of the new kernel-socle node, applied to the opposite radical explicitly covered by its final clause. The freeness identification from step 1 transports the left annihilator, with the same order and parametrizations for f_top. The nilpotent-ideal argument is written out: choose the largest nonzero J-power on W and use its nonzero image in the one-dimensional annihilator. No finite-group-point invariant theorem or implicit socle classification is used. This step is elementary once those statements are given.

Step 3 uses the precise scalar identity in the new top-recovery node. Its A, B_r-character, balanced module and chosen root distributions agree with steps 1--2. It gives a unit scalar, so stability under the displayed element of A puts v in W. The equality M=Av follows directly from the defining tensors, not from another unstated theorem. The substantive calculation is isolated as an unsplit statement rather than passed off as elementary.

Step 4 uses the dual-action formula in the new dual/PBW node. I checked the direction of the antipode: (a ell)(w)=ell(sigma(a)w), and sigma(a) is again in A. Thus annihilators of restricted-coaction-stable subspaces are submodules. The finite-dimensional basis-extension argument excluding a proper subspace with zero annihilator is included. This step invokes only preceding steps and that formula. `citations.json` quotes the actual statements, not their proof text or metadata, for every node in every step.

Small cases: for S=1, N=0, H=M=Z=F, J=0, the top products and scalar are 1. For a rank-one additive root kernel, the distribution basis d^(i), 0<=i<q, multiplies by binomial coefficients; its augmentation has top annihilator F d^(q-1), including r>1. For SL2 at highest weight q-1, e^(q-1)f^(q-1)v=binom(q-1,q-1)v=v, also for p=2,r=2. With highest weight 0 the same top scalar vanishes when q>1; this checks that the special-weight hypothesis cannot be dropped. Product groups give tensor products of these tests. No factorial inverse is used when q>=p, and no differentiation of torus characters substitutes for character identities in small characteristic.

All notions have defining dependencies or inline definitions, all new statements introduce their own objects, all copied mathematics has single TeX backslashes after JSON decoding, and no statement was weakened. I checked the parent's dependency direction and avoided its other descendants. The three new inputs do not depend on the item or its parent. Every main proof step is below 2000 characters, and the four-step assembly is below 3000 characters. No long-step hidden lemma remains. The largest non-elementary operations are precisely the three unsplit inputs.

## What could not be finished

No assembly obligation remains. The three new nodes are deliberately statement-only, as a one-level stage-1 split requires. The missing book is a literature limitation explicitly recorded above; it was not used as a reason to leave the item's proof incomplete. Mechanical preflight and server DAG/review diagnostics are recorded by the delivery command.

## Delivery tool outcome

The full dry run exited successfully: `OK (not pushed) deliver/Q86/lem-sfb-steinberg-infinitesimal-induced-simple at cda1ca783ce: preflight passed`.

Two subsequent non-overlapping push invocations each passed server preflight but failed during remote Git unpack with `remote unpack failed: unable to create temporary object directory` and `(unpacker error)`. The attempted commits were b9bfd5bf0d15f4a912671749fe54a8b83c368057 and b16384f90627b6f53e6070f2c3795dda2af8e3e6. Neither command printed DELIVERED. All split/report/search/citation artifacts remain in this sandbox for retry after the remote server is repaired. No launcher or repository was modified to work around the failure.
