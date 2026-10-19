# Worker report: lem-weil-proetale-isomorphism-inverse-image

## Files written

- dag/nodes/sec-smooth-purity/lem-weil-proetale-isomorphism-inverse-image.json: re-split into nine steps; statement, statement dependencies and Lean record preserved verbatim.
- dag/nodes/sec-smooth-purity/lem-weil-iso-weakly-etale.json: statement; Mathlib leaf, WeaklyEtale.instOfEtale with the existing instance chain from IsIso through open immersion and etale.
- dag/nodes/sec-smooth-purity/lem-weil-sheaf-scalar-extension-ring-iso.json: statement-only general normalized tensor comparison for an invertible coefficient-ring map on any small site; no complete Mathlib match.
- citations.json: verbatim statement quotations for every dependency used in each of the nine steps.
- searches.jsonl: actual search-command log. Searches from this run, including exploratory searches not used in a node, are retained.

## Attachments

None for the item. Searched WeilConjectures in the read-only slopmaster2 source by its blueprint tag and by the inverse-image/isomorphism notions. Its general pro-etale operations do not provide an exact closed declaration containing all the specified comma normalization, constant-ring naturality, module pullback, and tower-comparison clauses. The existing Sheaf.* Lean record is retained; its presence is not an upstream WeilConjectures attachment. The exact master checkout is reference material, not evidence of proof completion.

The closest existing helper, AlgebraicGeometry.etaleModuleRingIsoTensor, belongs to lem-weil-pbc-etale-module-ring-iso-tensor already. Its DAG statement is restricted to small etale sites. It cannot be cited for the pro-etale module comparison (C4).

## WANTED

None. The Stacks source and current blueprint needed here are available locally.

## Problems corrected

This is the repair recorded in coord/repair-notes/lem-weil-proetale-isomorphism-inverse-image.json. The retained proof packed independent arguments into long steps. I preserved its route and all five original mathematical parts, while extracting the geometric input as a Mathlib leaf, citing the already existing site-equivalence theorem and sheafification-compatibility leaf, and extracting the normalized module-tensor identification as a general lemma. The comma initial-object verification and terminal-index colimit calculation are written out in one short elementary step, rather than made into new elementary nodes. No statement dispute was found and no target or Lean statement was changed.

The scalar-extension helper is deliberately only the identification of the tensor-defined module on a fixed site. It does not assert the scheme-isomorphism equivalence, identify g_* or g^{-1}, or prove any clause of the item by itself. This is the inline identification that the human's long-step instruction requires to become a cited node. It is not a renamed module clause. No new site-equivalence or sheafification node was created because the DAG already supplies them.

## Unfinished work

The new scalar-extension lemma is left unsplit, as required for a one-level delivery. Its mathematical argument is: on each object, the balanced map m tensor s maps to c^{-1}(s)m, with inverse m maps to m tensor 1; the tensor relations show the composites are identities. These maps commute with restrictions and with module homomorphisms. The target is already a sheaf, so the presheaf isomorphism extends uniquely through sheafification. This proof belongs to the later split of that helper and is not stored in its statement. There is no unresolved argument in the item's nine steps once its cited statements are supplied.

## Review by Q52

I read the current node and the maintainer's repair note, the current main-20261015 coefficient-object paragraph in def-weil-ordinary-compact-cohomology, the recorded unit and chapter, and the constant-Weil-structure parent. The current blueprint still asks for the canonical constant coefficient comparison and its compatibility with reduction and limits. The re-split follows that route. The historical sk-def-sf-admissible metadata and the Lean record are preserved rather than changed by this worker.

For sources I read Stacks proetale.tex, Tag 09A5, which constructs the base-change morphism of sites; sites.tex, equation 053L in 00VC and the adjunction 00WX, the sheafification universal property 00WH and constant-sheaf definition 0H7J; the site-equivalence criterion 03A0; more-morphisms.tex, definition 094P and its following etale paragraph; and sites-modules.tex, the restriction/change-of-rings construction and adjunction 03CZ. I also read the actual Mathlib instance bodies in WeaklyEtale.lean:44 and :58, Etale.lean:78, and OpenImmersion.lean:481; the equivalence/sheafification constructions in Sites/Equivalence.lean:109–167; the exact dense-subsite sheafification compatibility in DenseSubsite/Basic.lean:805; and the terminal-index cocone and colimit proof in Limits/Shapes/IsTerminal.lean:385–399. Only Stacks and Mathlib are sources here, with no SGA route.

Step 1 uses the new weakly-etale Mathlib leaf, the existing composition theorem, and the actual small pro-etale site definition. These say respectively that g and h are eligible morphisms, their postcompositions remain weakly etale, and the covering condition depends only on the underlying covering arrows. The inverse identities act on the same U and arrows, so no qcqs, nonempty or finite-type assumption enters.

Step 2 uses precisely the comma category and coprojection/restriction construction in def-weil-proetale-inverse-image. I checked the orientation: D_U is initial in I_U and terminal in its opposite, the diagram is contravariant restriction, and the arrow is pr_2 phi. The two fibre-product projections establish the equation and uniqueness; the coprojection and restriction cocone give inverse maps. Naturality is verified for both a site arrow and a sheaf morphism. This uses no non-elementary uncited colimit theorem: its elementary universal-property proof is included. Ring operations are respected because these are restriction homomorphisms, rather than arbitrary set bijections.

Step 3 cites the statement of lem-weil-pbc-site-equivalence-is-morphism-of-sites, especially its clause (3), not its proof. That statement supplies both sheafhood and the set/abelian equivalences under the exact covering-iff hypotheses from Step 1. The ring extension uses the same sectionwise operations and identities. The sheafification definition supplies the universal property needed to replace sheafification of an already-sheaf by itself. The size requirement is exactly the site's recorded choice of universes.

Step 4 uses the actual g_* formula in def-weil-proetale-inverse-image and the full limit/colimit preservation statement of lem-galois-equivalence-preserves-limits. The explicit fibre-product isomorphism identifies g_* with S. Exactness in the abelian category follows by preserving kernels and cokernels and the sectionwise addition on morphisms.

Step 5 uses the statement of lem-pc-dense-subsite-sheafification-compatibility, not merely a generic equivalence theorem: it supplies (P restricted)^# isomorphic to P^# restricted. I checked all its hypotheses: full faithfulness, covering of every object by an object in the image, induced topology, restriction equivalence for ring sheaves, and existence of ring sheafification. The first three follow from Step 1 and covering invariance under isomorphisms; Step 3 gives the fourth; the cited sheafification definition is the construction in use for the fifth. Constant sheaves are the sheafifications of constant presheaves by their cited definition. Choosing the unique map extending the unit fixes beta_A on constants; no assertion that all sections of A_Y are constant is used.

Step 6 uses the specific definition of rho_A and c_A as adjoints, including the unit coprojection. Computing at (V,id) and restricting along pr_2 gives the required adjoint on constants. Sheafification uniqueness then identifies the actual map and proves the coefficient-homomorphism square. This is a short normalization argument from the cited definitions and the earlier explicit comparison, so it is marked elementary.

Step 7 applies the new tensor lemma with the precise ring sheaves R=T(A_Y), S=A_X, isomorphism beta_A, and module M=T(F). These objects are introduced before the application, and the scalar map is proved invertible in Steps 5–6. The helper's statement includes exactly the formula and inverse needed, with no etale-site restriction. The given pro-etale inverse-image definition specifies that same sheafified tensor construction. Thus the item no longer hides the tensor-comparison lemma in a long step.

Step 8 checks the specified module g_* action, using its definition and equality of the constant-section-normalized ring maps from Step 6. The two inverse scalar identifications make the unit and counit linear. The cited module-category definition explicitly states abelianness and the kernel/cokernel descriptions. The preservation theorem really gives all existing limits and colimits, rather than merely finite ones.

Step 9 uses the full inverse-limit statement, including its coordinate projections, and the limit-preservation theorem. The inverse-limit node includes modules, abelian groups and rings, but not sets; accordingly I retained the explicit coordinatewise gluing and cone argument for sets. The universal-property argument identifies exactly the map induced by the inverse images of the projections, not an unspecified isomorphism of limit objects.

I checked B–E of delivery-errors.md against these files: the new non-leaf has a statement only, all its objects and hypotheses are introduced, sources have labels/tags, no Lean-sorry declaration is treated as an attachment, and no new node restates a pro-etale clause. Every uses entry was opened and compared with the needed assertion; citations.json quotes the actual statements verbatim. The small cases checked are g=id, empty schemes and empty coverings, the zero coefficient ring, disconnected sites with nonconstant locally constant sections, the identity coefficient-ring isomorphism, and a nontrivial ring automorphism. In the last case the inverse c^{-1} in the module action and theta formula is essential; the stated formula has that inverse. The tower comparison remains valid for a constant or zero tower. The new ring-sheaf lemma has no finite-coefficient, finite-generation, flatness or noetherian hypothesis. All nine final steps have fewer than 1100 characters; none hides an additional non-elementary subclaim.

The off-unit site-equivalence theorem is declared in split_report.tool_uses as an abstract tool. The dense-subsite compatibility is already a Mathlib leaf. Neither replaces the unit's route.

## Not duplicates

lem-weil-iso-weakly-etale vs def-weil-weakly-etale-morphism: the existing node defines weak etaleness; the new Mathlib leaf asserts that every scheme isomorphism satisfies it.

lem-weil-iso-weakly-etale vs def-weil-pbc-weakly-etale-morphism: the existing node defines weak etaleness; the new Mathlib leaf asserts that every scheme isomorphism satisfies it.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-weil-pbc-etale-module-ring-iso-tensor: the existing statement assumes small etale sites and comparison functors L_0,L_M,t; the new fixed-site statement applies to arbitrary small sites, including pro-etale sites, and compares the tensor directly with the inverse-ring-action module, without those extra functors.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-sc-hom-tensor-comparison-natural: the existing node concerns Naturality of the sheaf tensor comparison isomorphism; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-sc-hom-tensor-summand-restriction-ext: the existing node concerns Internal Hom maps determined by total tensor summand restrictions; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-sc-internal-hom-coproduct-fan: the existing node concerns Internal Hom of a coproduct is a product; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-pc-sheaf-modules-tensor-closed: the existing node concerns Sheaves of modules on a site form a symmetric monoidal closed category; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-sc-hom-tensor-section-natural: the existing node concerns Naturality of the canonical presheaf-to-sheaf tensor map; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-sc-hom-tensor-summand-localized-ext: the existing node concerns Localized pure-tensor extensionality for a sheaf tensor; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-pc-sites-sheaf-tensor-bilinear-universal: the existing node concerns Universal property of sheaf tensor product; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-sc-internal-hom-product-fan: the existing node concerns Internal Hom preserves integer-indexed product fans; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-sc-hom-tensor-reverse-pair: the existing node concerns Reverse currying for one pair of module sheaves; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-weil-pbc-continuous-module-encoding-scalar-extension: the existing node concerns Scalar extension under the continuous integral and rational module encodings; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs def-weil-pbc-ringed-tensor-section-calculus: the existing node concerns Section calculus for the actual sheaf tensor and scalar extension; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-weil-pbc-tensor-local-bijection-universes: the existing node concerns Tensoring a local module bijection commutes with sheafification in independent universes; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-w2-inverse-image-change-of-rings-unit-smul: the existing node concerns Scalar compatibility of the inverse-image change-of-rings unit; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-weil-pbc-continuous-module-encoding-lattices: the existing node concerns Local freeness and lattice compatibility of the explicit continuous encodings; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-weil-pbc-scalar-tensor-comparison-universes: the existing node concerns Scalar-extension tensor associativity on underlying abelian sheaves in independent universes; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs def-pur-kummer-module-coefficients: the existing node concerns Kummer sheaves with module coefficients and their scalar actions; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs def-pur-sheaf-tensor-product: the existing node concerns Tensor product of sheaves of modules on a site; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs lem-pur-change-of-rings-tensor-comparison: the existing node concerns Natural comparison of restricted scalar extension and sheaf tensor; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.

lem-weil-sheaf-scalar-extension-ring-iso vs def-pur-presheaf-tensor-product: the existing node concerns Presheaf tensor product of modules; the new node asserts the normalized isomorphism M tensor_R S to the same sheaf with inverse-c scalar action for a ring-sheaf isomorphism c, with its inverse on all sections.
