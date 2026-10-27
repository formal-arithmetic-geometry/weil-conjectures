# Stage-1 delivery: lem-sfb-adequate-relative-spectrum

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adequate-relative-spectrum.json: item split into five proof steps; statement unchanged; appended genuine Mathlib searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-relative-spec-construction.json: one new statement-only general algebraic-stack relative-spectrum lemma, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every use in every item step.
- searches.jsonl: actual msearch output digests; no invented query.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for adequate, relative spectrum, relativeSpec and relative_spec. The affine relative-spectrum declarations found in AffineMorphismRelativeSpec, RelativeSpectrumAffineRealization and RelativeSpectrumStructureAlgebra concern schemes. They do not give an algebraic-stack assertion or any adequate-moduli conclusion. No new Lean was written and no compiler was run.

## WANTED

WANTED: Jarod Alper, Adequate moduli spaces and geometrically reductive group schemes, arXiv:1005.2398v3, Lemma 5.2.11 (printed p.28), for lem-sfb-adequate-relative-spectrum. The primary PDF was read online at https://arxiv.org/pdf/1005.2398v3; there is no local Alper PDF. This is why proof_origin.by is agent, with the local Stacks construction as its document. The elementary assembly follows the source's affine-composition idea, expanded via affine etale charts.

## Findings and route

The item was unsplit with no previous sandbox node or report. No released repair note was found. Its statement is true as written; no STATEMENT-DISPUTED correction is needed. The existing source's one-sentence proof suppresses the algebraic-stack relative-spectrum construction and the affine-target adequacy checks. These are made explicit, rather than applying Alper 5.2.11 as a new node identical to the item.

Read the chapter record and unit record, the latest sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (3). This is the existing alteration/moduli supporting chain below the direct-image input, and no chapter or unit route was changed. The item's inherited blueprint.from.node is null; blueprint_refs.py ancestor also returns None. Retained that provenance, filled the new node's precise from.place and prepended the item to via. Whole-blueprint searches for adequate, relative spectrum, affine algebra, relative spectrum algebraic stack and 05UM found no equivalent blueprint node. The existing scheme and space relative-spectrum nodes are constituents, not the missing stack theorem.

The only off-unit proof tool is lem-trf-space-chartwise-etale-permanence. It supplies generic composition/base-change of the etale cover and is declared in split_report.tool_uses. All other proof inputs belong to this item's supporting unit. No SGA reference is used.

Mathlib searches for the item and the new construction were run through msearch.py, including two natural-language phrasings, Loogle, LeanSearch and grep. The hits were read: affine schemes, the scheme Spec/Gamma correspondence, affine scheme morphism properties, algebraic ring spectra and scheme structure-sheaf stalk maps. None proves a theorem over algebraic stacks or adequate moduli spaces. No Mathlib leaf is claimed.

## Review by N6

I read delivery-errors B through E in full and applied the checks to the actual statements, not their titles. I read Alper 5.2.11 in the primary PDF. For the new construction I read constructions.tex Tag 01LX (lemma-spec-properties: arbitrary base change and the tautological algebra isomorphism), morphisms.tex Tag 01SA (lemma-affine-equivalence-algebras), algebraic.tex Tag 05UM (lemma-representable-morphism-to-algebraic), and spaces-morphisms.tex Tags 081V/081W. This new theorem concerns all algebraic stacks and arbitrary quasi-coherent algebras; it says nothing about adequacy. Its later proof can take the fibred groupoid of pairs, use the scheme relative-spectrum functor on every scheme test, and descend the tautological algebra maps. Representability and the stack condition permit 05UM; on smooth tests the tautological pushforward is the original algebra. The algebraic-space clause is the existing 081V construction. These details are report material; the new node itself contains only a statement and an empty proof.

For step 1 I opened def-sfb-adequate-moduli-space and lem-sfb-stack-qcqs-algebra-direct-image. The former explicitly supplies qcqs. The latter explicitly supplies a quasi-coherent right adjoint with the smooth-test direct-image formula, including multiplication, and its etale restriction is precisely the statement's direct image. I also read the underlying 077A/0GQQ/0GQR source: this is a quasi-coherent right adjoint and a smooth/etale restriction, not a claim that naive pushforward on the entire big fppf site is quasi-coherent. The new construction's projection and universal object give exactly the evaluation map, with the direction of its algebra homomorphism checked.

For step 2 I opened the new construction, lem-sfb-stack-quasi-coherent-scheme-restriction, def-sfb-stack-quasi-coherent-algebra, lem-trf-space-chartwise-etale-permanence and lem-sfb-adequate-moduli-etale-locality. Their statements give respectively base change and the tautological structure-algebra map, arbitrary tensor restriction of quasi-coherent modules, the etale-test direct image formula, composition of etale maps, and the adequate base change to each member of the cover. I checked that C_i is identified with the direct image on X_i by evaluating on etale tests, not by invoking an unsupported arbitrary base change of phi_*. The global ring map of h_i is the tautological evaluation isomorphism, not merely an abstract isomorphism of the same rings.

For step 3 I opened lem-sfb-stack-qcqs-composition-affine and lem-sfb-stack-affinization-qcqs. The former says affine stack maps are qcqs and these maps compose. Thus V_i is qcqs over k because W_i is affine, phi_i is qcqs and q_i is affine. The latter gives the canonical affinization map and uniqueness by restrictions on scheme objects, and explicitly says it is qcqs without finite type or separated-diagonal assumptions. The h_i constructed from evaluation has those restrictions, so this is a legitimate application. This avoids silently assuming qcqs of h before applying the affine criterion. Read 075S(2), the geometric source of this permanence/affinization input.

For step 4 I opened lem-sfb-stack-affine-algebra-direct-image and the complete affine clause of lem-sfb-adequate-moduli-etale-locality. Affine direct image explicitly preserves surjections and gives natural global-section ring isomorphisms commuting with powers. The affine criterion explicitly quantifies over arbitrary algebras. Apply it on X_i to the pushforward of the arbitrary surjection on V_i and transfer the lift through the ring isomorphisms. Read 0GQY, which supplies the affine exactness underlying that node. No algebra on V_i is assumed to descend, and no invariant functor is assumed exact merely from adequacy.

For step 5 I reopened the locality criterion, chartwise-etale permanence and lem-sfb-stack-etale-local-qcqs-homeomorphism. The last statement includes qcqs descent along the etale cover, so the hypothesis of the moduli locality theorem is established before it is used. The cover of Z is the actual base change of the cover of Y; the theorem is applied to that base-changed map. Every citation has its required verbatim statement quotation in citations.json. All five non-elementary steps are under 2000 characters and contain the assembly argument; no long hidden lemma is retained.

I tested the new statement on C=0 (empty relative spectrum, zero section ring), C=O_Z (identity projection), a nonreduced algebra k[e]/(e^2), and an algebra with infinitely many generators. For the item, B=0 gives the empty-to-empty adequate map; B=O_X gives the original map using O_Y=phi_*O_X; phi=id gives identity relative spectrum. Nothing requires finite generation, flatness or reducedness. Empty affine charts have zero section rings and admit the trivial power lift with N=1. A nontrivial stabilizer of X need not disappear in V, which is correctly called a stack rather than a space; only the target relative spectrum is an algebraic space.

## Not finished

Nothing required for this stage-1 item is left unfinished. The one new general construction lemma is deliberately statement-only and unsplit, as required for a one-level split. Independent maintainer review remains after delivery.

## Not duplicates
lem-sfb-stack-relative-spec-construction vs lem-sbc-depth-two-finite-hom-extension: is a scheme-level statement (Extension of open morphisms from a finite depth-two source); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-sbc-depth-two-finite-hom-equality: is a scheme-level statement (Equality detected on the open of a finite depth-two source); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs def-fd-artin-schreier-function-cover: is a scheme-level statement (The function Artin–Schreier cover, its root, constants and induced fibre map); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-trf-qcqs-relative-affinization-map: is a scheme-level statement (Canonical relative affinization of a qcqs morphism); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-pc-affine-surjective-structure-map-closed-immersion: is a scheme-level statement (An affine morphism with surjective structure map is a closed immersion); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-sfb-dm-open-finite-etale-permanence: requires a smooth finite-type DM base with finite diagonal and a finite etale decoration; arbitrary stack bases and arbitrary algebras in the new theorem need not satisfy any of these.

lem-sfb-stack-relative-spec-construction vs lem-sfb-stack-affine-algebra-direct-image: starts with an existing affine morphism and proves exactness and the section adjunction; it does not construct a relative spectrum for an arbitrary algebra on a stack.

lem-sfb-stack-relative-spec-construction vs lem-sfb-space-relative-spec-correspondence: the base is an algebraic space, while the new theorem allows an arbitrary algebraic stack with positive-dimensional or non-DM inertia.

lem-sfb-stack-relative-spec-construction vs lem-sfb-representable-finite-stack-properties: requires a DM base and a pre-existing finite representable map; the new theorem constructs an affine map which need not be finite, over any algebraic stack.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-relative-spectrum-structure-algebra: is a scheme-level statement (Structure algebra from compatible affine spectral charts); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-affine-base-change-sections-induction: is a scheme-level statement (Generation of affine base-change sections); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-affine-basis-ring-action-gluing: is a scheme-level statement (Extension of compatible ring actions from affine opens); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-affine-algebra-reductions-cartesian: is a scheme-level statement (Compatible affine algebra quotient reductions yield cartesian scheme maps); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-affine-algebra-local-maps: is a scheme-level statement (Compatible local scheme maps from an affine structure-algebra morphism); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-balanced-action-quasicoherent-realization: is a scheme-level statement (Quasi-coherent realization of a balanced algebra action); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-relative-spec-base-change: is a scheme-level statement (Relative Spec commutes with base change); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-relative-spectrum-affine-realization: is a scheme-level statement (Affine realization of a quasi-coherent algebra); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-balanced-action-affine-open: is a scheme-level statement (Unique balanced action on a single affine open); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-affine-morphism-relative-spec: is a scheme-level statement (Affine morphisms and quasi-coherent algebras (relative spectrum)); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-relative-spec-morphism-chart: is a scheme-level statement (Relative spectrum morphism chart compatibility); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-balanced-action-direct-image-module: is a scheme-level statement (Extension of a balanced action to the direct-image structure algebra); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-balanced-action-affine-sections: is a scheme-level statement (Balanced actions on affine sections of the direct-image algebra); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-affine-structure-algebra-fully-faithful: is a scheme-level statement (Full faithfulness of the affine structure-algebra functor); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-weil-pbc-graded-finiteness-cohomology: is a scheme-level statement (Cohomology of a finite type graded module over f^*B~ is a finite B-module); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-pur-conormal-cone-hom-ext: is a scheme-level statement (Degree-one uniqueness for maps to conormal spectra); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-pur-rees-cone-normalized-existence: is a scheme-level statement (Homogeneous-normalized Rees cone comparison exists); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-pur-conormal-graded-algebra-hom-ext: is a scheme-level statement (Degree-one uniqueness for conormal algebra morphisms); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-pur-conormal-zero-section-pullback: is a scheme-level statement (The relative-Spec conormal zero section pulls back by augmentation); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs lem-pur-rees-associated-graded-chart: is a scheme-level statement (Homogeneous chart for the extended Rees zero fibre); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

lem-sfb-stack-relative-spec-construction vs def-pur-rees-cone-normalization: is a scheme-level statement (Degree-one normalized comparison predicate); it neither constructs relative spectra over arbitrary algebraic stacks nor establishes their stack representability and structure-algebra identification.

