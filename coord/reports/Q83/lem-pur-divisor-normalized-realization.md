## Worker report

1. Files written: `dag/nodes/sec-smooth-purity/lem-pur-divisor-normalized-realization.json` (statement, split, no Mathlib match); `dag/nodes/sec-smooth-purity/lem-pur-relative-extension-cohomology-normalization.json` (statement only, unsplit, no Mathlib match). Also `citations.json`, the actual `searches.jsonl`, and this report. One new node; zero Mathlib leaves. The statement of the item is unchanged.
2. Attachments: none. Searches of `lean/WeilConjectures/` by the exact blueprint identifier, framed-line and relative-Kummer concepts found no declaration stating every clause. Existing ordinary cohomology and affine-line Kummer computations are insufficient. Reading `lean/Sheaf/CategoryTheory/Sites/RelativeTorsorExtension.lean` and `lean/Sheaf/AlgebraicGeometry/DivisorTorsorBoundarySigns.lean` confirmed the available generic extension and raw-sign interfaces; neither proves this item or the new normalization statement in full.
3. WANTED: none. All sources used are available locally.
4. The imported item has no proof. I retained its repaired Yoneda sign convention and did not reproduce the older blueprint's local-to-global argument or its incorrect description of a divisor sum as a two-element frame. The current ancestor already records these corrections. The new split supplies the integral derived-unit uniqueness argument explicitly, instead of treating coefficient forgetting as fully faithful. No further statement dispute was found.
5. Unfinished within this delivery: the one new generic normalization lemma is intentionally statement-only and enters the stage-1 queue. Its intended proof and search evidence are recorded below. No Lean was written and no compiler, Lake or build tool was run.

## New node and its argument

`lem-pur-relative-extension-cohomology-normalization` is the comparison for an arbitrary abelian sheaf torsor with a complementary section. It has no roots, finite coefficient ring, scalar extension, line bundle, or site-comparison conclusion. It therefore does not restate the item or a clause consisting of the entire finite Kummer realization. The two classifications being compared are distinct existing interfaces; a positive ordinary forgetful image alone cannot identify relative classes because the localization map need not be injective.

For a proof, take the canonical free extension of the torsor, split its open restriction using the specified frame, and quotient by that splitting as in the existing relative-extension theorem. Compute derived Hom from the exact presentation `j_! Z_W -> Z_T -> i_* Z_Z` on an injective resolution. Evaluation at the constant integer generator identifies the resulting Hom fibre complex with the signed relative section complex. An equivariant map to an extension is exactly the lift over supported one; the condition on the chosen frame is exactly the relative nullhomotopy. Comparison with the lifting-torsor classification, including the minus sign in its raw cone representative, gives the Ext-normalized class. This comparison must be computed before forgetting support. Pullback and restriction of the splitting give the indicated morphisms of the same presentation. Pulling the extension back along `Z_T -> i_* Z_Z` leaves the torsor P as the fibre over one, hence gives the positive ordinary class by Tag 03AJ. Empty open and empty support use the identical cokernel construction. This argument belongs to the future split of that generic lemma, not to its statement field.

## Searches

Before creating the node I searched the whole DAG for the relative extension, relative torsor cohomology, Ext normalization, supported scalar comparisons and Tags 03AJ/0A45. Blueprint searches were `relative torsor`, `torsor extension`, `relative cohomology`, `supported torsor`, `Ext-normalized`, `scalar adjunction`, and `supported scalar`; the ancestor query identifies `lem-pur-divisor-class`. I read the matching nodes, rather than using their proofs as stronger statements. The imported blueprint has ordinary Ext/torsor classification but no full relative-extension normalization comparison.

All new-node Mathlib searches ran through the prescribed msearch.py command and appear unchanged in searches.jsonl and mathlib_searches. Two semantic formulations separately asked for relative torsor extensions and their signed supported comparison. LeanFinder found ordinary `Sheaf.H` and injective-resolution Ext/cohomology comparisons, not the relative torsor statement. LeanSearch also found ordinary Ext and nonabelian cocycle relations, which do not incorporate the specified open section. Loogle found ordinary degree-zero sheaf cohomology formulas; the focused injective-resolution query found `CategoryTheory.InjectiveResolution.extEquivCohomologyClass_extMk`. I read Mathlib/CategoryTheory/Abelian/Injective/Ext.lean (the formula at line 138 and its surrounding construction) and Sites/SheafCohomology/Basic.lean. These compare an existing resolution cocycle with an Ext class, but do not construct or identify the relative torsor extension. Broad grep had unrelated support/extension hits; the subsequent grep restricted to CategoryTheory/Sites returned zero hits. No service failure was represented as absence. The item received its own semantic finite-coefficient realization search, whose hits were derivations and ordinary sheaf cohomology. Existing imported search history is retained.

## Not duplicates

lem-pur-relative-extension-cohomology-normalization vs sbc-prop-torsors-h1: states Torsors and etale $H^1$; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sf-etale-generic-immersion-projection: states Projection formula for an immersion extension by zero; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-coef-etale-locally-closed-shriek: states Etale locally closed exceptional restriction and finite quotient coefficients; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sf-etale-generic-exchange-algclosed: states Geometric-generic closed-support and internal-Hom exchange over arbitrary algebraically closed fields; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-wf-finite-constant-h1-pi1: states Finite constant torsors and the etale fundamental group; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs sk-def-purity-conv: states Purity conventions and the rank-one datum; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sfb-strict-log-jacobian-criterion: states Strict logarithmic Jacobian criterion; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-regular-supported-base-change: states Regular base change for closed supported restriction; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-codimension-one-costalk-reduction: states Strict local curve reduction and costalk identifications; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-supported-yoneda-localization: states Yoneda coefficient splice versus the signed localization boundary; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-etale-local-infinitesimal-lifts-smooth: states Etale-local infinitesimal solutions imply smoothness; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-cartier-gysin-kummer-boundary: states Cartier Gysin normalization in the signed relative Kummer model; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-procyclic-torsor-tower-descent: states Cartan--Leray descent for a procyclic tower of finite etale torsors; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-transverse-gysin-limit: states Continuity of supported Kummer maps for preserved regular sequences; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-pure-principal-divisor-kummer-residue: states Localization residues of unit Kummer symbols when divisor purity is given; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-smooth-divisor-kummer-purity: states Kummer-normalized cohomological purity for a smooth divisor; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-finite-closed-support-exchange: states Closed extraordinary restriction commutes with finite direct image; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-supported-generators-costalk-detection: states Detection of supported cohomology bounds by geometric costalks; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-noetherian-affine-line-unit: states Ordinary finite-coefficient affine-line unit over a Noetherian base; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-localization-dual-boundary-pairing: states The dual localization boundary transposes to evaluation followed by the support boundary; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-noetherian-supported-product-calculus: states Supported products and Cartier interchange on ordinary etale sites; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-divisor-purity-strict-local-criterion: states Strict-local complement criterion for regular divisor purity; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs def-per-closed-support-plus-adjunction: states Bounded-below closed-support right adjoint and its fixed adjunction; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-open-closed-constructible-test: states Bounded constructibility detected by open and exceptional closed restriction; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-torsion-torsor-descent: states Torsors under torsion local systems are local systems; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-ind-etale-closed-support-base-change: states Ind-etale base change for the closed etale support right adjoint; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-punctual-strict-completion-test: states Testing closed-point purity after strict completion; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-codimension-support-filtration: states Codimension support filtration and local graded complexes; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-field-exceptional-tensor: states Exceptional tensor comparison for coefficients pulled from a field; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-per-coniveau-top-edge-presentation: states Coniveau edge and its normalized flag components; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-weil-pbc-gabber-h1-torsor-cohomology-bridge: states Torsor triviality implies constant H1 vanishing; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lemma-weil-pbc-h1-torsor-comparison: states Finite-etale torsor comparison; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-weil-pbc-gabber-h1-absolutely-algebraically-closed: states First constant cohomology vanishes on closed subschemes of the spectrum of a normal domain with separably closed fraction field (Stacks 09ZB); it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-weil-pbc-finite-etale-equivalence-h1: states Finite etale pullback equivalence implies finite constant H1 comparison; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-amb-relative-cocycle-coordinates: states Concrete first homology coordinates for the relative restriction cone; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-pur-kummer-additivity: states Kummer additivity; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-exc-closed-support-triangle: states Closed-support triangle before restriction; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs det-sp-tower-classes: states Kummer and diagonal classes of towers; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs def-amb-relative-etale-cohomology: states Resolution model of relative etale cohomology and its cone maps; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-pur-affine-coordinate-support-stalk-continuity: states Affine continuity for coordinate-supported geometric stalks; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs def-amb-torsor-with-section: states Torsors with a specified section and their isomorphism classes; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs def-asd-ordinary-supported-kummer-boundary: states Relative supported Cartier Kummer boundary specification; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-pur-principal-torsor-yoneda-sign: requires a global frame of P and computes an inverse-unit pushout; the new lemma allows nontrivial P.

lem-pur-relative-extension-cohomology-normalization vs lem-pur-etale-injective-support-sequence: states Degreewise-injective ordinary etale support sequence; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-amb-relative-torsor-cohomology: classifies framed torsors by relative cohomology but does not equate that class with the independently specified supported integral extension.

lem-pur-relative-extension-cohomology-normalization vs lem-asd-ordinary-supported-chern-normalization: states Ordinary Chern realization of a normalized supported class; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-asd-supported-kummer-support-hom-naturality: states Naturality of the supported Hom identification under base change; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-amb-relative-torsor-class-naturality: states Equivariant naturality of framed relative torsor classes; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-amb-relative-torsor-forget-normalization: states Ordinary normalization of the framed relative cocycle; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-pur-divisor-torsor-boundary-signs: computes raw lifting representatives and boundary signs but does not identify the quotient relative extension with the Ext-normalized class.

lem-pur-relative-extension-cohomology-normalization vs lem-pur-cartier-pair-tensor-addition: states Tensor addition of framed Cartier pairs before applying Kummer; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sp-relative-torsor-extension: constructs and uniquely characterizes the relative extension but does not identify it with relative cohomology.

lem-pur-relative-extension-cohomology-normalization vs lem-pur-divisor-normalized-realization: asserts finite Kummer module and pro-etale realization; the new lemma is only the generic degree-one integral torsor comparison.

lem-pur-relative-extension-cohomology-normalization vs def-asd-ordinary-supported-kummer-system: states Normalized ordinary supported Cartier Kummer map systems; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sp-etale-torsor-extension-presentation-exists: states Existence of the free extension presentation of an etale torsor; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-asd-ordinary-supported-kummer: states Supported Cartier Kummer map for ordinary etale arbitrary finite coefficients; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-amb-framed-lifts-classification: states Pointed lifting torsors modulo global translation; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-etale-inverse-image-lifts-fibre: states Underlying lifting-fibre comparison for etale inverse image; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-etale-contracted-product-exists: states Existence of the contracted product of an etale torsor; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-etale-torsor-inverse-image-extension: states Inverse image of the torsor extension; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-etale-contracted-product-exists-data: states Translation torsor structure on the explicit sheafified orbit quotient; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-etale-inverse-image-lifting-torsor: states Inverse image of a lifting torsor; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs def-sc-torsor-extension-presentation: states Canonical extension presentation of an etale torsor; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-etale-contracted-product-exists-universal: states Universal property of the explicit sheafified orbit quotient; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs new-etale-torsor-inverse-image-extension-core: states Extension core after inverse-image torsor transport; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-extension-presentation-short-exact: states Short exactness of extension presentation; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-torsor-h1: states First cohomology classifies torsors; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-etale-torsor-h1-functoriality: states Functoriality of the etale torsor classification of H1; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs def-sc-contracted-product-presentation: states Contracted product presentation under change of coefficients; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-extension-presentation-generator-fibre: states Generators identify the fibre; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs lem-sc-etale-torsor-pushout-extension: states Pushout of the etale torsor extension; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

lem-pur-relative-extension-cohomology-normalization vs new-etale-torsor-inverse-image-torsor: states Inverse-image torsor and equivariance; it does not assert the generic equality between the complementary-section integral extension and the Ext-normalized relative torsor class.

## Review by Q83

I read the item's source against the current main-20261015 ancestor proof, then read Stacks 03AJ (sites-cohomology.tex, lemma-torsors-h1), 03PL (etale-cohomology.tex, lemma-kummer-sequence), 0A45 (lemma-cohomology-with-support-triangle), 099W (proetale.tex, lemma-compare-cohomology), and the support-functoriality discussion 0G71/0G78 in cohomology.tex. The new node's source is the relative refinement of 03AJ and 0A45, explicitly marked agent-stated; neither source is misrepresented as already stating that refinement. No SGA source is used.

Step 1 cites the actual open-closed short exact sequence and the open extension-by-zero adjunction, giving precisely the hypotheses of the relative-extension node (L=j_! Z_W, Q=i_* Z_Z). Its specified equivariance, supported one and zero on the frame are exactly what the item asks for. The new node is used for its explicit equality with the relative class, not merely its forgetful consequence. The frame torsor and section are already the inputs of the item, so no line-bundle classification stronger than its statement is used.

Step 2 cites the Kummer exact sequence for m invertible and the generic abelian-category connecting/Ext-composition node at degree one. The latter is not the more restrictive O_X-module degree-zero connecting lemma. Its statement says exactly shifted composition by the short exact extension class. Naturality of the derived supported-Hom isomorphism and the stated relative connecting map identify the relative Kummer class. I checked m is invertible because T is a k-scheme with ell distinct from characteristic, and mA=0 even when n is not divisible by the ramification index. G_m remains an abelian sheaf, with no fictitious finite-ring action.

Step 3 uses the integral supported derived-unit node, whose statement applies to any closed immersion and finite ring killed by a positive integer, and its definition, which quantifies over every unbounded target K. Substituting K=B[2] gives exactly the required comparison map and its bijectivity. A right inverse chosen from an arbitrary class existence theorem is not used as a new data definition; the class here is uniquely determined. In particular coefficient forgetting is not assumed fully faithful.

Step 4 uses the existing supported roots/scalar/site comparison, whose statement includes the full relative lift, the formula q nu^-1 u=sigma rho, and arbitrary closed support without A-flatness. Uniqueness from Step 3 identifies its arrow with b_A. The finite ring A may be ramified and nonflat over Z/m; the cited theorem explicitly allows this. The witness B is a sheaf in degree zero, so the bounded-below site-comparison hypothesis holds. I checked no smoothness or Cartier hypothesis was silently supplied here.

Step 5 uses the new node's explicit relative extension naturality and the existing relative-torsor and signed-cone functoriality statements. Restricting W to W' is enlargement of the closed support, with the correct direction. Additivity is a separate short computation: composition, exact forgetting, precomposition with the integer generator and the supported cohomology maps are additive, so their bijections and inverses preserve sums. It does not assume additivity of an arbitrary torsor-class bijection.

Step 6 uses the exact clause that forgetting support is precomposition by the ambient constant unit, the new lemma's positive ordinary torsor image, and the generic connecting-composition theorem. This proves the ordinary positive Kummer image; the raw cone class was never substituted for its negative. The signed cone/site node explicitly commutes with coefficient maps and forgetting support, so the same roots map is used on both sides. Thus no local-to-global equality of cohomology classes is claimed from an open covering.

I checked B1-B10 on the new file: it is self-contained and statement-only; all named notions have statement dependencies; its source has tags and actual labels; it has no proof or proof dependencies; blueprint provenance has the extra via entry for this non-blueprint item; all search records are real. No Mathlib leaf is claimed. I checked C1-C8 by reading every cited statement and generating verbatim citation records, and checked that each existing proof dependency has no path back to the item. Off-unit generic tools are declared in split_report.tool_uses.

For E1-E7 I tested empty T, empty support (W=T), full support (W empty), a trivial framed pair, a nontrivial line bundle with W empty, a nonreduced closed support, and the ramified coefficient case ell in (varpi) with n=1. The empty-support relative group and supported source vanish; full support recovers the ordinary torsor class and Chern map; a zero integral extension yields zero through every additive map. The generic new lemma is degree one for arbitrary G and does not require a global frame, unlike the principal-unit sign lemma. The quotient construction treats empty opens with the zero open-source object. No new statement needed correction. Every item step is below 2000 characters; none hides the scalar uniqueness or site comparison under the word 'transport'.
