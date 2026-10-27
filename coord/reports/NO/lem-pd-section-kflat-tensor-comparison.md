# Stage-1 re-split report

1. Files written

- `dag/nodes/sec-poincare-duality/lem-pd-section-kflat-tensor-comparison.json`: unchanged statement; five-step short assembly.
- `dag/nodes/sec-poincare-duality/lem-pd-conjugate-tensor-localization-counit.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-poincare-duality/lem-pd-ringed-kflat-native-model-identification.json`: statement, unsplit; no Mathlib match.
- `citations.json`: verbatim statement quotations for every cited node in every assembly step.

2. Attachments: none. The requested SectionKFlatTensorComparison module is absent in this read clone. Searches of WeilConjectures by the blueprint tag and K-flat/section concepts found no declaration stating the whole item. Sheaf/Paper/InternalSectionDerivedTensorComparison.lean defines a TensorComparison structure with a normalization field; it is not a proof of the existence, uniqueness, localization, and coherence assertions here.

3. WANTED: none.

4. The released 2026-10-24 repair order supersedes the old passing review. Its issue is granularity, not a statement error. I preserve the statement and all existing metadata. No STATEMENT-DISPUTED issue was found. The original Step 6 had already been repaired by the previous reviewer; that repair is retained in the second new task.

5. Unfinished: the two new nodes are intentionally statement-only, with no proof steps or proof dependencies; their independent workers will supply proofs. This is the required one-level split, not a claim that their Lean is proved.

## Allocation of every original argument

- Old Steps 1–2: assembly Step 1 reuses lem-pe-internal-section-tensor-comparison and the cone criterion; lem-sfb-ringed-equivalence-resolving-tensor-descent supplies the internal resolving localization. Conjugating the existing section arbitrary-target bijection through its commuting equivalence square supplies the internal pair version. No duplicate localization lemma is created.
- Old Steps 3–4: new lem-pd-conjugate-tensor-localization-counit owns extension of the representative formula and its inverse, uniqueness, the exact-functor counit equation, extension from equivalence images, and cancellation identifying both prescribed localization transformations.
- Old Step 5: assembly Step 3 retains the regular-unit flatness/K-flatness test and the localized ordinary unit map. This elementary test is not made a node.
- Old Step 6: new lem-pd-ringed-kflat-native-model-identification owns the acyclic-test/two-sided bridge, identification of native and ringed models, compatibility on all complex pairs and K-flat pairs without flat terms, and identification of their constraints. Assembly Step 4 then applies the existing exact-functor normalization theorem. The cone/symmetry test already has the general node lem-sfb-exact-monoidal-equivalence-total-kflat, so no duplicate test-only node is created.
- Old Step 7: assembly Step 5 retains the transported-constraint argument and cancellation, using the existing symmetric monoidal equivalence transport theorem.

The source proof text below is retained verbatim as handoff material. It is not inserted as a proof sketch in either new statement.

### Original Step 1

Apply the ordinary comparison to $R_T$ and the fixed small site, with coefficient universe containing both its object and morphism universes. It is the prescribed comparison: both maps are characterized by the same local pure tensors, and the total map by its summands. It preserves and reflects acyclicity, flat modules and K-flat complexes. The cone criterion then gives preservation and reflection of quasi-isomorphisms: termwise additivity identifies the image cone with the cone of the image. Thus $E_T$ and its inverse restrict to equivalences $\mathcal P_T^{\mathrm i}\simeq\mathcal P_T^{\mathrm s}$ respecting their quasi-isomorphisms.

Cited nodes: lem-pe-internal-section-tensor-comparison, def-pd-section-derived-tensor-data, lem-pur-quasi-iso-cone-acyclic.

### Original Step 2

Termwise localization of the equivalence, its inverse and their unit/counit gives the fixed $D(E_T)$ and $\kappa$. The site tensor descent theorem says that the section representative subcategory localizes equivalently onto the section derived category. Step 1 and $\kappa$ conjugate this assertion to the internal category. Explicitly the square with top $E_T|_{\mathcal P}$, bottom $D(E_T)$ and sides the two restricted localizations commutes via $\kappa$; its horizontal functors are equivalences. Therefore the internal restricted localization has the same universal property, including the bijection on natural transformations with arbitrary target category. Applying the section resolving-pair assertion and conjugating both arguments gives fully faithful restriction on internal resolving pairs as well.

Cited nodes: def-pd-section-derived-tensor-data, lem-weil-pbc-site-derived-tensor-descent, lem-weil-pbc-localization-universal-property.

### Original Step 3

Temporarily write $\otimes^{\mathbf L}_{\rm nat}$ for the independent ringed tensor. On internal resolving pairs set
$$a_{P,Q}=(\kappa_P\otimes^{\mathbf L}_{\rm nat}\kappa_Q)^{-1}r^{\mathrm s}_{E_TP,E_TQ}\,q_T^{\mathrm s}(t_{P,Q})\,\kappa_{\operatorname{Tot}(P\otimes Q)}\,D(E_T)(r^{\mathrm i}_{P,Q})^{-1}.$$
All factors are invertible and natural in homotopy-category maps; this includes inverse denominators, by the site descent statement. Step 2 extends $a$ and $a^{-1}$ uniquely to natural transformations between the two derived bifunctors. Their composites are identities since their restrictions are identities. Denote the resulting isomorphism $\theta_{\rm nat}$. Multiplying its formula by the two outer factors gives exactly the required normalization; conversely that equation forces the formula and hence uniqueness.

Cited nodes: lem-weil-pbc-site-derived-tensor-descent, lem-weil-pbc-localization-universal-property, def-pd-section-derived-tensor-data.

### Original Step 4

Let $B_{\rm conj}$ and $\theta_0$ be the prescribed conjugate section tensor and comparison. Apply the general derived-comparison theorem with all three exact functors equal to $E_T$ and ordinary total comparison $t$. Its hypotheses hold: $E_T$ is an additive exact equivalence, hence a left adjoint; it preserves flats by Step 1, and the internal and section functorial flat resolutions are those fixed in the tensor-data node. The resulting comparison to the native ringed tensor equals $\theta_{\rm nat}$ by Step 3 and is compatible with the tensor-localization counits on every pair of complexes. Define, on pairs of $D(E_T)$-images, $v=\theta_{\rm nat}\theta_0^{-1}:B_{\rm conj}\cong B_{\rm nat}$. The inverse equivalence and its counit extend this uniquely to section derived objects. Inserting the defining formula for the conjugate localization map gives $q_{\rm nat}v=q_{\rm conj}$ on termwise $E_T$-images: the factors $\theta_0^{-1}$ cancel and the remaining equality is precisely the general derived-comparison counit equation. Every section complex is isomorphic to such an image, so naturality gives this equality on all complex pairs. Thus $v$ identifies the localization maps, not just the tensors. Under $v$, $\theta_0$ is exactly $\theta_{\rm nat}$, proving the specified-comparison assertion.

Cited nodes: lem-pur-derived-tensor-comparison, lem-pe-internal-section-tensor-comparison, sk-def-sfb-derived-tensor-hom, def-pd-section-derived-tensor-data, def-pd-section-derived-realization.

### Original Step 5

The regular module is flat: tensoring with it is isomorphic to the identity by the ordinary unitors. Its degree-zero complex is K-flat because total tensor with it is the test complex itself, hence sends every acyclic test to an acyclic complex. All its terms are flat, including the zero terms. The ordinary normalized unit map $E_T(R_T)\cong R_{T,\mathrm{sec}}$ in degree zero therefore localizes, after $\kappa_{R_T[0]}$, to the stated $e_T$. This also identifies the conjugate regular unit with the independent native regular unit.

Cited nodes: lem-pe-internal-section-tensor-comparison, lem-sfb-termwise-strong-monoidal, def-pc-flat-sheaf-modules, def-pc-kflat-complex, def-pd-section-derived-tensor-data.

### Original Step 6

Apply the exact-functor derived normalization theorem to $E_T$ with its ordinary pure-tensor strong monoidal structure. The categories and functorial flat resolutions are those of the fixed internal derived tensor and its section realization; exactness, additivity and flat/K-flat preservation were checked in Steps 1 and 4. The total comparison is the prescribed one, since the termwise strong-monoidal theorem pins it on every summand. On the section side the native structure of that theorem is the one of the derived monoidal construction, and it is identified with the ringed tensor of Step 3: a flat-term K-flat complex is two-sided K-flat, since the cone criterion and the tensor-cone identification turn the acyclic test into preservation of quasi-isomorphisms, and symmetry gives the other side. Hence both tensors have invertible comparisons with $q_T^{\mathrm s}\operatorname{Tot}$ on pairs in $\mathcal P_T^{\mathrm s}$, and the section bijection of Step 2 extends the composite of these comparisons, and its inverse, uniquely to an isomorphism of bifunctors respecting all localization maps. Through it $\theta_{\rm nat}$ and the counits of Step 4 are read in the native structure. The comparison of Step 4 satisfies the theorem's normalization even for K-flat complexes without flat terms: its counit equation holds for all complexes and the native localization comparisons are invertible on K-flat pairs, since the derived tensor is computed by replacing either argument by a K-flat resolution. The theorem now gives the associator and both unitor equations for $\theta_{\rm nat}$, with unit the localized ordinary unit from Step 5. These are the claimed native derived diagrams.

Cited nodes: lem-sfb-exact-tensor-functor-derived-normalization, lem-sfb-termwise-strong-monoidal, lem-sfb-derived-monoidal, sk-def-sfb-derived-tensor-hom, def-pd-section-derived-tensor-data, lem-weil-pbc-site-derived-tensor-descent, lem-pur-quasi-iso-cone-acyclic.

### Original Step 7

The fixed conjugate section constraints are transported internal constraints. Conjugating any one of their diagrams back along the equivalence reduces it to the corresponding internal constraint equation: the adjacent equivalence unit/counit maps cancel by their triangle identities. Hence $\theta_0$ satisfies the same three equations with the conjugate constraints. Substituting $\theta_{\rm nat}=v\theta_0$ into these equations and Step 6, and cancelling invertible $\theta_0$ and its unit, shows that $v$ also identifies the fixed conjugate constraints with the native constraints. Therefore the displayed $\theta_T,e_T$ have all the requested coherences in either model. Every total used is a signed direct-sum total over integer indices; no step imposes boundedness or identifies the site object and morphism universes.

Cited nodes: def-pd-section-derived-tensor-data, lem-sfb-exact-tensor-functor-derived-normalization.

## Review by NO

I read the item and its released repair note, the chapter and exchange-unit records, the current blueprint exchange section under `literature/blueprint/latest/`, and the statements of every old proof dependency. The latest blueprint exchange section is broader than the historical unit record, but this extraction concerns the seeded internal/section realization below the unit; it changes neither the unit nor a geometric route. `blueprint_refs.py ancestor` reports no imported blueprint ancestor for this seeded target chain. The new nodes therefore retain the existing null ancestor and name the precise seeded place, with this item prepended to the inherited via chain. Searches of the whole blueprint for K-flat, conjugate, tensor comparison, localization equivalence, localization counit, K-flat tensor model, and conjugate derived found no blueprint statement of either new task. DAG searches included these notions and the source tags. The new statements retain arbitrary small ringed sites rather than repeating the pro-etale/condensed conclusion of the item.

For the item and the first new task I read `sites-cohomology.tex` at 06YS, lemma-K-flat-resolution, and the construction preceding and including 06YU, definition-derived-tor. These supply flat-term K-flat representatives and the independent ringed construction. I also read Categories 04VK, lemma-properties-right-localization. The exact-functor comparison on all complexes is taken from the explicitly stated `lem-pur-derived-tensor-comparison`, not attributed to a verbatim Stacks theorem. Its hypotheses hold for an exact equivalence: it is additive, is a left adjoint to its inverse, and preserves flats. The first new task's displayed formula has source D(E) of the internal derived tensor and target the ringed tensor of the two D(E)-images: the inverse of D(E)(r) occurs on the right and the inverse kappa tensor on the left. Inverting each factor gives the inverse natural transformation. Restriction to resolving pairs and the section/internal localization square extend both transformations; identity of their composites on representatives gives inverse transformations everywhere. Apply the general exact-derived comparison to obtain its all-complex counit equation, then set v theta_0 = theta. Substituting the prescribed conjugate counit formula cancels theta_0 on images of E. Every section complex is isomorphic to such an image through the termwise equivalence counit; naturality yields the equation on arbitrary pairs. This is the substantive extra localization assertion absent from the generic ringed-equivalence theorem.

For the second new task I read 06YP, lemma-K-flat-quasi-isomorphism; 06YT, lemma-derived-tor-quasi-isomorphism-other-side; 06YU, definition-derived-tor; 0FPQ, lemma-symmetric-monoidal-cat-complexes; and 0FPT, lemma-symmetric-monoidal-derived. The last Stacks proof is omitted; I do not present it as a complete external proof. The task is an agent extraction of the original repaired Step 6. The cone/tensor-cone argument and symmetry identify the acyclic and two-sided tests; the existing `lem-sfb-exact-monoidal-equivalence-total-kflat` already states that bridge. For the two native models, on resolving pairs the proposed w is r^R (r^a)^{-1}; the section resolving-pair bijection extends this and its inverse. For arbitrary U,V choose flat-term K-flat quasi-isomorphisms P -> U and Q -> V. Naturality of both localization transformations expresses their components at U,V through their components at P,Q, after precomposition by the invertible derived images of the resolution maps. This proves the all-complex equation without pretending the ordinary total tensor inverts arbitrary quasi-isomorphisms. If either input is K-flat, replace the other by a resolution; the 06YP/06YT argument makes its total-tensor image a quasi-isomorphism, so the localization transformation is invertible, without a flat-term assumption. For constraints, on resolving triples the two associators are the localized map (x tensor y) tensor z -> x tensor (y tensor z); on unit pairs they are scalar multiplication by R. The resolving-triple faithfulness stated in `lem-pur-derived-tensor-additive-constraints` extends their equalities, with unit map the identity. This extra all-complex comparison is not a one-line use of the generic localization iso in Mathlib.

Assembly Step 1 cites the ordinary internal/section comparison for acyclicity, flatness and K-flatness, and the separate cone-criterion statement for quasi-isomorphisms. The definition of fixed tensor data pins the chosen comparisons. The ringed-equivalence descent theorem, applied with F = E_T inverse and G = E_T, states exactly the internal resolving localization equivalence; its hypotheses are supplied by the ordinary comparison and the fixed signed total. The section site-descent statement explicitly allows any target category for transformations of bifunctors. Conjugate precomposition by the two equivalences in the kappa square to obtain the internal arbitrary-target assertion. No definition is cited as if it proved resolving descent.

Assembly Step 2 uses the first new statement, not its future proof: it asserts the normalized isomorphism and the v/counit equality. The tensor-data and realization definitions supply precisely the fixed conjugate construction to which that statement applies. Multiplication of its representative formula gives the item's displayed square. This step claims no associator coherence yet. Assembly Step 3 uses the ordinary tensor/unit comparison and the termwise-strong-monoidal statement to identify the degree-zero unit; flatness and K-flatness follow directly from their two stated tests, since tensoring with the regular complex is the identity. Zero terms are flat. The comparison is localized after kappa, in the direction required for e_T.

Assembly Step 4 invokes the second new statement to identify the ringed tensor with the abstract model, including counits on all complexes and normalization without flat terms. This addresses the prior reviewer's specific Step-6 correction, rather than conflating the two constructions. Then `lem-sfb-exact-tensor-functor-derived-normalization` supplies exactly the derived associator and both unitor equations, with its localized ordinary unit formula. Its additivity, exactness, left-adjoint, flat/K-flat, and functorial-resolution hypotheses are checked above; `lem-sfb-termwise-strong-monoidal` pins the total comparison on every bidegree summand. Assembly Step 5 uses the stated monoidal equivalence transport theorem and the fixed conjugate data. The canonical conjugate comparison obeys the transported constraint equations by the equivalence triangle identities. Substituting theta_nat = v theta_0 and cancelling invertible comparisons identifies the constraints in the two models. This is a short formal cancellation, and is kept elementary.

I tested the new formulas for the identity equivalence, an empty site/zero module category, R = 0, regular degree-zero inputs, and an acyclic input. All inverse factors have the indicated types. Neither task assumes boundedness, flat cohomology, that arbitrary complexes have flat terms, or that the site object and morphism universes agree. Each new statement introduces its site, ring, categories, functors and model maps. The two tasks have comparable size and disjoint main arguments (conjugation counits versus two definitions of the native model); neither contains the whole item. No new elementary test-only or definition-only node is introduced. The old proof is retained verbatim above with its allocation, and no non-elementary assembly step exceeds 2000 characters; the assembly has 2340 characters total.

Mathlib searches were run only through msearch.py and are recorded verbatim from searches.jsonl. I read the semantic hits and inspected `CategoryTheory/Localization/Bifunctor.lean` around lift₂NatIso, `Functor/Derived/LeftDerived.lean` around leftDerivedNatIso and totalLeftDerivedCounit, `Localization/Monoidal/Basic.lean`, `Localization/Monoidal/Functor.lean` around lifting_isMonoidal, and `Monoidal/Tor.lean`. Those are useful general tools, but do not prove either new statement in one line: the concrete K-flat models, their localization transformations on all complexes, and the acyclic/two-sided test identification still need the stated arguments. The initial Loogle query using an obsolete namespace returned an identifier error; it was not treated as evidence of absence. The later valid Loogle queries were read. Searches of WeilConjectures and the existing Sheaf definitions yielded no complete attachment. The assembly's verbatim citations were checked against the actual statement strings; proof_deps is exactly the union of uses. No SGA route, Lean writes, compiler, Lake, repository writes or direct git commands were used.

## Not duplicates

lem-pd-conjugate-tensor-localization-counit vs lem-pd-section-kflat-tensor-comparison: The item assembles a specified condensed internal/section comparison, representative localization, unit, and derived coherence; this task isolates one generic cross-model argument and asserts no such complete package.

lem-pd-conjugate-tensor-localization-counit vs lem-pe-kflat-roos-representative-invariance: The existing statement proves representative invariance of an algebra-tower Roos complex and its unit map; it does not identify conjugate and native tensor localization transformations.

lem-pd-conjugate-tensor-localization-counit vs lem-sfb-ringed-finite-free-resolution-tensor: The existing statement computes tensor from a bounded-above specified finite-free resolution and its matrices; it does not compare two unbounded derived tensor constructions and their localization transformations.

lem-pd-conjugate-tensor-localization-counit vs lem-sbc-koszul-tensor-derived-tower: The existing statement compares a strict Koszul tensor tower to its derived tensor tower; it does not address the conjugate tensor construction under an arbitrary exact equivalence.

lem-pd-conjugate-tensor-localization-counit vs lem-sbc-scalar-extension-counit-properties: The existing statement treats the unary scalar-extension derived functor and its K-flat counit; the new task is a two-variable conjugation with specified tensor comparisons.

lem-pd-conjugate-tensor-localization-counit vs lem-sf-cochain-tensor-model-rigidity: The existing statement uniquely compares derived bifunctors from model isomorphisms on flat-term cochain representatives. It is reused conceptually; it does not assert the all-complex localization-counit identity or compare the two K-flat tests and native monoidal constraints.

lem-pd-conjugate-tensor-localization-counit vs lem-exc-intrinsic-resolution-tensor-homology: The existing statement is a cohomology identification for a finite constant coefficient realization and one module input; it does not compare arbitrary exact-equivalence conjugate tensors and all-complex localization maps.

lem-pd-conjugate-tensor-localization-counit vs lem-coef-derived-system-evaluation-calculus: The existing statement concerns normalized coefficient systems, reduction adjunctions and derived Hom limit projections; it does not identify the conjugate tensor localization map with its independent ringed construction.

lem-pd-conjugate-tensor-localization-counit vs lem-sf-open-operation-models: The existing statement constructs an open-square Operations record from TensorModels and direct-image data; it does not state equality of conjugate/native localization transformations on all complexes.

lem-pd-conjugate-tensor-localization-counit vs lem-sf-open-tensor-support: The existing statement asserts support of an open tensor product; it asserts no comparison of derived tensor constructions or localization maps.

lem-pd-conjugate-tensor-localization-counit vs lem-sf-open-pullback-support: The existing statement asserts support of an open pullback; it asserts no comparison of derived tensor constructions or localization maps.

lem-pd-conjugate-tensor-localization-counit vs lem-exc-intrinsic-tor-amplitude-transport: The existing statement transports a finite-coefficient Tor-amplitude predicate; it does not identify the conjugate/native derived tensor bifunctors and their prescribed localization maps.

lem-pd-conjugate-tensor-localization-counit vs lem-sfb-ringed-equivalence-resolving-tensor-descent: The existing statement supplies resolving localization and a coherent derived comparison normalized on K-flat models. It does not state equality with the conjugate construction's prescribed localization transformation on every complex pair; that is the new first task. The second task separately compares acyclic-test and two-sided native constructions and their all-complex localization transformations.

lem-pd-conjugate-tensor-localization-counit vs lem-sfb-exact-tensor-functor-derived-normalization: The existing theorem assumes the native tensor models and gives coherence for its exact-functor comparison; the new tasks identify those assumed native models with the independently fixed ringed model and compare conjugate localization maps, so they supply hypotheses rather than duplicate that theorem.

lem-pd-conjugate-tensor-localization-counit vs lem-weil-pbc-site-derived-tensor-descent: The existing theorem gives the ringed tensor, resolving localization and arbitrary-target pair restriction. It does not compare it with the conjugate or abstract native tensor and their all-complex localization transformations.

lem-pd-conjugate-tensor-localization-counit vs lem-sfb-exact-monoidal-equivalence-total-kflat: The existing statement supplies the ordinary signed total equivalence and the two K-flat tests, which will be reused; it does not identify independently constructed derived tensors with all-complex counits and constraints.

lem-pd-conjugate-tensor-localization-counit vs lem-sf-ringed-derived-closed-symmetric-monoidal: The existing theorem gives the ringed monoidal structure; the second new task compares it with the separately constructed abstract native tensor, its two-sided K-flat model and its localization maps.

lem-pd-conjugate-tensor-localization-counit vs lem-pur-derived-tensor-additive-constraints: The existing theorem supplies normalized ringed constraints and resolving-tuple faithfulness; it does not compare all-complex localization transformations for two independently constructed native models.

lem-pd-ringed-kflat-native-model-identification vs lem-pd-section-kflat-tensor-comparison: The item assembles a specified condensed internal/section comparison, representative localization, unit, and derived coherence; this task isolates one generic cross-model argument and asserts no such complete package.

lem-pd-ringed-kflat-native-model-identification vs lem-sfb-ringed-finite-free-resolution-tensor: The existing statement computes tensor from a bounded-above specified finite-free resolution and its matrices; it does not compare two unbounded derived tensor constructions and their localization transformations.

lem-pd-ringed-kflat-native-model-identification vs lem-sfb-ring-isomorphism-tensor-transport: The existing statement changes scalars along a ring-sheaf isomorphism; it does not compare the fixed conjugate localization transformation with an independent model on all complex pairs.

lem-pd-ringed-kflat-native-model-identification vs lem-sfb-flat-scalar-tor-comparison: The existing statement identifies individual cohomology objects with scalar Tor; the new statement compares derived bifunctors and their all-complex localization transformations.

lem-pd-ringed-kflat-native-model-identification vs lem-sfb-exact-monoidal-equivalence-total-kflat: The existing statement supplies the ordinary signed total equivalence and the two K-flat tests, which will be reused; it does not identify independently constructed derived tensors with all-complex counits and constraints.

lem-pd-ringed-kflat-native-model-identification vs lem-sfb-flat-scalar-tensor-units: The existing statement is the degree-zero regular-unit tensor identity; no comparison of native derived tensor models and counits occurs there.

lem-pd-ringed-kflat-native-model-identification vs lem-sfb-flat-scalar-tensor-resolution: The existing statement computes realized scalar modules by a scalar projective resolution; it does not identify arbitrary unbounded sheaf derived tensor constructions.

lem-pd-ringed-kflat-native-model-identification vs lem-weil-pbc-total-tensor-homotopy-cone-signs: The existing statement proves chain-level homotopy/cone/shift comparisons and preservation of quasi-isomorphisms; it does not compare the two derived models and localization transformations.

lem-pd-ringed-kflat-native-model-identification vs lem-cbc-regular-quotient-cone-chain: The existing statement constructs a chain map out of a scalar cone; the new task compares derived tensor bifunctors and their model/counit identifications.

lem-pd-ringed-kflat-native-model-identification vs lem-cbc-regular-quotient-cone-augmentation: The existing statement compares scalar extension with a regular-quotient cone and identifies its augmentation; it is not an identification of two constructions of the sheaf derived tensor itself.

lem-pd-ringed-kflat-native-model-identification vs lem-cbc-extension-tensor-comparison-independent: The existing statement compares ordinary scalar extension with tensor by the target ring; it has no derived bifunctor localization transformation or native constraint comparison.

lem-pd-ringed-kflat-native-model-identification vs lem-cbc-regular-quotient-flat-sequence: The existing statement is a short exact sequence after flat scalar extension; the new task is a comparison of unbounded derived tensor models.

lem-pd-ringed-kflat-native-model-identification vs lem-sfb-ringed-equivalence-resolving-tensor-descent: The existing statement supplies resolving localization and a coherent derived comparison normalized on K-flat models. It does not state equality with the conjugate construction's prescribed localization transformation on every complex pair; that is the new first task. The second task separately compares acyclic-test and two-sided native constructions and their all-complex localization transformations.

lem-pd-ringed-kflat-native-model-identification vs lem-sfb-exact-tensor-functor-derived-normalization: The existing theorem assumes the native tensor models and gives coherence for its exact-functor comparison; the new tasks identify those assumed native models with the independently fixed ringed model and compare conjugate localization maps, so they supply hypotheses rather than duplicate that theorem.

lem-pd-ringed-kflat-native-model-identification vs lem-weil-pbc-site-derived-tensor-descent: The existing theorem gives the ringed tensor, resolving localization and arbitrary-target pair restriction. It does not compare it with the conjugate or abstract native tensor and their all-complex localization transformations.

lem-pd-ringed-kflat-native-model-identification vs lem-sf-cochain-tensor-model-rigidity: The existing statement uniquely compares derived bifunctors from model isomorphisms on flat-term cochain representatives. It is reused conceptually; it does not assert the all-complex localization-counit identity or compare the two K-flat tests and native monoidal constraints.

lem-pd-ringed-kflat-native-model-identification vs lem-sf-ringed-derived-closed-symmetric-monoidal: The existing theorem gives the ringed monoidal structure; the second new task compares it with the separately constructed abstract native tensor, its two-sided K-flat model and its localization maps.

lem-pd-ringed-kflat-native-model-identification vs lem-pur-derived-tensor-additive-constraints: The existing theorem supplies normalized ringed constraints and resolving-tuple faithfulness; it does not compare all-complex localization transformations for two independently constructed native models.

lem-pd-conjugate-tensor-localization-counit vs def-a1-integral-completed-tower-pullback-universes: The existing node defines integral reduction tower and geometric pullback derived pairs in independent universes; it asserts no conjugate tensor comparison or equality of the two bifunctor localization transformations.

lem-pd-conjugate-tensor-localization-counit vs lem-a1-principal-koszul-strict-replacement: The existing statement constructs a strict principal Koszul replacement of a reduction tower; it does not identify conjugate and ringed derived tensor constructions.

lem-pd-conjugate-tensor-localization-counit vs lem-per-localized-pullback-tensor-normalization: The existing statement compares scalar extensions to a localized coefficient ring using explicit fractions; the new statement concerns an arbitrary exact monoidal equivalence and the prescribed conjugate tensor localization map on all complex pairs.

lem-pd-conjugate-tensor-localization-counit vs lem-per-proetale-scalar-slice-comparison: The existing statement gives unary scalar-extension/restriction comparison for a pro-etale slice; the new task compares two tensor bifunctors under an exact equivalence, without a slice or scalar-extension input.

lem-pd-conjugate-tensor-localization-counit vs def-fd-completed-scalar-shift-representative-property: The existing node defines predicates for shifts of completed scalar comparisons and asserts no existence; the new task proves existence and all-complex counit normalization for a conjugate tensor comparison.

lem-pd-conjugate-tensor-localization-counit vs def-pc-derived-tensor-cohomology-vanishes: The existing node defines a cohomology-vanishing predicate with a module as second argument; the new task identifies derived bifunctors and localization transformations.

lem-pd-conjugate-tensor-localization-counit vs def-pc-derived-tensor-complex-cohomology-vanishes: The existing node defines a cohomology-vanishing predicate with an arbitrary second derived argument; it does not compare tensor constructions or their specified maps.

lem-pd-conjugate-tensor-localization-counit vs def-pc-kflat-complex: The existing node defines the acyclic K-flat test and resolutions; the new task concerns a derived comparison and equality of counits, using that definition.

lem-pd-conjugate-tensor-localization-counit vs def-sc-bounded-flat-shift-representative: The existing node is a bounded-above flat representative predicate; it makes no assertion comparing unbounded tensor bifunctors or counits.

lem-pd-conjugate-tensor-localization-counit vs def-sc-derived-tensor-augmentation: The existing node defines a particular tensor augmentation to a structure-ring object through a complex map; it is not a universal tensor comparison between two independently fixed models.

lem-pd-conjugate-tensor-localization-counit vs def-sc-flat-telescope-stage-map: The existing node defines maps between bounded-flat telescopes through cone maps; it does not identify conjugate tensor localization transformations.

lem-pd-ringed-kflat-native-model-identification vs def-cbc-regular-quotient-cone-basic: The existing node defines a scalar multiplication cone and its coefficient map; it asserts no equivalence of K-flat tests, derived tensor models, localization maps or constraints.

Dry-run duplicate diagnostics additionally named the preceding same-tag nodes. I opened every statement before recording the differences. Shared tags refer to general K-flat constructions reused in many unrelated applications; they do not establish duplicate statements.
