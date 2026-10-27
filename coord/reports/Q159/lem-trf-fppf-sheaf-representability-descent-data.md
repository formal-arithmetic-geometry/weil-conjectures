# Repair report: Q159

## Files written

- dag/nodes/sec-trace-formula/lem-trf-fppf-sheaf-representability-descent-data.json: original statement retained; proof reassembled from two new tasks.
- dag/nodes/sec-trace-formula/lem-trf-fppf-local-representations-fully-faithful.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-fppf-scheme-data-sheaf-gluing.json: statement, unsplit; no Mathlib match.
- citations.json: exact statement excerpts for every parent step citation.

## Attachments

None. The current WeilConjectures source has no exact declaration of the item; the local Sheaf theorem fppfSheafRepresentabilityDescentData ends in sorry. The upstream DescendingRepresentable results descend a representing object along a single arrow assuming morphism descent; they do not construct this equivalence or either new functor.

## WANTED

None. All sources used are available locally.

## Fault and repair

The return requires spreading the 6749-character proof into at least two comparable statement-only tasks and retaining a parent assembly of at most 3000 characters. The sandbox initially contained only dispatcher markers, no delivered JSON or report. I copied the current repository item, whose nine proof steps match the returned lengths, retaining its citations, searches, ancestry, Lean record and review metadata. No git operation or Lean/build command was run.

The item statement is unchanged. The forward task contains the actual representing objects, product/slice conversion, coordinate overlap maps and full faithfulness needed for the reconstruction comparison. The inverse task contains the distinct gluing construction, product representations and the natural datum counit. Neither states effectivity or the full equivalence; neither depends on the parent. Original steps 1, 2 and 9 remain explicit in the parent. The assembly obtains the other natural comparison by lifting the counit through the forward Hom bijections; its local meaning is the gluing argument of old step 8, retained in full below.

## Unfinished

Nothing required for stage 1 is omitted. The two new proofs are deliberately left for parallel workers: status unsplit, empty proof/proof_deps and null proof_origin.

## Sources and searches

Read Stacks descent.tex lemma-descent-data-sheaves (02W5), including both constructions, both final clauses and the omitted verification; sites.tex lemma-glue-sheaves (04TR) and lemma-glue-maps (04TQ); topologies.tex lemma-zariski-etale-smooth-syntomic-fppf-fpqc (022C). Read the current blueprint local-term-locality node, chapter and unit; this preserves the existing quotient-presentation support route, without invoking any SGA source. The old item searches remain unchanged. All new searches were run through msearch.py and their actual logged results are in the node records and searches.jsonl. LeanSearch returned a rate-limit error, recorded unavailable. Each new argument was searched twice semantically, and with Loogle and grep. Inspected Mathlib DescentData.lean (550-628), IsStack.lean (71-78), PseudofunctorSheafOver.lean (1-52), and Representability.lean (19-60, 79-175). The abstract descent theorems assume prestack/stack conditions and do not construct the required represented slice/product comparisons. Zariski glueData requires open immersion charts, absent here. Thus neither new node is a one-line specialization.

Whole-DAG searches: tags 02W5 and lemma-descent-data-sheaves, local representation/gluing/fully-faithful keywords; blueprint_refs searches 'locally representable', 'descent data', 'representable', 'gluing sheaves'; ancestor query confirms lem-trf-local-term-locality. The small-etale locally constant descent nodes impose etale/finiteness assumptions and different sites. The general set-sheaf gluing node supplies no scheme representations or scheme transition comparison. The effective-scheme morphism descent node presupposes global schemes and cannot supply either task.

## Review by Q159

I read the full statement of every cited node, including the set-sheaf gluing node's morphism clause, Yoneda's natural bijection (not merely full faithfulness), uniqueness of a representing object, the exact finite-affine fpqc covering definition, affine refinement, and the fpqc morphism equalizer theorem. Parent step 1 uses precisely flatness, cover base change and the finite affine refinement needed for that definition: inverse images of affine opens are open in each source. Parent step 2 uses unique gluing of scheme maps, including target B to prove the glued map remains over B. These are the two prerequisites for both new constructions.

For parent step 3, the forward node states both the functor and its Hom bijection, and the inverse node states the natural isomorphism RG to identity for that very normalized R. Its hypotheses match the chosen site, family and representations. Fullness lifts the counit and its inverse; faithfulness proves inverse identities and naturality. This is a formal assembly, with no hidden sheaf-gluing or overlap argument. The two tasks each specify the local representations and coordinate maps, so the comparison also identifies the full descent datum. Parent step 4 uses the fibre-product universal property and uniqueness of representing schemes in the forward implication; in the converse it uses the forward task's explicit slice bijections and the morphism clause of set-sheaf descent to glue a local isomorphism and its inverse. Effectivity supplies exactly their agreement on double overlaps. No assumption that arbitrary scheme descent is effective is made.

For the new forward statement I checked 02W5's right-to-left construction against old steps 3 and 4: the projection is over Ti, products have the same three coordinates, triple compatibility is equality after Yoneda, and maps preserve identities/composition. Its full-faithfulness/reconstruction content is old step 8's unique local gluing, with the same morphism argument applied to arbitrary compatible local maps. For the inverse statement I checked 04TR and 04TQ against old steps 5-7: the small site has fibre products and terminal object T; e_j=theta_ij e_i has the correct orientation; taking all fibres yields the product representation; the resulting transition is the specified phi rather than an unspecified isomorphism. Compatible f_i give the displayed naturality equality, and uniqueness gives identities/composition and naturality of the datum comparison. No new proof has been smuggled into a statement as a sketch: these are the precise constructions and properties to prove.

Edge cases: repeated indices use full triple overlaps, not a false assertion phi_ii is the identity on Ti times_T Ti; diagonal pullback is identity from the cocycle and invertibility. Empty covering forces T empty; its slice sheaf is terminal by the empty-cover axiom and both categories are terminal up to equivalence. Empty local schemes and disconnected covers require no nonempty sections, no chosen points, no finiteness or separation. For a singleton identity cover both constructions reduce to Yoneda. Large families are bounded by the existing size convention; no unbounded colimit or proper class of gluing factors is taken. Each new node is a proper construction lemma, not an extra copy of the equivalence or the effectivity clause, and the parent proof stays below the requested bound.

B-E audit: statements introduce their own base, site, cover, functors, schemes, transitions and morphisms. Sources have tags and labels. Every new node has blueprint ancestry and actual searches, no proof steps. No Mathlib match was asserted merely from a name. All non-elementary parent inputs are cited by their statements, quotes were checked literally, and graph checks are delegated to the server. No off-unit route was substituted; the old declared affine-refinement and sheaf-gluing tool uses remain. No statement dispute was found.

## Preserved arguments and work allocation

The following is the complete original argument, retained verbatim for the future workers. These are report notes, not proof fields of the new unsplit nodes. Steps 3, 4 and the local-map/naturality checks of step 8 go to the forward node; steps 5, 6 and 7 go to the inverse node. Steps 1, 2 and 9 remain in the parent, with its new assembly using precisely those two interfaces.

### Original step 1

An fppf covering $\{W_a\to W\}$ is an fpqc covering in the sense of [def-weil-pbc-fpqc-covering]: flatness is part of [def-pc-fppf-site]. For every affine open $V\subset W$, restrict the covering to $V$ using the base-change axiom in [def-weil-pbc-sites-and-cohomology]. Apply [lem-pc-fppf-affine-refinement] to obtain finitely many affine opens of the inverse images $W_a\times_WV$ whose images cover $V$. These are also affine opens of $W_a$, since $W_a\times_WV$ is the inverse-image open subscheme. They are precisely the finite affine opens required in the fpqc definition. This applies on the big fppf site over any of the bases occurring below.

Cited statements: def-weil-pbc-fpqc-covering, def-pc-fppf-site, def-weil-pbc-sites-and-cohomology, lem-pc-fppf-affine-refinement.

### Original step 2

For any $B$-scheme $Z$, the presheaf $h_Z^B(W)=\operatorname{Mor}_B(W,Z)$ is an fppf sheaf. Indeed, step 1 and [lem-weil-pbc-fpqc-representable-descent] glue any compatible family of maps $W_a\to Z$ uniquely as scheme maps. The glued map is over $B$: its composite to $B$ equals $W\to B$ because the two maps have equal restrictions, and the uniqueness clause of the same node applies with target $B$. Thus the equalizer sheaf condition in [def-weil-pbc-sites-and-cohomology] holds. In particular this applies to $h_{T_i}$ and to each $h_{X_i}^{T_i}$.

Cited statements: lem-weil-pbc-fpqc-representable-descent, def-weil-pbc-sites-and-cohomology.

### Original step 3

Let $H$ be a sheaf as in the statement and choose $\alpha_i:h_{X_i}\xrightarrow{\sim}h_{T_i}\times H$. By [lem-pc-yoneda] the first projection of $\alpha_i$ is induced by a unique map $p_i:X_i\to T_i$. For a fixed $a:W\to T_i$, taking fibres over $a$ gives $\operatorname{Mor}_{T_i}(W,X_i)\simeq H(W)$. Conversely, any such isomorphism on the slice gives $\operatorname{Mor}_T(W,X_i)\simeq\coprod_{a\in\operatorname{Mor}_T(W,T_i)}H(W)=h_{T_i}(W)\times H(W)$ by separating maps according to their composite with $p_i$. All maps commute with restriction, since precomposition sends the fibre over $a$ to the fibre over $a\circ b$. Here slice restriction has the sectionwise meaning of [def-pur-localized-ringed-site].

Cited statements: lem-pc-yoneda, def-pur-localized-ringed-site.

### Original step 4

Write $T_{ij}=T_i\times_TT_j$. By the fibre-product universal property [def-pc-fibre-product], both $X_i\times_TT_j$ and $T_i\times_TX_j$ represent $h_{T_i}\times H\times h_{T_j}$. Apply [lem-pc-representable-unique] to the identification through this same functor to define $\phi_{ij}$. Its two projections to $T_i,T_j$ are unchanged, so it is over $T_{ij}$ by [lem-pc-yoneda]. On a triple overlap, both $\phi_{ik}$ and $\phi_{jk}\circ\phi_{ij}$ preserve the three base coordinates and the $H$ coordinate; hence their induced transformations are equal, and Yoneda gives the cocycle. If $v:H\to K$ is a sheaf map, $\mathrm{id}_{h_{T_i}}\times v$ gives a unique map between their representing schemes by Yoneda, over $T_i$. The same coordinate calculation shows compatibility with $\phi_{ij}$. Yoneda's injectivity shows that these maps preserve identities and composition. This defines the functor $R$ from sheaves to scheme descent data.

Cited statements: def-pc-fibre-product, lem-pc-representable-unique, lem-pc-yoneda.

### Original step 5

Conversely, let $D=(X_i,\phi_{ij})$ be a scheme descent datum. On the slice over $T_i$ put $F_i(W\to T_i)=\operatorname{Mor}_{T_i}(W,X_i)$, a sheaf by step 2. For $W\to T_{ij}$, the map $\phi_{ij}$ takes a map $W\to X_i$ together with the prescribed $W\to T_j$ to a unique map $W\to X_j$ over $T_j$; its inverse gives the inverse transformation. Thus it defines an isomorphism $\theta_{ij}:F_i|_{T_{ij}}\to F_j|_{T_{ij}}$, and the scheme cocycle gives $\theta_{ik}=\theta_{jk}\theta_{ij}$. Apply [lem-pe-set-sheaf-cover-descent] to obtain $H_D$ and $e_i:H_D|_{T_i}\xrightarrow{\sim}F_i$ with $e_j=\theta_{ij}e_i$. The hypotheses of that node hold: use the universe-small big fppf site from [def-weil-size-convention], its fibre products [def-pc-fibre-product], its terminal object $T$, and the given set-indexed covering. Localization over that terminal object is the original site, with the slice restrictions of [def-pur-localized-ringed-site].

Cited statements: lem-pe-set-sheaf-cover-descent, def-weil-size-convention, def-pc-fibre-product, def-pur-localized-ringed-site.

### Original step 6

For every $W/T$, the inverse of $e_i$ on the slice fibres gives the natural bijection $\operatorname{Mor}_T(W,X_i)=\coprod_{a:W\to T_i}\operatorname{Mor}_{T_i}((W,a),X_i)\xrightarrow{\sim}\coprod_{a:W\to T_i}H_D(W)=h_{T_i}(W)\times H_D(W)$. Therefore $h_{T_i}\times H_D$ is represented by $X_i$. On $W\to T_{ij}$ the equality $e_j=\theta_{ij}e_i$ says that the resulting comparison sends a map to $X_i$ to exactly its image under $\phi_{ij}$. By [lem-pc-yoneda], $R(H_D)$ is isomorphic to $D$, including its specified overlap maps, rather than just its local schemes.

Cited statements: lem-pc-yoneda.

### Original step 7

A morphism $f:D\to D'$ is a family $f_i:X_i\to X'_i$ over $T_i$ satisfying $\phi'_{ij}(f_i\times\mathrm{id})=(\mathrm{id}\times f_j)\phi_{ij}$. Postcomposition yields $F_i\to F'_i$ compatible with $\theta_{ij}$. Conjugating by $e_i,e'_i$ gives maps $H_D|_{T_i}\to H_{D'}|_{T_i}$ agreeing on double slices. The morphism clause of [lem-pe-set-sheaf-cover-descent] gives a unique global map $G(f):H_D\to H_{D'}$. Its uniqueness gives $G(\mathrm{id})=\mathrm{id}$ and $G(gf)=G(g)G(f)$. Hence $G:D\mapsto H_D$ is a functor. The local representing isomorphisms of step 6 commute with $f_i$ by their construction, so [lem-pc-yoneda] makes $RG\cong\mathrm{id}$ natural.

Cited statements: lem-pe-set-sheaf-cover-descent, lem-pc-yoneda.

### Original step 8

Starting instead with $H$, the local identifications in step 3 and the gluing isomorphisms for $G(R(H))$ give isomorphisms $G(R(H))|_{T_i}\to H|_{T_i}$. They agree on double overlaps because both transitions preserve the $H$ coordinate, as in step 4. By the morphism clause of [lem-pe-set-sheaf-cover-descent], these isomorphisms and their inverses glue to global maps. Their composites restrict to identities, so uniqueness in that clause makes them identities globally. The resulting isomorphism $GR(H)\cong H$ is natural: for a map $H\to K$ the two maps in the naturality square agree on each slice by the definition of $R$ and $G$, and hence agree globally by uniqueness. Together with step 7, this proves the asserted equivalence of categories and the identification of its local representing objects.

Cited statements: lem-pe-set-sheaf-cover-descent.

### Original step 9

If $H\simeq h_X$ for a $T$-scheme $X$, the universal property [def-pc-fibre-product] gives $h_{T_i}\times H\simeq h_{T_i\times_TX}$. By [lem-pc-representable-unique] the representing schemes $X_i$ are isomorphic to $X\times_TT_i$, and the isomorphisms induce exactly $\phi_{ij}$ since both comparisons preserve the $X$ coordinate. Thus $R(H)$ is effective. Conversely, suppose a $T$-scheme $X$ and isomorphisms $X\times_TT_i\simeq X_i$ realize the datum $R(H)$. They give local isomorphisms $h_X|_{T_i}\simeq H|_{T_i}$ by step 3. Effectivity says precisely that they agree on double overlaps. Step 2 makes $h_X$ a sheaf; apply [lem-pe-set-sheaf-cover-descent] to glue these local maps and their inverses. Uniqueness makes their composites identities. Hence $h_X\simeq H$, proving representability. Effectivity here is exactly the covering-family definition in the statement, consistent with [def-pd-descent-datum].

Cited statements: def-pc-fibre-product, lem-pc-representable-unique, lem-pe-set-sheaf-cover-descent, def-pd-descent-datum.

## Not duplicates

lem-trf-fppf-local-representations-fully-faithful vs lem-pe-set-sheaf-cover-descent: abstract set-sheaf gluing is an input; no representing schemes, Yoneda overlap comparison or product representations are stated.

lem-trf-fppf-local-representations-fully-faithful vs lem-pe-site-sheaf-gluing: abstract set-sheaf gluing is an input; no representing schemes, Yoneda overlap comparison or product representations are stated.

lem-trf-fppf-local-representations-fully-faithful vs def-weil-pbc-augmented-module-complex-glue-data: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs def-weil-pbc-finite-local-model-canonical-transport: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs def-weil-pbc-finite-local-model-comparison-point: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs def-weil-pbc-finite-local-model-compatible-transport: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs def-weil-pbc-finite-ring-torsor-associated-module: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs def-weil-pbc-proetale-local-submodule-gluing-data: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs def-weil-pbc-proetale-local-subobject-kernel: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs def-weil-pbc-site-module-compatible-tuples: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs def-weil-pbc-torsor-associated-module: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs def-weil-pbc-torsor-section-representation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs finite-local-models-transport-compatibility: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs finite-local-models-transport-exists: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs finite-local-models-transport-naturality: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-augmented-module-complex-gluing: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-connected-torsor-module-descent: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-constant-module-locally-constant: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-continuous-lattice-finite-coproduct: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-etale-coproduct-representation: combines specified etale local models into a coproduct on the small etale site, rather than constructing either functor for arbitrary schemes on the big fppf site.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-etale-representable-descent-glue: assumes an effective etale representing scheme and proves representability on the small etale site; neither arbitrary scheme-data gluing nor the forward functor is asserted.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-finite-local-model-compatible-transport-cocycle: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-finite-local-model-compatible-transport-datum: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-finite-local-model-compatible-transport-diagonal: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-finite-local-model-compatible-transport-transport: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-finite-local-models-descent-datum-compatibility: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-finite-local-models-descent-datum-existence: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-finite-local-models-descent-datum: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-finite-ring-torsor-module-comparisons: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-finite-ring-torsor-module-descent: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-proetale-compatible-local-submodules: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-proetale-compatible-local-subsheaves: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-proetale-local-quotient-vanishing: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-proetale-local-subobject-kernel-effective: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-site-module-compatible-tuples: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-site-module-sheaf-gluing-aux: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-site-module-sheaf-gluing: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-associated-module-comparisons: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-associated-module-essential-image: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-associated-module-full: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-diagonal-evaluation-bijective: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-diagonal-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-equivariant-module-diagonal-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-equivariant-module-is-sheaf: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-equivariant-module-recover-linear: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-equivariant-presheaf-sheaf: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-graph-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-invariant-sections: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-module-descent-equivalence: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-normalized-graph-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-ordinary-evaluation-equivariant: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-ordinary-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-section-evaluation-bijective: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-section-evaluation-local: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-weil-pbc-torsor-section-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-local-representations-fully-faithful vs lem-sfb-locally-prescribed-modules-small: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-sfb-sheaf-cover-local-isomorphism: detects that an existing sheaf morphism is an isomorphism; it constructs neither local representing schemes nor a global sheaf from scheme data.

lem-trf-fppf-local-representations-fully-faithful vs lem-pur-clopen-ringed-module-gluing: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-pur-degree-zero-derived-map-gluing: glues degree-zero derived module morphisms on Zariski opens, not scheme representations or their descent transitions.

lem-trf-fppf-local-representations-fully-faithful vs lem-pur-sheaf-hom-cover-gluing: glues linear morphisms of module sheaves, without local scheme representations or their product/slice comparisons.

lem-trf-fppf-local-representations-fully-faithful vs lem-pur-sheaf-hom-is-sheaf: the Hom presheaf of module sheaves is a sheaf; it does not supply a scheme-valued descent construction or represented product/slice comparison.

lem-trf-fppf-local-representations-fully-faithful vs def-trf-fine-log-etale-descent-datum: defines fine-log/monoid descent data on a small etale site, not a theorem constructing either scheme/set-sheaf functor.

lem-trf-fppf-local-representations-fully-faithful vs def-trf-scheme-cover-descent-datum: definitions of the two categories and effectivity, with no functor-construction theorem.

lem-trf-fppf-local-representations-fully-faithful vs lem-trf-fppf-sheaf-representability-descent-data: the parent states the equivalence and effectivity criterion; this node extracts the forward construction and its Hom bijection.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-pe-set-sheaf-cover-descent: abstract set-sheaf gluing is an input; no representing schemes, Yoneda overlap comparison or product representations are stated.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-pe-site-sheaf-gluing: abstract set-sheaf gluing is an input; no representing schemes, Yoneda overlap comparison or product representations are stated.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-weil-pbc-augmented-module-complex-glue-data: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-weil-pbc-finite-local-model-canonical-transport: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-weil-pbc-finite-local-model-comparison-point: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-weil-pbc-finite-local-model-compatible-transport: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-weil-pbc-finite-ring-torsor-associated-module: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-weil-pbc-proetale-local-submodule-gluing-data: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-weil-pbc-proetale-local-subobject-kernel: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-weil-pbc-site-module-compatible-tuples: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-weil-pbc-torsor-associated-module: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-weil-pbc-torsor-section-representation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs finite-local-models-transport-compatibility: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs finite-local-models-transport-exists: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs finite-local-models-transport-naturality: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-augmented-module-complex-gluing: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-connected-torsor-module-descent: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-constant-module-locally-constant: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-continuous-lattice-finite-coproduct: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-etale-coproduct-representation: combines specified etale local models into a coproduct on the small etale site, rather than constructing either functor for arbitrary schemes on the big fppf site.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-etale-representable-descent-glue: assumes an effective etale representing scheme and proves representability on the small etale site; neither arbitrary scheme-data gluing nor the forward functor is asserted.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-finite-local-model-compatible-transport-cocycle: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-finite-local-model-compatible-transport-datum: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-finite-local-model-compatible-transport-diagonal: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-finite-local-model-compatible-transport-transport: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-finite-local-models-descent-datum-compatibility: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-finite-local-models-descent-datum-existence: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-finite-local-models-descent-datum: finite etale local models of a sheaf on the small etale site; these transport statements do not construct the functor for arbitrary local schemes on a big fppf cover.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-finite-ring-torsor-module-comparisons: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-finite-ring-torsor-module-descent: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-proetale-compatible-local-submodules: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-proetale-compatible-local-subsheaves: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-proetale-local-quotient-vanishing: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-proetale-local-subobject-kernel-effective: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-site-module-compatible-tuples: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-site-module-sheaf-gluing-aux: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-site-module-sheaf-gluing: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-associated-module-comparisons: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-associated-module-essential-image: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-associated-module-full: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-diagonal-evaluation-bijective: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-diagonal-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-equivariant-module-diagonal-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-equivariant-module-is-sheaf: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-equivariant-module-recover-linear: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-equivariant-presheaf-sheaf: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-graph-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-invariant-sections: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-module-descent-equivalence: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-normalized-graph-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-ordinary-evaluation-equivariant: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-ordinary-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-section-evaluation-bijective: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-section-evaluation-local: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-weil-pbc-torsor-section-evaluation: equivariant module sections or representation descent for a finite group torsor on a small etale site; no arbitrary scheme descent datum or locally represented big-fppf set sheaf is considered.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-sfb-locally-prescribed-modules-small: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-sfb-sheaf-cover-local-isomorphism: detects that an existing sheaf morphism is an isomorphism; it constructs neither local representing schemes nor a global sheaf from scheme data.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-pur-clopen-ringed-module-gluing: a module/complex or proetale subobject gluing statement, not a construction with local representing schemes and their Yoneda transition comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-pur-degree-zero-derived-map-gluing: glues degree-zero derived module morphisms on Zariski opens, not scheme representations or their descent transitions.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-pur-sheaf-hom-cover-gluing: glues linear morphisms of module sheaves, without local scheme representations or their product/slice comparisons.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-pur-sheaf-hom-is-sheaf: the Hom presheaf of module sheaves is a sheaf; it does not supply a scheme-valued descent construction or represented product/slice comparison.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-trf-fine-log-etale-descent-datum: defines fine-log/monoid descent data on a small etale site, not a theorem constructing either scheme/set-sheaf functor.

lem-trf-fppf-scheme-data-sheaf-gluing vs def-trf-scheme-cover-descent-datum: definitions of the two categories and effectivity, with no functor-construction theorem.

lem-trf-fppf-scheme-data-sheaf-gluing vs lem-trf-fppf-sheaf-representability-descent-data: the parent states the equivalence and effectivity criterion; this node extracts the inverse gluing construction and its natural local datum comparison.

