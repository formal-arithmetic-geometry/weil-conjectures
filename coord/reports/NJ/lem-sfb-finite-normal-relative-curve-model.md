# Stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-normal-relative-curve-model.json`: item, statement, split into eleven steps; no statement change; not a Mathlib leaf.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-dominant-normal-base-universally-open.json`: one new statement-only node, unsplit; no Mathlib match after two semantic formulations, Loogle, LeanSearch and source searches.
- `citations.json`: one verbatim statement quotation for each node used by each proof step.
- `searches.jsonl`: actual searches logged by msearch.py; the item retains its inherited searches and adds this worker's searches. The new node records the searches concerning universal openness, with their exact queries.

## Attachments

None for this item or the new node. Searched the live project under `lean/WeilConjectures/` by the item's blueprint tag, normalization/curve terms and universal-openness terms. Read `Mathlib/AlgebraicGeometry/Normalization.lean` in the project root WeilConjectures: its normalization-in-a-field declarations cover existing DAG inputs, not the complete relative-curve assertion. Read the finite-normal dense-open comparison and quasi-finite modules too; neither gives the new openness theorem. No Lean was written or compiled.

## Wanted literature

WANTED: local copy of de Jong, *Families of curves and alterations* (1997), §§3.2 and 3.5, printed pp.605,607–608, for lem-sfb-finite-normal-relative-curve-model. The publisher PDF at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf was read online, including §2.9 and §§3.1–3.6. It is not present in local literature. The explicit supplement to its normalization argument is marked `proof_origin.by = agent`; its generic inputs were checked against the local Stacks source.

## Corrections and scope

No statement dispute or alteration of the statement. The item had no proof and no earlier sandbox delivery. Its function-field, projectivity, full-product surjectivity, geometric-purity, semilinear functoriality and finite factorization clauses are all retained. The source's §3.2 uses the reduced base change before subsequent normalization; the item uses its normal finite model. This distinction is explained by the affine construction, rather than silently identifying the reduced base change with its normalization.

The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor` confirms it. Its precise inherited from.place and via chain are retained, and the new node inserts this item into that chain. The chapter is the current six-functors-basics chapter; the inherited unit record is the historical sk-thm-sf-ctf-stability. This is an auxiliary node, not that unit's key statement, so no chapter or unit files are changed. The construction stays within the inherited de Jong finite-normal-model prerequisite of the plurinodal alteration route. Off-unit generic inputs that are not Mathlib leaves or Lean-closed are explicitly declared in split_report.tool_uses.

## Not duplicates

lem-sfb-finite-dominant-normal-base-universally-open vs lem-a1-normal-etale-components-clopen: the existing statement concerns clopen components of etale schemes over a normal base, not universal openness of a possibly ramified finite dominant map.

lem-sfb-finite-dominant-normal-base-universally-open vs lem-a1-normal-geometric-cover-components: the existing statement concerns geometric covers and components; our map is only finite dominant and may be ramified.

lem-sfb-finite-dominant-normal-base-universally-open vs lem-a1-normal-completed-integral-model: the existing statement constructs a completed integral coefficient model, not openness of a finite scheme map.

lem-sfb-finite-dominant-normal-base-universally-open vs lem-a1-normal-locally-constant-finite-section: the existing statement concerns finite sections and locally constant sheaves on a normal scheme, not this morphism property.

lem-sfb-finite-dominant-normal-base-universally-open vs lem-a1-normal-proetale-monodromy: the existing statement concerns pro-etale monodromy; it supplies no universal-openness conclusion for ramified finite covers.

lem-sfb-finite-dominant-normal-base-universally-open vs lem-a1-smooth-lisse-integral-lattice: the existing statement concerns lisse integral lattices, not the openness of scheme morphisms.

lem-sfb-finite-dominant-normal-base-universally-open vs lem-sc-scheme-over-field-universally-open: the latter assumes a field target; the new statement allows every normal integral locally Noetherian base and requires the map finite dominant.

Whole-DAG and whole-blueprint searches included normalization, finite normalization, finite dominant, universally open, normal/open and the Stacks tags. No existing node states the new theorem; none has Tag 0F32. The six pairs above arise from the shared supporting Tag 0BQ3. The integral-closure, localization, finite-normalization, finite-over-projective, H-projective permanence, fibre-dimension openness and local-dimension facts already have nodes and were reused. No elementary affine calculation, clause of the item, or duplicate normalization theorem was made into a node.

## Review by NJ

I read the publisher's de Jong §§3.2 and 3.5 and the local Stacks proofs of 0307 (integral-closure localization), 034L (integral closure inside a normal domain), 00GY (normal localization), 00GQ (lying over), 01T6 (finite type over Noetherian), 035D (finite permanence), 087S (the distinction between projective and H-projective), 0GK4 (projective normalization), 02FZ (local fibre dimension is upper semicontinuous), and 02FY (local fibre dimension under base change). For the sole new statement I read more-morphisms.tex, lemma-quasi-finite-Noetherian-universally-open, Tag 0F32, in full and properties.tex, lemma-normal-geometrically-unibranch, Tag 0BQ3. The source requires a locally quasi-finite map, locally Noetherian geometrically unibranch target, and dominance for every source component. Finiteness implies the first condition; normality gives the second geometric condition; integrality and dominance give the third. No separability or flatness is needed in that new node.

I also made the separation hypothesis explicit before using finite-over-separated-finite-type: H-projective composition gives X/k projective, and projective-implies-proper gives separatedness. The affine-fibre-product-spectra statement is cited in steps 2, 3 and 6 for the concrete tensor-product formulas, not inferred merely from the fibre-product definition.

Step 1 uses the actual statements of the finite-extension normal-closure, normal-localization, closure-localization, injective lying-over and finite-normalization nodes: together they give normal local rings, integral charts with fraction field L/E, surjectivity and finiteness. The finite-over-separated-finite-type and finite-type-over-Noetherian statements give exactly the finiteness and Noetherian hypotheses subsequently needed. Every affine base ring is a domain and all the specified field extensions are finite.

Step 2 uses the definition's integral-closure charts, localization, and the already cited finite-normalization theorem. I wrote the homomorphism A tensor_R R_E to A_L explicitly. Its finiteness follows from the very same finite module generators, so it needs no extra projectivity or factorization lemma.

Step 3 takes from geometric integrality exactly its requirement of integrality after every field extension. The localization of D tensor_K E is nonzero since E/K is a field extension. It is finite-dimensional over F since E/K is finite. The elementary injective-endomorphism argument proves it is a field. Thus the single generic point used in step 4 is justified before that step.

Step 4 applies the new openness theorem only to T to S: S is normal integral and locally Noetherian, and T to S is finite dominant by step 1. Its statement explicitly gives openness after the arbitrary base change X to S. I then checked the dense-point argument on the whole W, not just the component containing the generic fibre. The finite-closed-map node says exactly that the image is closed; together these facts give the full surjectivity claimed by the item, even if W has nilpotents.

Step 5 uses H-projective composition, the affine-base clause of finite-over-projective, projective-implies-proper, and H-projective permanence. I checked the full finite-over-projective statement: it gives only local projectivity over a general base. Here its base is Spec k, so it does give the global embedding we need. Only after obtaining Y projective over k do I apply permanence along the separated morphism T to Spec k. This avoids incorrectly assuming every finite morphism to an arbitrary base is H-projective.

Step 6 uses the localization theorem with R minus zero and the definition of normalization. It identifies both the base generic point Spec E and the actual E-structured generic fibre. C is a hypothesis, so no smoothness conclusion about arbitrary normal curves over imperfect fields is inferred.

Step 7 uses equidimensional-open local dimension for the supplied E-curve C, and the local-fibre-dimension openness node with n=0. An open of integral Y contains its generic point, so the indicated zero-dimensional locus is empty. Step 8 uses finite base change, integral injective dimension equality applied to B/ker to D, base-change invariance of local fibre dimension, finite-type Noetherianity, and the constant-local-dimension component theorem. These statements provide exactly the upper bound, lower bound after geometric extension, and passage to pure component dimension. The target fibre is a geometric fibre of the original family, so its dimension bound is part of the hypothesis. No flatness, normality of X, or normality after geometric base change of Y is assumed.

For steps 8, 9 and 11 I also added the existing Mathlib leaf lem-weil-pbc-finite-algebra-is-integral, whose statement supplies precisely the implication from finite module to monic integral equation. This repairs a citation omission found during self-review after the first successful dry run.

Step 9 uses primitive element only for the finite separable field extension E/K. The Bezout relation survives extension to F. Smooth-relative-dimension and projective-base-change nodes give the corresponding properties of X_K tensor E; geometric integrality gives integrality; smooth-normal applies to that smooth curve over E. The normal-affine comparison proves it is the normalization, instead of claiming that arbitrary normalization commutes with arbitrary field extension.

Steps 10 and 11 are explicit affine arguments. Monic equations are invariant under a compatible field isomorphism even if it acts on k; inverses and composition already agree in L and E. For the final factorization, the given embedding sends every integral element of B into A_L. The same finite A-module generators establish finiteness over B. Injectivity into L proves uniqueness; no unproved universal property is taken from a definition node.

I checked B–E of delivery-errors.md against these files: the new node is self-contained and statement-only; its notions are cited or defined inline, source tags and labels are explicit, and Mathlib searches were actually run and read. Every cited node's statement was opened; citations.json quotes those statements verbatim. The proof has no hidden large step (the longest is under 900 characters), no moved-out item clause and no cycle by construction. Small cases checked include S=Spec K, trivial extensions E=K and L=F, nonnormal X with smooth generic fibre, singular normal bases, ramified constant extensions, imperfect ground fields, a nonreduced fibre product, nonfaithful semilinear actions, intermediate Z=X_U when it is normal, Z=Y_U, and the vacuous empty-open case. The only new node also handles identity maps, zero-dimensional normal bases, and ramified finite covers. Dropping normality would allow normalization of a nodal curve and invalidate openness, so normality is retained.

## Unfinished work

No unfinished part of the item's split. The one new generic theorem is intentionally unsplit for a future stage-1 worker. No new Mathlib leaves are claimed. Maintainer review remains independent of this signed self-review.
