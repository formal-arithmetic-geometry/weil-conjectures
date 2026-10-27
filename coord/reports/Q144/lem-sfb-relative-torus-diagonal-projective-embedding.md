## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-torus-diagonal-projective-embedding.json`: item, split into five steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-normal-line-power-linearization.json`: new statement-only intermediate, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-linearized-line-sections-coaction.json`: new statement-only intermediate, unsplit; no Mathlib match.
- `citations.json`: eleven step/dependency entries with verbatim statement excerpts.

Attachments: none. Searched `lean/WeilConjectures/` by the item tag, Sumihiro, Thomason, torus, diagonal projective embedding, relative linearization, and the two new intermediate notions. No project declaration states the item. Ordinary projective charts and finite-group equivariance do not attach it. No Lean was written or compiled, and no git command was run in the read repository.

WANTED: R. W. Thomason, *Equivariant resolution, linearization, and Hilbert's fourteenth problem over arbitrary base schemes*, Adv. Math. 65 (1987), 16–34, DOI 10.1016/0001-8708(87)90016-8, proof of Theorem 3.3 and Corollary 3.4(3), printed p.32; local path `literature/thomason-equivariant-resolution-linearization.pdf`, for the item and relative-normal-line-power-linearization. The local copy is absent. I read the primary article's full text online at the ResearchGate URL recorded in the nodes. I did not substitute an unrelated Stacks tag for its linearization input. The assembly proof is marked agent-written. No SGA source is used.

What needed repair: the item had no proof. The tempting existing normal-line-power-linearization and linearized-qcoherent-cohomology-coaction statements both have field hypotheses; they do not prove this result over arbitrary Noetherian A. The finite-projective relative-torus-bundle-weights node also does not apply to a possibly non-finitely-generated section module. The new proof avoids those applications. It uses finitely many Laurent coefficients of finitely many immersion sections, then a free module on that list. A weight module need not be free, and no such claim is made. Coordinate weights are the negatives of forward section weights, as checked below. The original statement was not disputed or weakened.

Unfinished work: the two new intermediate statements deliberately remain unsplit, as required for a one-level stage-1 split. No unfinished part of the assembly proof is deferred except those named intermediate lemmas.

## Searches and blueprint route

I read AGENTS.md, the worker role, GOAL.md, the three levels in SETUP.md, the stage-1 brief and stage document, delivery-errors B–E in full, tools/README.md, and the item's chapter and unit records. No repair note exists for this item. The sandbox initially contained only dispatcher markers; there was no previous split, report or search log to overwrite.

The current blueprint is `literature/blueprint/latest` -> `main-20261024`, commit ef6f9619fdbffa59e88528fb56483d76c70258c8. The unit record is legacy: its former sk-thm-sf-ctf-stability directory has moved, so I read the current `sec-six-functors/sk-thm-sf-kunneth-verdier/thm-sf-ctf-stability.proof.md` and the surrounding unit section instead of an older snapshot. This node is a supporting geometric lemma on the inherited relative torus quotient/invariant-affine branch, not the unit's key theorem. `blueprint_refs.py ancestor` reports a null ancestor for this inherited branch. I retained that null value and the existing via chain, and gave both new nodes exact supporting places and via lists with the item prepended.

I searched the whole DAG by title/statement for Thomason, Sumihiro, normal line power linearization, relative torus, weight decomposition, section coaction, and the relevant Stacks tags. I ran whole-blueprint searches for torus, linearization, very ample, equivariant immersion, coaction, normal, Thomason, global sections and 02KH. The results include proper-over-field ampleness and categorical module linearization, but no imported node stating either relative intermediate. `same_as` is therefore empty. I opened the finite-sections, relative-ampleness, quotient-comparison, projective-bundle classification, field linearization, field coaction, relative bundle weights, flat base change, and equivariant groupoid pushforward statements before selecting dependencies.

For the item and each new node I ran msearch.py with LeanFinder, Loogle, grep and LeanSearch, and a second LeanFinder formulation. The fifteen actual searches and result digests are retained in searches.jsonl and assigned to the appropriate node with the exact queries. All services responded. Hits concerned ordinary Proj, projectivization of vector spaces over division rings, abstract group representations, ordinary section localization, and Laurent Hopf algebra structures. I read the returned signatures, the projectivization action in `Mathlib/LinearAlgebra/Projectivization/Action.lean`, the Laurent Hopf instance in `Mathlib/RingTheory/HopfAlgebra/MonoidAlgebra.lean`, and the representation linearization declarations under `Mathlib/RepresentationTheory/Rep/`. They do not provide either relative equivariant sheaf assertion. There are zero Mathlib leaves.

## Review by Q144

I read Thomason's standing hypotheses 1.1 and Theorem 3.3 with its proof and Corollary 3.4(3) on printed p.32 in the primary online article. The first paragraph linearizes a positive power of a relatively very ample line before introducing a coherent module of sections. That is the new relative-normal-line-power-linearization node, restricted to the split torus and an affine Noetherian base. The affine base is separated Noetherian, the split torus is affine, smooth, of finite type and has connected geometric fibres, and X is normal and quasi-projective because it has the specified relatively very ample line and is finite type over affine S. Normality of S is not an assumption. The node introduces its own group algebra, action, line, tensor power, identity and cocycle, including the empty and disconnected cases. It does not assert an embedding, so it is an intermediate linearization input rather than a restatement of the item.

For relative-linearized-line-sections-coaction I read `coherent.tex`, Tag 02KH, label `lemma-flat-base-change-cohomology`, including the canonical map and affine-base formulation. The new statement is the degree-zero torus consequence over a ring, not a claim of arbitrary nonflat cohomological base change. Here is the argument intended for its later split: the Laurent algebra C and C tensor C are free over A. The flat-base-change map identifies V tensor C with sections of p_2^*L on T times X. Pull a section back by the inverse universal torus element and then apply the forward linearization to produce the universal translated section. Take its inverse image under this base-change isomorphism to define c. The identity and cocycle equalities, applied on T times T times X, give the counit and coassociativity identities. Specializing this section construction along C -> B gives the stated formula for every B, even nonflat B; it uses only natural pullback of a section and never an inverse nonflat base-change map. This needs the qcqs hypothesis, which follows here from finite type and separatedness, and an invertible line, which is quasi-coherent. It is an independent comparison between a geometric linearization and a rational coaction, rather than a clause of the requested embedding. No finite-dimensionality or freeness of V is assumed. The existing field-only coaction statement cannot replace it.

Step 1 uses the statement of lem-trf-projective-bundle-quotient-geometry for the canonical invertible twist and its free-projective-space model, and def-trf-relatively-very-ample for the pullback along the given immersion. The new relative linearization lemma then applies to that line. I checked normality of X, Noetherianity of A, separated finite type, and the actual scheme-action identities; no algebraic closure or field is available. The cited field-only linearization node is not used.

Step 2 uses exactly the equivalence in lem-trf-relative-ample-very-ample: a very ample power exists if and only if all sufficiently large powers are very ample. Thus I choose a large multiple mk, instead of silently assuming a linearized power is still very ample. Tensoring k copies of the linearization tensors its identity and cocycle maps, using the explicit tensor-power definition in def-pur-sheaf-tensor-product. Lem-sfb-very-ample-affine-finite-sections supplies a finite generating section list and the immersion of its actual quotient. It applies because f is finite type and S is affine; properness is unnecessary.

Step 3 uses the new coaction lemma's actual counit and coassociativity clauses. In the tensor square of the Laurent monomial basis, the coefficient equation says each coefficient section is itself homogeneous; the counit says the old section is their sum. Taking the finite union of the supports therefore gives finitely many generators of the line. This is a coefficient calculation, written out in the step, not a new representation-theoretic theorem. It does not use an eigenbasis, semisimplicity over a field, or projectivity of any section submodule. Appending a zero section keeps the list nonempty without changing its image or weight identities.

Step 4 uses the arbitrary-module quotient classification in lem-trf-projective-bundle-quotient-geometry to define j from the new finite free quotient. I checked the statement of lem-trf-projective-quotient-comparison: it accepts a map E -> F, not necessarily an injection, whose composite quotient is the original generating quotient with an immersion. Here E is the old free module and F the free module on coefficient sections. The explicit column sums recover each s_i, so all its hypotheses hold on the single base open S. That lemma concludes an immersion, which is exactly what is required. No unsourced assertion that an immersion remains one after adding arbitrary coordinates is left in the assembly.

Step 5 uses the normalization clause of the new coaction lemma and the natural invertible-quotient classification. For a forward section weight u, theta_{g,x}(v(x)) = g^u v(gx), so v(gx) = g^{-u} theta_{g,x}(v(x)). Consequently the coordinate coaction has weight w=-u. The common theta is a line isomorphism, and quotient classification identifies the two morphisms, not merely their geometric points. It is natural on every affine test scheme and under pullback, hence gives equality of scheme morphisms and survives every base change. The action laws are checked on the polynomial generators as written. This corrects the sign ambiguity that would arise if a weight of forward sections were identified directly with a coordinate weight.

Small cases: for a trivial action take the canonical trivial linearization, so the construction has zero weights; for r=0 the Laurent basis has just exponent zero. For X empty all section quotients into the zero sheaf are surjective, the zero list is allowed and gives its unique immersion into P^0, including the zero-ring base. For disconnected normal X the same globally finite section list and a single exponent are used, with no integrality assumption on X. For A = k[epsilon]/(epsilon^2) the Laurent monomials are still an A-basis, so coefficient comparison still applies even when X is supported on the reduction. Nonfree finite projective weight summands cause no problem because the proof takes a free module on finitely many homogeneous generators. For a nonflat quotient A -> A/I the proof specializes section identities only; it does not claim nonflat cohomological base change.

Against delivery-errors B–E: both new statements are self-contained, statement-only and properly sourced; all nonstandard notions are defined inline or have definition dependencies, and TeX uses one backslash after JSON decoding. The non-elementary linearization and section-comparison facts are named nodes, the other substantive inputs already exist, and the remaining coefficient and sign arguments are explicit elementary steps. I checked every cited node's statement, not its proof. Each of the eleven step/dependency edges has a verbatim excerpt in citations.json. No step exceeds 2000 characters; the longest is 1075, and none hides a comparison other than the separately named section-coaction input. The new nodes depend only on definitions and do not depend on the item, so no circular proof was introduced. No unit or chapter route was changed, and no existing node was edited. Generic tool citations from the trace-formula unit are declared in split_report.tool_uses for maintainer review; no maintainer-owned tool_uses field was set.

## Not duplicates

lem-sfb-relative-normal-line-power-linearization vs lem-sfb-normal-line-bundle-power-linearization: the existing statement is over an algebraically closed field; the new input is relative to a possibly nonnormal or nonreduced Noetherian ring, for a relatively very ample line.

lem-sfb-relative-normal-line-power-linearization vs lem-sfb-normal-quasiprojective-equivariant-immersion: the existing immersion theorem is over an algebraically closed field and does not state relative line-power linearization over a ring.

lem-sfb-relative-normal-line-power-linearization vs lem-sfb-relative-torus-diagonal-projective-embedding: the item concludes an equivariant immersion into a free diagonal projective space; this intermediate only gives a linearization on a tensor power of a specified line.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-relative-torus-bundle-weights: the existing statement starts from an already supplied coaction on a finite projective module; the new statement constructs the coaction geometrically on a section module with no finiteness assumption.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-hopf-coaction-linearization: the existing equivalence assumes a field and an affine source; the new statement concerns global sections on a possibly nonaffine separated finite-type scheme over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-cartesian-groupoid-pushforward-adjunction: the existing statement constructs equivariant pushforward modules and an adjunction, but does not state a Laurent coaction on the global section module or the normalized inverse-action section formula.

lem-sfb-relative-linearized-line-sections-coaction vs def-sc-general-curve: the existing node is “Curves over an arbitrary field”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sc-fraction-field-sections-base-change: the existing node is “Normalized degree-zero base change to the fraction field”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sc-picard-product-open: the existing node is “Triviality on two slices and one fibre is open in a product family”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sc-picard-universal-rank-match-residue-criterion: the existing node is “Universal Picard matching tested on a fixed-rank residue-field fibre”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sc-proper-flat-global-sections-criterion: the existing node is “Proper flat morphisms with fibrewise constant functions”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-per-bounded-genus-rational-model: the existing node is “Bounded genus produces a model with rational singularities”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-per-local-cohomology-flat-base-change: the existing node is “Flat base change for derived ideal-torsion local cohomology”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-per-regular-model-completion: the existing node is “Normal completion and completed regular birational model”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-per-regular-point-blowup-acyclic: the existing node is “Geometry and first-direct-image vanishing of a regular point blowup”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-per-regular-surface-rational: the existing node is “Regular local surfaces define rational singularities”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs def-pc-affine-alternating-cech-model: the existing node is “Explicit sheafified affine alternating Cech model”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs def-pc-flat-cohomology-comparison: the existing node is “Canonical scalar-extension comparison on Ext-based scheme cohomology”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs def-pc-flat-filtered-scalar-extension: the existing node is “Scalar extension of filtered complexes”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-affine-alternating-cech-base-change-factorization: the existing node is “Canonical mate factorization on the explicit affine alternating Cech model”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-affine-alternating-cech-exchange-resolution: the existing node is “Alternating affine resolution with invertible ordinary exchange”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-affine-alternating-cech-model-flat: the existing node is “Flat terms of the explicit affine alternating Cech model”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-affine-alternating-cech-pinned-mate: the existing node is “Affine alternating Cech computation for the fixed derived counit”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-base-change-closure-components: the existing node is “Components of a smooth projective curve over an algebraic closure”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-cohomology-mayer-vietoris-ext-presentation: the existing node is “Geometric Ext presentations for the Mayer--Vietoris base-change comparison”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-cohomology-mayer-vietoris-inverse-image: the existing node is “Mayer--Vietoris inverse-image comparison before extension of scalars”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-degree-base-change: the existing node is “Degree: base change and tensor products”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-finite-affine-cech-model-acyclic-resolution: the existing node is “An acyclic resolution representing the specified finite affine section complex”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-affine-base-change-sections: the existing node is “Canonical scalar-extension sections on one affine open”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-base-change-cohom: the existing node is “Cohomology and flat base change”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-cech-base-change-differential: the existing node is “Canonical Cech component maps commute with the differential”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-cech-base-change-terms: the existing node is “Canonical isomorphisms of individual finite affine Cech terms”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-cech-base-change: the existing node is “Canonical scalar-extension isomorphism of finite affine Cech complexes”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-cech-cocycle-comparison: the existing node is “Inverse-image compatibility of Leray comparisons on original Cech cocycle classes”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-cech-cohomology-square: the existing node is “Canonical cohomology comparison and the Cech homology square”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-cohomology-gluing: the existing node is “Mayer--Vietoris gluing of canonical flat cohomology comparisons”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-cohomology-mayer-vietoris: the existing node is “Exact Mayer--Vietoris diagram of canonical flat base-change comparisons”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-cohomology-separated: the existing node is “Flat cohomology comparison on compact separated schemes”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-filtered-complex-comparison: the existing node is “Flat comparison of filtered cochain complexes”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-flat-tensor-complex-cohom: the existing node is “Flat tensor product commutes with cohomology of a bounded complex”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-genus-well-defined: the existing node is “Well-definedness of the genus”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-h0-geom-connected: the existing node is “$H^0=k$ is equivalent to geometric connectedness”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-proper-geometrically-reduced-global-sections-separable: the existing node is “Separability of global sections of a proper geometrically reduced scheme”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-s3-affine-alternating-cech-augmented-construction: the existing node is “Augmented increasing-tuple sheaf complex with affine section comparison”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-s3-affine-alternating-cech-resolution-core: the existing node is “Core affine alternating Cech resolution data”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-s3-affine-alternating-cech-resolution-exchange: the existing node is “Affine alternating Cech ordinary exchange”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-s3-alternating-cech-sheaf-affine-comparison: the existing node is “Affine pushforward of the constructed increasing-tuple sheaf complex”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-s3-alternating-cech-sheaf-affine-quasicoherent: the existing node is “Quasi-coherence of the pushed-forward increasing-tuple sheaf terms”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pc-s3-alternating-cech-sheaf-affine-sections: the existing node is “Global sections of the constructed increasing-tuple sheaf complex”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sc-flat-base-change-coherent: the existing node is “Flat base change for coherent cohomology”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs def-weil-pbc-formal-functions-local-comparison: the existing node is “Local-base-change cohomology and canonical germ comparison”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pbc-additive-cohomology-base-change-square: the existing node is “Linear untensored additive cohomology base-change square”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pbc-additive-cohomology-linear-base-change: the existing node is “Canonical linear scalar extension of additive first etale cohomology”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pbc-additive-cohomology-pullback-comparison: the existing node is “Coordinate-normalized additive cohomology pullback comparison”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pbc-additive-cohomology-tensor-kernel: the existing node is “Trivial kernel of additive cohomology tensor pullback”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pbc-additive-cohomology-tensor-surjective: the existing node is “Surjectivity of additive cohomology tensor pullback”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pbc-additive-scalar-base-change: the existing node is “Scalar-compatible canonical base change for additive first cohomology”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pbc-artin-schreier-frobenius-exact-rows: the existing node is “Compatible Artin--Schreier exact rows with coherent Frobenius models”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pbc-artin-schreier-prime-base-change-model: the existing node is “Prime-coefficient Artin--Schreier base-change model”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-pbc-cartesian-unit-cohomology-transport: the existing node is “Ordinary unit cohomology transport across a cartesian square”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sc-artin-schreier-base-change-model: the existing node is “Artin--Schreier model of characteristic-p degree-one pullback”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-coherent-frobenius-comparison: the existing node is “Frobenius compatibility of the canonical additive/coherent cohomology comparisons”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-completed-affine-pullback-objects: the existing node is “Completed affine coherent pullback objects”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-flat-base-change-affine-dictionary: the existing node is “Normalized affine cohomology section identifications independent of the resolution lift”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-flat-base-change-global-sections-qcqs: the existing node is “Flat base change of global sections over an affine base (Stacks 02KH, degree 0)”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-flat-base-change-resolution-affine-sections: the existing node is “Affine-section dictionary for the resolution flat base-change map”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-flat-base-change-resolution-iso: the existing node is “Invertibility of the resolution-defined qcqs flat base-change map”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-formal-comparison-completed-affine-data: the existing node is “FormalComparisonCompletedAffineData”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-formal-comparison-flat-transport-square: the existing node is “Flat transport squares for the formal comparison”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-formal-flat-quotient-mate-data: the existing node is “Ordinary flat quotient comparisons and adjunction mates”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-formal-functions-finite-quotient-comparison: the existing node is “Finite quotient and fibre cohomology comparison”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-formal-functions-local-dictionary: the existing node is “Geometric dictionary for stalk and infinitesimal quotient cohomology”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-formal-functions-local-stalk-comparison: the existing node is “Canonical uncompleted local stalk comparison”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-formal-functions-stalk: the existing node is “Theorem on formal functions at a point of the base”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-formal-systems-push-pull: the existing node is “A system on the base agrees with the completion of a proper pushforward up to a power of the exceptional ideal”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-fpqc-descend-affine: the existing node is “Being affine descends along fpqc coverings (Stacks 02L5)”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-local-derived-stalk-transport: the existing node is “Local total-cohomology transport for an arbitrary sheaf comparison”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-ordinary-flat-exchange-prescribed-adjunction: the existing node is “Ordinary flat exchange for a prescribed vertical adjunction”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-proper-flat-geometric-components-locally-constant: the existing node is “Geometric component count is locally constant in a proper smooth family”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-stein-factorization-affine: the existing node is “Stein factorization of a proper morphism to an affine scheme”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-stein-flat-base-change-global-sections: the existing node is “Flat base change for proper global sections”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-weil-pbc-stein-universally-closed-factor: the existing node is “Universal factorization before Stein connectedness”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs new-flat-base-change-affine-canonical-comparisons: the existing node is “Canonical affine cohomology section comparisons without flatness”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs new-flat-base-change-affine-source: the existing node is “Source affine dictionary”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs new-flat-base-change-affine-target: the existing node is “Target affine dictionary”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs new-flat-base-change-chart-coefficient-transport: the existing node is “Affine base-change chart coefficient h-map transport before cohomology”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs new-flat-base-change-chart-cohomology-transport: the existing node is “Affine scalar-extension chart transport of module cohomology”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs new-flat-base-change-chart-unit-iso: the existing node is “Invertibility of the explicitly adjoint restricted tensor unit on a fixed chart”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs new-flat-base-change-module-leray-comparison: the existing node is “Affine target Leray comparison for the module cohomology unit map”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs new-flat-base-change-target-leray-comparison: the existing node is “Target affine Leray comparison compatible with a natural source Ext comparison”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs new-module-cohomology-ext-pullback-comparison: the existing node is “Natural module/Ext comparisons intertwining the scalar-extension unit”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-a1-intersection-sections-flat-base-change: the existing node is “Flat affine base change for sections on intersections of quasi-compact opens”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-a1-qc-open-flat-section-diagram: the existing node is “Compatible flat base-change section diagrams on finite intersections of quasi-compact opens”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-abelian-euler-degree-square: the existing node is “Degree of the line-bundle homomorphism is the Euler-characteristic square”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-borel-homomorphism-rigidity: the existing node is “Homomorphisms of connected affine groups are determined by restriction to a Borel”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-cartesian-groupoid-pushforward-adjunction: the existing node is “Cartesian groupoid pushforward and the restricted ordinary adjunction”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-derivation-cohomology-scalar-square: the existing node is “Scalar extension square for cohomology of the universal derivation”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-equivariant-coherent-proper-pushforward: the existing node is “Proper pushforward on equivariant coherent Grothendieck groups”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-flag-cohomology-finite-exact: the existing node is “Finite rational cohomology and character filtrations for homogeneous bundles”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-hodge-first-differential-zero: the existing node is “The first Hodge differential vanishes in characteristic zero”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-homogeneous-coherent-acyclicity: the existing node is “A nontrivial homogeneous invertible module on an abelian variety is coherently acyclic”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-koszul-ideal-faithfully-flat-descent: the existing node is “Faithfully flat descent of locally Koszul-regular ideals”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-linearized-qcoherent-cohomology-coaction: the existing coaction statement assumes a field, while this node is over an arbitrary ring and only asserts the section coaction, not full cohomology or nonflat base-change isomorphisms.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-minimal-parabolic-line-cohomology: the existing node is “Rank-one homogeneous line cohomology and the minus-one acyclicity”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-nodal-trait-twister-extremal-degree: the existing node is “Extremal subcurve degree for a generically trivial line on a nodal trait”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-norm-pencil-differential-polynomial: the existing node is “Polynomial alternating differential of a parametrized pencil”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-normal-quasiprojective-equivariant-immersion: the existing node is “Equivariant projective immersions of normal quasi-projective schemes”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-pgl-invariant-image-restriction: the existing node is “Restriction to an invariant scheme-theoretic image”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-pgl-invariant-section-finiteness: the existing node is “Finiteness of invariant sections with structural coefficients”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-pgl-section-affine-action: the existing node is “Affine action induced on a projective section ring”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-pgl-semistable-affine-quotient-gluing: the existing node is “Gluing affine quotients of a stable semistable open”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-point-blowdown-factorization: the existing node is “Factorization through a regular surface point blowdown”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-projective-hilbert-polynomial-dimension: the existing node is “Dimension is the degree of a projective Hilbert polynomial”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-projective-picard-identity-representability: the existing node is “The rigidified Picard scheme of a smooth projective variety”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-projective-quotient-field-extension: the existing node is “Coherent projective quotients, Euler characteristics and regularity under field extension”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-qcqs-functions-local-comparison: the existing node is “Localization, stalks and the local coefficient criterion for qcqs regular functions”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-regular-point-blowup-functions: the existing node is “Regular functions under a regular point blowup”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-regular-quotient-coefficient-tor: the existing node is “Normalized Tor of a regular quotient with annihilated coefficients”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-relative-norm-pair-interpolation: the existing node is “Simultaneous special and generic norm-pair interpolation”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-rigidified-product-seesaw: the existing node is “See-saw extends a prescribed section isomorphism uniquely”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-scheme-etale-higher-image-comparison: the existing node is “Etale and Zariski quasi-coherent higher direct images agree”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-scheme-quasi-affine-fpqc-descent: the existing node is “Quasi-affine scheme morphisms descend along fpqc coverings”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-semiabelian-effective-square-generation: the existing node is “Squares of effective lines on semiabelian varieties are globally generated”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-separating-pair-open: the existing node is “Nonempty separating open for pairs of norm sections”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-smooth-projective-torus-invariant-affine-cover: the existing node is “Invariant affine cover for a smooth projective torus scheme”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-smooth-proper-coherent-trace-pairing: the existing node is “Smooth proper coherent trace pairings and their geometric naturality”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sfb-universal-norm-generation-open: the existing node is “Universal polynomial norm sections and their open generation locus”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sbc-normalization-affine-localization: the existing node is “Relative normalization under affine localization”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sbc-normalization-stalk-base-change: the existing node is “Relative normalization commutes with stalk base change”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-sbc-stalk-normalization-generic-comparison: the existing node is “Stalk normalization compared with normalization of its generic torsor”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-trf-base-modification-comparison-fibre-image: the existing node is “Finite image of a projection fibre under a proper comparison after modifying the base”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-trf-canonical-affine-envelope-descent-datum: the existing node is “Canonical affine envelope with its induced descent datum”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-trf-contracted-component-generic-spread: the existing node is “Generic numerical data of a proper component in an ambient nodal family”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-trf-geometrically-integral-curve-factorization: the existing node is “Factorization with a geometrically integral generic curve”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-trf-infinitesimal-vanishing-section-lifting: the existing node is “Vanishing on infinitesimal layers gives neighbourhood lifts of fibre sections”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-trf-no-isolated-contracted-fibre-component: the existing node is “A curve modification cannot contract an isolated whole fibre component”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: the existing node is “Zariski and small etale quasi-coherent modules agree functorially”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

lem-sfb-relative-linearized-line-sections-coaction vs lem-trf-zariski-etale-functor-comparison-square: the existing node is “Canonical Zariski-etale module functor square and flat-base-change section maps”; its statement does not construct the normalized Laurent coaction on sections of an invertible line for a torus action over an arbitrary ring.

## Validation

Server `srvcheck.py ... review_split` exited 0 and reported PASS. It recognized the declared generic tool uses; the inherited unit has no realization recorded. The full delivery dry run, including the two new nodes, passed preflight and exited 0: `OK (not pushed)` at 3d75aa25c57. The final report records the citation excerpt repair below.

The first delivery dry run rejected the short excerpt “In particular $r$ is an immersion.” because it did not meet the citation gate's 40-character minimum. I replaced it with the entire quotient-comparison statement, including its hypotheses, and retained the proof unchanged.
