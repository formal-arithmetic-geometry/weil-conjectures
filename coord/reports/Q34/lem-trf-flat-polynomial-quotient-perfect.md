## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flat-polynomial-quotient-perfect.json`: item, split in five proof steps; no Mathlib match.
- `citations.json`: one verbatim statement quote for every node cited by every step.

There are no new nodes and no new Mathlib leaves. The initial uncommitted candidate was dropped after the deeper duplicate search found `lem-pc-polynomial-tor-bound`; all proof inputs now already exist.

## Attachments

None. Searches for the item id/docstring tag and polynomial-quotient/perfectness concepts in the read-only project Lean source found no declaration giving this theorem. No compiler was used.

## WANTED

None for this split. The polynomial-bound theorem is used through its already existing DAG statement, rather than re-proving its Weibel source.

## Statement corrected

STATEMENT-DISPUTED (dependency typing): the imported node cited `def-weil-flat-morphism`, a definition for morphisms of schemes, for a homomorphism of rings, and cited `def-weil-finite-tor-amplitude`, whose objects are bounded constructible coefficient-sheaf complexes on schemes, for the arbitrary ordinary R-module A. Those references cannot be instantiated: an arbitrary commutative Noetherian ring R is not the finite coefficient ring A_{E,n} and no scheme or constructible complex was supplied. I replaced the first citation with `def-weil-pbc-flat-ring-map` and wrote the ordinary-module Tor dimension predicate explicitly. No mathematical hypothesis or conclusion changed. In particular the statement retains arbitrary Noetherian bases, all polynomial presentations, and the bounded finite-projective resolution; it does not assume lci or smoothness.

## Not duplicates

No new node is delivered. I searched the whole DAG for Tags 067J, 068Y, 068X, Noetherian pseudo-coherence, finite-projective resolutions, and polynomial Tor bounds; the search through `lem-pc-localized-polynomial-finite-projective-dimension` and `lem-pc-localized-polynomial-tor-bound` led to the existing more general `lem-pc-polynomial-tor-bound`. The whole-blueprint search via `tools/blueprint_refs.py search` for polynomial/perfect and polynomial/Tor concepts found no blueprint node stating the item; `blueprint.same_as` remains empty. The existing polynomial Tor bound allows no localization, Noetherianity or finite-generation assumptions, so there is no reason to create a special-case node. It is used as a generic tool below the unit's semistable-alteration polynomial-chart input. The complete historical ancestor/via chain is retained.

## Review by Q34

I read the item and its parent `lem-trf-algebraic-shriek-relative-perfect`, the chapter record and the full unit `sk-i-curve-zero` (the item lies deep in the nearby-cycle/semistable branch of `lem-trf-local-term-locality`). I read Stacks `more-algebra.tex` Tags 067J (flat finite presentation gives a perfect map), 068Y (polynomial presentation criterion), 068X (base-to-polynomial Tor interval), and 0658, together with `dualizing.tex` Tag 0BZW, whose proof applies perfectness to the chosen presentation. I also opened the full statements used in the split: the generic finite-type Noetherian theorem; the flat-ring definition; bounded-above flat K-flatness; the ordinary-module K-flat tensor model; Tor computed on a flat resolution; the general polynomial Tor bound; finite-free resolutions over Noetherian rings; finite-free flatness; the bounded finite-Tor perfectness criterion; and the definitions of perfect ring complexes and derived-category cohomology. The source of each step is given by tag and label. This is an agent assembly of existing algebra tools, so `proof_origin.by` is `agent`.

Step 1 takes only Noetherianity from `lem-weil-pbc-finite-type-algebra-noetherian`, with polynomial variables as the finite algebra generators. The cyclic-module argument is written explicitly: surjectivity makes every a a P-multiple of 1. Step 2 applies bounded-above flat K-flatness to A[0] (zero terms are flat), and the K-flat tensor-model theorem gives the actual derived tensor, rather than merely citing a flatness definition for derived exactness. The flat-resolution Tor comparison applied to the identity augmentation of A in degree zero gives first-variable Tor vanishing; no symmetry convention is assumed. This checks both the additional conclusion over R and the exact premise of Step 3.

Step 3 applies `lem-pc-polynomial-tor-bound` with d=0, base R, number of variables n and polynomial module A. Its statement explicitly permits arbitrary modules, zero rings and n=0; it concludes the required Tor vanishing for every P-module, not only residue fields. Step 4 first uses the Noetherian finite-free resolution theorem, with P Noetherian and A cyclic from Step 1. Finite-free flatness and bounded-above K-flatness justify the cochain tensor model, while the flat-resolution comparison identifies its degree -j cohomology with exactly the first-variable Tor groups in Step 3. Reindexing sends F_j to F^{-j}; therefore the bound j>n is exactly vanishing below -n, and positive cohomology is zero because all positive terms vanish. Every needed non-elementary comparison is cited in the step.

Step 5 applies `lem-weil-bounded-finite-tor-perfect` with the ordered interval [-n,0], to the single-degree finite P-module complex A[0]. Its statement gives a projective model in precisely this interval. I checked the augmentation rather than inferring an augmented resolution from an unspecified derived isomorphism: since E^1=0, E^0 surjects onto H^0(E)≅A, and the negative cohomology vanishing is exactness of the augmented complex. This gives the full resolution clause of the item. All citation quotes in `citations.json` are literal text of the node statements, not proof excerpts. The off-unit generic tools are individually declared in `split_report.tool_uses`; they do not replace the unit's geometric route.

For B–E: no new nodes remain, so there is no hidden restatement, duplicate or unsourced new statement. Every proof step introduces its objects and uses only conclusions present in the cited statements; no source's omitted proof is treated as a citation. No flatness of P→A, smoothness of A, lci hypothesis, locality, or finite dimension of R is used. I checked A=0, the zero base ring, n=0, A=R with a redundant polynomial variable (resolution [P --x--> P]), polynomial A, and a singular base R=k[ε]/(ε²). The singular-base example explains why one must transfer flat dimension from R to P rather than assume P regular. With n=0 the polynomial bound yields amplitude [0,0] and the criterion gives a finite projective quotient, as it should for a flat cyclic quotient over a Noetherian ring. All five proof steps are shorter than 2000 characters; none hides an inline auxiliary lemma. The two initial dry-run failures were search-log provenance checks on an uncommitted candidate now dropped; no successful dry run or push was claimed for them.

## Unfinished

None in the split. The existing prerequisites retain their own stage status; no Lean was written or compiled, and no repository or launcher files were edited.
