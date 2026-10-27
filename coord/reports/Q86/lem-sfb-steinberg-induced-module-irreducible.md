# Stage-1 report: lem-sfb-steinberg-induced-module-irreducible

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-steinberg-induced-module-irreducible.json`: item, statement unchanged, split into six steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-induced-weyl-dimension-formula.json`: statement, unsplit; no Mathlib match. General dominant-weight induced-module dimension formula, in arbitrary characteristic.
- `dag/nodes/sec-six-functors-basics/lem-sfb-restricted-rho-simple-dimension.json`: statement, unsplit; no Mathlib match. Dimension of an already simple module at the first restricted rho weight.
- `dag/nodes/sec-six-functors-basics/lem-sfb-restricted-highest-weight-dimension-product.json`: statement, unsplit; no Mathlib match. General numerical consequence of Steinberg's restricted-weight tensor product theorem.

`citations.json` contains a verbatim statement quote for every step/node citation. `searches.jsonl` retains the previous attempt's queries and the additional searches from this session. The sandbox initially contained no node or report, only the earlier search log and dispatcher markers; there was no completed split to discard or to dry-run first.

## Attachments

None. Searched `lean/WeilConjectures/` for the item tag, Steinberg/steinberg, highest-weight and Weyl-dimension terminology. The Steinberg hits concern Lang--Steinberg for semilinear Frobenius and Artin--Schreier cohomology, not this item. Searched `lean/Sheaf/` too; no declaration there states any of the three new rational algebraic-group dimension results.

## WANTED

WANTED: J. C. Jantzen, *Representations of Algebraic Groups*, second edition (2003), Part II, 3.16--3.18, for `lem-sfb-steinberg-induced-module-irreducible`, `lem-sfb-restricted-rho-simple-dimension`, and `lem-sfb-restricted-highest-weight-dimension-product`.

WANTED: the same book, Part II, 5.10--5.12 (Weyl character/dimension formula for induced modules and Kempf vanishing), for `lem-sfb-induced-weyl-dimension-formula`.

The book is not present locally. No PDF was downloaded and no claim to have read Jantzen is made. The item is expressly marked `proof_origin.by = agent`. Read the local Milne PDF, printed pp.467--471, for the primitive/highest-weight and induced-module conventions. Read these public primary sources as corroboration:

- G. Williamson, *Algebraic representations and constructible sheaves*, [arXiv:1610.06261v1](https://arxiv.org/pdf/1610.06261), sections 1.1--1.4, pp.4--7: his Borel has negative roots, equation (1.4) gives induced and Weyl characters, Theorem 1.3 and equation (1.7) give Steinberg tensor products. The dimension-product node extracts only the integer consequence. Frobenius twist leaves the underlying vector-space dimension unchanged. His Borel convention must be opposed to the item's convention.
- T. Heidersdorf and H. Wenzl, *Generalized negligible morphisms and their tensor ideals*, [published article](https://doi.org/10.1007/s00029-021-00749-9), sections 5.1--5.2 and 7.5.1: the first paragraph of 7.5.1 gives the simple Steinberg module's ordinary dimension. Only its case r=1 is used as a new prerequisite, not its identification with an induced or Weyl module. The article distinguishes ordinary integer dimension from categorical dimension modulo p; our nodes use the former.

## Problems found and changes

No statement dispute: the given item has the correct sign and the simply-connected hypothesis needed at small primes. Its initial proof was empty. The source is unavailable locally, so the assembly is agent-written, not labelled as a transcription of the book. There is no use of SGA.

The item and every new node keep the inherited chapter and unit. Read the chapter record, unit record, and the latest blueprint through `literature/blueprint/latest` (currently `main-20261023-1620`), especially `sk-thm-sf-ctf-stability-direct-images.proof.md` paragraph (3). The inherited provenance describes an alteration/moduli/Haboush supporting branch; the current blueprint paragraph (3) only states the direct-image/compactification route, not a Steinberg theorem. `tools/blueprint_refs.py ancestor` returns null because this inherited created-item chain has no surviving imported ancestor. Retained null and the existing via chain; each new node prepends this item and adds a precise numerical purpose to the inherited place. No ancestor or blueprint equivalence was invented, and no chapter/unit statement was changed.

## Not duplicates

lem-sfb-induced-weyl-dimension-formula vs lem-sfb-rho-section-modules: the latter constructs and proves nonzero finite-dimensional rho section spaces; it gives no dimension formula for arbitrary dominant characters.

lem-sfb-induced-weyl-dimension-formula vs lem-sfb-induced-module-primitive-line: the latter determines the U-fixed line of a nonzero induced module, not the dimension of the module.

lem-sfb-restricted-rho-simple-dimension vs lem-sfb-steinberg-induced-module-irreducible: the new node assumes a module already simple and gives only its first restricted-weight dimension; the item proves simplicity of an explicitly constructed induced module for every r. A dimension theorem about an already simple module does not alone identify that induced module or establish its simplicity.

lem-sfb-restricted-highest-weight-dimension-product vs lem-sfb-simple-module-dual-highest-weight: the existing node gives highest-weight lines and uniqueness and the dual highest weight, not a characteristic-p dimension multiplication law.

lem-sfb-restricted-highest-weight-dimension-product vs lem-sfb-steinberg-induced-module-irreducible: the new node concerns arbitrary restricted/dominant weights and three already simple modules, with no assertion about induced modules. The item's argument must still construct its simple submodules, identify their highest weights, establish the initial dimension, induct on r, and compare with induced-module dimensions.

Searched the whole DAG by Steinberg, Weyl dimension, highest weight, restricted weight and tensor-product-theorem terminology, then read the statement fields of the relevant hits. Searched the whole imported blueprint with `tools/blueprint_refs.py search` for Steinberg, Weyl dimension, highest weight, dimension formula, p-restricted and Weyl. Only the Lang--Steinberg vector-space node matched Steinberg; it states a different theorem. No new node shares a Stacks tag: these are algebraic-group representation results, and no Stacks tag was assigned to an unrelated fact.

## Mathlib searches

Reused the queries actually recorded by the earlier attempt after reading their logged hits. The new statements were already the subjects of those questions: first-rho dimension, induced Weyl dimension, and restricted-weight dimension multiplication. Each new node records semantic searches, Loogle and source grep, including two phrasings. Additional searches and source reads confirmed the exclusions. Every entry's tool and query is copied from the actual search log, including the grep subdirectory when applicable.

Read `Mathlib/LinearAlgebra/RootSystem/Irreducible.lean:125,162`: the simplicity result is for the Weyl group's root representation. Read `Mathlib/RepresentationTheory/FinGroupCharZero.lean:90`: the endomorphism criterion assumes a finite abstract group of invertible order. Read `Mathlib/RepresentationTheory/Induced.lean:61`: `Representation.IndV` is abstract-group coinvariant induction, not regular-function rational induction. Read `Mathlib/RepresentationTheory/Basic.lean:624`: `Representation.tprod` only defines a tensor representation, giving no highest-weight simplicity theorem. Read `Mathlib/Algebra/Lie/Rank.lean:65` and `Mathlib/Algebra/Lie/Weights/Linear.lean:133`: these concern a Lie-module rank and positivity of a nonzero generalized weight space, not any of our dimension formulas. Thus none is an exact match or a one-line specialization. No leaf is claimed.

## Unfinished work

The three new prerequisites are intentionally statement-only nodes for subsequent workers; no proof sketches were put inside their statements. The item's six-step argument is complete relative to their stated conclusions. No Lean was written or compiler/build tool run. Required delivery checks and their result are recorded below after execution.

## Review by Q86

I read delivery-errors B through E in full and checked the node statements and proof against those failure modes. The item retains all original hypotheses: F algebraically closed of positive characteristic, S semisimple and simply connected, the specified Borel convention, and r at least one. I checked the local Milne text at 22.18--22.22 and the public sources named above, while clearly marking the unavailable Jantzen places WANTED. The three new statements introduce their own field, group, coactions, submodules, Borel data and weight meanings; they assert integer dimensions, not equality of scalars in F. Each is unsplit with empty proof and proof-dependency lists. Their statements contain no proposed proof. The original statement and its statement dependencies are unchanged.

Step 1 uses the actual statement of `lem-sfb-reductive-borel-pair-structure`, which supplies the reduced root datum, simple-root coefficients and reflection formula. The short argument explains why every positive root other than the chosen simple root stays positive under its reflection, and derives the pairing 1 from the half-sum. This verifies dominance and p-restrictedness, including p=2, without silently assuming those properties or using a divided scalar in F.

Step 2 uses `lem-sfb-rho-section-modules` exactly for the concrete nonzero finite-dimensional rational function space, and `lem-sfb-induced-module-primitive-line` exactly for its fixed line and weight. Both statements were opened, and both apply in positive characteristic. The latter gives w_0 sending positives to negatives. Summing gives w_0 rho = -rho; taking its weight at the negative character in E_B produces the positive highest weight required in the dimension inputs. No finite-group or Lie-algebra invariant calculation is substituted.

Step 3 uses the new Weyl dimension formula with the dominant character from step 1. Its function equation and left action match E_k literally. Each fraction cancels in the rational numbers, not modulo p. This supplies the ambient module's dimension without asserting it simple.

Step 4 uses the existing simple-module-highest-weight node only for a simple module's one-dimensional U-fixed space. Minimal positive dimension of a submodule constructs L_k and proves simplicity by finite-dimensional linear algebra. The inclusion and tensor-injectivity argument show its fixed line equals E_k's line. This step does not take a socle theorem or an existence theorem from that citation when its statement gives neither.

Step 5 uses the first-rho simple-dimension node for the base and the restricted dimension-product node for the induction. The three modules in the latter are already simple by step 4. Their weights satisfy eta_(k+1) = eta_1 + p eta_k, eta_1 has all simple-coroot pairings p-1, and eta_k is dominant. The induction explicitly gives p^N times p^(kN), hence the desired integer dimension. No self-duality, simplicity of E_1, or theorem from this item's descendants is used circularly. I checked the dependency closures of the existing cited highest-weight and induced-line nodes; none reaches this item.

Step 6 is the elementary basis-extension argument: a subspace of the same finite dimension is the whole space. Together with the already constructed simple submodule, it gives exactly every clause of the item. Thus no new node restates a simplicity clause, and no non-elementary argument is hidden in the final step. No step is longer than 2000 characters.

I tested rank zero (empty roots, all products 1), p=2, r=1, and S=SL_2 (N=1, induced dimension m+1, required equality p^r). For the general product rule I checked lambda=0 or mu=0, where the dimension becomes unchanged, and the SL_2 p-adic digit identity. For the Weyl formula I checked lambda=0 and a rank-one dominant n, giving 1 and n+1. For a product of two rank-one groups the first-rho dimension becomes p^2, consistent with multiplication of the root counts. These tests explain why the new statements retain the simply-connected and restricted-weight hypotheses. The unavailable source and the inherited null blueprint ancestor are recorded openly above; neither was silently repaired by asserting an unread reference or changing the route.
