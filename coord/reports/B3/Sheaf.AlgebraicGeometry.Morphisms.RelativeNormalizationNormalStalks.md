## What changed

Proved AlgebraicGeometry.Scheme.relativeNormalization_normal_stalks with its signature and
public imports unchanged. Its proof chooses an affine chart, decomposes source sections into
normal domains, proves normality of the integral closure at primes, and identifies the stalk
with such a localization. Updated the item's proof, proof_deps and proof_origin accordingly.

Added two fully proved modules:

- Sheaf.AlgebraicGeometry.NormalSectionsFiniteProduct proves
  AlgebraicGeometry.Scheme.normal_sections_finite_product. It uses connected components,
  the source-library irreducibility theorem for connected locally Noetherian schemes with
  domain stalks, normality of sections of integral schemes, and the sheaf gluing axiom.
- Sheaf.RingTheory.IntegralClosureFiniteNormalProduct proves
  integralClosure_normal_localizations_of_finite_product. It constructs the coordinate
  integral-closure equivalence by a product of monic polynomials, then applies the existing
  proved Pi.isNormalRing_of_finite and transports prime localizations.

All three modules compile cleanly together. Explicit #print axioms for the item and both
new public theorems reports exactly propext, Classical.choice and Quot.sound, with no sorryAx.
The delivery dry run printed OK, leaving only the second reading for the next worker.
Neither new module contains a sorry; all private helpers are proved. The arguments include empty opens and empty products. No arbitrary data
is selected from an unproved theorem, and no existing signature or definition is changed.

## Proved and sorry left

Closed the item's only hole: AlgebraicGeometry.Scheme.relativeNormalization_normal_stalks
(node lem-sbc-relative-normalization-normal-stalks).

Also proved AlgebraicGeometry.Scheme.normal_sections_finite_product
(node lem-sbc-normal-sections-finite-product) and
integralClosure_normal_localizations_of_finite_product
(node lem-sbc-integral-closure-finite-normal-product).

No holes remain in any delivered module. Holes added: zero. Split-off unproved statements: zero.

## No longer needed

Removed the proof import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization from the
item. The integral-source theorem Scheme.Hom.isIntegrallyClosed_stalk_normalization and
its node lem-weil-pbc-normalization-normal-stalks are not used by this proof.

The old dependency lem-weil-pbc-noetherian-finite-components is not needed: compactness and
local connectedness directly make the connected-component quotient finite. Consequently
its irreducible-component enumeration is replaced by connected components. The relative
normalization construction and affine-chart theorem (lem-weil-pbc-relative-normalization,
Mathlib.AlgebraicGeometry.Normalization) remain necessary.

The new ring proof reuses Sheaf.RingTheory.FiniteProductNormal instead of proving finite
product normality again. The existing Sheaf.RingTheory.IntegralClosureFinitePi concerns
products of base rings; it is not needed for this single-base-ring A-algebra calculation.
The direct imports Mathlib.Algebra.Polynomial.AlgebraMap and
Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing were tested and removed as redundant
from the new modules. All retained imports supply statements or proof declarations.
These are dependencies removed from this item's route, not a claim that unrelated callers
no longer require those modules. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's integral-component route was valid but required
scheme disjoint-union normalization glue that the ring calculation avoids. The source
library already proves connected locally Noetherian domain-stalk schemes irreducible and
normal integral scheme sections integrally closed; these close the component argument.

The finite-product integral-closure module already in the library has different base rings
in each coordinate, whereas this item uses one A acting on all coordinates. The new theorem
addresses that distinction. FiniteProductNormal is an existing proved tool from another
unit; it is used only for the algebraic prime-localization step and changes no unit route.

## New nodes

lem-sbc-normal-sections-finite-product records the proved finite product description of
sections, with Stacks 0357/0358 and a connected-component implementation. Empty U gives n=0;
one component and several disjoint normal components give the expected section rings.

lem-sbc-integral-closure-finite-normal-product records the proved algebraic calculation,
with Stacks 035L/034L/0CYA. The base map may be noninjective, including a quotient map; the
argument uses only induced algebra structures and normality of the factors. Empty products
have no primes. Both nodes have matching Lean records and logged searches. No change record
is needed because existing interfaces and statements are unchanged.

## Second reading by B3

1. **Existing interface unchanged: pass.** Compared every delivered module with the
   repository. Only RelativeNormalizationNormalStalks already exists; its entire declaration
   signature, docstring and public imports are byte-for-byte unchanged. Its only edits replace
   the proof-only normalization import and the theorem's sorry. The other two modules are new;
   there are no adaptations, changed definitions or change records.
2. **Kernel-checked proof: pass.** Independently ran lcompile.py --all on all three modules:
   clean compilation, approximately 2.4, 3.4 and 2.6 seconds respectively. A scratch import
   compiled with explicit #print axioms for relativeNormalization_normal_stalks,
   normal_sections_finite_product and integralClosure_normal_localizations_of_finite_product:
   each uses exactly propext, Classical.choice and Quot.sound, without sorryAx. Inspected all
   private helpers and scanned for forbidden declarations/options; no sorry or forbidden
   mechanism occurs. There are no definitions with postponed data, and all choices used in
   proofs come from proved results. Removed the scratch audit file after compilation.
3. **New statements and edge cases: pass.** There are zero split-off unproved statements.
   Read the complete new proofs and their nodes against Stacks
   [035L](https://stacks.math.columbia.edu/tag/035L),
   [0357](https://stacks.math.columbia.edu/tag/0357),
   [0358](https://stacks.math.columbia.edu/tag/0358) and
   [034L](https://stacks.math.columbia.edu/tag/034L).
   The section theorem assumes exactly locally Noetherian X, normal domain stalks and compact
   U. Connected components of U are finite because their quotient is discrete and compact;
   each component is nonempty, connected and integral, so the nonempty-open section theorem
   is legitimately applied. An empty U gives Fin 0, and gluing still identifies its zero ring
   of sections with the empty product. A single component recovers a normal domain; finitely
   many disjoint components give its product. The ring theorem uses a common base A, with no
   injectivity assumption. Projection preserves integrality; the finite product of monic
   annihilators proves the converse. The zero base can only map to zero factors, so a prime
   cannot occur; an empty product likewise has no primes. For a quotient map such as
   Z -> F_p the coordinate closure is F_p, and the conclusion is correct. Read the existing
   IntegralClosureFinitePi theorem: its product of base rings differs from this common-base
   assertion, so it is not a duplicate. Additional msearch grep, Loogle and LeanFinder searches
   with coordinate-integrality/common-base wording found ingredients but no exact result.
   Searched repository Lean files with component, section, normality and product wording;
   the existing irreducibility, section-normality and finite-product-normality results are
   reused, rather than restated as new holes.
4. **Route and pruning: pass.** Read the proof from the stalk goal downwards. The affine chart
   is identified with an integral closure, then its prime localization with the stalk; the
   two supporting results supply exactly the finite normal section factors and their normal
   closure localizations. All proof-only imports are plain import, and retained public imports
   supply signature notions. Every removed old proof dependency is listed above:
   lem-weil-pbc-noetherian-finite-components and lem-weil-pbc-normalization-normal-stalks;
   lem-weil-pbc-relative-normalization remains used. Read sk-prop-input-spreading.json:
   its realized arrays contain no nodes bypassed by these local calculations. Its spreading,
   trait and depth-two assembly is unchanged. FiniteProductNormal is a proved algebraic tool,
   not a replacement for a unit step. No shorter exact library theorem was found.
5. **DAG agrees with Lean: pass after metadata repair.** The item's steps describe the actual
   affine-chart proof and use exactly its new section and closure nodes plus relative
   normalization. The section node describes stalk transport, connected-component finiteness,
   integral component sections and sheaf gluing; its steps explicitly name the proved upstream
   declarations. The closure node describes induced algebra structures, coordinate integrality,
   normal coordinate closures and Pi.isNormalRing_of_finite followed by localization transport.
   Their proof_deps are the union of the uses in their steps, and proof_origin records this
   route. Checked new-node chapter, unit, source, creation, blueprint ancestry, searches and
   Lean records. Replaced the two new nodes' whitespace-flattened lean.statement fields with
   the exact multiline theorem signatures from their files, as the brief requires.

Second-reading changes: repaired only the two new nodes' verbatim Lean signature metadata and
added this independent review. No Lean proof, interface, import or mathematical statement needed
repair. Holes closed remain one existing hole out of one; holes added zero; unproved statements
split off zero. The two supporting theorems are fully proved additions, not a decomposition.
