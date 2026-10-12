## What changed

Replaced the sole `sorry` in
`Sheaf.RingTheory.SmoothNormalDomainApproximation`,
`RingHom.Smooth.exists_noetherian_normal_model_colimit`, with a complete Lean proof.
The statement is unchanged. The proof lifts the base ring to the maximum universe,
uses Mathlib smooth Noetherian descent, constructs a directed covering family of
normal finite-type integer subalgebras, forms the tensor ring colimit, and supplies
Noetherian bases with smooth stage maps and normal prime localizations.

Added two proved helper modules, each with its node:
- `Sheaf.RingTheory.NormalFiniteTypeSubalgebraExtension`: normalize a finite-type
  subalgebra in its own fraction field, embed the normalization in the ambient
  normal domain, and transfer finite type and integral closure to its image.
- `Sheaf.RingTheory.DirectedSubalgebraTensorColimit`: construct the tensor diagram
  and prove its categorical universal property directly using the already proved
  source subalgebra colimit and the algebra tensor-product universal property.

Added proof-only imports of these helpers, Mathlib smooth Noetherian descent and
ring universe lifts. Existing public imports and all existing signatures remain
unchanged. The tensor helper publicly imports tensor-product Basic for its statement
and privately imports Maps and the proved source colimit construction for its proof.
Updated the original node's proof, proof dependencies and proof origin. Recorded the
already proved source union-colimit construction in a new node without a new module.
The unit's route is preserved.

## Proved and sorry left

Proved, with no `sorry` in their bodies:
- `RingHom.Smooth.exists_noetherian_normal_model_colimit`
  (`lem-weil-pbc-smooth-normal-domain-approximation`).
- `Subalgebra.exists_fg_integrallyClosed_extension`
  (`lem-weil-pbc-normal-finite-type-subalgebra-extension`).
- `Subalgebra.exists_tensorProduct_colimit_of_directed_cover`
  (`lem-weil-pbc-directed-subalgebra-tensor-colimit`).

There are no `sorry`s left in the assigned module or added anywhere in the delivery.
The proof still depends on the existing declaration
`RingTheory.finiteTypeZDomain_integralClosure_finite`
(`lem-weil-pbc-finite-type-z-domain-normalization-finite`), imported by the
normalization helper. This declaration now has a proof, but its import closure still
contains the open `isUniversallyJapanese_of_isNagataRing`
(`lem-weil-pbc-nagata-universally-japanese`). Thus the main theorem and the
normalization helper are reductions to existing obligations, not yet globally free
of `sorryAx`. Closed holes: `RingHom.Smooth.exists_noetherian_normal_model_colimit`
(one of one original holes). Added holes: none (zero split-off obligations). The tensor helper uses only
standard axioms. `#print axioms` also verifies the reused source union colimit has
only `propext`, `Classical.choice` and `Quot.sound`. All three delivered modules
compile locally without warnings under `lcompile.py`; their statement signatures
and the 100-character line limit were checked.

## No longer needed

The proof does not need the old planned dependency
`lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise` or its module
`Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise`. It is omitted entirely:
the tensor-colimit proof instead descends the two factor maps and uses tensor
extensionality. Consequently the old route through its underlying-module,
elementwise-module-colimit and tensor-commutes-with-module-colimits obligations is
unnecessary on this branch. Other callers may still need those nodes.

The current repository file already has the two planned proof-only imports.
Removed `Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise` in favor of the
proved direct tensor helper. Replaced the direct import
`Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite` by the normalization helper,
which still uses it privately. The existing seven public imports supply the
unchanged statement. All new proof imports are used.

The other old direct proof dependencies absent from the updated list are
`lem-weil-pbc-integral-closure-algebraic-extension-normal` and
`lem-weil-pbc-finite-type-z-domain-normalization-finite`: both moved to the
normalization helper and remain needed transitively; they are not pruned. Normalization finiteness, normality of integral
closure, finite-type Noetherianity, localization normality, finite-type smooth
models, base-change smoothness and categorical colimits remain needed, directly
or through the new proved helpers; none is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker began before the planned imports were inserted. At second reading
the repository version already imports the tensor-elementwise and normalization
modules privately. The report now describes the actual repository diff.

The planned elementwise tensor route is valid but unnecessary. The adopted source
library already proves the general directed-subalgebra ring colimit
`CommRingCat.isColimitSubalgebraCocone`; it had no DAG node, so this delivery records
it rather than restating or reproving it.

The local repository has no `literature/stacks-project/algebra.tex`. The existing
read-only source copy `/home/ubuntu/c1-stacks-review/algebra.tex` was read at
`lemma-normal-goes-up` (Tag 033C). Its third paragraph supports the normalization
and tensor-colimit route and explicitly omits some details. Those details are
written in the new docstrings and node proofs, with agent proof origin recorded.
LeanSearch returned Internal Server Error; its searches are recorded as unavailable,
not as evidence of absence. LeanFinder, Loogle and local source searches were used.

Edge cases checked mathematically before the helper statements: normalize C in its
own fraction field, not in an arbitrary ambient extension; no algebraicity of R over
C is required. R is a domain, so its subalgebras are nontrivial domains. B and S may
be zero rings, and the tensor-colimit construction and smooth base change still
apply. Nonemptiness of the covering family is explicit; no injectivity of tensor
transition maps is assumed. Universe lifts put bases, stages and indices in the
original statement's maximum universe.

## New nodes

`lem-weil-pbc-normal-finite-type-subalgebra-extension` records the first proved helper,
with the existing normalization-finiteness theorem as its sole open algebraic input.

`lem-weil-pbc-directed-subalgebra-tensor-colimit` records the second proved helper,
including its full ring-cocone factorization and uniqueness argument. It does not
assume smoothness, normality or finite type.

`lem-weil-pbc-directed-subalgebra-ring-colimit` records the already proved declaration
`CommRingCat.isColimitSubalgebraCocone` and its diagram/cocone definitions in
`WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`. No source module
is changed and no duplicate statement module is added. There are no change records:
no existing statement or definition changed.


## Second reading by A3

1. Compared every delivered module with the repository: only the assigned module
   previously exists. Its theorem signature and existing docstring are byte for
   byte unchanged; only private imports and the proof body differ. The declaration
   parser independently reports no statement changes. No change record is needed.
2. Compiled all three modules in import order with `lcompile.py`: no errors or
   warnings. Scanned for forbidden declarations and holes: none. In a scratch
   module, `#print axioms` gave only the three permitted axioms for the tensor
   helper and reused source colimit. The main theorem and normalization helper
   additionally use `sorryAx` through the existing normalization-finiteness
   dependency; its proof reaches the open Nagata theorem. No new obligation or
   hollow definition was added. The scratch module was removed before delivery.
3. No statement was split off with `sorry`. Read both new proved helpers and their
   nodes. Normalization is in C's own fraction field; embedding it in R uses
   integrality and R's normality, with no ambient algebraicity assumption.
   Characteristic-p domains, C=R, singleton covering families, and B=0 are valid
   edge cases. The tensor statement explicitly requires nonempty directed cover
   and does not assume injective tensor maps. Independent LeanFinder, Loogle and
   local-source searches found constituent lemmas, but no duplicate helper.
4. Read the main proof from its conclusion down to the helper inputs. It uses
   Mathlib smooth descent and normal localization and the already proved source
   union colimit. The source also has tensor-left preservation of filtered
   colimits in CommAlgCat; applying it here would need a separate algebra-colimit
   construction and forgetful comparison, so it does not provide a shorter direct
   replacement of this ring universal-property proof. All added imports are
   proof-only except those needed by the new helper statements. Checked the old
   proof-dependency list against the new one and corrected the pruning report,
   distinguishing removed tensor obligations from normalization inputs moved
   into a helper. `sk-thm-p1.json`'s realized statement and four steps are preserved;
   this construction lies below those nodes and changes no unit route.
5. Read all four delivered nodes against their Lean declarations. Existing-node
   changes are only `proof`, `proof_deps`, and `proof_origin`; their steps and
   dependency unions match the proof. New nodes have source, complete proof steps,
   searches, provenance, blueprint ancestry, chapter/unit and Lean records. The
   source ring-colimit node attaches the existing proved declaration and adds no
   duplicate module. Verdict: passes all five checks.

Changed the report's inaccurate import/pruning description and stale description
of normalization finiteness as itself open; recorded the extra independent search
in the normal-subalgebra node. No Lean proof or signature needed repair.
