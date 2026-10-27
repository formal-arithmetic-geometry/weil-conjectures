## What changed

Proved `CategoryTheory.purAdicIntegralComparison_exists` in
`Sheaf.Paper.PurAdicIntegralComparison`, with its public signature unchanged.
All 42 supporting constructions, lemmas and instances are private and proved. No other Lean module
or definition is changed.

The coefficient comparison and cofinal restriction first prove that the set-sheaf
inverse image preserves the strided coefficient limit. Compatible bases identify
restricted ring and module towers. The dependent-sum presheaf on a slice, followed
by sheafification, converts these identifications to products with the sheafified
representable. Product with a fixed object preserves connected tower limits.
Finite-limit preservation therefore transfers coefficient-limit preservation to
module-limit preservation after each such product. The existing proved theorem
`Sheaf.map_jointly_locally_surjective` carries the covering family to a locally
inhabited family on the target. Products with this family detect isomorphisms by
local bijectivity. This constructs the underlying normalized comparison.

Projectionwise addition and scalar equations then show that the comparison is
linear for the specified graph-transported module structure, giving an actual
module-sheaf isomorphism and the required projection equations. The module inverse
is obtained from the componentwise invertible linear map, not from arbitrary
existence data.

Updated `lem-pur-adic-integral-comparison`'s proof, proof dependencies and origin to
record this implemented route. Proof imports include the already proved local
family theorem and Mathlib's product, limit and sheafification APIs.

## Proved and sorry left

Closed one hole: `CategoryTheory.purAdicIntegralComparison_exists`
(node `lem-pur-adic-integral-comparison`). Added zero holes; split off zero theorems.
There are no remaining `sorry` declarations in the delivered module. All private
helpers have complete proofs. The resumed profiled `lcompile.py` run passed in
42.2 seconds; the temporary profiling option has been removed. Delivery performs
the final clean compile and axiom checks.

## No longer needed

No existing public import was removed: `Sheaf.Paper.PurAdicLineSystemData` is still
required by the statement. The data module's three proved sheaf-composition helpers
are registered as local instances to avoid expensive general typeclass searches;
this has no effect on importers. The trial proof imports
`Mathlib.CategoryTheory.Limits.Types.Pullbacks` and
`Mathlib.CategoryTheory.Comma.Over.Pullback` were removed from the sandbox proof.
`Mathlib.CategoryTheory.Limits.Connected` was also removed after replacing its
universe-restricted lemma with the private tower proof.

The former direct proof dependency `lem-weil-pbc-left-exact-site-inverse-image-tensor`
(module `Sheaf.CategoryTheory.SiteInverseImageTensor`) is not used: the theorem
already supplies the adjunction and left exactness of L. Neither tensor structure
nor a construction of L is required. The slice inverse-image comparison of Tag
03CF and `Sheaf.Paper.PurInverseImageCompatibleFreeTower` are not imported; the
product argument works in the statement's independent universes directly.
These are claims about this proof's direct dependencies, not withdrawals of any
of those modules or declarations. No library module is withdrawn.

The dependencies on local module restriction, inverse limits, module sheaves,
the adic data and the local bijectivity criterion remain. Added the existing proved
`lem-weil-pbc-inverse-image-local-families` as a tool: it transfers the one common
cover, while providing none of the coefficient or module-limit comparison itself.
Its unit is `sk-thm-properbasechange`; no realization of the present unit is
bypassed (the unit's realized statement and steps are empty).

## Where the brief, the DAG or earlier work was wrong

The original slice-comparison plan was sufficient mathematical motivation but
unnecessary for this proof: the dependent-sum construction and product comparison
prove exactly the needed local limit assertion using the supplied geometric
adjunction. The current blueprint integral-twist paragraph uses representability;
the assigned node's abstract, compatible-local-basis statement is retained
unchanged and proved directly from its stronger explicit local data.

The proof includes arbitrary independent site universes. Its cover detection
argument also handles empty covering families and empty section sets through
covering sieves. Cofinal restriction is used through its supplied universal
property, with no extra positivity assumption on the stride. Addition and scalar
compatibility are checked on all projections and generalized sections. No
statement, target, or data definition has been weakened.

Preflight requested a scope record for the private instance and local instance
attribute commands. `coord/changes/pur-adic-integral-private-instances.md` records
the exact commands and the sole consumer, whose call and meaning are unchanged.
No consumer adaptation is needed. The first delivery attempt pushed nothing.

On resuming the existing sandbox packet, the current server exposed a universe
restriction in Mathlib's `prod_preservesConnectedLimits`: its shape universe is
tied to the target category's morphism universe. The private `prodTowerLimits`
helper now proves preservation directly from the tower cone using its level-zero
first projection and the original limit's second projection. This preserves the
independent universes of the unchanged public statement.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
