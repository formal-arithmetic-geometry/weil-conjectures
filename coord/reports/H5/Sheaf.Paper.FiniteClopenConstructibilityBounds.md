## What changed

Proved `WeilConjectures.PurityFiniteSetting.finite_clopen_constructibility_bounds`
without changing its signature or the coefficient instance. Only its module and its
DAG proof record change.

The proof imports the existing stratification models, finite clopen module/derived
calculus, ordinary pro-etale operations, native tensor pullback comparison, and proved
constructibility and Tor-amplitude helpers. All added imports are private proof imports;
`import all` reuses existing proved private helpers rather than redeclaring them.
The local coefficient comparison identifies actual ordinary pullback with the
sectionwise restriction used by the gluing theorem. The induced derived equivalence
therefore has exactly the functors in the statement. Private categorical helpers restrict
that equivalence to the two full subcategories and keep the required forgetful comparison.

Tor bounds use native tensor representatives, canonical pullback compatibility, and
explicit zero insertion through the module equivalence. Finite unions detect bounded
support. A lower bound and upper bound for the finite sets of component Tor endpoints,
with interval `[min a b, b]`, also handle the empty index type.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.PurityFiniteSetting.finite_clopen_constructibility_bounds`.
All nine conjuncts are proved. The coefficient finiteness instance is preserved.
There are zero `sorry` declarations left in the item and zero holes added by this delivery.
There are no split-off statements or data chosen from an unproved mere existence theorem.
Imported statements can still have their own existing proof obligations; this delivery
uses those declarations as the stage-3 brief permits.

## No longer needed

`lem-pur-product-tensor-test-bounds` / `Sheaf.Paper.ProductTensorTestBounds` is not needed
by this proof. The zero-insertion family is defined explicitly, its chosen coordinate is
identified by the gluing counit, and native tensor tests prove the prescribed bounds
directly. The exploratory proof import was removed and this dependency was removed from
the node's proof plan. This does not withdraw its declarations or assert that other parents
no longer need it.

All other original proof dependencies remain needed, directly or through the existing
clopen calculus and stratification modules. No modules are withdrawn. Public statement
imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned sectionwise gluing functors and the statement's actual ordinary pullbacks
have different coefficient sheaves. Their comparison must include the ring inverse-image
adjunction and canonical constant-ring coefficient isomorphism, rather than silently
identifying the functors. The proof supplies this comparison explicitly.

The empty-index case needs no extrema of a nonempty family: boundedness of the two finite
endpoint ranges and `[min a b, b]` work uniformly. The DAG proof record now describes the
actual Lean route, including the canonical tensor pullback theorem used for that route.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
