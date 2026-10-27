## What changed

Replaced the hole in `WeilConjectures.integralScalarPullbackRoosQuasiIso` by a
complete reduction to the finite-filtration cone-vanishing statement in the new
module `Sheaf.Paper.IntegralScalarPullbackConeProZero`.

The private `scalar_products` proof uses completed integral finite freeness and
the sectionwise ordinary scalar formulas to identify restricted extension with a
finite power functor. The existing scalar-restriction properties theorem makes
restriction conservative and product-preserving; it therefore detects preservation
of countable products. The private `product_roos_isIso` proves the diagonal Roos
map is an isomorphism using both signed cocone coordinates. The prescribed equations
uniquely identify the given kappa with this map.

The private `roos_pro_zero` applies the general ringed strict-tower homotopy-limit
theorem directly to the completed coefficient modules. Its evaluation isomorphism
transports the cone transitions. The explicit Roos derivation, the termwise limit
isomorphism and uniqueness of right derived functors then give quasi-isomorphism
of the concrete map. This also retains the published homotopy-cofiber map and
its signs: it is identified with the shifted mapping-cone map, not replaced by an
arbitrary map of triangles.

The existing item adds proof imports and private proved helpers. Locally, the
commutative-ring presentation may unfold to the underlying completed ring; the
ring limit itself remains irreducible. Its declaration signature, public imports
and definitions are unchanged. The parent DAG proof and dependencies now describe this route. Both delivered modules
compiled together through `lcompile.py --all`; profiling options were removed
after checking the proof. The delivery command performs the final timed compile
and axiom checks.

## Proved and sorry left

Original hole closed by decomposition:
`WeilConjectures.integralScalarPullbackRoosQuasiIso`
(`lem-pur-integral-scalar-pullback-roos-quasi-iso`).

One new hole:
`WeilConjectures.integralScalarPullbackConeProZero`
(`lem-pur-integral-scalar-pullback-cone-pro-zero`). Its conclusion is solely that
finite-level cone transitions eventually become nullhomotopic (and hence vanish
in the derived category). It contains no scalar/Roos comparison, no countable products and no inverse limit.

Thus one original hole is replaced by one strictly smaller hole: this is a
decomposition, not a net hole reduction or an unconditional proof of the item.
The product-commutation and derived-limit combination arguments have complete
Lean proofs.
No other sorry is introduced or retained in the delivered Lean files.

## No longer needed

No original public import was removed. The proof does not use
`lem-pur-compact-support-roos-cofinality` or the module
`Sheaf.CategoryTheory.CompactSupportRoosCofinality`: direct pro-zero invariance in
the completed-ring module category replaces arithmetic selection/block Roos
cofinality. No constant-coefficient-to-completed-coefficient forgetful bridge is
needed.

`lem-weil-l-adic-extension-integers-dvr` and
`lem-weil-pbc-completed-constant-sheaf-reduction` are now dependencies of the new
finite-filtration node rather than direct dependencies of the parent. They are
still needed; no global pruning of them is claimed. The finite-freeness,
well-defined operation models and exact-products dependencies remain needed.
No module is withdrawn and no source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned constant-ring
Roos cofinality theorem is unnecessarily specialized for the final step: the
published general ringed strict-tower theorem already applies directly to the
completed coefficient ring, with the existing exact-products theorem. The
remaining coefficient-filtration argument is explicitly isolated before any
products are formed. The e=1, zero-complex and empty-site cases satisfy that
argument without assuming completeness of the representative.

## New nodes

`lem-pur-integral-scalar-pullback-cone-pro-zero` states the finite-filtration
part of the original plan. Ramification identifies the source tower with the
arithmetic subsequence of the target tower; the generator condition identifies
alpha with its transition map. A sufficiently late transition factors through
the subsequence at the earlier level, giving the off-diagonal chain homotopy on
its mapping cone. Its node and docstring specify this entire proof and its
sources. This is the only unfinished step; it can be proved independently of all
Roos and product infrastructure. No change record is required because no
existing signature or definition is changed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
