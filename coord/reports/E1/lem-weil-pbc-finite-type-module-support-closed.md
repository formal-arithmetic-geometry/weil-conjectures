## Worker report

The module states `AlgebraicGeometry.Scheme.Modules.finite_type_module_support_closed`.
For a scheme `X` and a quasi-coherent finite-type module `F`, the first conjunct is
an existential closed subset whose underlying set is exactly the nonzero-stalk locus
`{x | ¬ Subsingleton (F.presheaf.stalk x)}`. This renders the node's support and
closedness conclusion. The second conjunct states the affine algebra calculation:
for every commutative ring `A`, finite `A`-module `M`, and prime `p`, membership in
`Module.support A M` is equivalent to `Module.annihilator A M ≤ p.asIdeal`, rendering
`V(Ann_A(M))`.

The hypotheses `[F.IsQuasicoherent]` and `[F.IsFiniteType]` use
`SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType` from
`Sheaf.AlgebraicGeometry.Coherent`. The stalk is `F.presheaf.stalk` from the recorded
stalk dependency. The affine criterion uses Mathlib `Module.support`,
`Module.annihilator`, and `PrimeSpectrum.asIdeal`; finite generation is
`[Module.Finite A M]`. The closed-subset encoding follows
`Scheme.Modules.HasSupportProperOver` in `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`.

Edge cases checked: the existential closed subset permits empty support (including
`F = 0`); the affine clause permits the zero module and arbitrary prime ideals;
`Module.Finite` is explicit so the annihilator criterion applies exactly to finite type.

Searches: the node's recorded LeanSearch, LeanFinder/Loogle, and Mathlib grep searches
found no scheme-level support theorem; only Mathlib's ring-level
`Module.support_eq_zeroLocus` and ideal-sheaf support declarations. `rg` over the
project found no existing theorem with this statement.

No `STATEMENT-DISPUTED` or node fault.

## Earlier second reading (a previous round; superseded)

The node and module were read together. The scheme, module, quasi-coherence and
finite-type hypotheses match the node. The first conjunct matches the support locus
and closedness claim. The second conjunct records the local affine annihilator
criterion with the finite module hypothesis and Mathlib's prime ideal representation.

## Second reading by E1

I read the node statement clause by clause against
`FiniteTypeModuleSupportClosed.lean`. The objects are `X : Scheme.{u}`,
`F : X.Modules`, the quasi-coherence and finite-type instances, a closed subset
`Z`, affine opens `U : X.affineOpens`, the section ring `Γ(X,U.1)`, section
module `Γ(F,U.1)`, and arbitrary ring-level `A`, finite module `M`, and prime
`p`. The first Lean conjunct renders the support set as the nonzero-stalk locus
and its closedness. The second now renders, for each affine open, the equality
of that locus on `U` with the image under `U.2.fromSpec` of the ring-module
support. The final conjunct renders the finite-module annihilator criterion
`p ∈ support ↔ annihilator ≤ p.asIdeal`.

The worker Lean had omitted the affine-local support clause (and therefore did
not connect `F` to `M` or `U`); I added the universal affine-open equality and
updated the node's recorded signature verbatim. The stalk-localization
isomorphism in the prose is represented by the affine support equality using
the standard `fromSpec` support chart; no hypotheses were added. Empty support
(including the zero module), empty affine opens, arbitrary primes, and the
universe `u` remain allowed. Searches recorded in the worker report were
rechecked with `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf`; only the
ring-level `Module.support_eq_zeroLocus` and ideal-sheaf support declarations
exist, so this theorem is not duplicated.

## Reviewer fix (R-fsc, stage 2)

Restated to the node clause by clause. Dropped the free-floating ring-level conjunct
(arbitrary `A`, `M`, `p`: not tied to `F` or `U`, a clause the node does not state in that form).
Added the stalk identification `F_x ≅ M_{p_x}` the node states, tied by
`s_x • e (m / s) = m_x` on the recorded stalk module `RingedSpace.moduleStalkFunctor`.
The annihilator criterion is now stated for `M = Γ(F, U)` and `p_x = U.2.primeIdealOf x`,
with `Supp F ∩ U = fromSpec '' V(Ann_A M)`. Closedness is `IsClosed` of the inline support
set (STATE SUPPORT OF A MODULE) instead of an existential `Closeds`.
