## Worker report

The module states the local injectivity criterion from Stacks Tag 00ME. It binds commutative local rings R and S, a local homomorphism φ preserving maximal ideals, a Noetherian S, an S-finite N (with an R-module structure), a flat R-module M, and an R-linear map u. The hypothesis `hu` is the injectivity of the induced residue map rendered elementwise: every n whose image lies in the maximal-ideal submodule of M already lies in the maximal-ideal submodule of N. The conclusion is injectivity of u and flatness of the quotient by `LinearMap.range u`; proof is `sorry`.

Dependencies used: `IsNoetherianRing` (Mathlib.RingTheory.Noetherian.Defs), `Module.Flat` (Mathlib.RingTheory.Flat.Basic), and `Module.Finite` (Mathlib.RingTheory.Finiteness.Defs). Local-ring maximal ideals use `IsLocalRing.maximalIdeal` from Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs.

Edge cases checked: zero modules and zero maximal ideals are admitted; no finiteness or characteristic restrictions beyond the node hypotheses are added. Searches: msearch leanfinder/loogle/grep for the full local injectivity criterion found no existing declaration; ripgrep of WeilConjectures and Sheaf found no duplicate.

## Earlier second reading (a previous round; superseded)

Read the node and module. The binders correspond to the two local rings, local homomorphism, Noetherian target, finite source module, flat target module, and linear map. The elementwise `hu` exactly expresses injectivity after quotienting by maximal-ideal multiples, and the conclusion has both injectivity and flat quotient clauses. No additional theorem is proved.

## Second reading by J1

The node introduces commutative local rings `R` and `S`, a local homomorphism
`φ`, Noetherian `S`, a flat `R`-module `M`, an `S`-finite module `N` regarded
as an `R`-module through `φ`, and an `R`-linear map `u : N → M`. The Lean
binders `[CommRing R] [CommRing S]`, `[IsLocalRing R] [IsLocalRing S]`,
`φ : R →+* S`, `hφ`, `[IsNoetherianRing S]`, `[Module R M] [Module.Flat R M]`,
`[Module S N] [Module.Finite S N]`, and `u` render these objects and hypotheses.
The `u` type uses `letI : Module R N := Module.compHom N φ`, so the R-action on
`N` is exactly the one induced by `φ`, as required by the node.

The hypothesis `hu` is the elementwise form of injectivity of the residue map:
membership in the span of maximal-ideal multiples in `M` implies membership in
the corresponding span in `N`. The conclusion is exactly
`Function.Injective u ∧ Module.Flat R (M ⧸ LinearMap.range u)`, preserving both
clauses and their order. All proofs remain `sorry`.

The zero modules, zero maximal ideals, empty generating sets, and arbitrary
characteristic are admitted; no Noetherian, finiteness, or universe condition
beyond the node is added. The source was checked at Stacks Tag 00ME, including
its local-ring and quotient-flatness hypotheses. Searches with msearch
LeanFinder/Loogle and ripgrep over Mathlib, WeilConjectures, and Sheaf found no
existing declaration.

Mismatch repaired: the worker had an unconstrained `[Module R N]`, which did not
express that `N` is regarded through `φ`. I removed that binder and used
`Module.compHom N φ` in the `u`, `hu`, and conclusion types. The file compiles
cleanly with `scompile.py`.
