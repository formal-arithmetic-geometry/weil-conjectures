## Worker report

The module defines the statement that a bounded coherent object of the derived category of
modules on a Noetherian scheme is pseudo-coherent.  The Noetherian hypothesis is rendered by
`[IsNoetherian S]`, which combines local Noetherianity and quasi-compactness.  The derived
category is `schemeDerivedCategory S` with the shared `HasDerivedCategory` instance, and the
additional open restrictions provide the instances required by `IsPseudoCoherent`.

The boundedness clause is rendered by `hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
IsZero ((DerivedCategory.homologyFunctor (SheafOfModules (moduleRings S.toRingedSpace) i).obj E))`.
The coherence clause is rendered by `hcoherent : ∀ i : ℤ, RingedSpace.IsCoherent S.toRingedSpace
((DerivedCategory.homologyFunctor (SheafOfModules (moduleRings S.toRingedSpace) i).obj E)`.
The conclusion is `IsPseudoCoherent S E` from `def-pur-pseudo-coherent-complex`.  The proof is
`sorry`, as required for stage 2; its documented source proof is the finite descending induction
on standard lower truncation triangles, using coherent sheaf pseudo-coherence and closure under
distinguished triangles.

Dependencies used: `schemeDerivedCategory` from
`Sheaf.AlgebraicGeometry.DerivedCategory`, `AlgebraicGeometry.Scheme.IsPseudoCoherent` from
`Sheaf.AlgebraicGeometry.PseudoCoherentComplex`, and Mathlib's
`AlgebraicGeometry.IsNoetherian`, `CategoryTheory.DerivedCategory.homologyFunctor`, and
`AlgebraicGeometry.RingedSpace.IsCoherent`.

Edge cases checked: the integers `a ≤ b` may include an empty cohomological interval; the
outside-range condition then forces all cohomology to vanish.  The empty scheme is allowed by
`IsNoetherian`; zero cohomology sheaves satisfy coherence, and the conclusion is the vacuous
local pseudo-coherence condition.  The zero derived object is covered by any valid bounds.

Searches made: `msearch.py leanfinder "bounded coherent cohomology complex on a Noetherian scheme is pseudo-coherent"`
(no exact declaration); `msearch.py loogle "DerivedCategory, PseudoCoherent, triangle"` (no hits);
Mathlib grep `pseudo.?coherent|PseudoCoherent` (no hits); project `rg` for pseudo-coherent and
Noetherian bounded-coherent statements (only the dependency definitions and unrelated lemmas).
No existing declaration states this theorem, so a new module was written.

## Earlier second reading (a previous round; superseded)

The statement was read a second time against the node and source. Every binder and clause is present: Noetherian scheme, derived object, bounded cohomology, coherent cohomology, and pseudo-coherent conclusion. The signature compiled cleanly on the server.

## Second reading by F1

The node introduces a Noetherian scheme `S`, an object `E` of the derived category,
bounded coherent cohomology, and pseudo-coherence as the conclusion.  The source Tag
08E8 additionally requires `E` to lie in `D_QCoh(O_S)`.  The Lean renders `S` as
`Scheme.{u}` with `[IsNoetherian S]`, uses the shared `HasDerivedCategory` instances,
`E : schemeDerivedCategory S`, and renders this missing source hypothesis as
`hQCoh : schemeDerivedQCohProperty S E`.  Boundedness is the existence of integer
bounds with `IsZero` homology outside them; coherence is `RingedSpace.IsCoherent`
for every integer homology sheaf; the conclusion is `IsPseudoCoherent S E`.

The source check also covered the empty scheme, zero object, empty cohomological
interval, and all integer degrees.  No universe is independently introduced for the
index: homology uses the same `u` as the scheme.  Searches of Mathlib, the project,
and the source checkout found no existing theorem with this statement; the existing
pseudo-coherence and derived-category declarations are used directly.

Mismatch found: the worker omitted the source's `D_QCoh` hypothesis, and coherence
alone does not imply quasi-coherence for an arbitrary sheaf.  I corrected the node and
Lean by adding `hQCoh : schemeDerivedQCohProperty S E`, and recorded the correction
and citer impact in `statement_change`.  The proper-pushforward citer does not expose
this hypothesis in its statement (`holds: false`); the distinguished-triangle citer
remains unaffected (`holds: true`).

(Superseded in part by the reviewer fix below: the correction was reverted.)

## Reviewer fix (R-nbc1323, stage 2)

The delivered statement correction (adding D_QCoh, `hQCoh : schemeDerivedQCohProperty S E`) is
reverted (`--revert-statement`): its premise is false. A coherent module (Stacks 01BV,
`RingedSpace.IsCoherent`: finite type with finite-type kernels of every local map from a
finite free module) is locally of finite presentation (O^m -> O^n -> F -> 0), hence
quasi-coherent (Stacks 01BE / Mathlib `SheafOfModules.IsQuasicoherent`). So "coherent
cohomology" already places E in D_QCoh, the sheaf-dag statement is equivalent to Tag 08E8's
restricted to bounded objects, and the node's reviewed proof (truncation induction through
lem-sc-coherent-pseudo-coherent, which has no QCoh hypothesis) never uses D_QCoh. The citer
lem-pc-bounded-coherent-finite-tor-proper-pushforward-perfect therefore keeps holding.
The Lean drops `hQCoh`; the docstring now carries the node's proof in words.
