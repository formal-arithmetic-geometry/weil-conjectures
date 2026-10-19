## Worker report

The node is already stated by the landed project module
`Sheaf.Paper.CondensedConstantConstructibility` (branch `newtargets-dag`).  I therefore
add no module and record the existing declarations.  The module's declarations are:
`AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`,
`AlgebraicGeometry.ProEtale.IsFiniteConstantStratified`,
`AlgebraicGeometry.ProEtale.IsConstantModelConstructible`,
`AlgebraicGeometry.ProEtale.ConstantModelConstructible`,
`AlgebraicGeometry.ProEtale.constantModelBoundedConstructible`,
`AlgebraicGeometry.ProEtale.ConstantModelBoundedConstructible`, and
`AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor`.

The Lean rendering of the statement is clause by clause as follows.  The commutative
condensed ring is the module parameter `Λ` with `[MonObj Λ] [IsCommMonObj Λ]`; its
pullback coefficient is `condensedRingObj Λ X` and the module category is
`Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.  A finite
constant local model is `HasFiniteConstantLocalModel`, using a pro-etale cover and a
finitely presented module over the scalar ring on the point.  The qcqs finite
constructible-stratification condition is `IsFiniteConstantStratified`; the affine-local
condition for arbitrary schemes is the `else` branch of
`IsConstantModelConstructible`.  Thus `ConstantModelConstructible X` is the full
subcategory `ObjectProperty.FullSubcategory (IsConstantModelConstructible Λ X)`, i.e.
`Cons(X,Λ)`.  The bounded constructible object property is
`constantModelBoundedConstructible Λ X`, namely
`DerivedCategory.TStructure.t.bounded ⊓ (fun K => ∀ n : ℤ,
IsConstantModelConstructible Λ X ((DerivedCategory.homologyFunctor _ n).obj K))`; its
full subcategory is `ConstantModelBoundedConstructible X`, i.e. `Dbc(X,Λ)`.  The
finite-Tor subcategory is `ConstantModelConstructibleFiniteTor X`, the full
subcategory of the intersection of that bounded property with
`DerivedCategory.finiteTorAmplitude _`; the latter is the existential choice of an
integer interval and tests derived tensor against every module object in degree zero,
so it is exactly `Dctf(X,Λ)`.  The canonical t-structure boundedness predicate is
definitionally the finite-range cohomology condition, and the generic
`DerivedCategory.finiteTorAmplitude` is the relative derived tensor predicate used by
the node.  The source module documents the isomorphism invariance, shifts, triangle
extension, retract, thick-subcategory, and intersection well-definedness clauses.

Dependencies used by these existing declarations are the recorded project interfaces:
`Sheaf.AlgebraicGeometry.FiniteConstantLocalModel` (finite constant local models),
`Sheaf.AlgebraicGeometry.ProEtaleModuleObjects` (the internal module category),
`Mathlib.Algebra.Homology.DerivedCategory.Basic` (`DerivedCategory` and homology),
and `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`
(`torAmplitudeIn` and `finiteTorAmplitude`).  The module also imports the pro-etale
upper-star module interface and the existing bounded/constructible framework.

Edge cases checked against the definitions and source: the zero module and zero complex
(use the rank-zero finite presentation), empty schemes (the affine-local condition is
vacuous where appropriate), a one-stratum identity decomposition on qcqs schemes,
non-qcqs schemes (the explicit affine-open branch), intervals with negative endpoints
and `a > b` (the homology predicate has the corresponding empty range), and arbitrary
module test objects including the zero object.

Searches for a duplicate or missing implementation:

* `msearch.py ... leanfinder "finite constant local model constructible bounded derived category finite Tor amplitude over pulled-back condensed ring"`: only generic condensed-module and derived-category hits; no competing package.
* `msearch.py ... loogle "AlgebraicGeometry.ProEtale.IsConstantModelConstructible, constantModelBoundedConstructible, ConstantModelConstructibleFiniteTor"`: no hits because the names are project declarations, not Mathlib declarations.
* `rg -n 'ConstantModelConstructible|constantModelBoundedConstructible|constructibleFiniteTor|finiteTorAmplitude' lean/Sheaf /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: found the exact seven declarations in `lean/Sheaf/Paper/CondensedConstantConstructibility.lean`; the upstream source has only generic finite-Tor notions and no duplicate constant-model package.
* `grep -rl 'det-def-sfb-constructible-tor-amplitude' dag/nodes`: no existing node-specific Lean binding; the parent constructibility node's landed declarations define the same notions and are recorded here.

No statement correction or `STATEMENT-DISPUTED` flag is needed.

## Second reading by NQ

I reread the node and the existing module signature.  The finite scalar local model,
constructible stratification and affine-local convention, bounded cohomology condition,
universal relative derived-tensor test, and finite-Tor intersection all match the node.
The only presentational difference is that boundedness is rendered by the canonical
`t-structure` predicate rather than an explicit finite set of nonzero cohomology
indices; these are the same definition in the recorded derived-category interface.
No mismatch was found and no source file was changed.

## Maintainer review fix

The four definitions are the landed declarations of
`Sheaf.Paper.CondensedConstantConstructibility` and are correct for clauses 1-4 (checked by
`Iff.rfl` that `DerivedCategory.finiteTorAmplitude` on this module category uses exactly the
recorded relative derived tensor `CondensedRing.derivedTensor Λ X`). The node's statement also
asserts well-definedness: the four conditions are isomorphism invariant, the shift rule
`[a,b] ↦ [a-1,b-1]`, the extension rule for distinguished triangles, closure under direct
summands, and thickness of finite Tor amplitude. That landed module states none of these; the
worker report's sentence that "the source module documents" them is not accurate. Downstream
nodes cite these rules from this node, so an `existing: true` record of the definitions alone
does not state everything the node says.

The fix adds `lean/Sheaf/Paper/ConstantModelTorAmplitude.lean`, which imports the landed
module (no definition is duplicated) and states
`AlgebraicGeometry.ProEtale.constantModelConstructibleFiniteTor_wellDefined` with `sorry`.
Its docstring gives the node's seven proof steps. The item's record now points to it, and the
note names the reused definitions. The module compiles cleanly with
`tools/nt_compile.py`; `#print axioms` shows only `sorryAx` beyond the standard axioms.
