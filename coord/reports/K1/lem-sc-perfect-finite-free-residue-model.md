## Worker report

The module `lean/Sheaf/AlgebraicGeometry/PerfectFiniteFreeResidueModel.lean` states
`AlgebraicGeometry.Scheme.exists_finiteFreeResidueModel`; its only proof is `sorry`.
No definition, dependency module, or statement correction is needed.

Hypothesis and clause correspondence:

- The scheme is `(X : Scheme.{u})`, with the recorded Mathlib scheme structure.
- The object is `(E : schemeDerivedCategory X)` and perfectness is
  `(hE : IsPerfect X E)`, exactly the recorded scheme perfectness predicate.
- The point is `(x : X)`. There is no inhabitedness or nonemptiness hypothesis on X.
- The global and per-open `HasDerivedCategory.{w}` binders are the shared category
  construction parameters required by `IsPerfect` and derived restriction. The further
  binder supplies the same construction for `Spec (X.residueField x)`.
- `Li_x^* E` is `((derivedPullback (X.fromSpecResidueField x)).obj E)`.
  `DerivedCategory.homologyFunctor ... i` is its degree-i cohomology sheaf.
  On `Spec κ(x)`, a one-point scheme, that sheaf's `residueFiber` at
  `IsLocalRing.closedPoint (X.residueField x)` is its cohomology vector space. The scalar
  field appearing in `Module.Finite` and `Module.finrank` is the residue field of this
  unique point. It is canonically isomorphic to κ(x): the stalk of the structure sheaf
  on the one-point spectrum of a field is that field and its maximal ideal is zero.
  Thus the displayed dimensions are exactly the dimensions specified by the node,
  with no choice of representative or unconstrained fibre object. Tensoring with the
  residue field here is exact, so this also agrees with cohomology after that scalar
  identification.
- `∃ d : ℤ → ℕ` and `∀ i, d i = Module.finrank ...` introduce the node's prescribed
  dimensions as natural numbers. The preceding `∀ i, Module.Finite ...` explicitly
  asserts their finiteness; `finrank` alone would not ensure this.
- `(∃ a b : ℤ, ∀ i, i < a ∨ b < i → d i = 0)` states that all but finitely many d_i
  are zero. A finite subset of ℤ lies in such an interval and conversely.
- `∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U` gives an affine open neighbourhood.
- `K : CochainComplex (SheafOfModules ... over U) ℤ` is a complex of O_U-modules
  on exactly the localized site used by the recorded definition of `IsPerfect`.
- The existential integer bounds with `IsZero (K.X i)` say K is bounded.
- The degreewise isomorphisms with `SheafOfModules.free ... (ULift.{u} (Fin (d i)))`
  express terms O_U^{⊕d_i}. A free sheaf on that finite index set is this finite sum;
  ULift preserves its cardinality and makes the index live in the sheaf universe.
- The final `Nonempty (...mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K)` says
  precisely that K represents E restricted to U, using the same derived restriction
  as `IsPerfect`. Termwise isomorphisms allow transporting the differential to the
  literal displayed free sheaves; the node's usual phrase 'term is O_U^{⊕d_i}' does
  not require equality of chosen carriers.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`;
  its docstring, full signature, and strictly-perfect/restriction definition were read.
- Added the already-landed `def-pc-derived-pullback` to stmt_deps:
  `Sheaf.AlgebraicGeometry.DerivedPullback`, `AlgebraicGeometry.derivedPullback`.
  Read its existence statement and chosen-functor definition, including the universal
  property and computation on K-flat representatives.
- Added the already-landed `def-weil-pbc-module-residue-fiber` to stmt_deps:
  `Sheaf.AlgebraicGeometry.Modules.ResidueFiber`, `Scheme.Modules.residueFiber`.
  Read its full definition as extension of the module stalk along the residue map.
- Added the Mathlib leaf `def-weil-residue-field` to stmt_deps:
  `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField`,
  `Scheme.fromSpecResidueField`, and the canonical spectrum residue-field description.
- Mathlib's `DerivedCategory.homologyFunctor`, `Module.Finite`, `Module.finrank`, and
  `SheafOfModules.free` supply cohomology, dimensions, and finite free sheaves.

Edge cases checked: the empty scheme has no x and is not excluded by a new hypothesis;
E=0 permits d=0 and the zero complex; Fin 0 gives the zero free sheaf; all integer
positions and both positive and negative shifts are included; bounds may enclose an
empty support; arbitrary residue characteristic is allowed; no Noetherian assumption
is added. The point ensures U is nonempty, as required by the rank argument in the
natural-language proof. Universes u and w and every variable are explicitly bound.

Source checked: https://stacks.math.columbia.edu/tag/0BCD, Lemma lift-perfect-from-residue-field.
The local literature file is absent on this machine, so the source tag was opened.
It gives the ring version with finite dimensions, finite support and prescribed free
terms after principal localization; the node's proof explains its affine-local scheme
form. The theorem docstring includes all three DAG proof steps and their tools.

Searches for an existing statement:

- `msearch.py ... leansearch "perfect complex finite free local model ranks residue
  field cohomology"`: unavailable, Internal Server Error (no verdict assigned).
- `msearch.py ... leanfinder "perfect complex local finite free model prescribed
  residue field cohomology dimensions"`: eight hits, on cotangent spaces, free loci
  and formal smoothness; no matching theorem.
- `msearch.py ... loogle "DerivedCategory, SheafOfModules.free"`: zero hits.
- `msearch.py ... grep "lift-perfect-from-residue-field|IsPerfect|finiteFreeResidueModel"
  AlgebraicGeometry`: zero hits.
- `rg` in Mathlib and WeilConjectures for `Li_x|lift-perfect-from-residue-field|finite
  free`: ring/module results and source FreeComplex/DirectImage encodings, no theorem
  asserting this local minimal model of an arbitrary perfect derived object.
- `rg` for the item id and `finiteFreeResidueModel` in WeilConjectures: zero hits.
- `rg` for residue/perfect/free/derived expressions in project `lean/Sheaf`: found
  PerfectComplex, DerivedPullback, ResidueFiber, and MinimalFreeModel. The last is
  the local-ring pseudo-coherent theorem (Tag 0BCC), not the affine-neighbourhood
  scheme statement (Tag 0BCD). Reused the definitions rather than copying them.

Server compile: clean, no errors and no warnings, 3.7 seconds. The theorem remains
unproved as required in stage 2. No statement dispute or dependency fault found.

## Second reading by K1

I independently read the node, its source (Stacks Tag 0BCD), the dependency
signatures, and the delivered file. The node introduces a scheme `X`, a perfect
object `E : schemeDerivedCategory X`, a point `x : X`, and the integers
`d_i = dim_{κ(x)} H^i(Li_x^* E)`. Its conclusion has four clauses: every fibre
cohomology module is finite; `d i` is its finrank; `d` vanishes outside an integer
interval; and there is an affine neighbourhood `U` with a bounded complex `K`
whose terms are finite free of rank `d i` and which represents the restriction of
`E`. The Lean theorem renders these as the explicit `Module.Finite` clause,
`Module.finrank` equality, the two integer-bound clauses, and the final
`Nonempty` isomorphism. `derivedPullback (X.fromSpecResidueField x)` and
`Scheme.Modules.residueFiber` are the recorded dependency notions, and the
`HasDerivedCategory` binders are the construction parameters they require.
Every hypothesis and every conclusion clause is present exactly once; no
Noetherian, separatedness, characteristic, or nonemptiness assumption was added.

The source's ring statement (Tag 0BCD) gives finite residue cohomology ranks,
finite support, and a principal localisation carrying the prescribed free
complex. The scheme statement is its affine-local sheaf form. The empty scheme
is harmless because it has no point; the zero object gives `d = 0` and a zero
complex; `Fin 0` gives the zero free term; negative and positive integer degrees
and `n = 0` are included; and no characteristic restriction occurs. The
residue-field spectrum has its unique closed point, so the residue-fibre module
used by Lean has the same scalar field and dimension as `κ(x)`.

Searches were repeated with `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf`,
plus LeanFinder/Loogle queries for a perfect finite-free residue model. They
found no existing theorem or definition; the only nearby project result is the
distinct local pseudo-coherent model (Tag 0BCC). The existing dependency modules
`DerivedPullback` and `ResidueFiber` were opened and match their node statements.
No mismatch was found and no source, node, or Lean file was changed.

## Reviewer fix (R-pfr1348)

The fibre dimensions were written a second way (finrank over the residue field of the closed
point of `Spec κ(x)` of `Scheme.Modules.residueFiber` of the cohomology sheaf), beside H1's
landed `Scheme.derivedFiberBetti` / `derivedFiberCohomology` (def-sc-derived-fiber-betti,
bc1cca7cb), which is the one notion of `dim_{κ(x)} H^i(Li_x^* E)` (H4). Restated through it:
the auxiliary `∃ d` with `d i = finrank …` is replaced by `derivedFiberBetti X E i x` itself,
`Module.Finite` is on `derivedFiberCohomology X E i x` over `X.residueField x`, and the
single-point `HasDerivedCategory` binder on `Spec κ(x)` becomes the `∀ x : X` family that
`derivedFiberBetti` takes (as in lem-sc-perfect-jump-loci). Imports `DerivedFiberBetti` in place
of `DerivedPullback`/`ResidueFiber`. Everything else (IsPerfect, affine U ∋ x, bounded K with
terms `SheafOfModules.free (ULift (Fin d_i))`, derived restriction via `overFunctor`
`mapDerivedCategory`) unchanged. Compiled clean in lean/.sandbox/L.
