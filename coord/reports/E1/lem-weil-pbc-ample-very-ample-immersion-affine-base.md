## Worker report

The main module `Sheaf.AlgebraicGeometry.AmpleImmersionAffineBase` states
`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_immersion_affine_base`, with `sorry` as its
only proof. Its statement is the item's original statement; no correction is needed.
The six steps of the node's proof are included in the theorem docstring. The accompanying
module specializes the already implemented homogeneous-fraction twist to the specified
polynomial projective space (see Dependency modules below).

Hypotheses and conclusions, clause by clause:

- The commutative ring A is `(A : Type u) [CommRing A]`. The scheme is
  `(X : Scheme.{u})`, and its specified morphism is `(f : X ⟶ Spec (.of A))`.
- Locally of finite type is exactly `[LocallyOfFiniteType f]`; quasi-compactness or
  separatedness is not imposed separately, since the node derives it from ampleness.
- The invertible module is `(L : X.Modules) [L.IsInvertible]`, using the recorded
  `Scheme.Modules.IsInvertible`, not the site-level invertibility predicate.
- Absolute ampleness is `(hL : IsAmple X L)` from the recorded Ample module. This is
  quasi-compactness plus the pointwise affine nonvanishing-locus condition of Stacks 01PS.
- A positive integer d is `∃ (d : ℕ) (hd : 0 < d)`; a nonnegative integer n is `(n : ℕ)`.
  These are exactly the positive/nonnegative integer ranges in the statement.
- `Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) A` unfolds to
  `Proj (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) A)`:
  the polynomial ring in n+1 variables with total-degree grading. ULift preserves the
  index set while putting it in the arbitrary ring universe.
- The required map is `(i : X ⟶ Proj.projectiveSpaceOverAffine … A)`. Its immersion
  condition is `IsImmersion i`. Mathlib's `IsImmersion.isImmersion_iff_exists` identifies
  this with a closed immersion followed by an open immersion. It even supplies the
  actual open subscheme via `coborderRange`, matching the node's parenthetical clause.
- The base condition is `i ≫ Proj.projectiveSpaceOverAffineToSpec … A = f`.
  This existing structure map is `Proj.toSpecZero` followed by `Spec.map` of
  `MvPolynomial.homogeneousSubmoduleZeroEquiv`; on standard opens this restricts to
  the map induced by constants A into the degree-zero homogeneous localization.
- The last clause is
  `Nonempty (SheafOfModules.positiveTensorPower X.sheaf L d hd ≅
    (tensorPullback i).obj (Proj.polynomialProjectiveTwist A n 1))`.
  `positiveTensorPower` is the recorded dependency's d-fold sheaf tensor power,
  degree one L and successive degrees obtained by tensoring with L.
  `tensorPullback` is the required sheafified tensor/inverse-image pullback. The right
  factor is exactly the O(1) on this polynomial Proj, rather than an arbitrary line bundle.
  `Nonempty` of the isomorphism type states existence of an O_X-module isomorphism.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `AlgebraicGeometry.LocallyOfFiniteType`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, reached through Ample.
- Sheaf.AlgebraicGeometry.Ample: `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme/Basic:
  `AlgebraicGeometry.Proj` and `Proj.toSpecZero`, reached through ProjectiveSpace.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace:
  `Proj.projectiveSpaceOverAffine`, `Proj.projectiveSpaceOverAffineToSpec`.
- The twist dependency is supplied by the dependency module below; its data is the
  existing `AlgebraicGeometry.Proj.twist` from
  WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion and OpenImmersion:
  `IsClosedImmersion`, `IsOpenImmersion`; the main file uses the bundled `IsImmersion`
  from Mathlib.AlgebraicGeometry.Morphisms.Immersion and its factorization equivalence.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct:
  `SheafOfModules.positiveTensorPower`, reached through TensorPullback.
- Sheaf.AlgebraicGeometry.TensorPullback:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`.

Edge cases: X may be empty; no `Nonempty X` is added. In that case the source proof uses
n=0, d=1 and the empty immersion, with the unique module isomorphism. The zero ring A is
allowed, so its empty spectrum is covered as well. Dimension n=0 gives one homogeneous
coordinate; no dimension positivity is assumed. d=1 uses exactly L. d=0 is excluded only
by the required positivity. There is no field, characteristic, Noetherian, properness,
or reducedness assumption. All type and universe variables are explicitly bound.

Source checked: [Stacks 01VS](https://stacks.math.columbia.edu/tag/01VS), first proof
paragraph gives the existence assertion; [Stacks 01VT](https://stacks.math.columbia.edu/tag/01VT)
gives the corresponding affine-base criterion. The item uses the existence consequence
of 01VS, not its stronger eventual assertion. The local Stacks source was absent on this
machine, so these original source pages were opened instead.

Searches (all remote search requests recorded in searches.jsonl):

- LeanFinder: "ample invertible module tensor power immersion into projective space over
  an affine ring": Proj.fromOfGlobalSections, Proj.toSpecZero, basic-open maps, and Proj;
  none is the ample-module theorem.
- LeanSearch: "ample invertible sheaf has tensor power inducing immersion into projective
  space": service unavailable (Internal Server Error), recorded as unavailable.
- Loogle: `AlgebraicGeometry.IsImmersion, AlgebraicGeometry.Proj`: zero hits.
- msearch grep: `IsAmple|veryAmple|very_ample` under Mathlib/AlgebraicGeometry: zero hits.
- rg in WeilConjectures: `ample|Ample|veryAmple` finds Modules.Ample and
  ProjectiveSpace.OfAmple, which were read. The former's relative ampleness uses a
  closed-immersion variant of very ampleness; the latter's
  `exists_isImmersion_projectiveSpace_of_isAffineOpen` assumes a specified finite family
  of sections and separatedness, and does not state the tensor-power/twist isomorphism.
  Neither is the node's statement.
- rg in lean/Sheaf for ampleness, powers, Proj, and twists found Ample and
  AmpleFiniteAffineCover, not the item. Searches for both new declaration names in
  Mathlib, WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json returned no match.
- rg for the item id in WeilConjectures returned no match.
  `tools/lean_names_upstream.py show <item>` likewise found no recorded declaration.
- Searching for projective-space structure maps found the exact existing
  `Proj.projectiveSpaceOverAffineToSpec`; searching for twist implementations found the
  usable general `Proj.twist` and the incompatible recorded relative `ProjectiveSpace.twist`.

Server validation: the two modules compiled together in dependency order, exit code 0,
with no errors or warnings. The first combined attempt exposed a repeated universe name
between the two independently valid modules; the dependency module's universe is now v,
while the main module's is u, and the combined compile is clean.

## Dependency modules

`def-pc-projective-space-twist`: the recorded main declaration is a Cech-complex theorem,
and its accompanying `ProjectiveSpace.twist` has type `(ℙ(σ; S)).Modules`. The node instead
specifies a module on `Proj(A[x₀,…,xₙ])`. The relative-twist source explicitly lists the
identification with the polynomial Proj and its twist as TODO, so this record cannot be
used directly with the item's objects. `Sheaf.AlgebraicGeometry.PolynomialProjectiveTwist`
defines `AlgebraicGeometry.Proj.polynomialProjectiveTwist` by specializing the existing
`Proj.twist` to `MvPolynomial.homogeneousSubmodule (ULift (Fin (n+1))) A`. The source's
homogeneous-fraction construction has local generators x_i^d and transition
(x_i/x_j)^d, exactly the dependency node. The definition has fully specified data and no
sorry. Only this dependency's lean record is changed, with the required explanatory note.
No new DAG notion is introduced, and no source definition is replaced by a private copy.

## Second reading by E1

I independently read the item node, its source place (Stacks Morphisms 01VS and 01VT),
and both delivery modules. The statement's objects and clauses match as follows:

- A ring `A` is `(A : Type u) [CommRing A]`; `X : Scheme.{u}` and the named base map
  are `(f : X ⟶ Spec (.of A))`. The same-universe presentation is forced by the scheme
  category and the specified `Spec A` target.
- Locally finite type is exactly `[LocallyOfFiniteType f]`, with no added noetherian,
  separated, field, characteristic, properness, or reducedness assumption.
- The module is `(L : X.Modules) [L.IsInvertible]`, and ampleness is the recorded
  `IsAmple X L`; no second invertibility or ampleness predicate is introduced.
- The quantified integers are `∃ (d : ℕ), 0 < d`, followed by `n : ℕ`, so they are
  respectively positive and nonnegative exactly as in the node.
- `Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) A` is the node's
  `Proj(A[x₀,…,xₙ])` with degree-one variables, and
  `projectiveSpaceOverAffineToSpec` is its structure map induced by constants.
- The map `i` has the node's source and target; `IsImmersion i` expresses the stated
  closed-then-open factorisation, and the next conjunct is precisely `q_n ∘ i = f`.
- The final conjunct is the node's module isomorphism: `positiveTensorPower ... d hd`
  is the d-fold tensor power (degree one is `L`), and `tensorPullback i` is the required
  pullback of modules. `polynomialProjectiveTwist A n 1` is the O(1) twist on this exact
  polynomial Proj, so `Nonempty` states existence of the required isomorphism.

Edge cases were checked against the source proof: empty `X` is permitted; the zero ring
is permitted; `n = 0` is permitted; `d = 1` is permitted while `d = 0` is excluded;
no characteristic or field hypothesis is present; and the finite index is lifted without
restricting the ring universe. The empty-index and zero-object cases are therefore not
silently excluded by the Lean binders.

Searches were rechecked in Mathlib's algebraic-geometry files, `WeilConjectures/`, and
`lean/Sheaf/` for ample/very-ample statements, projective twists, and this item or its
declaration names. LeanFinder/LeanSearch and Loogle searches found only generic Proj
constructions and immersion predicates, not this theorem. The source repository has the
general `Proj.twist`, but no declaration specializing it to `Proj(A[x₀,…,xₙ])`; the
recorded relative `ProjectiveSpace.twist` has the wrong object. Thus the dependency module
`PolynomialProjectiveTwist.lean` is required and was read as a dependency-module repair.

The only mismatch found was that the dependency node's prior Lean record pointed to the
relative-projective-space twist (and a Cech theorem), whose type is not a module on the
node's polynomial Proj. I changed only that dependency's `lean` record and supplied
`AlgebraicGeometry.Proj.polynomialProjectiveTwist`, specializing the existing homogeneous
fraction `Proj.twist`. The item's theorem statement itself required no change. Both modules
compile together cleanly with `scompile.py`; no unused-variable or warning output occurs.

## Reviewer FIX (R-avi1412, stage 2)

The statement was restated on the projective space form of the landed siblings and of the
recorded twist: `P_n` is `ℙ(ULift (Fin (n + 1)); Spec (.of A))` (as in `IsHProjective`,
`IsVeryAmple`, DimOneQuasiProjective; identified with `Proj(A[x₀,…,xₙ])` over `Spec A` by
Stacks 01O3, which the node's source cites), `q_n` is `ℙ(…; Spec A) ↘ Spec A`, and `𝒪(1)` is
the recorded declaration of def-pc-projective-space-twist, `ProjectiveSpace.twist … 1`.
The dependency module `Sheaf.AlgebraicGeometry.PolynomialProjectiveTwist` (a second
declaration of the twisting-module notion, H4) is left out and def-pc-projective-space-twist
is kept as on sheaf-dag (`--revert-nodes`). The section "Dependency modules" above is
therefore superseded. All other binders and clauses are unchanged; `IsAmple` was checked
with `#check` to be `AlgebraicGeometry.Scheme.Modules.IsAmple` (the cited
def-weil-pbc-ample-invertible-module), not J1's relative `AlgebraicGeometry.IsAmple`.
