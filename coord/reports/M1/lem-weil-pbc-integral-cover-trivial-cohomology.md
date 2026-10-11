## Worker report

The module `lean/Sheaf/Paper/IntegralCoverTrivialCohomology.lean` states
`AlgebraicGeometry.exists_integral_cover_trivial_cohomology`.  It introduces an affine
scheme `X` (`[IsAffine X]`), then existentially a scheme `X'` and a morphism
`π : X' ⟶ X`.  The conjuncts `IsIntegralHom π` and `Surjective π` render the integral
and surjective requirements.  For every scheme `Z'` and closed immersion
`i : Z' ⟶ X'` (`[IsClosedImmersion i]`), it quantifies a type `M : Type (u + 1)` with
`[AddCommGroup M] [Finite M]`, and an integer `q` with `1 ≤ q`.  The final clause is
`IsZero` of the object obtained by applying
`AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1} Z' q` to the degree-zero
complex given by `DerivedCategory.singleFunctor _ 0` applied to
`(constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)`.
Thus it states that the positive-degree étale cohomology group of every finite constant
abelian sheaf is zero.

The statement dependencies used are:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` from Mathlib's
  `Mathlib.AlgebraicGeometry.Scheme` (the affine hypothesis is Mathlib's `[IsAffine X]`).
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsIntegralHom` from
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`/`Integral`.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective` from
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf` from
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `def-weil-pbc-etale-cohomology`: `AlgebraicGeometry.Etale.cohomology` from
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.

Edge cases checked: the bound `1 ≤ q` includes the first positive degree and excludes
only degree zero; the quantified finite abelian group is arbitrary (including the trivial
group), and no nonemptiness assumption is added; `Z'` may be any scheme in the same
universe, including the empty scheme; and no extra finiteness, separatedness, or
Noetherian hypotheses are imposed on `X` or `X'`.

Searches for an existing statement or definition: `msearch.py ... leanfinder` with
"integral surjective cover affine scheme etale cohomology finite constant sheaf
vanishing" returned only unrelated affine-transition and integral-morphism results;
`msearch.py ... loogle` for `AlgebraicGeometry.IsIntegralHom,
AlgebraicGeometry.Surjective, AlgebraicGeometry.Etale.cohomology` returned no result;
`msearch.py ... grep` for "integral cover trivial cohomology" in `WeilConjectures`
returned no result.  Direct `rg` searches in `WeilConjectures` and `lean/Sheaf` likewise
found no declaration of this theorem.  The Mathlib/source declarations listed above
were read and used directly.

## Earlier second reading (a previous round; superseded)

I reread the node and the module independently.  The affine hypothesis is represented by
`[IsAffine X]`; the existential morphism has exactly the integral and surjective clauses;
the universal quantifiers range over every closed immersion, every finite abelian group,
and every integer `q ≥ 1`; and the conclusion is `IsZero` of the stated constant-sheaf
étale cohomology object.  The cohomology functor is applied to the degree-zero single
complex, so its object is the group named by the node.  No clause or hypothesis from the
node was added or omitted.

## Second reading by M1

The node was checked item by item against Stacks Project Lemma 09ZD(1),
etale-cohomology.tex line 14467 and its first proof paragraph:

- `X` is `(X : Scheme.{u})` with `[IsAffine X]`; this is exactly the affine
  scheme hypothesis.
- The existential objects are `X' : Scheme.{u}` and `π : X' ⟶ X`, with exactly
  `IsIntegralHom π ∧ Surjective π`.
- Every closed subscheme is rendered by `Z' : Scheme.{u}`, `i : Z' ⟶ X'`, and
  `[IsClosedImmersion i]`, matching the node's closed immersion notion.
- Every finite abelian group is `M : Type (u + 1)` with
  `[AddCommGroup M] [Finite M]`; this is the coefficient universe required by
  `AddCommGrpCat.{u+1}` and adds no hypothesis.
- Every integer `q` has `1 ≤ q`, exactly the source's `q ≥ 1` condition.
- The conclusion is `IsZero` of `Etale.cohomology AddCommGrpCat.{u+1} Z' q`
  applied to the degree-zero single complex of the constant sheaf, exactly the
  source's assertion `H^q(Z'_et, underline M) = 0`.

Edge cases checked: `q = 1` is included and `q = 0` excluded; the trivial finite
abelian group is allowed; `Z'` may be empty; and no nonemptiness, Noetherian,
separated, finite-type, characteristic, or extra universe assumptions occur.

I searched Mathlib, the slopmaster2 source, this project's `lean/Sheaf`, and DAG
names with LeanFinder/Loogle/grep. No existing theorem or duplicate definition was
found. The recorded dependency declarations (`Scheme`, `IsIntegralHom`, `Surjective`,
`IsClosedImmersion`, `constantSheaf`, and `Etale.cohomology`) were opened and agree
with the node. No mismatch was found and no source or Lean change was needed. The
module compiled with `scompile.py`; only the required theorem proof is `sorry`.
