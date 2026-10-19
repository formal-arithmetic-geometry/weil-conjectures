## Worker report

The module `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField` states
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_geometric`.
Its proof is exactly `sorry`; no definition or other theorem is introduced.
Read the complete node, its seven proof steps, and the source blueprint file
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-sc-cd-ground-field.md`.
The source and the node agree. No statement correction, new node, or dependency module is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field K: `(K : Type u) [Field K]`.
- An algebraic closure Kbar of K: `(Kbar : Type u) [Field Kbar] [Algebra K Kbar]
  [IsAlgClosure K Kbar]`. This means algebraically closed and algebraic over K, not
  merely an unspecified algebraically closed extension. Read the class and docstring
  in Mathlib/FieldTheory/IsAlgClosed/Basic.lean:262-272.
- A scheme over K: `(X : Scheme.{u}) [X.Over (Spec (.of K))]`, whose structure map
  is `X ↘ Spec (.of K)`. Read Mathlib/AlgebraicGeometry/Over.lean:33-36.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of K))]` together with
  `[QuasiCompact (X ↘ Spec (.of K))]`, exactly the two properties prescribed by
  the scheme-conventions node's finite-type pointer. Read both full class definitions
  and their docstrings in Morphisms/FiniteType.lean:39-46 and QuasiCompact.lean:37-46.
- Nonnegative bounds: `(c e : ℕ)`, as in def-sc-etale-torsion-cd.
- The field bound: `hK : (Spec (.of K)).HasTorsionEtaleCohomologicalDimensionLE c`.
- The geometric scheme: `pullback (X ↘ Spec (.of K))
  (Spec.map (CommRingCat.ofHom (algebraMap K Kbar)))`. This is precisely
  X ×_(Spec K) Spec Kbar, not X alone or its reduced scheme.
- The geometric bound: `hgeom` applies the same recorded predicate to that pullback
  with bound e.
- The conclusion: `X.HasTorsionEtaleCohomologicalDimensionLE (c + e)`.

Dependency declarations used:

- def-sc-etale-torsion-cd: `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`,
  `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`. Read its full
  docstring and definition in lean/Sheaf. It quantifies over every locally torsion
  abelian small-etale sheaf, with no uniform annihilator, and uses ordinary
  derived-section cohomology of the degree-zero complex, vanishing as Subsingleton.
- def-weil-pbc-scheme-conventions: its `lean.convention` record explicitly fixes no
  notion of its own and has no module/declaration. Follow its pointer to
  def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
  There is no unusable dependency and no reason to duplicate the conventions.
- Existing Mathlib `IsAlgClosure`, `Scheme.Over`, `Spec.map`, and `Limits.pullback`
  render the algebraic closure and base-change objects. No private copies.

Every stated proof dependency's module is imported without `public`; Mathlib leaves
are imported from the file recorded in mathlib_match. The only public imports provide
notions used in the signature. The theorem docstring carries all seven proof steps:
qcqs; strict localization as Spec Ksep over K; purely inseparable invariance;
higher-direct-image stalks and annihilators; Grothendieck/Leray; finite filtration;
filtered union of bounded-torsion subsheaves. No separatedness is assumed.

Edge cases checked before writing: c=0 and e=0 remain allowed; the empty scheme and
zero sheaf are allowed; nonseparated finite-type schemes are allowed; positive and
zero characteristic both are allowed; K already algebraically closed permits the
identity algebraic closure. There is no uniform torsion exponent in the signature.
One arbitrary universe u covers the fields and schemes, with algebraic closures
available in that same universe; no fixed small field or scheme is selected and no
quantification over smaller test objects is introduced. All variables and universes
are explicitly bound, with no file-local notation or instances.

Searches actually run:

- msearch leansearch: `etale cohomological dimension descent from algebraic closure`:
  UNAVAILABLE, Internal Server Error (not a no-match verdict).
- msearch leanfinder: `The etale cohomological dimension of a scheme over a field is
  bounded by the sum of the field and geometric cohomological dimensions`:
  eight hits concerning Etale/FormallyEtale composition, etale locus, and smooth
  relative dimension zero; none states the descent bound.
- msearch loogle: `"cohomological", "dimension"`: zero hits.
- msearch grep: `cohomologicalDimension|CohomologicalDimension|torsion.*dimension`:
  two polynomial finite-dimensional torsion-module hits, neither about etale cohomology.
- rg in WeilConjectures and lean/Sheaf for `etaleTorsion|EtaleTorsion|torsionCd|
  torsion.*[Cc]ohomological|cd_ground|cdGround`: found the dependency predicate,
  unrelated torsion modules, and upstream Sites/CohomologicalDimension.lean.
  Read the latter: it states the 2d+c finite-dimensional bound, not this descent
  statement, and uses Sheaf.H rather than the recorded derived-section predicate.
- grep for the exact item id in WeilConjectures: no hits.
- rg for the proposed declaration name and item id in dag/lean_names_upstream.json,
  WeilConjectures and lean/Sheaf: no hits. No name collision or exact existing theorem.

Validation: server scompile only, nice 19, two threads, 60 seconds per file.
The initial compile succeeded with a long-line warning; that line was wrapped.
A first line wrap caused a field-notation parse error; the predicate is now written
in prefix form. The final compile and deliver2 --no-push results are recorded by the tools.

## Second reading by NA

I reread the node statement, its blueprint source, dependency records, and the Lean module.
The correspondence is exact:

- The field is `K : Type u` with `[Field K]`, rendered by the first two binders.
- The algebraic closure is `Kbar : Type u` with `[Field Kbar]`, `[Algebra K Kbar]`, and
  `[IsAlgClosure K Kbar]`; this is Mathlib's algebraic-closure notion, including algebraicity.
- The scheme is `X : Scheme.{u}` with `[X.Over (Spec (.of K))]`, so its structure map is
  `X ↘ Spec (.of K)`.
- Finite type is rendered by exactly `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and
  `[QuasiCompact (X ↘ Spec (.of K))]`, with no separatedness or other extra hypothesis.
- The natural-number bounds are `(c e : ℕ)`.
- The arithmetic bound is
  `hK : (Spec (.of K)).HasTorsionEtaleCohomologicalDimensionLE c`.
- The geometric object is exactly
  `pullback (X ↘ Spec (.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap K Kbar)))`, and `hgeom` applies the same
  predicate to it with bound `e`.
- The conclusion is exactly
  `X.HasTorsionEtaleCohomologicalDimensionLE (c + e)`.

The quantifier order and universes agree with the node. The edge cases `c = 0`, `e = 0`,
empty schemes, zero sheaves, nonseparated finite-type schemes, both characteristics, and an
already algebraically closed `K` remain admitted. No uniform torsion exponent is added.
The pullback is the base change to `Spec Kbar`, rather than `X` itself or a reduced scheme.

I checked the dependency declaration for `def-sc-etale-torsion-cd` and used its landed
`HasTorsionEtaleCohomologicalDimensionLE`; the scheme-conventions dependency supplies the
finite-type convention and requires no private definition. Mathlib declarations
`IsAlgClosure`, `Scheme.Over`, `Spec.map`, and `Limits.pullback` are used directly. Searches
(LeanSearch, LeanFinder/Loogle, grep of Mathlib, `WeilConjectures`, and `lean/Sheaf`) found no
existing theorem matching this descent statement and no declaration-name collision. The
upstream cohomological-dimension file gives a different `2*d+c` theorem, so it is not reused.

No mismatch was found and no source, node, dependency, or Lean change was needed. The module
compiled with the prescribed server `scompile.py` command; only the expected `sorry` proof is
present.
