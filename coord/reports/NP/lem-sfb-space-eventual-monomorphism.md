## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceEventualMonomorphism` states
`AlgebraicGeometry.AlgebraicSpace.eventually_injective_of_limit`, with proof `sorry`.
There are no new definitions, additional theorems, or statement corrections.
The source was read in `literature/stacks-project/spaces-limits.tex`,
lemma-finite-type-eventually-closed, clause (4) and its proof (Tag 0828).

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The auxiliary scheme is `{S : Scheme.{u}}`; `B : AlgebraicSpace S` is the arbitrary
  algebraic-space base. All algebraic spaces use the recorded fppf full subcategory.
- `{I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]` is the small,
  nonempty directed set. No antisymmetry, countability or chosen initial stage is required.
  The index universe is the schemes' universe, following the project's limit convention.
- `D : Iᵒᵖ ⥤ Over B` is the inverse system over B. Its maps are already B-morphisms.
  `haff` asserts `MapIsAffine (D.map f).left` for every transition. This is exactly
  the existing affine-scheme-test definition, including the representing cartesian square.
- `hqs : ∀ i, IsAbsolutelyQuasiSeparated (D.obj i).left` is absolute
  quasi-separatedness, equivalent to quasi-compactness of the diagonal over Spec Z
  by the recorded definition's Stacks 0AHR affine-test criterion. It is not separation
  relative to S or B. There is no assumption that S or B is quasi-separated.
- `c : Cone D` and `hc : IsLimit c` express the assumed limit in algebraic spaces
  over B. In particular no assumption about preservation by the sheaf forgetful functor
  has been substituted for the node's categorical limit hypothesis.
- `A : Over B` supplies A and its structure map. `hAqc : IsQuasiCompact A.left.obj`
  is precisely existence of a representable surjective etale atlas from a quasi-compact
  scheme. No quasi-separatedness of A is required.
- `u : A ⟶ c.pt` is the given B-morphism. `hlft : MapIsLocally
  (@LocallyOfFiniteType) A.hom` is local finite type of A to B, tested on every
  compatible pair of representable etale scheme charts, using the scheme predicate
  recorded by `def-weil-finite-type-morphism`.
- `hu : ∀ T : Over S, Function.Injective (u.left.hom.hom.app (op T))`
  is exactly the node's sectionwise definition of monomorphism on every S-scheme T.
  In particular it does not replace monicity by injectivity just on field points.
- The conclusion `∃ i₀ : I, ∀ i : I, i₀ ≤ i → ∀ T : Over S,
  Function.Injective ((u.left ≫ (c.π.app (op i)).left).hom.hom.app (op T))`
  says that every canonical map A to Z_i is a monomorphism for every i at least i₀.
  All composites and projections are fixed by u and the cone; no arbitrary maps are chosen.
- The opening explanations of quasi-compact and quasi-separated morphisms and of finite
  presentation specify conventions, rather than extra assumptions on the objects. The
  existing definitions in the imported property modules give those conventions. In
  particular neither finite presentation of A to B nor quasi-compactness of Z_i is added.

Dependency declarations read and reused (names below are under `AlgebraicGeometry`
unless otherwise indicated):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` (and the etale-cover pullback clauses).
  This is already publicly imported by the morphism-properties module.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocally`, `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`:
  `AlgebraicSpace.MapIsAffine`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `AlgebraicSpace.IsQuasiCompact`.
- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  the explicit `universe u` and index bound implement its role here.

The last four owning definition nodes are already landed and have been added to
`stmt_deps`, as allowed by brief-stage2 section 5. None is restated or changed.
The proof dependencies with available modules are imported without `public`:
`AlgebraicSpaceLftDiagonalLfp`, `AlgebraicSpaceEtaleOpenImage`,
`SpaceQuasiCompactAffineTests`, and Mathlib's `Sites.MorphismProperty` (the recorded
composition-of-coverings match). Other proof dependencies have no recorded declaration
at the time of writing; they remain named in the proof docstring and DAG, not fabricated.

Edge cases checked before writing: the index is explicitly nonempty, as required; a
singleton or constant inverse system is allowed. The empty scheme, empty A, empty B
and empty stage spaces are allowed whenever the displayed arrows exist. The atlas of
an empty space may be empty, and sectionwise injectivity includes empty section sets.
There is no field, characteristic, reducedness, separatedness, Noetherian, or
transition-surjectivity assumption. Non-quasi-compact Z_i and non-quasi-separated A
are retained. The index is not forced to be a partial order. No false statement or
unusable dependency interface was found.

Searches for an existing statement:

- `msearch.py leanfinder`: "A monomorphism from a quasi compact algebraic space locally
  of finite type over a base to an inverse limit of quasi separated algebraic spaces
  with affine transition maps is eventually monic". Eight hits, all scheme-limit
  results, including `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`;
  none states the algebraic-space result.
- `msearch.py loogle`: `AlgebraicGeometry.AlgebraicSpace, CategoryTheory.Mono`.
  Zero hits; Mathlib does not recognize the project's algebraic-space type.
- `msearch.py leansearch`: "monomorphism algebraic space inverse limit eventually
  monomorphism". Eight hits, principally categorical preservation of monos by limits
  and scheme universal injectivity; no eventual monicity result.
- `msearch.py grep`: `eventual.*[Mm]ono|eventually.*[Mm]ono`, AlgebraicGeometry:
  zero hits. A further Mathlib grep for
  `MapIsAffine|MapIsLocally|IsAbsolutelyQuasiSeparated` also had zero hits.
- `rg` of `lean/WeilConjectures` for the item id and of the project sources for
  eventual monomorphism names found no existing statement. Searches of `lean/Sheaf`
  located the shared property definitions above, including the distinction between
  absolute and relative quasi-separatedness. The proposed full declaration name was
  also checked against Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json`;
  no collision was found.

Validation: prescribed `scompile.py NP lem-sfb-space-eventual-monomorphism` compiled
the delivered module both as a sandbox and at its library path, cleanly (3.3 s each).
The only postponed proof is the assigned named theorem. `set_option autoImplicit false`
checks that every variable and universe is explicitly bound.

## Second reading by NP

This is a second self-audit, not an independent-agent review: the dispatcher explicitly
prohibits starting another agent, and the maintainer performs the independent reading.
Reopened the node and completed Lean file and checked each binder and conclusion above.
The critical checks were that `hc` is the limit in `Over B`, that local finite type
belongs to `A.hom` rather than u, and that `hqs` is absolute while `hAqc` adds no
quasi-separatedness. The conclusion uses the canonical projection followed after u,
and requires a single late-stage bound uniform in both i and every test scheme T.
These match the node. No mismatch was found and no statement correction was needed.
