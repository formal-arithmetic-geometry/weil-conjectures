## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleAffineFiniteFibreRefinement` states
`AlgebraicGeometry.Scheme.Hom.exists_etale_affine_finite_fibre_refinement` with a single
`sorry` proof. No definitions, additional nodes, dependency repairs, or statement corrections
are needed. The node is unchanged outside `lean`.

The statement matches the node hypothesis by hypothesis and clause by clause:

- Schemes `X`, `W`, `Z` are `{X W Z : Scheme.{u}}`, with arbitrary explicit universe `u`.
  The affineness of `W` and `Z` is `[IsAffine W] [IsAffine Z]`; `X` is unrestricted.
- The maps are `(q : X ⟶ W)` and `(h : W ⟶ Z)`. The etale and pointwise-surjectivity
  assumptions are `[Etale q] [Surjective q]`. Mathlib's `Surjective` is precisely
  `Function.Surjective q` on underlying points.
- Local quasi-finiteness of the composite is
  `(hcomp : (q ≫ h).IsLocallyQuasiFinite)`, using the recorded Stacks 01TD predicate,
  which includes local finite type. This is not the weaker Mathlib `LocallyQuasiFinite`.
- The nonnegative integer and finite family are `∃ (m : ℕ) (A : Fin m → X.Opens)`.
  `Fin m` labels the node's `A_1,...,A_m`, with no nonemptiness condition on `m`.
- Each open subscheme is affine by `∀ j : Fin m, IsAffineOpen (A j)`.
  The scheme carried by an open has its actual restricted structure sheaf, and
  `(A j).ι` is its canonical inclusion into `X`.
- The image-cover clause is `(⋃ j : Fin m, q '' (A j : Set X)) = Set.univ` in `Set W`.
  Thus the finite family covers `W` by its images under `q`, rather than covering `X`.
- The restricted composite is `(A j).ι ≫ q ≫ h`. For every `j`, the conclusion explicitly
  includes its `.IsQuasiFinite` and `.HasFiniteFibres`, with the recorded definitions.
- For every `z : Z`, the conclusion equates `h ⁻¹' {z}` with the indexed union of
  `((A j).ι ≫ q) '' (((A j).ι ≫ q ≫ h) ⁻¹' {z})`. The latter set consists exactly of
  the `q`-images of points of `A_j` satisfying `h(q(a)) = z`; both sides are subsets of `W`.
- The final `h.HasFiniteFibres` is definitionally `∀ z : Z, (h ⁻¹' {z}).Finite`, so the
  final finiteness clause is included for every target point.
- There is no quasi-compactness assumption on `X` or `q`, no separation assumption,
  and no Noetherian assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite`, `Scheme.Hom.IsQuasiFinite`,
  `Scheme.Hom.HasFiniteFibres` (the node's recorded declarations); the full signature
  and docstring of `IsQuasiFiniteAtPoint`, on which local quasi-finiteness is built,
  were also read. These definitions retain the local finite-type condition of Stacks 01TD.
- Mathlib's `AlgebraicGeometry.IsAffine`, `IsAffineOpen`, and the actual open-subscheme
  inclusion; `Surjective` from `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.

The module also imports the recorded proof tools, with ordinary non-public imports:
`Mathlib.AlgebraicGeometry.Morphisms.Affine` (affine morphisms and their quasi-compactness),
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` (`Scheme.Hom.isOpenMap`),
`WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE`
(`Scheme.Hom.isLocallyQuasiFinite_resLE`),
`WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite`
(`Scheme.Hom.isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact`), and
`WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`
(`locallyQuasiFinite_and_quasiCompact_iff_finite_preimage_singleton`). The affine-open basis
and affine quasi-compactness declarations are available through `AffineScheme`, imported by
these modules. The declaration docstring carries all three proof steps and their DAG tools.

Source checks: opened `literature/stacks-project/descent.tex`,
`lemma-locally-quasi-finite-etale-local-source` (Tag 03X4), and
`literature/stacks-project/topologies.tex`, `lemma-etale-affine` (Tag 0218).
The latter allows affine opens in an arbitrary etale covering family; the former supplies
the finite-fibres descent paragraph. The node's expansion writes out the finite affine
selection and fibre equality without imposing quasi-compactness on the original source.

Edge cases checked mathematically before writing:

- If `W` is empty, a morphism `X → W` forces `X` empty. Choose `m = 0`; the image cover
  and each fibre-image equality are empty unions. The final fibres are empty.
- If `Z` is empty, the map `h` forces `W` empty and hence `X` empty; the same choice works.
- Points `z` outside the image of `h` have empty fibres on both sides of the equality.
- Infinite disjoint unions of etale sources remain allowed: compactness is used only
  on affine `W` to choose finitely many images, never on `X` or `q`.
- Affine empty opens and repeated family members are allowed. A finite union of their
  finite fibre images still has the required meaning.

Searches performed using `batch2/msearch.py`:

- `leanfinder`: "A surjective etale morphism to an affine scheme admits finitely many affine
  open source pieces covering the target, with quasi finite restricted composite and finite
  fibres when the composite is locally quasi finite". Eight hits, including
  `Scheme.AffineCover`, `locallyQuasiFinite_iff`, and
  `Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource`; none includes the prescribed
  source opens and fibre-image equality.
- `loogle`: `AlgebraicGeometry.Etale, AlgebraicGeometry.Scheme.Hom.HasFiniteFibres`.
  Zero hits; the external index does not know the project's `HasFiniteFibres` identifier.
- `grep`, subdirectory `AlgebraicGeometry`:
  `finite_preimage_singleton|finite.*affine.*refinement|affine.*finite.*refinement`.
  Nine hits in QuasiFinite, ZariskisMainTheorem, Group/Abelian and Finite. The finite-fibre
  lemmas apply to already quasi-compact maps and do not construct this refinement.
- `leansearch`: "A surjective etale map onto an affine scheme has a finite family of affine
  open source pieces covering its target and finite fibre descent for a locally quasi finite
  composite". Eight hits, including `Scheme.affineOpenCover`, `Scheme.affineCover`, and
  `QuasiCompactCover.of_finite`; none is the node's combined statement.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the
  node id and names involving finite affine refinement and finite fibres found no exact
  declaration. Related pro-etale refinement results concern different covers, and the private
  `exists_finite_affine_etale_cover_with_property` assumes a Noetherian base and omits the
  restricted composites and fibre-image formula. The recorded quasi-finite predicates were
  reused, not duplicated.

Validation: `scompile.py Q13 lem-a1-etale-affine-finite-fibre-refinement` compiled the module
on the server against the live published build, including its normal sandbox and library
checks (5.4 s and 2.4 s). No errors or non-sorry warnings. Explicit `autoImplicit false`
ensures every variable and universe is bound. No statement dispute or other node fault found.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
