## Worker report

States `AlgebraicGeometry.Flat.exists_open_neighbourhood_isAffineHom_of_mono` in
`Sheaf.AlgebraicGeometry.QcFlatMonomorphismAffineNeighbourhood`, with its proof `sorry`.
No definitions or helper nodes are needed. The node is unchanged except for `lean`.

Source checked: Raynaud, Un critère d'effectivité de descente, §1 Proposition 1.5(i),
printed p.3, https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf, PDF page 3
(zero-based). The source asserts a greatest open over which the map is affine, containing
its image. This node deliberately states only existence of such an open. Its given proof
is the local argument in that source, expanded in the declaration docstring.

Clause-by-clause translation:

- Schemes and a morphism `f : X → S`: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  The universe `u` is explicit and arbitrary, and `autoImplicit` is disabled.
- Quasi-compactness: `[QuasiCompact f]`, the preimage of every compact open is compact;
  equivalently it suffices to test affine opens by `quasiCompact_iff_forall_affine`.
- Flatness: `[Flat f]`, equivalent to flatness of the actual local ring maps by
  `Flat.iff_flat_stalkMap`.
- Monomorphism: `[Mono f]`. Its `right_cancellation` quantifies over every object of
  `Scheme.{u}` and every pair of maps to X, expressing precisely injectivity of
  postcomposition on Hom(T,X). It is not merely injectivity on underlying points.
- An open subscheme U of S: `∃ (U : S.Opens)`, using the genuine restriction
  `U.toScheme` and its canonical inclusion `U.ι`.
- Containment of the whole image: `(hU : Set.range f ⊆ Set.range U.ι)`.
  `Scheme.Opens.range_ι` identifies `Set.range U.ι` with the underlying open U.
  This dependent existential is a containment witness, not an additional input assumption.
- Affineness of the induced morphism X → U:
  `IsAffineHom (IsOpenImmersion.lift U.ι f hU)`.
  The Mathlib lift restricts the given morphism, including its structure-sheaf map;
  `IsOpenImmersion.lift_fac` states that composing with `U.ι` gives exactly f, and
  `IsOpenImmersion.lift_uniq` makes this the unique factorization.
- No quasi-affineness, quasi-separatedness, local finite presentation, or Noetherian
  assumption appears. U is not required to be affine: only the induced morphism is affine.

Dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; the recorded stalkwise equivalence was read.
- `def-weil-pbc-scheme-conventions`: a convention node with no declaration or module;
  its quasi-compactness notion is the existing `AlgebraicGeometry.QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` and its canonical `lift`.
  `Mathlib.AlgebraicGeometry.Restrict` supplies `Scheme.Opens.toScheme`, `ι`, and `range_ι`.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom`.
- Monicity uses the existing `CategoryTheory.Mono` from
  `Mathlib.CategoryTheory.Category.Basic`, available through these statement imports.

Proof dependency imports are private: `Mathlib.AlgebraicGeometry.Morphisms.Proper`
(`IsProper`, `IsSeparated`, `UniversallyClosed`), `.Separated`
(`IsSeparated.of_isAffineHom`, `IsAffineHom.of_comp`), `.ClosedImmersion`
(`IsClosedImmersion.isStableUnderBaseChange`), `.Basic`
(`HasAffineProperty.iff_of_openCover`), and `Mathlib.AlgebraicGeometry.Limits`
(finite coproducts of affines). The public `.Affine` import provides
`isAffineHom_isStableUnderBaseChange`, `isAffine_of_isAffineHom`,
`instQuasiCompactOfIsAffineHom`, and `isAffineHom_of_isAffine`.
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine` is imported privately for
`isAffineHom_tfae`, the recorded upstream declaration of `pqf-lem-affine-local-target`.
The proof dependency `lem-sfb-qc-flat-monomorphism-ringed-image` has no recorded Lean
module or Mathlib match in the read snapshot, so no import can be made for it yet;
its role remains explicit in the proof docstring. It is not a statement prerequisite.

Edge cases checked before writing:

- Empty X: U may be the empty open; its inclusion has empty range, so containment is
  vacuous and the empty-to-empty induced map is affine. Nothing requires a point of X.
- Empty S: any morphism has empty source; the same case applies.
- Surjective f: containment forces U to be all of S, and a quasi-compact flat surjective
  monomorphism is an isomorphism, in agreement with Mathlib's FlatMono theorem.
- Identity: U may be all of S, irrespective of whether S is affine or separated.
- A localization such as Spec Q → Spec Z need not be locally of finite presentation;
  the signature admits it. No false open-immersion conclusion is asserted.
- A non-quasi-compact target and an arbitrary image are permitted; U need not be
  quasi-compact or affine. There is no auxiliary index type or finiteness restriction.

Searches for an existing statement:

- `msearch.py leanfinder`, query `A quasi compact flat monomorphism is affine over an open
  neighbourhood of its image`: eight hits, including `Flat.isIso_of_surjective_of_mono`,
  `IsOpenImmersion.of_flat_of_mono`, and affine-map criteria. None is this existence theorem;
  the open-immersion result assumes local finite presentation, the isomorphism result
  assumes surjectivity. Read their signatures in `Morphisms/FlatMono.lean`.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Flat, CategoryTheory.Mono, AlgebraicGeometry.IsAffineHom`: zero hits.
- `msearch.py grep`, query `affine.*(neigh|[Mm]ono)|([Mm]ono|neigh).*affine`, restricted to
  `AlgebraicGeometry`: sixteen hits, concerning affine monoid schemes, immersion criteria,
  local ring-map criteria, and Zariski-site functors; no exact statement.
- Direct `rg` searches in `lean/WeilConjectures` and `lean/Sheaf` for the same terms,
  then for `flat monomorphism`, `flat quasi-compact monomorphism`, and
  `quasi-compact flat monomorphism`: inspected `FlatMonomorphismLocalStructure.lean`,
  which states injectivity, stalk isomorphisms, fibre and regularity properties,
  preservation of Noetherianity and reducedness, and base-change versions, not this
  open-neighbourhood assertion. Other hits concern ideal functoriality or graph immersions.
- `grep -rn` for the item's exact id in `lean/WeilConjectures`: no hits.

No statement correction or STATEMENT-DISPUTED issue was found.

Validation: compile with the prescribed `scompile.py`, then the prescribed `deliver2.py`
dry run and delivery. Only the expected declaration-uses-sorry warning is allowed.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
