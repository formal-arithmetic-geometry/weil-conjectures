## Worker report

The new module `Sheaf.AlgebraicGeometry.FieldCurveFittingSmoothPreparation` states
`AlgebraicGeometry.field_curve_fitting_smooth_preparation`. Its only theorem proof is
`sorry`; no definitions or subsidiary theorems are introduced. The node changes only
in its `lean` field. No statement correction or dependency repair is needed.

Hypotheses and conclusions, matched to the node:

- The field is `(k : Type u) [Field k]`.
- The scheme and its given structure morphism are `(C : Scheme.{u})`
  and `(f : C ⟶ Spec (.of k))`.
- “Locally of finite type” is `[LocallyOfFiniteType f]`. There is no quasi-compactness,
  separatedness, reducedness, or finite-type-in-place-of-local-finite-type assumption.
- “Equidimensional of dimension one” is `(hpure : C.IsPureDimension 1)`, using the
  recorded componentwise topological dimension definition.
- The given first-Fitting singular inclusion is the canonical
  `Scheme.firstFittingSingularSubscheme f`; its source is the subscheme cut out by
  `Scheme.firstFittingIdealSheaf f`. Naming this canonical inclusion directly avoids
  introducing an arbitrary closed immersion in its place.
- `(V : Set C)` is identified by `hV` with exactly the points having a smooth open
  neighbourhood: `∀ x : C, x ∈ V ↔ ∃ W : C.Opens, x ∈ W ∧ Smooth (W.ι ≫ f)`.
  This characterizes the set named in the node, without presupposing a global smooth
  morphism or a local finite presentation instance.
- The equality with the complement of the image of the singular subscheme is
  `V = (Set.range (Scheme.firstFittingSingularSubscheme f))ᶜ`.
- “Every x in V” is `∀ (x : C), x ∈ V → ...`.
- The neighbourhood is `∃ U : C.Opens, x ∈ U ∧ (U : Set C) ⊆ V ∧ IsAffineOpen U ∧ ...`.
  Since it is affine, its canonical coordinate ring is `A = Γ(C, U)`, and its open
  subscheme is canonically `Spec A`; a second, arbitrarily chosen coordinate ring is
  unnecessary.
- The field-algebra structure on that coordinate ring is exactly
  `(((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra)`.
  It composes the canonical `k ≅ Γ(Spec k, ⊤)` with restriction of the given structure
  morphism; no arbitrary algebra structure is quantified over.
- Finite generation is the existential witness `ft : @Algebra.FiniteType k (Γ(C, U))`
  for that precise algebra structure. The last clause is
  `@Algebra.IsLocalCompleteIntersection k (Γ(C, U)) ... ft`, using the dependency's
  complete-intersection predicate and its required finite-type witness.
- There is no nodality or unramifiedness premise, as required by the final sentence.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension`.
- `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`:
  `AlgebraicGeometry.Scheme.firstFittingSingularSubscheme` and its uniquely determined
  `firstFittingIdealSheaf`. The inclusion is the ideal sheaf's `subschemeι`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsLocalCompleteIntersection` (and the `IsGlobalCompleteIntersection`
  definition it uses).

The available proof dependencies are imported without `public` and their signatures
were inspected: `IsNoetherianRing` in `Mathlib.RingTheory.Noetherian.Defs`;
`AlgebraicGeometry.IsLocallyNoetherian` and
`LocallyOfFinitePresentation.iff_locallyOfFiniteType` in
`Mathlib.AlgebraicGeometry.Noetherian`; `Flat.of_field` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat` (the upstream audit's exact
field specialization of the Mathlib leaf); `flat_dense_generic_fibre_pure_dimension`
in `Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension`; `dthFitting_smoothLocus`
in `Sheaf.AlgebraicGeometry.DthFittingSmoothLocus`; `Algebra.Smooth` in
`Mathlib.RingTheory.Smooth.Basic`; and `Algebra.isLocalCompleteIntersection_of_smooth`
in `WeilConjectures.RingTheory.SmoothLocalCompleteIntersection`. Dependencies already
used in the signature remain public imports. The theorem docstring gives all five
steps of the node's proof, including field-base preparation and geometric fibres.

Source reading: `literature/stacks-project/curves.tex`, lemma-nodal-lci, states the
smoothness and local complete intersection of the complement. In
`literature/stacks-project/divisors.tex`, lemma-d-fitting-ideal-omega-smooth assumes
flatness, local finite presentation, and pure-dimensional nonempty fibres. These
hypotheses are consequences over the field in the node's proof, not extra premises
of this statement.

Edge cases checked before writing: the empty scheme satisfies `IsPureDimension 1`
vacuously; both sets in the equality are empty and the neighbourhood assertion is
vacuous. The same neighbourhood assertion is vacuous if `V` is empty. Non-quasi-compact
and nonseparated curves are included because only local finite type is assumed.
Arbitrary characteristics and imperfect fields are included: no perfectness or
geometric reducedness is assumed, and the Fitting criterion supplies the smoothness
test. A point's chosen neighbourhood is nonempty by `x ∈ U`; the reused lci predicate
also retains the zero-ring convention. The common scheme/field universe is the
ordinary `Scheme.{u}` convention and imposes no finite-cardinality condition.

Searches for an existing statement:

- `msearch.py`, LeanFinder: “For a pure curve over a field the first Fitting singular
  subscheme has smooth complement with affine local complete intersection
  neighbourhoods”. Eight hits: algebraic smooth loci, standard smooth presentations,
  and scheme smooth-chart results; no theorem with both of this node's conclusions.
- `msearch.py`, Loogle: `"Fitting", "Smooth"`. Zero hits.
- `msearch.py`, grep: `Fitting|fittingIdeal|IsLocalCompleteIntersection`, subdirectory
  `AlgebraicGeometry`. Zero Mathlib hits.
- `msearch.py`, LeanSearch: “The complement of the first Fitting singular subscheme of
  a pure curve is smooth and has affine local complete intersection neighbourhoods”.
  Eight hits concerning algebraic smooth loci and formal smoothness; no exact match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for `firstFitting`,
  `field_curve_fitting`, `fieldCurveFitting`, `fitting_smooth`, and `Fitting.*smooth`:
  existing first-Fitting construction, general d-th Fitting criterion, and nodal
  theorems with additional hypotheses, but no exact statement. Searching this node id
  in `lean/WeilConjectures` found nothing. Searches for
  `IsLocalCompleteIntersection`, `IsPureDimension`, and `smoothLocus` also located the
  related existing APIs; `LciAffineOpenLocality.lean` provides an example of the same
  canonical section-ring algebra structure, but a different theorem.
- The full declaration name `AlgebraicGeometry.field_curve_fitting_smooth_preparation`
  was not present in these source searches.

Validation: the prescribed `scompile.py` compiled the module against current server
sources with exit code zero and no Lean errors or warnings. The delivery dry run
checks the final module and node record again. No `STATEMENT-DISPUTED` issue was found.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
