## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` states
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
Its sole proof is `sorry`; there are no new definitions, auxiliary theorems,
new nodes, dependency repairs, or statement changes.

The previous blocked result confused stage-1 review with stage-2 completion.
The current node is split and reviewed PASS by NW/L, but its `lean` record is
absent. This delivery preserves the reviewed node and adds its Lean statement;
it does not re-split the node or reuse the dropped per-route theorem.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- “Let T be an integral scheme” is `{T : Scheme.{u}} [IsIntegral T]`.
  The Mathlib predicate includes nonemptiness and domain section rings on
  nonempty opens; equivalently it is reduced and irreducible.
- “A quasi-coherent ideal I contained in O_T” is `(I : T.IdealSheafData)`.
  This existing Mathlib structure records its ideals on affine opens and their
  localization compatibility, precisely quasi-coherent ideal-sheaf data.
  Its lattice bottom has zero ideal on every affine open.
- “Nonzero” is `(hI : I ≠ ⊥)`. This is nonzero as an ideal sheaf, not a
  condition on global sections or a demand for a proper ideal.
- “Of finite type, meaning its restriction to every affine open corresponds
  to a finitely generated ideal” is
  `(hfinite : ∀ U : T.affineOpens, (I.ideal U).FG)`.
  This is the node's explicit affine form, also used upstream in
  `Scheme.IdealSheafData.isProper_blowupMap`. It is not finite presentation,
  coherence, a globally bounded generating set, or a Noetherian assumption.
  `pqf-def-coherent` supplies the general module notion via
  `Scheme.Modules.IsQuasiCoherentFiniteType`, whose module is imported publicly;
  no duplicate predicate is introduced for its affine ideal specialization.
- “Let b : B = Bl_I(T) → T be its ordinary blowup” is the existing canonical
  `I.blowup` and `I.blowupMap` from the recorded global-blowup module.
  No extra blowup realization, arbitrary morphism, normalization, or choice
  is introduced.
- “B is integral” is `IsIntegral I.blowup`.
- “b is projective in the projective-bundle sense” is
  `IsProjectiveBundle I.blowupMap`, joined to the first conclusion by `∧`.
  The recorded definition factors the actual morphism as a closed immersion
  into the canonical relative Proj of Sym(E), followed by its structure map,
  for some quasi-coherent finite-type module E. It does not require E to be
  locally free or replace this with the H-projective convention.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`
  (`def-pc-integral-scheme`); read the class and its equivalence with reduced
  irreducible schemes.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`
  (`pqf-def-coherent`); its definition is quasi-coherence and finite type.
- `WeilConjectures.Blowup.Gluing`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup`, `blowupMap`,
  `blowupFunctor`, and `blowupGluingData`. The blowup is the glued scheme of
  the canonical affine Rees blowup diagram.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`:
  `AlgebraicGeometry.IsProjectiveBundle`
  (`def-trf-projective-bundle-morphism`); read its full existential signature.
- The ideal-sheaf encoding and its zero ideal were checked in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`.

The module imports all recorded proof-dependency modules with plain imports,
except those already public as statement dependencies. In particular:
`WeilConjectures.Blowup.Affine.Defs` (AffineBlowup),
`WeilConjectures.Blowup.Affine.ChartAlgebra` (chartRing),
`WeilConjectures.AlgebraicGeometry.RelativeProj.Basic` (GradedAlgebraData.relProj),
`WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`
(isClosedImmersion_relProjMap),
`Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`
(exists_quasiCoherentSymmetricAlgebra),
`WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`
(SymmetricAlgebra.graded_by_tensor_images),
`WeilConjectures.Blowup.FiniteDegree.Algebra`
(AffineBlowup.iSup_basicOpen_reesX_eq_top_of_span),
`WeilConjectures.Blowup.Complement`
(IdealSheafData.isIso_blowupMap_restrict_support_compl), and
`Mathlib.AlgebraicGeometry.RelativeGluing`
(Scheme.Cover.RelativeGluingData and its glued, toBase, and pullback interfaces).
`def-nagata-sheaf-rees-algebra` has no lean field but its closed upstream audit
records `IdealSheafData.reesData` in
`WeilConjectures.AlgebraicGeometry.RelativeProj.Rees`; that module is imported
as well, following brief-stage2 §0. Nothing is restated.

The docstring carries all three reviewed proof steps, including the generic-point
argument for nonzero ideals on each nonempty affine, domain chart rings and
empty zero-generator charts, the dense integral complement, and the graded
surjection Sym(I) → Rees(I) inducing a closed immersion into P(I).
The source was read directly in `literature/stacks-project/divisors.tex`,
lemma-blow-up-integral-scheme (02ND) and lemma-blowing-up-projective (02NS),
including its proof and specifically clause (1).

Edge cases checked before writing:

- The empty scheme is excluded exactly by integrality of T; no extra
  nonemptiness binder is needed.
- I = 0 would have empty blowup and would invalidate the integral conclusion;
  the explicit nonzero hypothesis excludes precisely this case.
- I = O_T is allowed: the blowup is T, its map is the identity, and the
  projective-bundle witness is the rank-one structure module.
- On the empty affine open the section ring is zero and its ideal is
  finitely generated; quantifying over every affine open excludes no case.
- Zero members of a chosen finite generating family give empty charts;
  no nonzero-generator or positive-rank assumption appears in the signature.
- Non-affine, non-quasi-compact and non-Noetherian integral bases remain
  allowed. Finite type is local with no uniform global bound on generators.
- The universe `u` is explicit and arbitrary. No characteristic restriction
  or independent test-object universe is imposed.

Searches made through `msearch.py` (2026-10-22):

- LeanSearch: “The blowup of an integral scheme in a nonzero finite type
  quasi coherent ideal is integral and projective”: eight results including
  IsIntegral and integral morphisms; no ordinary-blowup theorem.
- LeanFinder: “The ordinary blowup of an integral scheme along a nonzero
  quasi-coherent ideal of finite type is integral and projective in the
  projective bundle sense”: eight results about normalization, Proj and
  properness, none stating the node.
- Loogle: `"AlgebraicGeometry", "blowup"`: zero hits. An initial query naming
  IdealSheafData.blowup was unknown to Loogle's Mathlib-only index; it was
  repeated with the namespace/string query.
- Mathlib grep: `(blowup|Blowup|blowUp)` in AlgebraicGeometry: zero hits.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for blowup/integral
  and blowup/projective combinations found local affine embedding theorems,
  properness, and specialized consumers. `WeilConjectures.Blowup.Proper`
  explicitly says projectivity remains unformalized. No exact declaration.
- Direct rg for `IsProjectiveBundle.*blowup`, `blowupMap.*IsProjectiveBundle`,
  and the proposed theorem name in the source library, Sheaf, Mathlib, and
  `dag/lean_names_upstream.json` found no duplicate. A specialized flatification
  theorem has this conclusion for its own selected blowup only.
- The blueprint-id grep in `lean/WeilConjectures` found no declaration for
  this item. All structured search outcomes are saved in `searches.jsonl`.

There are no statement disputes or node faults. All writes are restricted to
the item's sandbox; compilation and delivery use the prescribed wrappers.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
