## Worker report

The module `Sheaf.AlgebraicGeometry.QEAlterationRegularNeighbourhood` states
`AlgebraicGeometry.exists_qe_alteration_regular_neighbourhood`. Its only postponed proof
is this theorem, with `sorry`. There are no new definitions, new nodes, dependency repairs,
or statement corrections. The original node is changed only in `lean`.

Hypothesis and conclusion correspondence:

- A commutative Noetherian integral domain is `(B : Type u) [CommRing B]
  [IsNoetherianRing B] [IsDomain B]`.
- The prime and ideal are `(q : Ideal B) [q.IsPrime] (J : Ideal B)`.
- Excellent localization is `hq : IsExcellent (Localization.AtPrime q)`.
- Quasi-excellence of the quotient is `hJ : IsQuasiExcellent (B ⧸ J)`.
- The element and neighbourhood are `∃ b : B, b ∉ q ∧ ...` with every structural
  morphism targeting exactly `Spec (.of (Localization.Away b))`.
- The finite family is `n : ℕ`, `X : Fin n → Scheme.{u}` and the indexed maps `φ`.
  Every chart has existential evidence `IsIntegral (X i)` and satisfies
  `IsNoetherian (X i)`. Mathlib's latter class is locally Noetherian plus compact,
  equivalent to a finite affine cover by Noetherian rings.
- Dominance is `IsDominant (φ i)`, whose field is precisely `DenseRange (φ i)`.
- Generic finiteness is
  `RingHom.Finite ((φ i).stalkMap (genericPoint (X i))).hom`.
  This is the ACTUAL canonical stalk map, with no arbitrary field algebra supplied.
  A dominant map between integral schemes sends the source generic point to the
  target generic point. Thus its source and target stalks are the two function fields,
  and `RingHom.Finite` means the induced field extension has finite dimension.
  This avoids introducing a second function-field map or choosing a ring-map witness.
  The known `Scheme.Hom.functionFieldMap` in
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback` is this same map after
  transporting the target stalk along the generic-point equality. Its signature and
  docstring were read, together with `apply_genericPoint_of_isDominant` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`. Using the stalk map
  directly requires no new base-integrality proof to elaborate a function-field abbreviation.
- Finite type is `LocallyOfFiniteType (φ i) ∧ QuasiCompact (φ i)`.
- For each chart point `x`, membership in the inverse image of the specified closed fibre
  is exactly `Ideal.map (algebraMap B (Localization.Away b)) J ≤ (φ i x).asIdeal`.
  The conclusion is `IsRegularLocalRing ((X i).presheaf.stalk x)`: this is the ambient
  chart's local ring, not the stalk of a quotient or closed subscheme.
- The witness is `V : Scheme.{u}`, existential `IsIntegral V`, and `IsNoetherian V`.
  The map `p` targets the same localization spectrum and has `IsProper p ∧ Surjective p`.
- Generic finiteness of `p` is `RingHom.Finite (p.stalkMap (genericPoint V)).hom`.
  Surjectivity implies dominance, so the same function-field interpretation applies.
- The open cover is `U : Fin n → V.Opens` with `(⨆ i : Fin n, U i) = ⊤`.
  The maps are `g : ∀ i, (U i).toScheme ⟶ X i`. Their being Y-morphisms is the
  commuting equation `g i ≫ φ i = (U i).ι ≫ p` for every index.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, `IsQuasiExcellent`, with their full
  definitions. These are the supplied excellence and quasi-excellence predicates.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Scheme.Hom.stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; its imported
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: the dependency's scheme predicate
  `IsRegularScheme` was read. This theorem uses the node's regular-local-ring clause,
  namely the imported `IsRegularLocalRing` from `Mathlib.RingTheory.RegularLocalRing.Defs`.
  It must not impose global regularity of a chart.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, with the actual
  ring and algebra structure imported from `Mathlib.RingTheory.Localization.Away.Basic`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`, `IsDominant`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField`, read to verify
  the generic stalk interpretation; `RingHom.Finite` is the existing finite ring-map
  predicate from `Mathlib.RingTheory.Finiteness.Defs`, not a new notion.

Proof-only imports match the recorded dependencies that already have declarations:
`Mathlib.Topology.Constructible` (`Topology.IsConstructible`),
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
(`Scheme.Hom.isConstructible_image`), `Mathlib.RingTheory.FinitePresentation`
(`Algebra.FinitePresentation.of_finiteType`), `Mathlib.Topology.Spectral.Basic`
(`SpectralSpace`), and `WeilConjectures.Topology.ProconstructibleClosureSpecialization`
(`Topology.exists_mem_iInter_closure_singleton`). Their signatures and docstrings were read.
The three proof-only nodes `lem-per-qe-weak-uniformization-cover`,
`lem-per-local-alteration-diagram-spreading`, and `lem-per-j2-closed-fibre-regular-locus`
have no Lean or mathlib declaration in the supplied snapshot; consequently there is no
module of theirs to import. They are not needed to type this statement. The docstring
includes all six proof steps and their DAG dependencies for stage 3.

Edge cases checked before writing: `J = ⊤` makes the specified closed fibre empty,
so the regularity implication is vacuous, as required. `J = ⊥` requires regularity
at every chart point. There is no assumption `J ≤ q`, no characteristic assumption,
no positive-height condition on `q`, no finite-dimensionality hypothesis, no restriction
on field extensions being separable, and no degree restriction. `b = 0` is excluded by
`b ∉ q`; thus the base is a nonempty integral spectrum. Integrality excludes empty charts
and an empty witness. `n = 0` is syntactically allowed, but its empty supremum cannot
cover the nonempty integral witness. Individual cover opens may be empty. Taking all
schemes in the base ring's universe is the standard finite-type size convention; the
statement imposes no universe equality between two independently given input objects.

Searches actually run with the prescribed msearch.py wrapper:

- leanfinder: `Noetherian domain excellent localization quasi-excellent quotient alteration
  cover regular above a closed fibre`; 8 hits on Zariski's main theorem, quasi-finite
  algebras and smooth loci, none stating this result.
- loogle: `"genericallyFinite"`; 0 hits.
- grep: `alteration|QuasiExcellent|GenericallyFinite`, subdirectory `AlgebraicGeometry`;
  0 Mathlib hits.
- leansearch: `Excellent local ring quasi-excellent quotient alteration neighbourhood regular
  closed fibre`; the returned results were unrelated Noetherian/localization facts,
  no matching alteration statement.
- Local `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `alteration|genericallyFinite|GenericallyFinite|IsQuasiExcellent`, followed by
  `functionFieldMap` and `generically finite`: existing excellence, function-field-map,
  and other alteration theorems were found; none states this node. The required
  `grep -rn` for the exact item id in `lean/WeilConjectures` returned no match.
  The project `Orgogozo.IsAlteration` was also read; its proper/finite-over-dense-open
  package is not the chart notion of this node, whose charts need not be proper.

Source checked directly: https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf,
Definition 3.2 and Lemma 4.4. The assigned node is the stated excellence/quasi-excellence
specialization. No counterexample or ambiguity requiring a correction was found.

Validation: scompile.py compiled the delivered file both in sandbox and module modes
cleanly (2.0 s and 2.2 s), with no error or warning. Every variable and universe is
explicitly bound (`autoImplicit false`). No proof, definition body, or local instance
was added. The final theorem uses exactly one `sorry`.

## Second reading by Q83

A separate agent is forbidden by the dispatcher brief. This is a second pass by the
same worker, not a claim of independent review; the maintainer's delivery review is
independent. I reopened the original node and final module and checked every binder
and conjunction against the correspondence above. The main risks checked were omission
of compactness in Noetherianity, omission of generic finiteness of the proper witness,
using regularity of a quotient stalk, omitting the same-index open cover, or forgetting
that its maps must commute over Y. All are explicitly present. The canonical stalk map
has domain the stalk at the actual image of the source generic point; dominance (or
surjectivity for `p`) identifies this point with the target generic point, so the field
extension is induced by the scheme morphism. No extra hypothesis or global chart
regularity was introduced. The failed attempt to use the transported function-field
abbreviation would have required evidence that the localization spectrum is integral;
the final statement uses the existing untransported canonical stalk map instead. The
node's TeX, stmt_deps and proof are unchanged, and its lean.statement is extracted
verbatim from the final source. No remaining discrepancy found.
