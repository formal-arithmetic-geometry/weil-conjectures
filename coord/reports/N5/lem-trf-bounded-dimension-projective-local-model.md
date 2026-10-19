## Worker report

The module `Sheaf.TraceFormula.BoundedDimensionProjectiveLocalModel` states
`AlgebraicGeometry.exists_boundedDimension_projective_local_model` with proof `sorry`.
It introduces no definition and no new DAG node. The theorem uses the canonical strict-local
map `Scheme.strictHenselizationMap` and the strict-local structural and evaluation maps already
provided by the project.

The Lean signature renders the node clause by clause:

- `{X S : Scheme.{u}}`, `f : X ⟶ S`, and `[LocallyOfFiniteType f]` are the morphism and
  locally-finite-type hypothesis `[def-weil-finite-type-morphism]`.
- `N : ℕ` and `hN : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ (N : WithBot ℕ∞)` state the
  nonnegative fibre-dimension bound, using `Scheme.Hom.fiber` from
  `[def-pc-scheme-fibre]` and `topologicalKrullDim` from
  `[def-kun-topological-krull-dimension]`.
- `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `x : Spec (.of Ω) ⟶ X` render the geometric point `[def-weil-geometric-point]`.
- `P : Scheme.{u}` and `p : P ⟶ Scheme.strictHenselizationScheme (x ≫ f)` set
  `B = S_(f(x))`; `IsProjective p` and `IsProper p` are respectively the projective and
  proper clauses `[def-pc-projective-morphism]` and `[def-weil-proper-morphism]`.
- `y : Spec (.of Ω) ⟶ P` is a geometric point. Its displayed equality identifies its image
  under `p` with the point of `B` represented by the canonical evaluation map at `x ≫ f`,
  so it lies over the closed point of `B`.
- `θ : Scheme.strictHenselizationScheme x ≅ Scheme.strictHenselizationScheme y` and
  `θ.hom ≫ Scheme.strictHenselizationStructuralMap y ≫ p =
  Scheme.strictHenselizationMap f x` state the isomorphism
  `X_(x) ≅ P_(y)` over `B`; the structural map is imported from
  `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` and the canonical map from
  `[def-weil-pbc-strict-henselization-limit]` and
  `[lem-weil-pbc-strict-henselization-functoriality]`.
- The final `∀ s : Scheme.strictHenselizationScheme (x ≫ f), ...` is the required bound on
  every scheme-theoretic fibre of `p`, again using `Scheme.Hom.fiber` and
  `topologicalKrullDim`.

The imported dependency declarations are:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`;
- `Mathlib.AlgebraicGeometry.Fiber`, `AlgebraicGeometry.Scheme.Hom.fiber`;
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`;
- `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`;
- `Sheaf.AlgebraicGeometry.StrictHenselization`,
  `AlgebraicGeometry.Scheme.strictHenselizationScheme` and
  `AlgebraicGeometry.Scheme.strictHenselizationRing`;
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`,
  `AlgebraicGeometry.Scheme.strictHenselizationClosedLift_over` (the recorded declaration for
  `[lem-weil-pbc-strict-henselization-functoriality]`);
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsProjective` and `AlgebraicGeometry.IsHProjective`;
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`;
- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`,
  `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap`;
- `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`,
  `AlgebraicGeometry.Scheme.strictHenselizationMap`,
  `strictHenselizationMap_over`, and
  `strictHenselizationPointEvaluation` (the canonical map interface used to make the
  functoriality map explicit).

The theorem docstring records the five proof steps from the node. Step 1 uses
`lem-sc-fibre-dimension-after-base-change`, `def-pc-scheme-fibre`,
`lem-weil-pbc-dimension-supremum-local-dimensions`, `def-kun-dimension`,
`lem-weil-pbc-strict-base-closed-point-localizations`,
`lem-weil-pbc-strict-henselization-functoriality`, and
`def-weil-pbc-strict-henselization-limit`. Step 2 uses
`lem-trf-local-quasi-finite-projection` and `def-nagata-relative-affine-space`; step 3 uses
`thm-pqf-zmt-factorization`; step 4 uses `lem-trf-finite-projective-envelope`,
`def-pc-projective-morphism`, and `def-weil-proper-morphism`; step 5 uses
`lem-trf-ind-etale-strict-local-invariance`, `def-weil-geometric-point`, and the canonical
strict-local map interface.

I checked the edge cases `N = 0`, empty fibres (where the dimension is `⊥`), an empty source,
and the identity morphism. The quantifiers permit these cases; no Noetherian, finite
presentation, or quasi-compact hypothesis is introduced.

Searches made:

- `msearch.py ... leanfinder "A locally finite type morphism with fibres of dimension at most
  N admits a projective proper model of the strict localization with the same fibre bound"`:
  only generic `LocallyOfFiniteType`, `LocallyQuasiFinite`, Proj, and properness declarations;
  no matching theorem.
- `msearch.py ... loogle "IsProjective, IsProper, strictHenselizationScheme,
  topologicalKrullDim"`: no exact hit (`IsProjective` is not a Mathlib identifier).
- `msearch.py ... grep "strictHenselizationMap|topologicalKrullDim.*fiber|IsProjective.*IsProper"
  AlgebraicGeometry`: no hit in the searched Mathlib subtree.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` for the item id, title, and
  `boundedDimension_projective_local_model`: no existing declaration. `grep -rl` over
  `dag/nodes` found only this node and its already-reviewed split siblings/citers; no duplicate
  statement node exists.

The prose source statement remains the same; its Lean encoding was corrected so that the
projective model is localized at the chosen geometric point `y`. No `STATEMENT-DISPUTED`
remains.

## Repair of returned delivery

The previous Lean clause introduced `θ : Scheme.strictHenselizationScheme x ≅ P`, which
identified `X_(x)` with all of the projective model `P`; the point `y` occurred only in the
closed-point equation. This is false (for example, take `X = A¹_k` at the origin over
`S = Spec k`). Following Orgogozo, Proposition 2.3, proof, printed p. 4, the corrected
clause identifies `X_(x)` with the strict localization `P_(y)`:
`∃ (θ : Scheme.strictHenselizationScheme x ≅ Scheme.strictHenselizationScheme y),
θ.hom ≫ Scheme.strictHenselizationStructuralMap y ≫ p =
Scheme.strictHenselizationMap f x ∧`.
The declaration now publicly imports `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`.
The DAG statement already specifies `P_(y)` and remains unchanged, so this is a repair of
`lean.statement`, not a source-based correction of the DAG node. The initial retained-packet
dry run passed, confirming the returned head compiled despite expressing the wrong conclusion.
The revised file was then compiled with `scompile.py`: both sandbox and library checks passed
without errors or warnings. The theorem's proof remains `sorry`.

## Second reading by N5

I reopened the DAG node and repaired module for a clause-by-clause self-check of H3/H11. The hypotheses occur in the same order:
locally finite type, integer `N`, the bound on every fibre of `f`, then an algebraically closed
geometric point `x`. The conclusion has exactly `P`, its map `p` to
`strictHenselizationScheme (x ≫ f)`, projective and proper properties, a point `y` over the
canonical closed point, and an isomorphism of strict localizations
`Scheme.strictHenselizationScheme x ≅ Scheme.strictHenselizationScheme y` whose composite
with `Scheme.strictHenselizationStructuralMap y` and `p` is
`Scheme.strictHenselizationMap f x`; this is precisely `X_(x) ≅ P_(y)` over `B`. The final
universal fibre-dimension bound is unchanged. No hypothesis or conclusion clause was added or
omitted, and the edge cases `N = 0`, empty fibres (dimension `⊥`), an empty source, and the
identity morphism remain admitted.

The defect found in returned head `971e52348d13` was the target `P` in the θ binder and
its direct composite with `p`. Both now explicitly use the strict localization at `y` and
its structural map. The previous second-reading claim was incorrect; this reading checks
the actual binder and composite shown above. Independent review is left to the maintainer,
as required for this dispatcher worker.
