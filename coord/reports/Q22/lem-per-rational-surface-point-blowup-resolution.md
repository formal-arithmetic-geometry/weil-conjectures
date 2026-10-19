## Worker report

The module `Sheaf.AlgebraicGeometry.RationalSurfacePointBlowupResolution` states
`AlgebraicGeometry.exists_regular_ordinary_point_blowup_tower`, with `sorry` as its entire
proof. It defines no new notions and proves nothing. The natural-language statement,
proof and proof dependencies are unchanged.

The previous worker's stale-assignment diagnosis confused stage 1 with stage 2: Q40's
`reviewed` PASS verifies the split, not a Lean statement. The current node has no `lean`
or `reviewed_lean` record. This delivery retains Q40's reviewed split and supplies its
missing stage-2 declaration.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- C commutative, Noetherian and local: `(C : Type u) [CommRing C] [IsNoetherianRing C]
  [IsLocalRing C]`. Completeness is
  `[IsAdicComplete (IsLocalRing.maximalIdeal C) C]`, including separatedness.
- B normal local domain: `(B : Type v) [CommRing B] [IsLocalRing B] [IsDomain B]
  [IsIntegrallyClosed B]`. This is the recorded normal-domain form, not the assertion
  that an arbitrary non-domain is integrally closed.
- Dimension two: `hDim : ringKrullDim B = 2`.
- B is a localization of a finitely generated C-algebra: `hEss` supplies a commutative
  ring `D : CommRingCat.{max u v}`, its structure homomorphism `φ : C →+* D`, a
  submonoid `S : Submonoid D`, `φ.FiniteType`, and a ring isomorphism
  `LocalizedModule S D ≃+* B`. For M = D, the recorded `LocalizedModule S D` is
  definitionally the ring localization `Localization S`. No chosen C-algebra structure
  on B was specified in the node, so none is additionally required. C and B have
  independent universes; the presentation ring is allowed in their maximum universe.
- The hypothesis ranges over **every** integral normal Z: `∀ (Z : Scheme.{v})
  [IsIntegral Z]`, followed by normality at every structure-sheaf stalk as
  `IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z)`.
- The model morphism is `f : Z ⟶ Spec (CommRingCat.of B)` with `[IsProper f]`.
  Mapping generic point to generic point is `hη`; the isomorphism is precisely
  `IsIso (f.functionFieldMap hη)`, the induced generic-stalk map. An arbitrary
  abstract isomorphism between the fields would not meet this condition.
- Ordinary Zariski H¹ of the structure sheaf vanishes:
  `Subsingleton (Sheaf.H' Z.structureSheafAb 1 ⊤)`. The reused `structureSheafAb`
  forgets the structure sheaf to its additive sheaf on `Opens.grothendieckTopology Z`.
  `H'` is the recorded cohomology and `⊤` is the whole space. Subsingleton is exactly
  zero for this abelian group; the Grothendieck-abelian HasExt instance is available
  from the published cohomology module. There is no assumed vanishing comparison.
- Finite tower: existential `n : ℕ`, `V : Fin (n+1) → Scheme.{v}` and structure maps
  `p i : V i ⟶ Spec B`. `IsIso (p 0)` identifies V₀ with Spec B, as in the existing
  normalized-refinement and completion-descent statements. This is an identification
  of the base, with the subsequent composition equations fixing all structure maps.
- Every Vᵢ is integral and normal: the conjunction universally quantified over
  `i : Fin (n+1)` asserts `IsIntegral (V i)` and the same stalkwise normal-domain
  conjunction. Both the initial scheme and the endpoint are included.
- For every `j : Fin n`, choose a center `x : V j.castSucc`, its closed-singleton
  proof `hx`, and an ideal sheaf I. `I = Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩`
  is exactly the canonical reduced point center (Mathlib's docstring explicitly
  identifies the quotient with the reduced induced scheme structure).
- Singularity of each chosen point is the explicit clause
  `¬ IsRegularLocalRing ((V j.castSucc).presheaf.stalk x)`.
- All centers lie above the original closed point:
  `p j.castSucc x = IsLocalRing.closedPoint B`.
- The arrow is an **ordinary** blowup: `e : V j.succ ≅ I.blowup` identifies its source
  with the recorded global blowup. The actual arrow is `e.hom ≫ I.blowupMap`.
  `IsProper (e.hom ≫ I.blowupMap)` asserts properness of each arrow; the equation
  `e.hom ≫ I.blowupMap ≫ p j.castSucc = p j.succ` makes the tower commute.
  No normalization appears anywhere in the conclusion.
- Regular endpoint: `IsRegularScheme (V (Fin.last n))`, the recorded definition
  including local Noetherianity and regular local rings at every point.
- Length zero is included: n has no positivity constraint, `Fin n` is empty at n = 0,
  and the endpoint `Fin.last 0` is the base index. There are no centers to choose.

Dependency declarations read and reused:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finitely generated).
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, together
  with `IsDomain`, the recorded normal-domain form.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, with values in WithBot ℕ∞.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map` (spectrum needed here).
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, extending separated,
  universally closed, locally finite type; universal closedness supplies quasi-compactness.
- `Sheaf.AlgebraicGeometry.FunctionField`: the integral-scheme clause uses the imported
  Mathlib `Scheme.functionField`, not the component-product definition for reducible curves.
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback` supplies the already existing
  `Scheme.Hom.functionFieldMap`; its current source was read using `scompile.py --source`
  because this module is absent from the older local slopmaster2 tree.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, the companion declaration
  recorded alongside `AdicCompletion`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `CategoryTheory.Sheaf.H'`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`, with
  upstream `IsRegular` and Mathlib `IsRegularLocalRing`.
- `Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback`:
  `AlgebraicGeometry.Scheme.structureSheafAb`. Its owning already-landed node
  `def-sc-structure-sheaf-cohomology-pullback` is added to stmt_deps under brief-stage2
  §5, STMT_DEPS MAY GAIN LANDED NODES. This reuses its definition instead of reconstructing
  the additive structure sheaf. The node and full declaration/docstring were read.

The modules of all currently stated proof dependencies are imported, non-public when
needed only for the proof: CompleteLocalExcellent, IsExcellentFiniteTypeLocalization,
QuasiExcellentNagata, Blowup.Proper, Mathlib.AlgebraicGeometry.Noetherian,
ClosedDominantDimension, ExcellentNormalSurfaceLocalData and AffineScheme. Dependencies
also used in the statement are publicly imported. The rational-singularity definition,
Gorenstein-blowup, rationality-propagation, rational-double-point and ordinary-globalization
nodes have no recorded Lean declarations, so they supply no module to import yet. They
are proof dependencies only and are not extra hypotheses of this statement.

Source and edge-case checks: read the full 0BBV lemma/proof, the 0BGE lemma, and the
0BGM proof including both globalization applications in `literature/stacks-project/resolve.tex`.
The source's complete-base specialization supplies dualizing complexes; excellence and
Noetherianity of B follow from its localization presentation, so neither is added as a
hypothesis. The statement assumes neither a residue characteristic nor a perfect or
algebraically closed field. C need not be a domain and its map to D need not be injective.
The ring B is a genuine dimension-two domain, so zero rings and fields cannot accidentally
instantiate the surface hypothesis. The identity proper model Z = Spec B is included in
the vanishing quantifier. Both already-regular surfaces and zero-length towers are covered.
The finite singular set in the proof may be empty. A tower whose ordinary blowup failed
normality would not satisfy the explicitly required intermediate normality. No source
statement correction or STATEMENT-DISPUTED issue was found.

Searches (all performed through the prescribed wrapper or read-only rg/grep):

- msearch leanfinder: “A normal rational surface singularity essentially of finite type
  over a complete local ring admits resolution by ordinary blowups at singular closed
  points”. Eight hits: standard smoothness, smooth charts and Weierstrass reduction or
  minimal models; read their returned signatures, none states this theorem.
- msearch loogle: `"blowup", "regular"`. Zero hits.
- msearch grep: `PointBlowup|pointBlowup|rational.*singular|resolve.*surface`. Zero hits.
- msearch leansearch: “Resolution of rational two dimensional normal local singularities
  by blowups at singular closed points”. Eight hits, including closedPoint, its
  specialization properties, rational maps and a normalization dominance instance.
  Their returned signatures do not assert a surface resolution.
- rg of the slopmaster2 WeilConjectures and side Sheaf sources for rational surfaces,
  point-blowup towers and vanishing ideals: no exact theorem. The existing
  `SurfaceResolutionNormalizedRefinement` theorem needs this item in its proof and has
  normalized blowups as its conclusion; it cannot be reused as an exact match.
  `NormalizedBlowupCompletionDescent` also uses normalized, rather than ordinary, blowups.
- grep for this item's id in upstream WeilConjectures: no match.
- rg for structure-sheaf additive cohomology located `Scheme.structureSheafAb`; the
  delivered statement reuses it and cites its owning node.
- The prescribed source and Mathlib declaration files and docstrings were opened;
  current missing/stale upstream modules were read through `scompile.py --source`.

Validation: `scompile.py Q22 lem-per-rational-surface-point-blowup-resolution` compiled
both sandbox and library forms cleanly (4.3 s and 4.4 s); no errors or warnings.
The Lean file has no line over 100 characters, no auto-bound variables, no private
notions, no local notation/instances, and only the node's one named `sorry` theorem.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
