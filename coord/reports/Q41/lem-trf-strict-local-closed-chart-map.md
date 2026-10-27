## Worker report

The module `Sheaf.AlgebraicGeometry.StrictLocalClosedChartMap` states
`AlgebraicGeometry.Scheme.strictLocalClosedChartMap`. Its only postponed theorem is this
node's theorem, with proof `sorry`. The structure
`AlgebraicGeometry.Scheme.StrictLocalClosedChartRingData` packages its ring conclusion;
it introduces no second definition of a strict henselization, localization, residue
field, geometric point, or canonical map. Its fields are fully specified data and
properties, with no `sorry` and no chosen witness from mere existence.

I read the node and every statement dependency, its Lean record or Mathlib match, and
the recorded source declarations and docstrings. I also read the four proof steps and
proof-dependency declarations, Stacks etale-cohomology.tex Tag 04HX and the paragraph
after 03PS, algebra.tex Tag 04GU, and the current latest blueprint ancestor
`sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality` and its unit. This is a
generic ring/chart input beneath that ancestor's normal-cone route.

Hypotheses and objects are rendered as follows:

| Node | Lean |
| --- | --- |
| Schemes Z,W and closed immersion i | `{Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]` |
| Geometric point bar a | `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, and `x ≫ k` |
| Underlying point a | The image `(x ≫ k) (IsLocalRing.closedPoint Ω)`; not an independent point assumption |
| Affine open U=Spec A | `A : CommRingCat.{u}`, `j : Spec A ⟶ W`, `[IsOpenImmersion j]` |
| Inverse-image chart Spec(A/I) | `I : Ideal A`, open immersion `k : Spec (.of (A ⧸ I)) ⟶ Z`, and `hsquare : IsPullback k (Spec.map …mk I) i j` |
| Point lies in the inverse-image chart | `x : Spec (.of Ω) ⟶ Spec (.of (A ⧸ I))`; every point in the chart is covered |
| Prime p containing I and specified residue embedding into Ω | `p : Spec A`, `[Algebra p.asIdeal.ResidueField Ω]`, and `hx`, identifying the chart point with `Spec.map` of that residue embedding followed by `fromSpecResidueField p` |
| R=A_p | Exactly `Localization.AtPrime p.asIdeal` |
| S=(A/I)_(p/I)=R/IR | Exactly `Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap A (Localization.AtPrime p.asIdeal))`; `chartS`, `chartS_eq`, and `localizationS` retain its A/I-action and localization universal property |
| K inside Ω | Exactly `separableClosure p.asIdeal.ResidueField Ω`, with its actual `subtype` into Ω |
| C,D and structural maps | Exactly `strictHenselizationRing ((x ≫ k) ≫ i)`, `strictHenselizationRing (x ≫ k)` and their existing `strictHenselizationStructuralMap` |
| Prescribed canonical u | Exactly `(Spec.preimage (strictHenselizationMap i (x ≫ k))).hom`; the full-faithful Spec preimage has no arbitrary-map parameter |

All conclusion clauses are retained:

| Node clause | Lean |
| --- | --- |
| Both structural maps factor through their affine charts | The existential maps `α`, `β` and the two equalities `Spec.map (ofHom α) ≫ j = …` and `Spec.map (ofHom β) ≫ k = …` |
| Chart maps extend to local R→C and S→D | `baseC`, `baseD`, `baseC_eq`, `baseD_eq`, `baseC_local`, `baseD_local` |
| C,D are algebraic strict henselizations relative to K | `presentationC`, `presentationD`, each using the recorded `Algebra.StrictHenselizationPresentationIn.{u,u}` |
| Both rings strictly henselian local | `localC`, `localD`, `strictC`, `strictD` |
| Geometric evaluations identify residue fields with K | Ring equivalences `residueC`, `residueD`; `residueC_eq`, `residueD_eq` tie them to the presentation maps; `evaluationC`, `evaluationD` identify those with the existing geometric evaluations into Ω |
| Residue embeddings are induced by the common base residue field | `residueC_base`, `residueD_base`, the coefficient towers `towerR`, `towerS`, and `closureS_eq` |
| u is local and R-linear with D acted on through R→S | `map_local`, `map_base` |
| u induces id_K | `map_residue : presentationD.residueMap.comp uCD = presentationC.residueMap` |
| u(IC)=0 | `ideal_killed : I.map α ≤ RingHom.ker uCD` |
| Q=C/IC with its quotient map | Exactly `C ⧸ I.map α` and `Ideal.Quotient.mk (I.map α)` in the record; never an arbitrary quotient object |
| Induced S-action on Q | `quotientAlgebra`, with defining action equation `quotientAlgebra_eq` |
| Unique S-algebra map bar u with u=bar u q | `desc`, `desc_eq`, `desc_unique` |
| Q local; bar u local; inverse(m_D)=q(m_C)=m_Q | `localQ`, `desc_local`, `maximalIdeal_comap`, `maximalIdeal_quotient` |

The residue equivalences and their characterizing equations imply that each
presentation residue map is surjective with maximal-ideal kernel: `IsLocalRing.residue`
is the quotient surjection and a ring equivalence is bijective. Thus the evaluation
image is exactly the specified subfield K, even when Ω is much larger. Ideal map under
the surjective quotient map is exactly the set-image ideal q(m_C). `map_base` is the
unbundled R-algebra-map condition; `desc` is an actual S-algebra homomorphism.

The chart maps α and β are existentially displayed, but uniquely forced by their
structural equations: open immersions are monomorphisms, and Spec is fully faithful.
They therefore are the actual colimit chart legs of the comparison dependency, not
free maps. The only algebra structures retained in the record are constrained by
the chart/quotient equations and coefficient towers. Both quotient structural maps
are surjective, so the induced actions are also uniquely determined.

Dependency declarations used (all are existing interfaces, imported directly):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are the
  recorded inline field-valued scheme maps.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Spec.residueFieldIso`, `Scheme.SpecToEquivOfField`
  (the last two express the prime/residue description in `hx`).
- `Mathlib.FieldTheory.SeparableClosure`: `separableClosure`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, `Scheme.strictHenselizationScheme`.
- `Sheaf.Paper.StrictHenselizationFunctoriality`:
  `AlgebraicGeometry.strictHenselizationFunctoriality`; the existing helper module
  `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap` supplies its uniquely
  characterized `Scheme.strictHenselizationMap` and `strictHenselizationMap_over`.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn`, `.residueMap`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.

Proof inputs also imported: `WeilConjectures.RingTheory.StrictHenselizationTriples`
(`Scheme.strictHenselization_triples`),
`Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison`
(`Scheme.affineStrictLocalChartMap`, `Scheme.affine_strict_local_ring_comparison`),
`Mathlib.RingTheory.Localization.Defs` (`IsLocalization.lift`, `.ringHom_ext`),
`Sheaf.Paper.StrictHenselizationPointEvaluation`
(`Scheme.strictHenselizationPointEvaluation`),
`Mathlib.CategoryTheory.Limits.HasLimits` (`colimit`, `colimit.desc`), and
`Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic` (`IsLocalRing.notMem_maximalIdeal`).
No dependency interface repair, new node, statement correction, or disputed statement.

Edge cases checked: I=0 and identity closed immersions; nonreduced/nilpotent I;
nonclosed p; arbitrary non-Noetherian A; Ω larger than K; all characteristics;
empty Z (no geometric point, so no instance of the hypotheses); I=top similarly
cannot carry x. Nothing assumes Noetherianity, reducedness, or that Ω=K. All schemes,
chart rings and the geometric field live in one arbitrary universe u as in the
recorded strict-local construction; its presentations use the recorded generalized
interface at `{u,u}`. Every binder is explicit (`autoImplicit false`).

Searches for this exact theorem (launcher msearch.py, group Q41, this item):

- LeanFinder, query `Canonical strict localization map of a closed immersion is
  compatible with affine quotient charts and algebraic strict henselizations`:
  eight hits about ideal-sheaf chart maps, `IsPreimmersion.of_isLocalization`,
  `Scheme.Hom.liftQuotient`, and ordinary open localization; none is this theorem.
- Loogle, query `AlgebraicGeometry.IsClosedImmersion, IsLocalRing`: 0 hits.
- Mathlib grep, query `strictHenselization|StrictHenselization|strict_henselization`
  in `AlgebraicGeometry`: 0 hits.
- LeanSearch, query `Geometric strict henselization of closed subscheme affine
  quotient chart map compatible local quotient map`: eight hits on ordinary
  localized quotients, ideal-sheaf affine charts, and localization/stalk maps;
  none compares geometric strict-local rings and their prescribed map.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for strict-local/closed-chart
  expressions found existing separate chart, functoriality, tensor, and closed
  immersion cartesian modules; none states all simultaneous chart and residue
  compatibilities with this quotient factorization. Searching the exact item id
  in `lean/WeilConjectures` and `lean/Sheaf` found no declaration for it.
- `rg` for `StrictLocalClosedChartRingData|strictLocalClosedChartMap` in Mathlib,
  both project roots and `dag/lean_names_upstream.json`: no name collision.

## Second reading by Q41

Sequential second reading of the node and completed file, performed in this worker
because the dispatcher explicitly prohibits starting other agents. The maintainer's
independent review remains separate. I checked every row above against the actual
signature and record fields. In particular, `hsquare` is the inverse-image chart
hypothesis, not just a commuting square; `hx` fixes p and its residue embedding;
C and D are the chosen geometric colimits; u is the preimage of the prescribed
canonical map; S and Q are the actual ideal quotients; and no invertibility of the
factor map is asserted. The presentation residue maps are tied simultaneously to
the geometric evaluations and the common K, so the residue-identity clause does not
silently choose unrelated residue identifications. The quotient maximal-ideal
clause preserves nilpotents and makes no Noetherian assumption.

The first compile found that R's action on K is not synthesized automatically. The
record now retains that action with its residue tower, which forces exactly the
composite R→κ(p)→K. This changed only its packaging, adding no hypothesis to the
theorem. All theorem proofs remain `sorry`; the helper is a structure with fully
specified fields. No other statement or dependency node is changed.
