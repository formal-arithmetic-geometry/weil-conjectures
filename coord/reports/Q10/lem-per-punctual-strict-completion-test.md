## Worker report

The delivery states `AlgebraicGeometry.Etale.punctual_strict_completion_test` and supplies three transparent helpers for the canonical rings it uses. Every theorem proof in this delivery is `sorry`; the helper definitions contain real data. The earlier partial attempt is retained in the scratch/log files, but its incomplete theorem and obsolete report have been repaired.

Source checked directly with `pdftotext -f 250 -l 250`: ILO XVI, printed page 244, Definitions 3.2.1--3.2.2, the paragraph after Definition 3.2.1, and Proposition 3.2.4. The paragraph gives invariance under strict henselization; the proposition gives invariance under completion for a regular strictly henselian local scheme. Neither assumes excellence.

Hypothesis and clause correspondence:

- A prime ell and A = F_ell: `(ℓ : ℕ) (hℓ : ℓ.Prime)` and the published `IsPunctuallyPureAt ℓ hℓ`. That predicate uses the level-one lifted `ZMod (ℓ ^ 1)` coefficient ring, canonically F_ell in the coefficient universe.
- Ordinary small-etale derived categories, finite Tate twists, the Kummer fundamental-class map, and its being an isomorphism: the existing `Sheaf.AlgebraicGeometry.PunctualPurity` definition `AlgebraicGeometry.Etale.IsPunctuallyPureAt`. Its `punctualPurityClassMap` is the adjunction transpose of `regularImmersionClasses`, with the exact-direct-image comparison and fully faithful inclusion of D+ into D. Its existential d is tied to `ringKrullDim` by equality, and its local closed immersion is `Spec.map (W.residue w)`. `IsPunctuallyPure` in that same module is the all-points clause. These definitions are reused, not redefined.
- The regular Noetherian local ring R: `(R : Type u) [CommRing R] [IsRegularLocalRing R]`. The regular-local class extends both `IsLocalRing` and `IsNoetherianRing`.
- Invertibility of ell: `(hℓR : IsUnit (ℓ : R))`.
- The fixed separable closure of k = R/m: `(K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]`.
- The actual strict henselization: `punctualGeometricPoint R K` is induced by R -> k -> K -> AlgebraicClosure K; `punctualStrictRing R K` is exactly `Scheme.strictHenselizationRing` at that point. Embedding K in its algebraic closure supplies the algebraically closed geometric point required by the recorded interface; its separable algebraic subextension over k remains K. No arbitrary ring model or comparison map is assumed.
- Completion at the maximal ideal: `punctualStrictCompletion R K` is literally `AdicCompletion` of that strict-henselization colimit at its maximal ideal. The local-ring proof is `Classical.choose (strictHenselizationLocalStructure ...)`, a proof of a proposition about the fixed ring, with no choice of ring data.
- Both canonical rings are Noetherian regular local: the existential witnesses `_hC` and `hB : IsRegularLocalRing ...` in the conclusion, not extra hypotheses.
- Their dimensions equal dim R: the first two displayed equalities of `ringKrullDim`.
- B is complete and strictly henselian: the `IsStrictlyHenselianLocalRing` and `IsAdicComplete` conjuncts, with the maximal ideal computed from `hB.toIsLocalRing` explicitly.
- Its residue field is the chosen separable closure: `Nonempty ((@IsLocalRing.ResidueField ... hB.toIsLocalRing) ≃+* K)`. This is an identification of already constructed fields, not the definition of either field.
- The closed-point purity equivalence: the final iff applies the same recorded predicate to `Spec R` and `Spec (punctualStrictCompletion R K)` at their actual `IsLocalRing.closedPoint` points.
- No excellence hypothesis: no `IsExcellent`, G-ring, or regularity assumption on the completion map occurs.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded ordinary `DerivedCategoryModule`, `DerivedCategory.Plus`, and homology encoding (current source read with `scompile.py --source`).
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `AlgebraicGeometry.Scheme.finiteEtaleTateTwist`, via the recorded class calculus and punctual-purity module.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`; the local ring assumption uses Mathlib's recorded `IsRegularLocalRing`.
- `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`: `RegularImmersionClassFamily` and `regular_immersion_class_calculus`, through the existing punctual-purity class map.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and `Scheme.residue`, through that same predicate; `IsLocalRing.ResidueField` and `IsLocalRing.residue` construct the geometric closed point.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `AlgebraicGeometry.Scheme.strictHenselizationRing`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.LocalRing`: `AdicCompletion` and `IsAdicComplete`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.
- `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`: `AlgebraicGeometry.strictHenselizationLocalStructure`. Added its existing, landed node `lem-weil-pbc-strict-henselization-local-structure` to stmt_deps to supply locality of the recorded colimit, rather than assuming that it is definitionally the upstream colimit.
- `Sheaf.AlgebraicGeometry.PunctualPurity`: `IsPunctuallyPureAt`, `IsPunctuallyPure`, `punctualPurityClassMap`. Added its existing, landed node `def-per-punctual-purity` to stmt_deps. It gives exactly the definitions in the first paragraph of this item. No new definition node or dependency module is delivered.

The recorded proof-dependency modules are imported without `public` where only the proof uses them. The theorem docstring carries all five DAG proof steps, including the explicit supported-cohomology comparison, naturality of the support long exact sequences, flat class compatibility, and the zero-dimensional case. Mathlib-only proof dependencies are available through the existing imports; no missing unstated proof prerequisite was replaced by an assumption.

Edge cases checked: dimension zero (R is a field, the completion of its separable closure is the same field, the closed-point class is the identity); imperfect residue fields (the geometric point is taken in AlgebraicClosure K, while the residue field asserted is K, not that algebraic closure); arbitrary positive dimension; both residue characteristics zero and p different from ell; ell equal to the residue characteristic is excluded precisely by hℓR. The zero ring is excluded by the source's local-ring hypothesis. No nonempty punctured-spectrum assumption is imposed. Universes are explicit, the coefficient category is the recorded u+1 lift, and autoImplicit is disabled.

Searches retained from the earlier attempt (`searches.jsonl`): msearch LeanFinder, query 'Closed-point etale purity is invariant under completion of the strict henselization of a Noetherian regular local ring', returned eight etale/local-algebra results and no completion test; Loogle, query 'IsRegularLocalRing, AdicCompletion, IsStrictHenselization', returned no match (last identifier unknown); msearch grep 'PunctuallyPure|punctual.*purity|strict.*completion' returned unrelated adic-completion/valuation results. Fresh `rg` of WeilConjectures and lean/Sheaf for the completion theorem/helpers found no existing completion test, and found Q03's published PunctualPurity module. Its full source and node were read and its definitions reused. The original item has no repair-note file in coord/repair-notes.

Validation: prescribed scompile.py checked the final module both as a sandbox file and at its library module path, exit 0, no warnings (7.3 s and 5.9 s respectively). The previous finite-Tate-overlay failure no longer occurs for this packet. The actual colimit interface required its existing local-structure theorem; an attempted use of the upstream instance correctly failed because the two colimit presentations are not definitionally equal.

## Second reading by Q10

Author self-check for the remote direct-delivery protocol; independent mathematical review remains the maintainer's. I reopened the natural node, ILO page 244, the final Lean module, and the reused punctual-purity definition. The retained draft had two concrete defects: B was arbitrary and unrelated to R, and the recorded signature included the := delimiter. Both were repaired. A fresh repository search also found a punctual-purity definition, so the draft's private copies of that notion and its class map were removed.

The final theorem quantifies the chosen separable closure explicitly and defines both rings from it. Regularity/Noetherianity, dimension, completeness, strict henselianity and the residue-field identification are conclusions. The purity iff is at the two actual closed points and uses one common predicate, preserving the specified Kummer sign and map. There is no extra geometric hypothesis or replacement of completion by an arbitrary strictly henselian ring. The three helper bodies are real constructions; the only choice selects a local-ring proof for a fixed ring. The dimension-zero and imperfect-field cases remain included. No natural statement was changed, no new node or dependency repair is needed, and no STATEMENT-DISPUTED issue remains.
