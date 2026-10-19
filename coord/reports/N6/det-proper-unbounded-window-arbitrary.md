## Worker report

The delivery states `det-proper-unbounded-window-arbitrary` in
`Sheaf.Paper.ProperIndConstructibleUnbounded`. Its two theorems are
`AlgebraicGeometry.ProEtale.proper_indConstructible_unbounded` and
`AlgebraicGeometry.ProEtale.proper_indConstructible_unbounded_padicAlgCl`.
Both proofs are exactly `sorry`. No definition, new node, dependency repair, or
statement correction is needed. The node changes only in `lean`.

Read the current blueprint detail statement and unit statement under
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-proper-unbounded-window/`,
the node's six proof steps, all four statement-dependency nodes and their source
modules, the framework manifest, and the stage-2 rules and delivery-errors H.
No maintenance repair note exists for this item.

Hypotheses and clauses, in both coefficient cases:

- “Lambda, p, d as in bounded-below”: `ℓ : ℕ`, `[Fact ℓ.Prime]`, and either
  `E : PadicAlgCl.FiniteIntermediateField ℓ` with
  `Profinite.continuousMapRingObj E`, or `Profinite.padicAlgClRingObj ℓ`.
  These are the canonical condensed rings, including the finite-subextension-valued
  sections of the algebraic closure; neither is replaced by discrete coefficients.
- The standing field hypotheses inherited explicitly from the recorded bounded-below
  dependency are `(k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀]`,
  `hp₀ : 0 < p₀`, and `hpℓ : p₀ ≠ ℓ`.
- `X Y : Scheme.{u}` have `[X.Over (Spec (.of k))]` and
  `[Y.Over (Spec (.of k))]`. Each structure map has `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact`: exactly separated finite type over k.
- The map is `(p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]`.
- `d : ℤ` is unrestricted. `hd` bounds `topologicalKrullDim` of the pullback
  of p along `Spec` of the algebraic closure of each residue field. A nonnegative
  d gives `(d.toNat : WithBot ℕ∞)` and a negative d gives bottom, as in the
  recorded bounded-below theorem. This is the geometric fibre bound, with empty
  fibres of dimension minus infinity; a canonical algebraic closure is enough
  since geometric dimension is invariant under algebraically closed extension.
- “K in Dic arbitrary”: `K : DerivedCategory (pulledBackModuleObjects Λ X)` and
  `hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
  (IsConstantModelConstructible Λ X) ((DerivedCategory.homologyFunctor _ n).obj K)`.
  No boundedness assumption is present. This is the same expanded Dic predicate
  as both recorded bounded-below and ambient-sums declarations.
- “For each q there is N, for n >= N the map is an isomorphism”: the first
  conjunct is `∀ q : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsIso (...)`.
  The arrow is exactly `(DerivedCategory.homologyFunctor _ q).map` applied to
  `(CondensedRing.moduleObjectDerivedPushforward Λ p).map` of
  `((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)`.
  Thus its source is H^q(Rp_*K) and target is H^q(Rp_*tau_ge(-n)K).
  Natural indices agree with the node proof's tower indexed by natural numbers;
  choosing a nonnegative threshold loses no eventual stabilization case.
- “Rp_*K in Dic(Y,Lambda)”: the second conjunct applies the same `ind` predicate
  to every homology object of `(moduleObjectDerivedPushforward Λ p).obj K` on Y.
- “Rp_*Dic^{>=a} contained in Dic^{>=a}”: the third conjunct is
  `∀ a : ℤ, K.IsGE a → (...obj K).IsGE a`.
- “Rp_*Dic^{<=b} contained in Dic^{<=b+2d+1}”: the fourth conjunct is
  `∀ b : ℤ, K.IsLE b → (...obj K).IsLE (b + 2 * d + 1)`.
  The last two conjuncts are ordered as in the recorded bounded-below declaration;
  their order changes neither clause. Together with the second conjunct they
  express the full subcategory inclusions.

Dependency declarations used:

- `det-proper-unbounded-window-bounded-below`:
  `Sheaf.Paper.ProperIndConstructibleBoundedBelow`,
  `AlgebraicGeometry.ProEtale.proper_indConstructible_boundedBelow` and its
  `_padicAlgCl` variant. Both full signatures and proof docstrings were read;
  their standing field, coefficient, scheme and dimension binders are retained.
- `det-ambient-ind-derived-sums`: `Sheaf.Paper.AmbientIndDerivedSums`,
  `AlgebraicGeometry.ProEtale.indConstructibleDerived_sums_and_truncations` and
  its `_padicAlgCl` variant. Its expanded Dic predicate and actual standard
  truncations are reused, rather than introducing a second Dic definition.
- `sk-def-sfb-module-derived-pushpull`:
  `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
  Read its complete definition: it is literally `(lowerStar Λ p).rightDerivedFunctor`.
  This published specialization avoids repeating structural inference and is
  definitionally the direct image in the bounded-below theorem. Also read the
  framework's `ModuleObject/Derived/UpperLowerStar.lean` declarations and description.
- `def-kun-truncations`: `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`.
  Its documentation records the components of this composite node, including the
  canonical derived t-structure. The needed component is Mathlib's
  `CategoryTheory.Triangulated.TStructure.truncGEπ`, in `TruncLTGE.lean`, at
  `DerivedCategory.TStructure.t`. Read its full signature and implementation;
  its direction is identity to lower truncation. The homotopy-colimit component
  is not substituted for a truncation.
- `Sheaf.Paper.ModuleObjects` supplies `pulledBackModuleObjects` through the
  bounded-below dependency. `Sheaf.Paper.CondensedConstantConstructibility`
  supplies the recorded `IsConstantModelConstructible`. `ObjectProperty.ind`
  is Mathlib's replete small filtered-colimit closure. All are reused.
- Stated proof dependencies are imported without `public` when they are not
  already public statement dependencies. They supply module objects, sheaf tensor,
  Grothendieck module sheaves, K-injectives, derived products, derived adjunction,
  triangulated right derivation, left completeness, homotopy-limit transport,
  derived-limit triangles, lower-truncation step triangles, cohomology exact
  sequences, and the existing inverse-limit construction. No downstream window
  theorem is imported, avoiding the proof dependency cycle.

Edge cases checked against the signatures and source proof:

- The zero complex is permitted; all conclusions give zero cohomology and
  invertible zero-to-zero maps.
- Empty X or Y is not excluded. Negative d is retained and forces every
  geometric fibre empty, exactly as in the recorded bounded-below interface.
- d = 0 gives the stated bound b+1; no sharper bound is silently substituted.
- q, a, b range over all integers, including negative degrees; n = 0 is legal
  and casts to integer before negation. No accidental natural subtraction occurs.
- K can be unbounded in both directions. Only its specified cohomology property
  is assumed; no common bound is inserted to make the limit argument easier.
- The two coefficient cases, and arbitrary universe u, are retained. Ind diagrams
  have the fixed coefficient/site universe u+1, as in the dependencies. No fresh
  arbitrary coefficient ring or arbitrary direct-image functor replaces the source.
- The proof threshold is max(0,2d-q+2), so the existence assertion is meaningful
  also for negative d and for every q; it does not require a uniform threshold in q.

Searches for an existing statement, run with the prescribed tools:

- `msearch.py ... leanfinder "proper direct image of unbounded ind constructible
  complexes stabilizes on lower truncations in each cohomology degree"`: eight
  results, including `CochainComplex.quasiIso_πTruncGE_iff`,
  `DerivedCategory.isGE_Q_obj_iff` and support instances. These concern truncation
  itself and do not state proper derived-image stabilization.
- `msearch.py ... loogle "CategoryTheory.Triangulated.TStructure.truncGEπ,
  DerivedCategory.homologyFunctor"`: zero results.
- `msearch.py ... grep 'proper.*trunc|trunc.*proper|indConstructible'
  Algebra/Homology`: zero results.
- `msearch.py ... leansearch "cohomology of proper pushforward of unbounded ind
  constructible complexes stabilizes on lower truncations"`: eight results, all
  concerning cochain truncation quasi-isomorphisms, strict support or augmentation;
  none gives the direct-image statement.
- `rg` over the named Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf`
  trees for proper/truncation and ind-constructibility terms: the bounded-below
  declaration exists and is used. Read `Sheaf.Paper.ProperUnboundedWindow`:
  its unit theorem includes Dic preservation and a finite two-truncation window,
  but does not state eventual stabilization for the canonical single lower
  truncation map; it cites this item in its proof, so importing it would be circular.
- `grep -rn 'det-proper-unbounded-window-arbitrary'` in the upstream source:
  no matches. `rg` for the proposed names in `dag/lean_names_upstream.json`,
  Mathlib, upstream and the side modules: no name clashes.

No statement fault or mathematical dispute was found. The inherited standing
hypotheses are already explicitly in the bounded-below dependency to which the
item refers, so no statement correction is made.

## Second reading by N6

Sequential self-check, with the node and final source open; the dispatcher's brief
forbids starting another agent. Independent review belongs to the maintainer.
Checked both theorem signatures against every hypothesis and every clause listed
above: no bounded-below hypothesis remains, both actual condensed rings are used,
all standing field/scheme/fibre conditions agree with the recorded dependency,
and the first conjunct uses the canonical projection with the correct direction.
Checked that the object under the fourth conjunct is Rp_*K and the bound is
exactly b+2*d+1. No endpoint is replaced by a free object or map. The two theorem
proof docstrings each carry all six node proof steps and retain the Roos-cone
projections used to identify the eventual isomorphism. No mismatch requiring a
statement change was found. Compilation and preflight results are recorded below.

Validation: prescribed `scompile.py N6 det-proper-unbounded-window-arbitrary` passed
with no diagnostics. The sandbox check took 4.8 seconds and the library-path
compile took 13.5 seconds, each below the unchanged 60-second limit. A source
check found exactly two named theorems, exactly two whole-proof `sorry` terms,
no line over 100 characters, a verbatim primary recorded signature, and only
`lean` changed in the item's node copy.

First dry run found a metadata extraction error: a search for the word theorem
started in the proof docstring. Re-extracted the primary signature from its
line-anchored declaration keyword; no Lean statement or mathematical content changed.

The repaired `deliver2.py ... --no-push` returned OK: dry-run commit
`6f827f5ec6` passes maintainer preflight and per-file compilation. This report
records that validation; the final delivery wrapper repeats its required checks.
