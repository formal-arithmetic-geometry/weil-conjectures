## Worker report

The module `Sheaf.AlgebraicGeometry.DivisorialSectionChartFactorization` states
`AlgebraicGeometry.exists_divisorial_section_chart_factorization`, with its sole
proof `sorry`. No definition, hypothesis or statement correction is introduced.
The item's node changes only in `lean`.

Source read: ILO, Exposé VI §§1.1 and 1.4, printed p. 69, and Proposition 1.9
proof, printed p. 71 (PDF pages 75–77). Section 1.1 supplies étale-local fs charts;
1.4 supplies exactly the divisorial sections; Proposition 1.9 uses h = εa.
The latest blueprint local-term-locality statement/proof was also read. As the
accepted split records, this is a local logarithmic auxiliary in its historical
ancestry, not a replacement of the current unit's contracting-correspondence route.

Clause-by-clause correspondence:

- The pair (Y,T) is represented by schemes `Y U`, the open immersion `j : U ⟶ Y`,
  and `hU : DenseRange j`; T is its closed complement. This is precisely the
  existing dependency's pair encoding, without any choice of a closed subscheme.
- Local Noetherianity is `[IsLocallyNoetherian Y]`. The divisorial fs log regular
  assumption is `hlog : IsDivisorialFineSaturatedLogRegularPair Y U j hU`.
- M_Y is the prescribed `divisorialSections j`/`divisorialLogPresheaf j` of that
  dependency, rather than a new log structure or an arbitrary monoid sheaf.
- The étale morphism V → Y is `f : V ⟶ Y` with `[Etale f]`.
- The prescribed geometric point is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`
  and `y : Spec (.of Ω) ⟶ V`.
- The finite list is `r : ℕ` and `h : Fin r → Γ(V, ⊤)`; no positivity is assumed.
- Each section's invertibility on V ×_Y U is exactly
  `hh : ∀ i, IsUnit ((pullback.fst f j).appTop (h i))`.
- The conclusion's `W : Y.Etale` is V' as an étale object of Y. The map
  `g : W.left ⟶ V`, `Etale g`, and `g ≫ f = W.hom` say it is a refinement over Y.
  `w : Spec (.of Ω) ⟶ W.left` and `w ≫ g = y` give the pointed lift with exactly
  the prescribed field Ω, not an enlarged algebraic closure.
- `P : Type u`, the explicitly bound `CommMonoid P` structure, and
  `IsFineSaturatedMonoid P` express the fs commutative chart monoid, without
  requiring sharpness or freeness.
- `c : P →* divisorialSections j W` is the chart section map. The universally
  quantified `IsDivisorialStalkChart ... ((divisorialGerm ...).comp c)` imposes
  the actual stalk pushout condition at EVERY geometric point on W, not only
  at the chosen lift. Its first clause is surjectivity of the product of P
  and ring units; its second identifies the kernel with the pushout congruence.
- The existential `hunit` is the proof witness required by this existing chart
  API that all strict-local units belong to the divisorial stalk. It is already
  included in `hlog`, is not an additional input hypothesis, and proof
  irrelevance makes its choice immaterial to the chart predicate.
- `a : Fin r → P` and `ε : Fin r → Γ(W.left, ⊤)ˣ` are the simultaneous choices.
  `∀ i, g.appTop (h i) = (ε i).val * (c (a i)).val` is exactly the required
  section equation. The structural map α is c followed by the existing
  submonoid inclusion into regular functions.

Dependency declarations used, read with their signatures and docstrings:

- `Sheaf.AlgebraicGeometry.LogRegularPair`:
  `IsDivisorialFineSaturatedLogRegularPair`, `divisorialSections`,
  `IsFineSaturatedMonoid`, `strictLocalRing`, `divisorialStalk`,
  `divisorialGerm`, `IsDivisorialStalkChart` (and its actual pushout congruence).
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`;
  the proof also uses its open-immersion, composition and cancellation facts.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, with the recorded inline
  `Spec (.of Ω) ⟶ V` geometric-point convention; `Scheme.SpecToEquivOfField`
  in `Mathlib.AlgebraicGeometry.ResidueField` explains the point/residue encoding.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded node
  explicitly prescribes `Limits.pullback f j` for scheme base change, with
  `pullback.fst` its projection to V. Module base change is irrelevant here.
- Proof-only `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`: base-change
  stability of the étale jointly-surjective precoverage.
- Proof-only `Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `Scheme.exists_fac_of_etale_of_isSepClosed`, preserving Ω. Its
  `Scheme.pointSmallEtale` also supplies the chart's canonical pointed stalk API.

The proof dependency `lem-trf-finite-monoid-stalk-data-spreading` has neither a
Lean record nor a Mathlib match. No import for it exists to add: it is needed
only by the future proof, and all notions in THIS statement are already supplied
by the stated definition dependencies. Its role is fully retained in the proof
docstring. No dependency module or new node is needed for this signature.

Edge cases checked before writing: r = 0 leaves empty functions a and ε and
vacuous factorization equations, but still requires an actual pointed fs chart;
non-sharp fs monoids are allowed; unit sections require no nonunit condition;
there is no nonzero or nonempty-list hypothesis. Empty Y or V has no such
geometric point, so the universal assertion there is vacuous. Empty boundary is
allowed and uses the trivial divisorial structure. There is no affine,
quasi-compact, separated, characteristic or regularity assumption beyond the
node. All schemes, fields, section monoids and chart monoids use the existing
API's universe u. All variables and universes are explicitly bound, with both
autoImplicit options disabled.

Searches for an existing exact statement:

- msearch leanfinder: “Every finite list of divisorial log sections factors etale
  locally as units times monoid chart elements”: eight hits on structure-sheaf
  fractions, ordinary étale presentations and étale loci; no logarithmic theorem.
- msearch leansearch: “A divisorial log section is etale locally a unit times a
  monoid chart element”: eight hits on localization representatives and basic
  open unit restriction; no chart-factorization statement.
- msearch loogle: `"IsDivisorialStalkChart"`: zero hits.
- msearch grep `divisorial|IsDivisorialStalkChart|logRegular` in Mathlib
  AlgebraicGeometry: zero hits.
- rg across both `lean/WeilConjectures` and `lean/Sheaf` for divisorial, chart
  factorization, the item ID, and the proposed declaration name: no exact
  statement. LogRegularPair gives the required definitions;
  NodalEtaleChart has the one-section assertion in a specialized nodal-family
  result with additional hypotheses, not this arbitrary finite-list theorem.
  The DAG upstream-name index likewise has no proposed-name match.

Validation: prescribed scompile.py compiled both sandbox and library forms
successfully (5.7s and 4.2s), with no errors or non-sorry warnings.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q71

Independent maintainer second reading (cc review service, 2026-10-24), replacing the
worker's in-thread self-check. Node clauses → Lean → verdict:

1. Pair (Y,T), T the closed complement of a dense open j : U ↪ Y → `{Y U} (j : U ⟶ Y)
   [IsOpenImmersion j] (hU : DenseRange j)`, the same encoding as the landed
   def-trf-log-regular-pair record. OK.
2. Divisorial fs log regular → `hlog : IsDivisorialFineSaturatedLogRegularPair Y U j hU`
   (Sheaf.AlgebraicGeometry.LogRegularPair). OK.
3. Y locally Noetherian → `[IsLocallyNoetherian Y]` (pqf-def-locnoeth record). OK.
4. M_Y = O_Y ∩ j_*O_U^× → `divisorialSections j W` = units of `Γ(pullback W.hom j, ⊤)`
   pulled back along `pullback.fst`: exactly the sectionwise description. OK.
5. V → Y étale → `f : V ⟶ Y` `[Etale f]` (Mathlib record). OK.
6. Geometric point ȳ : Spec Ω → V → `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]
   (y : Spec (.of Ω) ⟶ V)`, the inline convention of def-weil-geometric-point. OK.
7. h_1..h_r, r = 0 allowed → `(r : ℕ) (h : Fin r → Γ(V, ⊤))`. OK.
8. Each h_i invertible on V ×_Y (Y∖T) → `IsUnit ((pullback.fst f j).appTop (h i))`,
   with `pullback f j` the scheme base change prescribed by def-pc-base-change. OK.
9. Pointed étale neighbourhood V' → V of ȳ → `W : Y.Etale`, `g : W.left ⟶ V`,
   `Etale g`, `g ≫ f = W.hom`, `w : Spec (.of Ω) ⟶ W.left`, `w ≫ g = y` (same Ω).
   `Etale g` is implied but harmless. OK.
10. Chart c : P → M_Y|_{V'} by an fs commutative monoid, stalk-pushout meaning →
    `P : Type u`, `CommMonoid P`, `c : P →* divisorialSections j W`,
    `IsFineSaturatedMonoid P`, and `IsDivisorialStalkChart` for the germ composite at
    every geometric point of W: the same form as `HasDivisorialFineSaturatedCharts` of
    the dependency. The `∃ hunit` binder is a Prop witness required by that API; it is
    contained in `hlog` and proof-irrelevant, so neither stronger nor weaker. OK.
11. a_i ∈ P, ε_i ∈ Γ(V',O)^×, h_i|_{V'} = ε_i α(a_i), α = structure map of c →
    `a : Fin r → P`, `ε : Fin r → Γ(W.left, ⊤)ˣ`,
    `g.appTop (h i) = (ε i).val * (c (a i)).val`; the quantifier order (one chart,
    then a, ε for all i) is the node's. OK.

Edge cases: r = 0 (vacuous equations, chart still required, as in the node); unit h_i;
non-sharp P allowed; empty V (no geometric point, vacuous); empty boundary. No extra
affine/qc/separated/characteristic assumption; all universes u as in the dependency.

Searches: side-live lean/Sheaf and lean/WeilConjectures for `IsDivisorialStalkChart`,
`exists_divisorial_section_chart`, the item id: only LogRegularPair (the defs),
DivisorialLogChart (snc chart, Tag 0BIA), FreeCharacteristicRelativeNCCriterion and
NodalEtaleChart (one-section nodal case) — none states this finite-list factorization.

Docstrings carry the source place, `(blueprint: …)` and the node's four proof steps;
the proof is `sorry`; no new definitions. No mismatch found; nothing in the Lean changed.
