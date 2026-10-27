## Worker report

Item: `lem-trf-polynomial-log-chart-regularity`, group Q61, stage 2.
Module: `Sheaf.AlgebraicGeometry.PolynomialLogChartRegularity`.
Main declaration: `AlgebraicGeometry.polynomial_log_chart_regularity`.

The module states the complete polynomial-chart assertion with one `sorry`, as the
whole proof of the main theorem. Its seven helper definitions have real data. They
compose existing polynomial, monoid, stalk, ideal and spectrum maps; they do not
introduce a second log structure, group completion, characteristic, regularity
predicate or strict henselization. This repairs H2 on returned head
`800b572ba266`: the previous version cited two theorem nodes merely to reach their
plain helper definitions. The repair adds two definition nodes owning those existing
helpers, cites them and `def-trf-log-regular-pair`, and drops both theorem nodes from
statement dependencies. No dependency module or mathematical statement correction
is needed. The entire Lean source, including the signature, remains unchanged.

Sources read: the actual ILO PDF, Exposé VI 1.1--1.2 and 1.8--1.9, printed pp.69--71
(PDF pages 75--77), and Stacks `algebra.tex`, the lemmas
`lemma-flat-over-regular-with-regular-fibre` (031E) and
`lemma-dimension-base-fibre-equals-total` (00ON). ILO uses strict localizations in
1.2, and étale log structures and locally Noetherian schemes throughout 1.1.
The polynomial details are the agent expansion in the node's five proof steps,
not a quotation of a polynomial lemma separately stated in ILO.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
| --- | --- |
| Affine base `Y = Spec C` | `C : Type u`, `[CommRing C]`, and the actual scheme `Spec (.of C)` throughout. |
| Locally Noetherian base | `[hN : IsLocallyNoetherian (Spec (.of C))]`. |
| The fs log structure on the base | `M : EtaleLogStructure (Spec (.of C))` and `hfs : M.IsFineSaturated`. Its sheaf, structure map, and unit condition are the recorded dependency's structures. |
| Base log regularity in the stratum-and-dimension sense | `hreg : (FineSaturatedLogScheme.mk (Spec (.of C)) hN M hfs).IsLogRegular`. This is exactly the recorded definition, not a new predicate. |
| Fs chart monoid P | `P : Type u`, `[CommMonoid P]`, `hP : IsFineSaturatedMonoid P`. Multiplicative notation implements the source's componentwise additive notation. |
| Global chart `P → M_Y` | `cY` has target the monoid sheaf at the final étale object; `hcY` uses `M.IsChart`. |
| Structural map `α : P → C` | `α : P →* C`; `hα` equates its image under the canonical `ΓSpecIso.inv` with the image of `cY` under `M.alpha`. |
| Integer `r ≥ 0` | `r : ℕ`, with no positivity or nonemptiness assumption. |
| `W = Spec C[t_1,...,t_r]` | Exactly `Spec (.of (MvPolynomial (Fin r) C))`; no abstract smooth scheme substitutes for W. |
| `R = P ⊕ ℕ^r`, componentwise addition | `P × Multiplicative (Fin r →₀ ℕ)`. The finitely supported functions on a finite index set are precisely all `r`-tuples; product multiplication is componentwise addition in the source's convention. |
| Associated log structure on W | `N : EtaleLogStructure W`, its global chart `cW`, and `hcW : N.IsChart ... cW`. The dependency defines `IsChart` by the associated-log pushout on every geometric stalk, so this is the source's specified associated log structure presented by its chart. No fs or regularity property of N is assumed. |
| Image of `(p,n)` is `α(p) ∏ t_i^n_i` | `hβ` identifies the structural image of every `cW q` with `ΓSpecIso.inv (PolynomialLogChart.structuralMap α r q)`. The latter is `C(α(p))` times Mathlib's `monomialOneHom` on n, composed via `MonoidHom.coprod`. |

Quantifying over a log structure with the prescribed chart gives the assertion for
the associated log structure independent of any chosen construction: `IsChart` is
exactly the associated-log identification specified in the dependency node. This
neither requires fsness of W as input nor replaces a canonical associated structure
by an arbitrary map or `Nonempty` choice. Existence and the associated-log universal
property are already stated in the proof dependency
`lem-trf-associated-log-universal-stalks` and imported privately.

Clause-by-clause correspondence (below write A, B, I, J, K only as explanatory
names; the Lean signature spells out all terms and contains no `let`):

| Node | Lean |
| --- | --- |
| W is locally Noetherian fs log regular | The conclusion supplies `hNW : IsLocallyNoetherian W` and `hfsW : N.IsFineSaturated`, followed by `(FineSaturatedLogScheme.mk _ hNW N hfsW).IsLogRegular`. These witnesses are proofs, not choices of ring or sheaf data. |
| Every pair of compatible geometric points | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ W) (y : Spec (.of Ω) ⟶ Spec (.of C)) (hy : w ≫ Spec.map ... = y)`. This also retains arbitrary displayed compatibility with y, rather than only a syntactically composite point. |
| Strict local rings A and B | Exactly `Scheme.strictHenselizationRing y` and `Scheme.strictHenselizationRing w`, the recorded colimits of affine pointed neighbourhoods. |
| Nonunit ideals I and J | `PolynomialLogChart.nonunitIdeal M y` and `... N w`, defined by mapping the existing `EtaleLogStructure.nonunitIdeal` under `strictLocalRingStrictHenselizationIso`. Thus they are the images of actual nonunit log germs, not ideals chosen to make the formula hold. |
| Coordinates `t_i` in B | `PolynomialLogChart.coordinate w i` applies the structural strict-localization map on global sections to the actual polynomial variable, with the canonical `ΓSpecIso` identifications. |
| `K = {i : t_i ∈ m_B}` | `PolynomialLogChart.vanishingCoordinates w` is exactly `Finset.univ.filter` by that membership. |
| Canonical characteristic identification `Mbar_W ≅ Mbar_Y ⊕ ℕ^K` | The existential multiplicative equivalence `e : N.characteristic w ≃* M.characteristic y × Multiplicative (vanishingCoordinates w →₀ ℕ)`. Its following equation sends every chart image `(p,n)` to the base chart image of p and the restriction of n to K (`Finsupp.subtypeDomain`). This prescribes the canonical map on all chart generators and kills exactly the invertible coordinates; it is not a bare unrelated isomorphism. |
| Canonical `A → B` | The quantified `φ` is immediately equated to the existing `strictHenselizationRingMapAlong` for the actual polynomial projection, y, w and hy. Thus there is no freedom in φ. |
| `J = IB + (t_i : i ∈ K)` | Equality with `Ideal.map φ I ⊔ PolynomialLogChart.coordinateIdeal w`; the latter is the span of exactly the coordinate images indexed by K. |
| A and B are Noetherian local rings | Explicit `IsNoetherianRing` and `IsLocalRing` clauses for both strict henselization rings. |
| `A → B` flat and local | `RingHom.Flat φ ∧ IsLocalHom φ`. `RingHom.Flat` is the recorded definition of flatness of the target module via the displayed map. |
| Canonical quotient map `A/I → B/J` | `∃ hIJ : I ≤ Ideal.comap φ J`, followed by `Ideal.quotientMap J φ hIJ`. The inclusion is a conclusion supplying well-definedness of the specified map, not an extra hypothesis. |
| Quotient map is a flat local map of Noetherian local rings | The four explicit Noetherian/local clauses for A/I and B/J, followed by `RingHom.Flat (Ideal.quotientMap ...)` and `IsLocalHom (Ideal.quotientMap ...)`. |
| Regular first closed fibre `F = B / m_A B` | `IsRegularRing (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A))`. |
| Regular second closed fibre `F_K = B / (m_A B + (t_i : i ∈ K))` | `IsRegularRing (B ⧸ (Ideal.map φ (IsLocalRing.maximalIdeal A) ⊔ coordinateIdeal w))`. |
| The latter really is the quotient map's closed fibre | A ring equivalence from `B ⧸ (J ⊔ Ideal.map φ (maximalIdeal A))` to the displayed F_K, with `∀ b, E (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b`. Together with the quotient-map formula this identifies the closed fibre over the residue field of A/I. The formula fixes every class, and therefore specifies the canonical comparison. |
| `dim F = dim F_K + |K|` | The first `ringKrullDim` equality, with `(vanishingCoordinates w).card`. |
| `B/J` regular | The explicit final `IsRegularRing (B ⧸ PolynomialLogChart.nonunitIdeal N w)`. |
| `dim B = dim(B/J) + rank_Z Mbar_Y^gp + |K|` | The final equality uses `ringKrullDim`, `(M.characteristicRank y : WithBot ℕ∞)`, and the actual finite-set cardinality. The recorded `characteristicRank` is rational dimension of the characteristic group completion. |

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `EtaleLogStructure`, `EtalePrelogStructure.germ`, `IsChart`, `IsFineSaturated`,
  `characteristic`, `characteristicRank`, `nonunitIdeal`, `FineSaturatedLogScheme`,
  `FineSaturatedLogScheme.IsLogRegular`.
- Explicitly added definition dependency `def-trf-log-regular-pair`, module
  `Sheaf.AlgebraicGeometry.LogRegularPair`: `IsFineSaturatedMonoid`, `strictLocalRing`,
  and the structural stalk convention. Its recorded declarations include the actual
  ring-valued étale stalk needed by the new comparison definition node.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` / `Mathlib.AlgebraicGeometry.ResidueField`:
  `IsAlgClosed` and the geometric-point presentation recorded with
  `Scheme.SpecToEquivOfField`. Points themselves use the recorded inline convention.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`; its definition and colimit property were read.
  `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`, characterized by its neighbourhood legs.
- New owner `def-trf-strict-local-ring-affine-colimit-comparison`, existing module
  `Sheaf.AlgebraicGeometry.LogRegularCompletedChart`:
  `strictLocalRingStrictHenselizationIso`, whose full construction is the canonical
  comparison of the ring-valued geometric stalk and affine representative colimit.
  Only that existing helper is used; its definition now has a definition-node owner.
  The surrounding completed-chart theorem is not a statement dependency.
- New owner `def-trf-strict-henselization-local-ring-maps`, existing module
  `Sheaf.TraceFormula.SmoothGeometricStalkAlgebra`:
  `strictHenselizationLocalRing`, `strictHenselizationRingMap`, and
  `strictHenselizationRingMapAlong`. The full definitions and docstrings were reread.
  The map and local-ring instance occur in the signature; the surrounding theorem
  `smooth_geometric_stalk_algebra` remains only the original proof dependency.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularRing`, `IsRegularLocalRing`.
  These are the ring clauses of `def-weil-regular-scheme`'s retained `mathlib_match`.
  No scheme-regularity assertion is used, so no copy of `IsRegularScheme` is made.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, definitionally target-module
  flatness via `φ.toAlgebra` (and `Module.Flat` from the same dependency record).
- Mathlib also supplies `MvPolynomial`, `C`, `X`, `monomialOneHom`, `MonoidHom.coprod`,
  `Multiplicative`, `Finsupp.subtypeDomain`, `Associates.mkMonoidHom`, `Ideal.map`,
  `Ideal.span`, and `Ideal.quotientMap`; none are redefined.

Proof-only imports follow the DAG: Mathlib's affine space, finite-type and Noetherian
modules; `AssociatedLogUniversalStalks`; upstream `Morphisms.Smooth`;
`RegularLocalOfFlatWithRegularClosedFiber`; and Mathlib `KrullsHeightTheorem` for
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`. The face-localization
proof dependency currently has no `lean` record or Mathlib match and therefore has
no module to import. It is not needed to type this statement, and no new theorem
is postponed on its behalf here.

Edge cases checked mathematically before and after writing:

- `r = 0`: `Fin 0` is empty; its free monoid is trivial, K is empty, the coordinate
  ideal is zero, and both displayed dimension formulas reduce to the base case.
- `K = ∅` with positive r: every coordinate is a unit in B, the free characteristic
  factor is trivial, J is IB, and the two closed fibres agree canonically.
- All coordinates vanish: K is the full index set and its free characteristic
  factor has rank r; the coordinate-zero fibre formula has the expected r shift.
- Trivial base characteristic, one variable over a field: at the origin the
  formula is `1 = 0 + 0 + 1`; at the generic point it is `0 = 0 + 0 + 0`.
- Empty base: no `[Nontrivial C]`, field structure on C, positive dimension, or
  existence of a geometric point is imposed. The zero ring and its empty spectrum
  remain allowed. The polynomial spectrum is then also empty.
- No characteristic restriction, reducedness hypothesis, or maximality assumption
  on the polynomial point is present. Geometric fields and chart monoids range in
  the same ambient universe as the library's scheme/stalk interfaces; any input
  data can be placed in a common larger universe. No universe equality binder is
  added to the mathematics.

Searches for reuse (2026-10-24):

- `msearch.py ... leanfinder "Polynomial extension with logarithmic coordinate boundary
  over an fs log regular scheme is log regular with characteristic monoid and nonunit
  ideal formulas"`: 8 hits, ordinary smoothness/standard-smooth declarations only.
- `msearch.py ... loogle '"LogRegular"'`: 0 hits.
- `msearch.py ... grep 'LogRegular|IsLogRegular|characteristicMonoid' AlgebraicGeometry`:
  0 Mathlib hits.
- `msearch.py ... leansearch "Polynomial extension of fs log regular scheme with extra
  coordinate log generators remains log regular"`: 8 hits, algebra-generator extension,
  `Polynomial.isRegular_X`, and ordinary formal smoothness; no logarithmic assertion.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `PolynomialLog`, polynomial/log/chart combinations, and the proposed declaration:
  no exact theorem. Related `LogSmoothLogRegular` is the consuming broader theorem,
  not the full local polynomial-characteristic and stratum formula. `grep -rn` for
  this node's exact id in `lean/WeilConjectures` returned no attachment.
- Further `rg` searches for `strictLocalRing`, `strictHenselizationRing`, germ and
  coordinate declarations located the reused completed-chart comparison and smooth
  geometric-stalk map. The existing affine-space-coordinate helper takes an abstract
  affine-space isomorphism and ULift indices. Here the coordinate is the actual
  `MvPolynomial.X` on the specified polynomial spectrum; the helper merely composes
  its canonical global-section and strict-localization maps.

Compilation: `scompile.py Q61 lem-trf-polynomial-log-chart-regularity <file>` passed
both sandbox and module-name compiles (7.7 s and 2.6 s on the successful run), with
no errors or unexpected warnings. Initial definition elaboration required marking
`structuralMap` noncomputable (Mathlib's Finsupp instance) and giving classical
membership decidability locally to `vanishingCoordinates`; both were repaired.
There are no diagnostic commands, axioms, private definitions, local instances,
file-local notation, proofs of new theorems, or unbound implicit variables.

## Second reading by Q61

This is the author's second pass with the node and complete module reopened; the
dispatcher explicitly forbids subagents, and the maintainer supplies the independent
review. I checked the ILO source as well as the original node rather than relying
on the informal description of the desired theorem.

I matched each hypothesis and conclusion in the tables above. In particular,
`hcW` is only the definition of the stated associated log structure, while fsness
and log regularity of W occur solely in the conclusion. Both chart structural
maps are tied to the actual rings by `hα` and `hβ`. The equivalence is specified on
all chart elements; exponents outside K disappear by explicit restriction.
The local homomorphism cannot vary because of its equality to the published
canonical map. The ideal is transported from the real log nonunit ideal.
The quotient map's inclusion witness is concluded, not assumed.

The first pass stated regularity of the displayed F_K but did not separately
spell out its identification with the quotient map's closed fibre. I added the
ring equivalence fixing every quotient class. This expresses the node's
"closed fibres" clause and does not add an unrelated isomorphism. I also removed
an unused canonical base-map helper before the successful compile. The final
pass found no missing clause, strengthened hypothesis, changed object, excluded
edge case, hollow construction, or statement fault. No STATEMENT-DISPUTED flag is
needed. The item statement and proof remain unchanged. The previous pass missed
H2: the additional theorem-node dependencies did not give definition-node ownership
for the helpers. The repaired version replaces those edges with definition-node
edges and adds the missing `def-trf-log-regular-pair` edge.


## Repair of returned H2

Return: L's immutable-head review of `800b572ba266` accepted the mathematics,
universes, edge cases, docstrings and sorry-only proof, but required definition-node
ownership for the canonical helper declarations. I repaired that exact point:

1. Added `def-trf-strict-local-ring-affine-colimit-comparison` with an
   `existing: true` attachment to
   `AlgebraicGeometry.strictLocalRingStrictHenselizationIso` in
   `Sheaf.AlgebraicGeometry.LogRegularCompletedChart`.
2. Added `def-trf-strict-henselization-local-ring-maps` with an `existing: true`
   attachment covering `strictHenselizationLocalRing`, `strictHenselizationRingMap`
   and `strictHenselizationRingMapAlong` in
   `Sheaf.TraceFormula.SmoothGeometricStalkAlgebra`.
3. The item cites both new definition nodes and `def-trf-log-regular-pair`.
   It no longer cites `lem-trf-log-regular-completed-chart` or
   `lem-trf-smooth-geometric-stalk-algebra` in `stmt_deps`. The latter remains in
   its original `proof_deps`. Existing public module imports are retained because
   those same published modules supply the definitions now owned by the new nodes.
4. Compared the returned sandbox node with current main: only `lean` and
   `stmt_deps` differed. Rebuilt the repaired item from the current-main node,
   retaining every other field, and reapplied the unchanged Lean record plus the
   corrected definition edges. The authorized delivery wrapper refreshes and bases
   the eventual delivery on current main without direct Git mutations here.
5. Checked that the source's extracted main signature is identical to the node's
   `lean.statement`. The unchanged module has SHA256
   `13d36781ed1314a00cb80f47cf1e852678f4523204345680e9f92278c0d55e18`.

The two new nodes contain no theorem proofs or new Lean modules. Their records point
to existing full-data definitions; there is no duplicated declaration, replacement
canonical map, strengthened hypothesis, or change to the returned signature.
Both have `import_flags: []`: a traversal from current targets and former targets
through statement/proof dependencies reaches this item and hence the new nodes.
Their blueprint ancestor is `lem-trf-local-term-locality`, as printed by
`tools/blueprint_refs.py ancestor lem-trf-polynomial-log-chart-regularity`; their
`via` chains prepend the item to its existing chain.

## New nodes

`def-trf-strict-local-ring-affine-colimit-comparison`: defines the canonical ring
isomorphism from the ring-valued étale geometric stalk to the affine pointed-
neighbourhood strict-henselization colimit. Its sources are Stacks 04HX and 03PS,
read in `etale-cohomology.tex`, especially the proof's restriction to cofinal affine
pointed neighbourhoods. It cites the existing geometric-point, log-regular-pair
(stalk), and strict-henselization-limit nodes. Its existing declaration's construction
first identifies the point fibre with the full colimit, then restricts to the
cofinal affine diagram and its chosen small representatives. This preserves germs
of every regular function. The new node records that exact construction, without
requiring log regularity or a completed chart. The LeanSearch query about the
canonical étale-stalk/affine-colimit comparison returned eight ordinary structure-
sheaf localization results, Loogle `"strictHenselization"` returned zero, and the
Mathlib grep of the four helper names returned zero. Project grep found the exact
existing definition in `LogRegularCompletedChart`; the parsed full DAG definition
records had no owner for it. `blueprint_refs.py search` on the declaration names
returned zero blueprint nodes. The complete search outputs are in
`mathlib_searches`. Reuse is therefore recorded with `existing: true`, with no new
module and no dependence on the surrounding completed-chart theorem.

`def-trf-strict-henselization-local-ring-maps`: defines the canonical local-ring
structure on each recorded strict henselization and the contravariant ring map
induced by a scheme morphism, including equality transport to a separately named
compatible geometric point. Its sources are Stacks 03PS (definition and subsequent
functoriality paragraph), 04HX, and 04GU, read in `etale-cohomology.tex` and
`algebra.tex`. It cites the existing geometric-point, strict-henselization-limit,
and strict-henselization-structural-map nodes. The map's full existing definition is
the global-section pullback of `Scheme.strictHenselizationMap`, conjugated by
`ΓSpecIso`; the Along variant is exactly equality transport. The existing local
instance is `Classical.choose (strictHenselizationLocalStructure s)`, a choice of a
proof of `IsLocalRing`, not data for a new ring. Its statement imposes no smoothness,
flatness or Noetherianity assumption. LeanSearch and LeanFinder queries about
canonical strict-henselization local rings/maps returned eight ordinary local-ring
and residue-map results each. Mathlib grep found no exact helper. Project grep
found the existing definitions in `SmoothGeometricStalkAlgebra`; a full parsed
DAG-definition scan and blueprint-name search found no owner. Complete search
outputs are in `mathlib_searches`. The new node attaches all three existing names
with `existing: true`, so the theorem now refers to a definition node for them.

Second reading of the repair: I reopened both new node records and the full source
of all four owned definitions. The comparison direction is stalk to affine colimit,
the map direction is base strict henselization to source strict henselization,
and the point compatibility is precisely the one in `hy`. Neither new statement
asserts smoothness or the surrounding theorem's conclusion. Their listed
`stmt_deps` are exactly their bracket citations. The new definition nodes have
empty proof lists, null Mathlib matches, all three search kinds, the prescribed
created/blueprint/lean-audit fields, the item's chapter and unit, and existing
records without files. The source signatures in the new `lean.statement` records
were extracted verbatim up to `:=`. No independent second agent was started,
following the dispatcher instruction; this is the author's repair rereading for
L's subsequent independent review.
