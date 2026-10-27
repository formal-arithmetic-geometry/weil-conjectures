## Worker report

The module `Sheaf.AlgebraicGeometry.TameDiagonalStandardClosedImmersion` states
`AlgebraicGeometry.exists_tameDiagonal_standard_closedImmersion`, with `sorry` as its
whole proof. No theorem is proved. All six supporting definitions have actual data:
they unpack the canonical pointed-stalk maps, the character-kernel lattice and monoid,
the chart-realization data, and the canonical pullback comparison. They belong to this
node's displayed comparison construction and are listed in `lean.declarations`.
The proof docstring includes all fifteen DAG proof steps and their dependencies.
The informal node statement, proof and source are unchanged.

Hypotheses and clauses, in the order of the node:

- Locally Noetherian fs X: `X : FineSaturatedLogScheme.{u}` includes its scheme,
  locally-Noetherian proof, log structure and étale-local fs charts. Finite G and its
  genuine log action are `[Group G] [Finite G]` and `action : FSLogGroupAction G X`.
- A geometric point is `t : Spec (.of Ω) ⟶ X.scheme`, with `[Field Ω] [IsAlgClosed Ω]`.
  The subgroup `H` is specified exactly by `hH`, using equality of geometric-point maps,
  not just equality of underlying points.
- The finite surjective quotient with orbit fibres and invariant structure sheaf is
  `hquot : IsAdmissibleFiniteSchemeQuotient action.baseAction q`. Its definition gives
  finiteness, invariance, quotient topology, orbit fibres and the invariant structure
  sheaf on all opens. Its orbit-in-affine-open clause adds no restriction here: choose
  an affine neighbourhood of q(x); its inverse image is affine since q is finite and
  contains the whole orbit. Similarly finite surjectivity implies quotient topology.
  `[IsNoetherian Y]` is the stated Noetherian hypothesis on Y.
- The invariant log structure is `N : EtaleLogStructure Y` with
  `D : action.InvariantDirectImage q N`, whose section maps are injective, natural,
  structurally compatible and have exactly the invariant sections as image. No fs
  hypothesis is imposed on N; its P-chart on the target neighbourhood is a conclusion.
- The rings A and B are exactly `strictLocalRing X.scheme t` and
  `strictLocalRing Y (t ≫ q)`, the ring-valued pointed-étale colimits. The composite
  `t ≫ q` is the geometric point y-bar. `i` is normalized as their canonical map by
  `hi : IsPointedRingStalkMap ... i`. `hinj` and `hinvariants` say precisely B = A^H.
  `hfinite : i.Finite` is module-finiteness of A over B.
- The ring and monoid stabilizer actions `ρ` and `logActionStalk` are normalized by
  `hρ` and `hlogActionStalk` on every relative pointed-étale test. These are presentations
  of the induced maps, not arbitrary extra actions or assumptions. As for any left
  action on functions, they use inverse pullback; this also agrees with the reversed
  composition convention explicitly documented in `FSLogGroupAction`. Invariants,
  triviality on the stratum, and the available character pairings are unchanged by
  indexing geometric pullbacks by the inverse group element.
- `hn` says n = `Nat.card H` is a unit in A. `hQ` and `hsharp` say Q is fs and sharp.
  `a`, `ha`, and `hcharacteristic` identify the prescribed chart with the characteristic
  monoid at t, using the canonical map `Associates.mkMonoidHom.comp a`.
  `hfixed` says H acts trivially on this characteristic monoid.
- `χ : GrothendieckGroup Q →* (H →* rootsOfUnity (Nat.card H) A)` is exactly a
  bilinear character pairing on H_ab tensor Q^gp: the target is abelian, so each H
  homomorphism factors uniquely through H_ab. No tensor element or character is lost.
  `hroots` fixes all n-th roots of unity and `hdiagonal` is h(a(r)) = χ_r(h) a(r),
  multiplying via the existing canonical `unitsIn` inclusion into the log stalk.
- `hstratum` says h(z)-z belongs to `nonunitIdeal t` for every z. This ideal equals
  (α(a(r)) : r ≠ 1) because a identifies sharp Q with the characteristic monoid and
  is a stalk chart: every log element is a(r) times a unit. Thus this is exactly
  triviality on A/I, with multiplicative `1` representing the node's additive `0`.
- `tameDiagonalLattice χ = χ.ker` is L in Q^gp. `tameDiagonalMonoid χ` is its
  inverse image in Q under the canonical group-completion map, hence exactly Q ∩ L.
  The conclusion produces `b` into B and requires `i.comp b = α.comp a.comp subtype`.
  Injectivity of i makes this b unique, exactly the specified p ↦ a(p).
- The strict-local comparison is a morphism `φ` out of the pushout of
  Z[P] → B and Z[P] → Z[Q] in `CommRingCat`. This is precisely the commutative-ring
  tensor product B ⊗_{Z[P]} Z[Q], without additional chosen algebra structures. Its
  pure tensors are the products of the two pushout injections. The formula for
  every y and r says φ(y ⊗ z^r) = i(y) α(a(r)); these pure tensors generate the
  pushout ring, so the map is completely determined. `Function.Surjective φ`
  is exactly the ring-surjectivity assertion. Taking Spec gives the asserted
  strict-local affine closed immersion, with its prescribed structural maps.
- `c : TameDiagonalChartRealization ...` supplies V and W, the pointed étale
  neighbourhoods of t and t ≫ q, their lifts v and w, and their commuting comparison
  over q. V and W are actual objects of the respective small étale sites; no
  independent étaleness assumption is needed. `source_germ` preserves a verbatim;
  `target_germ` preserves b; `compatible` compares the actual invariant log pullback
  to the source chart, not merely their ring images.
- `c.source_chart` and `c.target_chart` are `IsChart` at every geometric stalk on
  these neighbourhoods. The target of `c.comparison` is exactly
  W ×_{Spec Z[P]} Spec Z[Q], using `chartToSpec`, `mapDomainRingHom`, and `pullback.lift`.
  Give this target the log structure associated to its Q-chart. By construction
  its chart pulls back to `c.chartX`; `c.source_chart` says that this associated
  pullback log structure is precisely the given source log structure. This is
  the strictness clause, expressed by the chart definition rather than choosing
  another log structure or merely asserting an unrelated characteristic isomorphism.
  The final `IsClosedImmersion c.comparison` is the ordinary closed-immersion clause.
- No log regularity or generic-freeness hypothesis or conclusion occurs.

Dependency interfaces opened and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogStructure.IsStalkChart`, `.IsChart`, `.unitsIn`, `.characteristic`,
  `.nonunitIdeal`, `EtalePrelogStructure.stalk`, `.stalkAlpha`, `.germ`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalk` and
  `pointedEtaleGerm`, via the log interface; the ring version is the identical
  pointed-neighbourhood colimit `strictLocalRing` in `LogRegularPair`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField` describes
  geometric points; the inline field-and-map form from its recorded node is used.
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, through `Scheme.Etale`.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `EtaleLogStructure.chartToSpec` and the
  exact comparison construction used by `FSLogChart.comparison`. The existing
  FSLogChart structure itself requires a globally fs target, which is not assumed
  here, so the owning-node realization uses the same construction with arbitrary N.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and
  `pullback.lift`, including the actual chart-square commutativity witness.
- `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction`,
  `FSLogGroupAction.InvariantDirectImage`, and `logInvariantTest`.
- `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient`:
  `IsAdmissibleFiniteSchemeQuotient`. The last two nodes already have usable landed
  records, and are added to stmt_deps under the standing landed-node addition rule.

All already-stated proof dependencies are imported with non-public imports, except
those already needed publicly for the statement. The proof-only
`lem-per-finite-quotient-strict-local-invariants` has no recorded Lean declaration;
no nonexistent import is invented. No downstream local-Kummer-quotient theorem is
imported, and no dependency cycle is introduced.

Edge cases checked mathematically before writing:

- Q trivial: P is trivial, I = 0, and triviality on A/I gives A = B. The chart
  comparison is the expected isomorphism onto the corresponding local piece.
- H trivial: n = 1, all characters are trivial, P = Q and A = B. All root and
  tameness hypotheses have the correct trivial-group interpretation.
- No faithfulness of either action is required; nonabelian H is permitted and
  the pairing factors through its abelianization. Smaller stabilizers away from
  the marked point are covered by `target_chart` at every geometric point.
- Empty X has no geometric point, so the pointwise statement has no invalid
  chosen point. A geometric point rules out the zero ring at its strict local ring.
- Characteristic zero and every residue characteristic prime to n are allowed;
  no prime is separately fixed. The empty generator list for Q trivial is
  covered by proof Step 5's exponent 1. Independent universe v for G is retained;
  schemes, geometric points, monoids and their actual stalks use the existing
  size convention u without forcing site object/morphism universes equal.
- The comparison is only a closed immersion: e.g. the reviewed stage-1 example
  k[x,y]/(x²,y²,xy), with x ↦ -x, can have a nonzero comparison kernel. No
  isomorphism or log regularity is accidentally asserted.

Searches (msearch.py Q116, this item; complete outputs in sandbox searches.jsonl):

- LeanFinder: "A tame finite group diagonal logarithmic chart comparison to a monoid
  base change is a strict closed immersion". Eight hits about ordinary scheme
  diagonals and immersions; no logarithmic chart theorem.
- Loogle: "MonoidAlgebra.lift, Algebra.TensorProduct.lift". No hits for that
  combined query; direct source inspection found `MonoidAlgebra.lift` and the
  ring-pushout API used here.
- Mathlib grep: "LogStructure|LogScheme|Kummer", AlgebraicGeometry. No hits.
- LeanSearch: "Tame finite group diagonal log chart strict closed immersion into
  monoid base change". Eight ordinary scheme closed-immersion/diagonal hits;
  none states the item.
- `rg` on upstream WeilConjectures for `LogStructure|LogScheme|tame_diagonal|tameDiagonal`
  and the exact item id: no item or equivalent statement. Project searches for
  quotient, invariant, diagonal and log-action interfaces found FSLogGroupAction,
  AdmissibleFiniteSchemeQuotient and FSLogSmoothEtale; those are reused above.
- `rg` across Mathlib, WeilConjectures and Sheaf for every proposed declaration
  name returned no collision. The compact-object example is now a withdrawn
  module; its node points to upstream `IsCompactObject`, so current module headers
  and visibility were checked against the active FSLogSmoothEtale module instead.

Source checked directly: ILO PDF pp.80--82 (printed pp.74--76), including 3.4's
pairing, Proposition 3.5(b), and the complete diagram and Nakayama argument in
3.7(b). Also read the current blueprint ancestor in literature/blueprint/latest;
this node is a supporting lemma, not the unit's own statement. No statement fault
or STATEMENT-DISPUTED issue was found.

## Second reading by Q116

Worker self-check only; no separate agent was started, as the dispatch brief
explicitly prohibits it. The maintainer's independent review remains the
independent reading. Reopened the node and the final module and matched each
binder and conclusion as listed above. Checked especially the geometric (not
ordinary) stabilizer, invariant N without a global fs assumption, actual strict
local rings, prescribed germs, the source-chart strictness criterion, and the
pure-tensor formula. Corrected the stalk-action normalization to inverse pullback
so that its left action is compatible with the existing scheme-automorphism
multiplication convention. The initial compile also caught a reserved identifier
and a line-length warning; both were repaired. No informal statement correction,
new DAG definition node, or dependency-record replacement was needed.
