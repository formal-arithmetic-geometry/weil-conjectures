## Worker report

The delivery states `AlgebraicGeometry.AdicFormal.supportedBlowup_precision_loss`
in `Sheaf.AlgebraicGeometry.SupportedBlowupPrecisionLoss`. Its only theorem proof
is `sorry`. No mathematical assertion is proved. The accompanying definition node
supplies actual predicates, finite data and fully characterizing equations; it
contains no postponed data or proofs.

The source read is Temkin, *Functorial desingularization of quasi-excellent schemes
in characteristic zero: the non-embedded case*, proof of Lemma 3.3.3, printed p.23,
and §3.3.5. The PDF was opened at the node's exact URL. The original automorphism
chart computation is generalized to the two-map calculation already written out
in the accepted node's seven proof steps. The current blueprint unit was read at
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/_section.md`;
this is a subordinate algebraic tool and does not change the Fourier/perverse unit.
No statement correction is made. The existing item's only changes are `lean` and
the addition of the new definition node to `stmt_deps`.

Hypotheses and clauses, in the order of the existing node:

- Commutative Noetherian A and B: `A B : CommRingCat.{u}` and
  `[IsNoetherianRing A] [IsNoetherianRing B]`. A common universe is only a size
  convention: either ring can be lifted into a universe containing both.
- Principal distinguished ideals: `π : A`, `ρ : B`, and `Ideal.span {π}` /
  `Ideal.span {ρ}` throughout. Completeness AND separation are exactly
  `[IsAdicComplete (Ideal.span {π}) A]` and its B counterpart; this class
  extends both `IsHausdorff` and `IsPrecomplete`.
- Non-zero-divisors: `π ∈ nonZeroDivisors A`, `ρ ∈ nonZeroDivisors B`.
- Finitely generated centers: `H L : Ideal ...`, `H.FG`, `L.FG`.
- The same nonnegative exponent e for both centers: `e : ℕ`, `π ^ e ∈ H`,
  `ρ ^ e ∈ L`; precision `m : ℕ` satisfies `e < m`.
- Continuous homomorphisms: `u v : A →+* B` and the two explicit
  `@Continuous` conditions using the principal-ideal `adicTopology` terms.
- Equality of extended distinguished ideals: the two `(Ideal.span {π}).map ...`
  equalities with `Ideal.span {ρ}`.
- Equality of extended centers: `H.map u = L`, `H.map v = L`.
- Pointwise initial congruence: `∀ a : A, u a - v a ∈ Ideal.span {ρ} ^ m`.
- The displayed formal blowup objects are `affineBlowupSystem A (Ideal.span {π}) H`
  and the corresponding B system. This is the EXISTING completion of the EXISTING
  ordinary global blowup along the extended ideal, not the blowup of A/π^n.
  Ordinary global blowup charts are the dependency `AffineBlowup.chartRing H s`.
  Completing those charts gives the displayed completed chart algebras; the
  module docstring records this identification. The model's rings and sheaves
  are inverse limits of the quotient structure sheaves, via the existing
  `AdicFormal.completion` interface and its source documentation.
- The affine conclusion provides the induced base maps f,g, projections bA,bB,
  and induced blowup maps f',g'. `InducesRingHom` fixes every finite-order base
  map by its equation into Spec A. `IsAffineBlowupProjection` fixes every
  projection the same way. `f' ≫ bA = bB ≫ f`, `g' ≫ bA = bB ≫ g` fix the induced
  blowup maps over their base maps. These are canonical characterizations,
  not arbitrary maps or noncanonical choices of a model.
- Equality on reductions modulo ρ^(m-e): `Congruent f' g' (m - e)`. Reduction
  n is modulo the (n+1)st ideal power, so `Congruent` says EXACTLY equality of
  ALL the induced scheme morphisms through that precision, including the
  structure sheaf maps. Natural transformations already commute with lower
  reductions, so this equals equality at the maximal indicated order.
- The extended distinguished ideal interpretation is encoded by the filtrations
  in all four completion systems and by equality of the extended ideals above.
- The formal-scheme clause (second conjunct) uses arbitrary Noetherian formal
  systems F,G and their existing `IsBlowup` models F',G'. `IsBlowup` includes
  Noetherianity and coherent open centers. `HasPrincipalRegularCharts` expresses
  precisely local principal regular distinguished ideals. `HasCenterExponent`
  expresses containment of their eth powers on formal affine charts.
  `IsAdicMap f/g` expresses equality of extended distinguished ideals by the
  cartesian squares of the actual thickenings. The two `comap` equalities express
  equality of the extended centers. It concludes the uniquely characterized
  induced pair and their congruence at `m-e`. The uniqueness is over the supplied
  base maps; it follows from the formal blowup's canonical mapping property,
  not an unrelated choice of maps. The argument is chartwise and imposes no
  algebraization on F or G and no affineness on chart intersections.
- The automorphism clause (third conjunct) takes `a : F ≅ F`, center preservation
  `(J n).comap (a.hom.app n) = J n`, and `Congruent a.hom (𝟙 F) m`. It gives the
  induced automorphism `a' : F' ≅ F'` over a and its congruence to the identity
  at `m-e`. A natural isomorphism already preserves the specified infinitesimal
  filtration, so no separate adic-map assumption is added here.
- The finite-tower clause (fourth conjunct) uses arbitrary finite precision
  towers S,T, including r=0. `PrecisionTowerMap` retains each induced level map,
  its adic property, its equation with the blowup arrows and the equality of
  every successive extended center. The two towers use the same exponents.
  Congruence at the base gives congruence at `Fin.last r` with precision
  `m - ∑ i : Fin r, T.exponent i`. Natural subtraction includes the zero quotient
  case without a negative ideal power or a lost case.
- Empty centers: center ideal ⊤ satisfies `HasCenterExponent ... 0`; this is
  because I^0=⊤ and its extension is ⊤. These are unit-ideal blowups in the
  existing `IsBlowup` definition and are retained in `PrecisionTower`.
- Flat pullback (fifth conjunct): hS and hT are maps of the actual completed
  formal systems; `IsFlatPullback` uses `AlgebraicGeometry.Flat` at every finite
  order and cartesian squares with the tower arrows. The shared flat adic base
  change `h : Z' ⟶ Z` and its levelwise cartesian comparisons are explicit.
  Both primed maps lie over that SAME Z' structure, and commute with the old
  maps and hS,hT. Consequently these are the canonical pullbacks of the two
  maps, not independently chosen identifications of fibre products. The center
  exponents on the primed towers are unchanged and the conclusion has the
  identical `m - ∑ ... T.exponent` bound. Complete rings are never replaced by
  uncompleted tensor products.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with
  `isNoetherianRing_iff_ideal_fg` verifying the intended meaning.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, `IsAdicComplete`,
  and `IsAdicComplete.le_jacobson_bot` (proof dependency).
- `WeilConjectures.Blowup.Affine.ChartAlgebra`:
  `AlgebraicGeometry.AffineBlowup.chartRing` and its source signature/docstring.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and its
  stalkwise equivalence `Flat.iff_flat_stalkMap`.
- `Sheaf.AlgebraicGeometry.NoetherianAdicFormalSystem` (existing definition node
  `def-per-noetherian-adic-formal-system`): `AffineChart`, `IsNoetherian`,
  `completion`, `affineIdeal`, `inclusion`, `IsBlowup`; the new definition node
  cites this owner, and all new notions use these exact declarations.
- Proof imports: `WeilConjectures.Blowup.Affine.StrictTransformChart`
  (`strictChartMap`); `Mathlib.RingTheory.AdicCompletion.Completeness`
  (`AdicCompletion.pow_smul_top_eq_ker_eval`, together with `evalₐ`,
  `surjective_evalₐ` and `evalₐ_of`); `Mathlib.RingTheory.Localization.Away.Basic`
  (`IsLocalization.Away.lift`, `lift_eq`, `IsLocalization.ringHom_ext`);
  `Sheaf.AlgebraicGeometry.FormalAffinePrincipalRefinement`
  (`adicFormalAffine_principal_refinement`). Their recorded signatures and
  docstrings were read. All stated proof dependencies are imported.
- `lem-per-formal-open-blowup-base-change` has no Lean record in the read clone.
  It is a proof prerequisite, not a missing statement object: the complete
  construction/predicate needed here is already `AdicFormal.IsBlowup`. Its
  future proof import is therefore absent, with the dependency named in the
  seven-step proof docstring for stage 3. No dependency interface was copied.

Searches for an existing statement or definition:

1. msearch leanfinder: “Congruent adic ring maps induce congruent maps on
   supported formal blowups with bounded precision loss”; no supported-blowup
   precision statement. Additional search “adic formal schemes maps equal on
   infinitesimal thickenings and supported blowup center exponent” returned
   eight ordinary scheme factorization/extensionality declarations (recorded
   in the new node), no matching interface.
2. msearch loogle: `AdicCompletion, Ideal.map` and `"blowup"`; no matching theorem
   or formal congruence notion; the latter has zero hits.
3. msearch grep: `blow.?up|congr.*blow`, Mathlib/AlgebraicGeometry; zero hits.
4. msearch leansearch: “formal scheme morphism equality modulo ideal power
   congruence supported blowup tower center exponent”; eight hits, mostly
   quotient-map congruence simplification, no matching formal interface.
5. rg over `lean/WeilConjectures` for the item id: no declaration. Concept searches
   for supported blowups/precision loss found no existing estimate. Searches
   over `lean/Sheaf` located the existing formal interfaces described above.
   `Congruent`, `IsAdicMap`, `HasCenterExponent`, `HasPrincipalRegularCharts`
   are absent in the existing formal-system/tower modules and relevant project
   algebraic geometry modules.
6. DAG searches found precision assertions but no definition of this interface.
   `tools/blueprint_refs.py search 'adic precision'` and `search 'precision'`
   both returned zero blueprint-node matches. `ancestor` returned
   `lem-per-artin-gabber-affine-curve`, retained in the new node's blueprint.

Edge cases and mathematical checks:

- e=0 forces H=L=⊤. Blowup is identity, and the conclusion retains full m.
- m=e+1 gives positive precision 1; the ratio of chart denominators is a unit
  already in the adic completion. No division or cancellation by a potentially
  zero-divisor generator is asserted.
- Principal centers give identity blowups. Empty centers and empty formal
  schemes are permitted; affine covers may be empty in `IsNoetherian`.
- Zero rings are not excluded by a `Nontrivial` hypothesis.
- A zero distinguished generator in a nonzero ring fails the explicit regularity
  hypothesis, exactly as required by the original affine statement.
- Length-zero tower has empty sum 0 and retains the original precision. If the
  total bound reaches or exceeds m, the output precision is 0 and `Congruent`
  is vacuous, matching the empty reduction modulo the unit ideal.
- Characteristic is unrestricted in this algebraic chart computation, as in
  the accepted node; no characteristic-zero or quasi-excellence hypothesis
  from the surrounding desingularization application was added.
- Flat-pullback negative control: without a common base-change structure, even
  pullback squares over a point can differ by a permutation of two points.
  The final clause explicitly fixes a shared Z' structure and the canonical
  equations, ruling out that erroneous interpretation.

Validation: both delivered files compile separately with scompile.py in module
mode, in dependency order, using only the published live library and the private
sibling overlay. The initially misspelled Mathlib non-zero-divisor import was
corrected to `Mathlib.Algebra.Ring.NonZeroDivisors`. The final compile has no
errors or unexpected warnings. Every universe/variable is explicitly bound;
`autoImplicit` and `relaxedAutoImplicit` are disabled.

## New nodes

`def-per-formal-blowup-congruence-data` records congruence through a specified
infinitesimal order, adic maps, numeric center bounds, local principal regular
charts, canonical affine-map/projection characterizations, and finite comparison
data. Its source is the notation and chart computation in Temkin Lemma 3.3.3 and
finite iteration in §3.3.5. Searches are recorded above and in `mathlib_searches`.
It uses the existing `AdicFormal` formal systems and `IsBlowup`, not a second
formal-spectrum or blowup definition. Existing `FormalTower` is over completion
of one specified ordinary scheme; imposing that on arbitrary formal F and G
would add a global algebraizability assumption. Existing ringed-space
`FormalBlowupTower` has a different model and no infinitesimal exponents or maps
between distinct bases. The new `PrecisionTower` is finite bookkeeping of the
already existing infinitesimal objects, retaining their numeric bounds, without
that restriction. Every helper in this definition module has the new node's
source/blueprint docstring and appears in its `lean.declarations` list.

## Second reading by Q20

This is an in-session second pass by the same dispatched worker, not an
independent agent review; the dispatcher explicitly forbids starting agents and
the maintainer supplies the independent delivery review. I reopened the complete
item statement and both final files for the following clause audit.

The first conjunct has both complete Noetherian rings, both regular generators,
both finite centers and both membership bounds; both maps, their continuity,
their equalities on distinguished ideals and centers, and the pointwise mth-order
congruence are present. The induced maps use the actual completions of the actual
ordinary blowups, and the conclusion compares their (m-e)th reductions. The
second conjunct makes the formal-local clause explicit; its hypotheses are the
same objects and center bounds in formal-affine notation. The third conjunct
compares the lifted automorphism with the actual identity. The fourth retains
every ordered center and the zero-length and zero-output-precision cases. The
fifth retains the identical numeric bound under a common completed flat base
change. I found and repaired the initially insufficient identification conditions
on pullbacks: two independently identified pullbacks are not a common base
change. The final clause supplies Z, Z', h, their cartesian squares and equations
over Z' so the induced maps are fixed. No change to the node's mathematical
statement was needed for that repair.

The definition module has no `sorry`, arbitrary data choices, private notions or
local notation. `Congruent` is actual equality of finite-order scheme morphisms;
`HasCenterExponent` is an ideal containment rather than an assumed precision-loss
conclusion. Canonical affine maps are fixed at every order by equations into the
ordinary spectra. The finite tower data use the existing formal-blowup predicate.
The item has precisely one named postponed theorem, with its entire seven-step
proof plan and all the stated proof imports. No STATEMENT-DISPUTED issue remains.
