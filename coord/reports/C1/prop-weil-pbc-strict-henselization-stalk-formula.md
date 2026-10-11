## Worker report

The module `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula` states the strict-henselization stalk formula. Its hypotheses render a morphism `f : X ⟶ S` with `[QuasiCompact f]` and `[QuasiSeparated f]`, an algebraically closed field geometric point `s : Spec (.of Ω) ⟶ S`, a sheaf `F` of abelian groups on `X`'s small etale site, and `q : ℕ`. The first conjunct is a `Nonempty` categorical isomorphism from the geometric stalk of the degree-q homology of `R⁺f_*F` to `H^q` on the pullback to the strict henselization, using `Scheme.pointSmallEtale`, `rightDerivedLowerStarPlus`, `cohomology`, `strictHenselizationStructuralMap`, `pullback.fst`, and `upperStar`.

The second clause quantifies a bounded-below derived object `K` and every integer `n`; it states an isomorphism between the stalk of the n-th homology of `R⁺f_*K` and the n-th cohomology of the derived pushforward to the strict henselization of the exact inverse-image of `K`. This is the cohomology-group formulation of the source's derived `D⁺` isomorphism, with `mapDerivedCategoryPlus` used for the exact inverse-image functor.

Dependencies used: `Sheaf.AlgebraicGeometry.StrictHenselizationRestriction` (strict henselization scheme and structural map, `Scheme.strictHenselizationScheme`, `Scheme.strictHenselizationStructuralMap`, and canonical restriction infrastructure); `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` (`AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`); `WeilConjectures.SixFunctors.Etale.Derived.GlobalSections` (`AlgebraicGeometry.Etale.rightDerivedGlobalSections`); `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (`AlgebraicGeometry.Etale.upperStar`); Mathlib's `CategoryTheory.GrothendieckTopology.Point.sheafFiber` via `Scheme.pointSmallEtale`.

Edge cases checked: `q = 0`; arbitrary integer `n` in the derived clause (including negative degrees); zero sheaves and zero derived objects; arbitrary algebraically closed geometric residue field in the prescribed universe; no torsion restriction was added because the node statement supplies the only stated sheaf hypothesis. The strict-henselization pullback is used with both projections, so the source and target schemes are kept distinct.

Searches made: `msearch.py ... leanfinder "stalk of higher direct image etale sheaf equals cohomology over strict henselization"` (no matching declaration); `msearch.py ... loogle "CategoryTheory.GrothendieckTopology.Point.sheafFiber"` (Mathlib point-fibre infrastructure only); `msearch.py ... grep "strictHensel|StrictHensel|stalk.*cohomology" AlgebraicGeometry` (no formula); `rg` over `WeilConjectures` and `lean/Sheaf` for strict-henselization stalk formulas (only the existing generic restriction and Gm specialization). The search records are in `searches.jsonl`.

STATEMENT-DISPUTED: the blueprint calls the second comparison a canonical isomorphism in `D⁺(Ab)`, while the available landed APIs do not provide a derived stalk functor for `sheafFiber` (no `Additive` instance). The Lean statement records the equivalent degreewise cohomology isomorphisms for every integer degree, avoiding an extra hypothesis or an unrecorded private definition.

## Earlier second reading (a previous round; superseded)

I reread the node and module independently. The quasi-compact and quasi-separated assumptions, geometric point, sheaf, and all displayed pullback objects are present. The ordinary clause uses the geometric stalk of `R⁺f_*F` and etale cohomology on `X ×_S S_(s)`. The derived clause quantifies all `K ∈ D⁺` and all integer degrees and uses exact derived inverse image followed by derived direct image and strict-local derived global sections. No proof is attempted; the only proof term is `sorry`.

## Second reading by C1

I reread the node statement and the declaration item by item. The objects are a morphism
`f : X ⟶ S` of schemes with `[QuasiCompact f]` and `[QuasiSeparated f]`, an
algebraically closed geometric point `s : Spec (.of Ω) ⟶ S`, a torsion abelian étale
sheaf `F`, and `q : ℕ`. These render as the first binders of
`strictHenselizationStalkFormula`, with the added hypothesis
`hF : Scheme.IsTorsionAbelianSheaf F`; the strict henselization is rendered by
`Scheme.strictHenselizationScheme s` and its structural map. The first conclusion is
the displayed `Nonempty` categorical isomorphism between the geometric stalk of the
`q`-th homology of `rightDerivedLowerStarPlus f` applied to `F` and the `q`-th
étale cohomology after `upperStar` along `pullback.fst` to the strict henselization.
The projections and the pullback scheme agree with the node.

The second conclusion quantifies `K : DerivedCategory.Plus (...)`, now requires
`Scheme.HasTorsionEtaleCohomology ((DerivedCategory.Plus.ι).obj K)`, and then
quantifies every `n : ℤ`. Its `Nonempty` isomorphism compares the `n`-th geometric
stalk homology of `rightDerivedLowerStarPlus f` with the `n`-th cohomology of the
strict-henselization derived pushforward of the derived `upperStar` pullback. Thus
negative degrees, zero degree, and the zero object remain included.

The worker declaration had omitted both torsion hypotheses from the node. I repaired
this by adding `hF : Scheme.IsTorsionAbelianSheaf F` and the torsion-cohomology
hypothesis on `K`, importing the landed declarations from
`Sheaf.AlgebraicGeometry.TorsionEtaleSheaf` and
`Sheaf.AlgebraicGeometry.EtaleSheaves`. I added
`def-weil-pbc-torsion-etale-sheaf` to `stmt_deps` and recorded the exact updated
signature in the node's `lean.statement`. No proof was added; the theorem remains
`by sorry`.

Edge cases checked: `q = 0`, arbitrary integer `n` including negative degrees, zero
sheaf and zero derived object, empty schemes and empty geometric-fibre index data,
and arbitrary algebraically closed `Ω : Type v`. No extra Noetherian, separated,
finite-type, characteristic, or coefficient-ring assumptions occur.

Searches were rechecked with `msearch.py` (LeanFinder, Loogle, and grep queries for
strict-henselization stalk/cohomology formulas) and `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`. No existing strict-henselization stalk formula
was found. The torsion predicates used after repair are the landed declarations
`AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf` and
`AlgebraicGeometry.Scheme.HasTorsionEtaleCohomology`, so no duplicate notion was
introduced.
