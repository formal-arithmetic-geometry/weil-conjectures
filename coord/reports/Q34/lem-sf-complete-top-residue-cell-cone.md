## Worker report

The delivery states `WeilConjectures.complete_top_residue_cell_cone` in
`Sheaf.Paper.CompleteTopResidueCellCone`. Its sole postponed proof is that theorem;
the docstring carries all seven DAG proof steps and their sources. Every helper
is an application of existing free sheaves, finite coproducts, single-term complexes,
canonical scalar reduction, or exact restriction. No new mathematical notion or
new DAG node is needed. The item statement and proof are unchanged.

Hypothesis and clause correspondence:

- Prime ell and finite E/Q_ell: `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E]`,
  `[Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. Padic's existing integer ring,
  uniformizer and positive quotient rings determine all coefficient sheaves.
- Scheme T and its small pro-etale site: `(X : Scheme.{u})`, `X.ProEt` and
  `ProEt.topology X`, retaining object universe u+1 and morphism universe u.
  The common ambient input universe u can contain both E and X; no site object/
  morphism universe equality is imposed.
- R_n and B: `integralCoefficientSheaf` and
  `completedIntegralCoefficientSheafUnrestricted`; index 0 denotes exponent 1.
  The latter is exactly `limit (integralCoefficientSheafSystem ...)`, not a
  constant valuation-ring sheaf. `scalarReductionSource` is its module category.
- Unbounded D(Mod(B)): `DerivedCategory (scalarReductionSource.{u,u} l E X)`.
- Quotient-tower completeness: `_hcomplete : IsDerivedCompleteUnrestricted ... M`.
  Its definition uses the actual quotient-tower augmentation and Roos triangle,
  restricted scalar actions and quotient transition maps. The auxiliary finite
  field in that published definition imposes no condition on X (F_2 or F_3
  always supplies the irrelevant datum).
- Quasi-compact T: `[CompactSpace X]`. Exact set-sheaf evaluation at T:
  `_hweak`, quantifying every epi of `Sheaf (ProEt.topology X) (Type (u+1))`
  and requiring surjectivity at `op (ProEt.mk (𝟙 X))`. No affine assumption added.
- M_1: `(scalarReductionDerivedExtension.{u,u} l E X 0).obj M`, canonical
  derived change of rings along the exponent-one limit projection.
- Ordered integer bounds: `(a b : ℤ) (hab : a ≤ b)`.
- Finite nonnegative ranks: `r : ℤ → ℕ`, used only in the stated finite intervals.
  Extending an interval-indexed family outside the interval changes no condition.
- Every prescribed theta_q: `theta : ∀ q : Set.Icc a b, ... ≅ H^q(M_1)`.
  `topCellResidueFree` is Mathlib `SheafOfModules.free (ULift (Fin (r q)))`.
- Tor tests on every site object: `_hTor : ∀ V : X.ProEt, HasProEtaleTorAmplitude
  V.left ... (proEtaleRingDerivedPullback ...).obj M_1 a b`. This is the
  published Tor predicate retained by the dependency's recorded module, testing
  every degree-zero module and every outside degree on each restriction.
- P=B^r_b: `topCellIntegralFree ... (r b)`, also Mathlib's free sheaf, hence zero
  when rank zero. `singleFunctor ... b` is P in degree b, equivalently P[-b].
- The morphism f and distinguished triangle: existential `f L g delta` and
  `Triangle.mk f g delta ∈ distTriang _`. The endpoint is the shift by 1 of P[-b].
- Complete L: `IsDerivedCompleteUnrestricted ... L`.
- Canonical source identification of f_1: existential isomorphism `e` together
  with `e.hom = topCellReductionComparison ...`. This is not arbitrary: the
  helper is the adjoint of coefficient reduction on the actual standard free
  generators, through the normalized published derived adjunction and the exact
  restriction localization factors. `topCellReducedMap` is e.inv followed by
  scalar extension of f.
- H^b(f_1)=theta_b: the displayed equality of homology maps, using
  `singleFunctorCompHomologyFunctorIso.hom.app` for the canonical identification
  H^b(k^r[-b])=k^r (not an arbitrary cohomology isomorphism).
- Every compatible split model: `∀ phi : Q.obj (topCellResidueSplit ... a b r) ≅ M_1`,
  with compatibility for every q expressed by the homology of the q-summand
  inclusion. The conclusion is the equality f_1=Q(top inclusion)≫phi.hom.
  Finite coproducts of single-term complexes give the literal zero-differential
  complex, and this condition covers any model inducing the stated theta_q.
- Explicit cone model: the first `Nonempty` identifies L_1 with Q of the chain
  mapping cone of that top inclusion. The next gives an isomorphism of actual
  complexes from this cone to the lower split complex coproduct Cone(id_A).
  Since A is a single-term complex in b, Cone(id_A) has the same free module
  in b-1,b and identity differential. `Nonempty (Homotopy (𝟙 Cone(id_A)) 0)`
  explicitly records its contractibility. Finite coproduct equals finite direct sum.
- Displayed residue-cone isomorphism: the next `Nonempty` is precisely
  L_1 ≅ Q(topCellResidueSplit ... a (b-1) r).
- Constant finite-dimensional cohomology: for every q in `[a,b-1]`, the next
  clause supplies the isomorphism with `topCellResidueFree ... (r q)`.
  The split model also gives zero cohomology outside that interval.
- Shorter Tor amplitude after every restriction when a<b: the implication
  `a < b → ∀ V : X.ProEt, HasProEtaleTorAmplitude ... a (b-1)`.
- Singleton interval: `a = b → IsZero L_1 ∧ IsZero L ∧ IsIso f`.
- Rank-zero case explicitly included: `r b = 0 → IsZero (topCellIntegralFree ... (r b))`.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: imports the recorded
  Padic coefficient constructions; `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Scheme`, `.Sites.Proetale`: `Scheme`, `Scheme.ProEt`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Limits.limit`, `limit.π`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `singleFunctor`, and `HasDerivedCategory.standard`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `IsDerivedLimitTriangle`, via the published completeness predicate.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem;
  its canonical ordinary/derived change-of-rings construction underlies reduction.
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` publicly retains
  `Scheme.HasProEtaleTorAmplitude` from `.ProEtaleTorAmplitude`, the appropriate
  original-site presentation used here.
- Cohomology dependency repaired to `DerivedCategory.homologyFunctor` and
  `.homologyFunctorFactors`, plus `.TStructure.t`, as detailed below.
- Added citations to already landed nodes for completed coefficients, completeness,
  and the normalized scalar-extension/restriction adjunction. They introduce no
  new assumptions. Their modules are `CompletedIntegralConstantMapOfUniverses`
  (the existing underlying completion), `DerivedCompleteOnSlices` (global branch
  is the exact `IsDerivedCompleteUnrestricted` predicate), and
  `DerivedScalarExtensionRestrictionAdjunction` (used for its normalized homEquiv).

All already stated proof dependencies are imported: CompleteResidueCohomologyBounds,
ProEtaleWeaklyContractibleEvaluationExact, ProEtaleIntegralCoefficientLimit,
DerivedCompletion, DerivedNakayamaFirstReduction, KFlatIndependentCoefficients,
the fixed-ring Tensor module, and Mathlib HomologySequence/Pretriangulated via the
explicit imports and their public imports. The two newly split proof nodes
`lem-sf-completed-coefficient-free-resolution` and
`lem-sf-projective-cohomology-split-model` have no recorded modules in this checkout;
the statement does not need their theorems to type, and their proof-plan references
remain in the docstring for stage 3.

Edge cases checked mathematically: a=b makes Icc a (b-1) empty and the lower sum
zero; the contractible identity pair has degrees b-1,b with the correct sign and
identity cross differential in Mathlib's cone convention. Rank r_b=0 gives an
empty free coproduct and unique map from zero; all ranks zero gives the zero
residue model. Negative a and b are unrestricted integers. Empty X gives zero
module categories, with no nonemptiness or characteristic condition added.
No statement correction and no STATEMENT-DISPUTED issue.

Searches: the exact wrapper results are in searches.jsonl in the sandbox. LeanFinder
query “Lift a top residue cohomology basis of a derived complete complex of sheaves
to a free cell with cone of shorter Tor amplitude” returned eight generic CM5b,
fraction and K-injective results, no match. Loogle query `"CochainComplex.mappingCone"`
returned twelve generic cone declarations, reused for the cone model. LeanSearch
query “Derived complete complex lift top residue basis cone shorter Tor amplitude”
returned eight generic cone/short-complex and local-ring spanning results, no match.
Wrapper grep `residue.*cone|top.*residue|split.*cohomology` in Mathlib/Algebra/Homology
returned zero hits. `rg` over both lean/WeilConjectures and lean/Sheaf for the item id,
`top_residue_cell`, and `topResidueCell` returned no preexisting declaration.
Further local source searches located and reused SheafOfModules.free/freeHomEquiv,
HomologicalComplex.single, singleMapHomologicalComplex,
DerivedCategory.singleFunctorCompHomologyFunctorIso, mappingCone and Homotopy.
The source read is literature/stacks-project/proetale.tex, lines 5825–5950,
particularly the final top-generator triangle and its omitted Tor-amplitude argument.

## Dependency modules

`def-weil-derived-cohomology-sheaves`: lean-only repair to existing Mathlib
`DerivedCategory.homologyFunctor` and `DerivedCategory.homologyFunctorFactors`,
declared in `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. The consumer
also imports `Mathlib.Algebra.Homology.DerivedCategory.TStructure` for the standard
t-structure. The former primary declaration
`WeilConjectures.sfModelCohomology` takes common-stage Weil coefficients and cannot
accept an arbitrary completed-ring module complex. Mathlib's general functor is
exactly the node's ker(d)/im(d) cohomology, with its representative comparison and
standard t-structure. No new module or duplicate cohomology definition was written.
Consumer validation is the full delivered theorem's uses in the theta hypotheses,
prescribed top map, all-model compatibility, and lower residue cohomology.

## Second reading by Q34

The dispatcher forbids starting another agent and assigns the maintainer's independent
review to the delivery. This is a separate self-check of the finished node and source,
not a claim of independent review. Matched each clause as listed above, including the
canonical free-generator comparison, the literal cone decomposition and its explicit
contractibility, the conditional shorter interval and singleton zero case. During
compilation this check corrected the direction of the single-term homology isomorphism
and retained the inverse direction for the exact-restriction comparison. The helper
instances are the existing Mathlib/published structures with fully specified sizes;
none is a new hypothesis or a new categorical structure. No mathematical statement
was changed. The server compile passed both sandbox and library module names cleanly.

Preflight repair: the existing-declaration record names HomologySequence, the defining
file, rather than its TStructure reexport. The added adjunction theorem dependency
is used for its normalized canonical adjunction data (`.choose.homEquiv`), not as
an added hypothesis or to assert the top-cell theorem. Its other recorded declarations
own the scalar-reduction functors used in the statement.
