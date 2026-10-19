## Worker report

Repair of L's independent definition-ownership return on immutable head 21a25d28cf8d. The retained packet passed the required initial dry run (e3af27bfff). The return explicitly accepted the mathematical statement and its Lean; this repair adds the requested definition node and changes statement dependency ownership. The Lean module is byte-identical to the retained packet. The delivery wrapper rebases the packet on current newtargets-dag; comparison with the read-only current node showed that the previous extra statement dependency was precisely the theorem node rejected in this return.

The module `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` now states the finite geometric-stalk decomposition with the specified operators and maps. `a1FiniteWeilSectionsDecompositionRational` is its common finite-field-stage assertion. The main declaration `a1FiniteWeilSectionsDecomposition` states the assertion over `c.Qbar`, by the actual `ModuleCat.extendScalars (R := E.val) (S := c.Qbar) E.val.subtype` functor. All helper definitions contain real data; the two assertions corresponding to this node have `sorry` proofs. The existing germ and moving-point definitions receive the new definition node described below; there are no new Lean constructions or dependency modules.

Hypotheses, matched individually:

- The global finite-field datum is `D : FiniteFieldDatum.{u}`. Its recorded construction supplies p prime, the positive power defining q, the finite base field and its fixed algebraic closure.
- The distinct coefficient prime and fixed coefficient algebraic closure are `c : D.CoefficientDatum`; `c.different` is used throughout the actual operations.
- The finite model is `Z₀ : Over (Spec (.of D.k₀))` with `[IsFinite Z₀.hom]`; its geometric fibre is `D.geometricFiber Z₀`. Properness, separatedness, and finite type are inferred from finiteness, not added as hypotheses.
- `E : Padic.FiniteCoefficientFields c.l c.Qbar` is the common finite coefficient field stipulated by the node. `K : sfWeilComplex D c.l c.different Z₀ E.val` retains the actual Weil isomorphism, and `hK : sfRationalHeartProperty c.l E.val (D.geometricFiber Z₀).left K.carrier` restricts its carrier to the constructible heart. Thus K is now a sheaf, rather than an unrestricted complex.
- Algebraically closed coefficients are explicit: the main theorem's vector spaces and maps use the scalar-extended cohomology and stalk functors and are linear over `c.Qbar`. Each Qbar Weil sheaf and each morphism is interpreted at a common finite field of definition, as the node stipulates; the theorem is universal in that field, K, L and the arrow. In particular no integral invertible lattice map is required.

Clauses, matched individually:

1. Closed points are `{x : Z₀.left // x ∈ closedPoints Z₀.left}`. `A1FinitePointLifts` retains the two original equations: z is over k, and its projection has image x. The theorem asserts `Finite` of the closed-point type, and for every x both `Nat.card (A1FinitePointLifts D Z₀ x) = localClosedPointDegree D Z₀ x` and `1 ≤ localClosedPointDegree D Z₀ x`.
2. V is `a1FiniteQbarCohomologyFunctor ... |>.obj K`: scalar extension of the recorded compact (`true`) Frobenius cohomology functor followed by `coefficientFdCohomology E.val 0`. The proper identity compactification presents compact cohomology, as allowed for a finite map. Each stalk is the corresponding `a1FiniteQbarStalkFunctor ... z.val |>.obj K`, scalar extension of H⁰ of the recorded `localPointComplex`.
3. `e` is now a linear map asserted bijective, not a linear equivalence with a redundant bijectivity condition. Its target is the nested `DirectSum` indexed by exactly x and its lifts. For every v, x, z, `(e v x) z = a1FiniteQbarEvaluation ... K x z v`. These equations determine every component. `a1FiniteEvaluation` is H⁰ of `ProperSemilinearGerms.rationalGerm`, the existing actual compact counit germ; `a1FiniteQbarEvaluation` is its scalar extension. The choice of e is therefore constrained to stalk evaluation, rather than an arbitrary vector-space isomorphism.
4. `FiniteDimensional c.Qbar` of V is an explicit conclusion. `a1FiniteQbarFrobenius` is scalar extension of `(globalGeometricFrobeniusOnCohomology D c E Z₀ (Compactification.ofIsProper Z₀.hom) K 0).2`. The rational theorem uses this operator itself. Bijectivity is asserted of these specified operators; no F is existentially supplied.
5. For each x there is `T : Equiv.Perm (A1FinitePointLifts D Z₀ x)` constrained by `(T z).val = ProperSemilinearGerms.movingPoint D Z₀ z.val 0`, i.e. h⁻¹ followed by z followed by g in Lean's composition order. The additional condition `∀ z w, ∃ n : Fin d_x, (T^[n.val]) z = w`, together with the lift count, says it is one d_x-cycle. This is stronger information than mere bijectivity of a permutation and fixes the geometrically intended cycle.
6. For every z, a linear equivalence b from the stalk at Tz to the stalk at z satisfies `e_z.comp F = b.toLinearMap.comp e_(Tz)`. Here both e_z terms are the actual evaluations defined above. Since T stays in P_x, this asserts block preservation by closed point; since e is bijective and its components are these evaluations, it asserts that the only block in output stalk z comes from input stalk Tz, by an isomorphism. Thus the summands are cyclically permuted (the input-to-output permutation is T⁻¹).
7. For every x,z the theorem asserts the semilinear return equality h at exponent d_x, then `e_z.comp (F ^ d_x) = F_xz.comp e_z`, where `F_xz` is literally scalar extension of `localFrobeniusCohomology ... K z.val (d_x - 1) h 0`. The rational theorem uses that exact recorded declaration without scalar extension. Neither e_z nor the local operator is existential map data. The equality h is the required scheme-map return; the local convention indexes exponent n+1, explaining d_x-1.
8. Naturality is explicit for every other heart-carrier L and every Weil morphism `f : K ⟶ L`: compact-cohomology of f followed by evaluation at L equals evaluation at K followed by stalk of f. The cohomology and stalk functors include `sfWeilForget` and hence act on the underlying morphism of the actual Weil pair. Combined with the component specification of e, these componentwise squares are exactly naturality of the evaluation isomorphism into the direct sum. A morphism at Qbar is represented with its source and target over a common field, so the universal common-stage formulation includes it, not only integral sheaf maps.
9. No reducedness, weight, semisimplicity, nonzero-stalk, or etaleness hypothesis was introduced.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `FiniteFieldDatum.CoefficientDatum`, `FiniteFieldDatum.geometricFiber`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilForget` (actual fixed pairs).
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeartProperty`.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`, with `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`: the recorded common-stage coefficient convention and `frobeniusCohomologyRationalFunctor`; `Sheaf.Paper.CoefficientCohomologyModules`: `DerivedCategory.coefficientFdCohomology`.
- `Sheaf.Paper.GlobalGeometricFrobenius`: `globalGeometricFrobeniusOnCohomology` (compact component).
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPointComplex` through its actual defining functors, `localClosedPointDegree`, `localPositivePower`, `localFrobeniusCohomology`.
- `Sheaf.Paper.ProperSectionsSemilinearGerms`: `ProperSemilinearGerms.rationalGerm` and `ProperSemilinearGerms.movingPoint`. These exact existing definitions are owned by the new definition node `def-a1-proper-sections-germ-and-moving-point`, which is added to stmt_deps. The theorem node `lem-a1-proper-sections-semilinear-germs` is absent from stmt_deps and retained in proof_deps. No second germ map or moving-point notion is supplied.
- `Mathlib.Algebra.DirectSum.Module`: `DirectSum`. `ModuleCat.extendScalars` supplies the actual coefficient-extension functor.

The proof-plan imports retain `ZlFiniteAdicDirectImage`, `ClosedPointField`, `IntegralPullbackComposition`, `ProperCoincidenceFrobenius`, `FrobeniusCohomologyTransportIso`, and the finite-field Galois modules. The source was checked at Stacks Tag 03QP(1), `etale-cohomology.tex` lines 8244–8290, and the blueprint's parent evaluation display, read with the DAG's recorded correction from arithmetic invariants to geometric stalks.

Edge cases reread against the actual signature: for the empty finite scheme the direct sum and V are zero and all point-indexed assertions are vacuous. For degree one, `d_x - 1 = 0` is the single Frobenius step in `localPositivePower` and `localFrobeniusCohomology`. For a degree-two closed point T must exchange the two lifts, independently of whether their stalks are zero. For zero K all linear maps are the unique maps between zero spaces, while T is still constrained geometrically. A nilpotent thickening is allowed: only `[IsFinite]` is used. For Spec(k₀) and a Weil line on which Frobenius acts by -1, the fixed global operator is -1 and the degree-one local operator is -1; neither can be silently replaced by the identity, and evaluation cannot be zero on a nonzero stalk because e is bijective.

Searches retained from the original packet (`searches.jsonl`): leanfinder “Geometric sections of a finite Weil scheme decompose into geometric stalks with Frobenius cyclic permutation and local return operators” found arithmetic Frobenius and scheme-stalk declarations, not this statement. Loogle `"stalk", "finite"` found stalk-rank and quasi-finite results, not constructible Weil cohomology. Mathlib grep `WeilSheaf|FrobeniusModule|finite.*stalk|stalk.*finite` in AlgebraicGeometry found scheme structure-sheaf material. LeanSearch “Finite scheme geometric sections are the sum of geometric stalks with Frobenius cyclic return operators” found ordinary scheme finiteness/stalk material, not this theorem. Additional repair rg searches in `lean/Sheaf` found the existing `ProperSemilinearGerms.rationalGerm` and `movingPoint`, which are now used. Searches in upstream `WeilConjectures/WeilSheaf` found the different legacy Weil-sheaf stalk framework, not the present fixed-pair common-stage statement. The current return requires a definition node for these already existing constructions; the new node has an `existing: true` binding to their unchanged module.

No node statement correction or STATEMENT-DISPUTED flag is needed: the node's mathematical statement and the retained Lean signature were accepted in the current return; the earlier signature defects described in the preceding self-check were already repaired. The item changes only its lean record and stmt_deps: it gains the new definition node instead of the theorem node. Its statement and proof_deps are unchanged from the base, and the semilinear-germ theorem remains a proof dependency.

## Second reading by Q110

This is a fresh self-check with the node and the repaired file open; the dispatcher's explicit instruction forbids starting another agent, so this report does not claim an independent sub-agent review.

H3: compared the component clause, operator definitions, cycle clause, return clause and naturality clause individually. The old arbitrary e is replaced by a bijective linear map with canonical counit-germ components. The old arbitrary F is removed: `a1FiniteFrobenius` unfolds to the compact component of the recorded global operator, and the main theorem uses its actual scalar extension. The old permutation tautology is removed: T is the actual moving-point map and every lift is reached within d_x iterates. The stalk-block equivalence is tied to F by an equation with those evaluations. The old ez=0, Fxz=1 witnesses are no longer available: ez is canonical and Fxz is the recorded local operator with an actual semilinear return proof. Naturality and finite-dimensionality are now explicit. The main theorem is Qbar-linear, rather than leaving the final coefficient extension implicit.

H4: opened the signatures of the recorded global and local Frobenius declarations and followed their use in the repaired file. Both now occur in the actual operators appearing in the conclusion. Opened `sfRationalHeartProperty` and checked its explicit hK hypothesis (and the corresponding L hypothesis in naturality). The germ and moving-point constructions reuse the existing dependency module rather than private copies.

H11: the original report incorrectly described a permutation as cyclic, an arbitrary equivalence as evaluation, and unconstrained local maps as local Frobenius. This reading checked those equations themselves, not their docstrings. It also checked d_x=1 against the positive-power indexing convention and the empty/zero/nonreduced cases above. Definitions contain no sorry data, all variables/universes are explicit, and both postponed theorem proofs are exactly `sorry` for this node.


## New nodes

`def-a1-proper-sections-germ-and-moving-point` owns the already landed
`WeilConjectures.ProperSemilinearGerms.rationalGerm`, together with `comparisons`,
`integralCounit`, `integralGerm`, and `movingPoint`, all in
`Sheaf.Paper.ProperSectionsSemilinearGerms`. It uses `existing: true`, so it delivers no
copy of that module. This is exactly the ownership repair requested by L. Source:
Deligne Weil II (1.1.7), (1.1.10)–(1.1.14), pp. 150–153, with Stacks 07A7 and 0D6D
for the counit and composition construction; the use is the first evaluation display
in the ancestor `lem-a1-finite-boundary-weights`. The ancestor was confirmed by
`tools/blueprint_refs.py ancestor`, and `via` starts with this item.

Every part of the definition statement was checked against the existing bodies.
`D : FiniteFieldDatum.{u}`, `Y₀ : Over (Spec (.of D.k₀))`, `[IsProper Y₀.hom]`,
`l : ℕ`, `[Fact l.Prime]`, `[Fact (l ≠ D.p)]`, `E : Type u`, `[Field E]`,
`[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]` are the explicit section
parameters. The coefficient categories are the recorded raw rationalization and
integral categories, and properness supplies the finite-type requirements.
`comparisons` is precisely `integralPullbackComparisonRealization` at the identity
embedding of the lifted base coefficient field. `integralCounit` composes pullback
realization, reconstruction counit, the system adjunction counit and inverse
completeness unit. `integralGerm` takes `z` and its exact equation `hz : z ≫ a = 𝟙 _`,
then composes the inverse identity comparison, `eqToHom` for hz, the specified
composition comparison, and pullback of that counit. `rationalGerm` applies
`pointRationalFibre` to `properFrobeniusRationalIso.hom`, the localized integral
germ on `M.obj`, and `localPullbackObjectIso.inv`. Its signature in the new lean
record is verbatim through the point immediately before `:=`. The additional
`movingPoint` declaration is the literal composite
`localPositivePower (frobeniusPointIso D).inv r ≫ z ≫
localPositivePower (D.geometricFrobenius Y₀).hom r`, hence mathematical exponent
r+1 and not r. The new statement does not assert `movingPoint_properties` or the
semilinear identity: these remain theorems in their original node.

Searches: msearch LeanSearch for “Canonical derived germ from proper compact
sections to a geometric stalk using the adjunction counit and semilinear moving
points” returned eight ordinary topological germ declarations, no match. LeanFinder
for “Proper compact rational cohomology germ via derived pullback adjunction counit
and moving point under geometric Frobenius” returned eight topological stalk
adjunction identities, no match. Mathlib grep for
`rationalGerm|integralGerm|integralCounit|movingPoint` returned zero hits. The same
rg search upstream in WeilConjectures returned no hits. Project rg found the exact
landed definitions at lines 71, 80, 103, 123 and 167 of the unchanged module.
DAG searches and blueprint search found no definition node owning them.
`def-weil-pbc-derived-global-germ` is an ordinary étale D⁺ construction, and
`lem-trf-finite-scheme-derived-germs` is a finite-torsion decomposition theorem;
neither owns this proper compact rational germ or moving point. Search records,
including returned hit names, are retained in the new node's `mathlib_searches`.

The new node cites the recorded operation/category definitions and the actual
comparison theorems used to construct its data. The latter are legitimate data
suppliers (the chosen comparison system, pullback compositor and proper comparison),
whereas `properSectionsSemilinearGerms` supplies none of these definitions and is
not a dependency of the new node. This keeps the theorem available solely for the
item's proof. No hypothesis, clause or mathematical statement of the item changes.

Additional second reading by Q110 for this return: read the new definition node
alongside all five existing definitions. Verified its explicit parameters and the
positive r+1 convention, that `rationalGerm` is the specified counit germ rather
than an arbitrary map, that `movingPoint` is defined even before the k-point
property is proved, and that no theorem conclusion has been reclassified as a
definition. Checked the item now cites this definition node in stmt_deps and still
cites the semilinear-germ theorem in proof_deps. The empty-scheme case has no
k-point germ to evaluate, the r=0 moving point is the single geometric Frobenius
step, and the zero coefficient object gives the canonical zero germ. Nonreduced
proper schemes remain included. The existing main-module hypotheses, component
specification, Frobenius operators, single-cycle clause and return equation were
reread and are unchanged from the mathematically accepted packet. No independent
agent review is claimed; this dispatcher explicitly forbids starting other agents.

Validation of this repair: scompile.py compiled the retained module cleanly (sandbox 28.9 s, library 32.2 s). The repaired delivery dry run printed OK at b0f727a5e4 after preflight and compilation. Local self-check confirmed only lean and stmt_deps differ on the item, proof_deps is byte-for-byte equal as JSON data to the current base, the new lean.statement is the exact existing rationalGerm signature, and the delivered Lean source is unchanged by this repair.
