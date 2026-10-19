## Worker report

Repair of the returned immutable head `8dadf10680b6`, H3/H4. The saved packet's
initial dry run passed as commit `06d4309d4d`, but rereading its source confirmed
the reported mathematical omission. This delivery retains its local predicates
and the four coefficient-stage evaluation formulas and adds the missing ordinary
finite/integral dual identification and ordinary module biduality.

Hypotheses and clauses:

- `D : FiniteFieldDatum`, `C : D.CoefficientDatum` encode p, a, q, k, prime ell
  different from p, and the chosen algebraic closure. `E`, its `Field`, `Algebra
  (Padic C.l)`, and `FiniteDimensional` instances give the finite coefficient field.
  `n` and `hn : 1 ≤ n` give every positive finite exponent.
- `S : SixFunctorDatum D C E n hn` fixes the coefficient categories and actual
  operations. `X : SixFunctorSpace D` gives a finite-type k-scheme;
  `[IsSeparated X.obj.hom]` supplies the remaining geometric hypothesis.
- `IsLocallyFiniteProjectiveCoefficientSheaf` supplies a covering sieve over each
  site object and a retraction from a finite product of coefficient units on each
  cover member. `Fin m`, with m any natural number, permits rank zero and varying
  ranks. `IsFiniteProjectiveCoefficientDegreeZero` requires precisely such a sheaf
  and an isomorphic degree-zero derived presentation.
- The finite and integral `FiniteProjectiveCoefficientHomFormula` conjuncts assert
  invertibility of the specified evaluation natural transformation for every N,
  derived biduality, and the displayed contravariant naturality in P. Naturality
  in N is built into `ringedSiteDualEvaluationLeftNatTrans`.
- Each of these two conjuncts is now followed by `FiniteProjectiveOrdinaryDual.Formula`.
  It quantifies over every module presentation `e` of every object of the actual
  finite-Tor category. Its first conclusion is `IsIso (bidual R P)` for the
  ordinary module map `P → homObj (homObj P R) R`. Its second conclusion is
  `IsIso (comparison R M P K e)`, with source the actual ordinary sheaf dual in
  degree zero and target ambient `derivedInternalHomOfUniverses` into the model's
  coefficient unit. The finite ring is the datum's finite constant coefficient
  sheaf; the integral ring is its completed integral coefficient sheaf.
- `comparison` is an explicit composite: `Q.map singleHomMap`, the published
  `ringedSiteOrdinaryHomComparison` (postcomposition by the fixed K-injective
  augmentation), and internal-Hom transport along e and the model's `unitIso`.
  `singleHomMap` is uniquely characterized by the identity on ordinary local
  functionals in the (0,0) product factor. Thus this is evaluation-built, not an
  arbitrary comparison or an assertion of `Nonempty` isomorphisms. The datum's
  `finiteModelComparison`/`integralModelComparison` anchor the coefficient Hom to
  precisely these ambient models and preserve evaluation and symmetry.
  Together with the existing evaluation formula this supplies the ordinary-dual
  tensor formula of the node, including its specified canonical map.
- The rational conjunct uses `IsRationalFiniteProjectiveCoefficient`, with actual
  local retractions after localization, and the common-stage conjunct uses
  `IsCommonStageFiniteProjectiveCoefficient`, allowing an isomorphic finite-stage
  representative. Their dual and bidual use the corresponding coefficient Hom,
  as required by the node's field-stage convention. No integral splitting of a
  rational retraction, or discrete constant field sheaf, is substituted.

Dependency declarations read and used: `SixFunctorDatum`, `SixFunctorOperationDatum`,
`SixFunctorSpace`, their finite-Tor domains and normalized ambient models in
`Sheaf.Paper.SixFunctorDatum` and `Sheaf.Paper.SixFunctorOperationDatum`;
`IsRationalFiniteProjectiveTerm`, `sitePerfectRationalAmbient`, and the common-stage
conventions of `Sheaf.Paper.SitePerfectComplex`;
`SheafOfModules.homObj` and `homObjMap` in
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom` (def-pur-sheaf-hom);
`ringedSiteOrdinaryHomComparison`, `RingedSiteDualityModel.unitIso`, and the existing
canonical dual evaluation maps in `Sheaf.CategoryTheory.RingedSiteDualityMaps`;
`homComplex_projections_exists` in `Sheaf.Algebra.Homology.HomComplexProjections`.
The geometric size, separatedness, and finite-type conventions use the recorded
Mathlib definitions through the datum. Independent site universes c and v remain
independent; the pro-etale instance has object universe u+1 and morphism universe u.

The helper existence-and-uniqueness theorems belong to this node's canonical arrows
and are recorded in `lean.declarations`. Each has its complete construction proof
in its docstring. Definitions select data only from those unique characterizations,
and never from a bare existence assertion. Every theorem proof is `sorry`, as
required at stage 2. The main proof docstring retains the node's eight steps and
now names the step-5 ordinary comparison explicitly.

Edge cases checked: rank zero, zero module, zero derived object, empty scheme/site,
empty covers only when admitted by the topology, varying local ranks, arbitrary N,
arbitrary degree-zero presentation isomorphism e, completed integral coefficients,
rational splittings which do not lift, and common-stage change of representatives.
In rank zero both ordinary bidual and comparison are the unique maps between zero
objects. The helper formulas have no perfectness assumption: only their asserted
invertibility uses the local finite-projective hypothesis. No statement disputed.

Searches retained in `searches.jsonl`: the original leanfinder and loogle queries
for finite-projective tensor-Hom and ordinary module duality had no four-stage
match; Mathlib, WeilConjectures and Sheaf grep searches likewise found no exact
statement. Repair searches: leanfinder, “ordinary sheaf Hom dual degree zero
canonical comparison to derived internal Hom finite projective”, returned
`Sheaf.ΓHomEquiv`, `sheafHom'Iso`, sheaf cohomology and light-condensed results,
none giving this comparison. Loogle `SheafOfModules.homObj` returned zero hits
(unknown identifier in its Mathlib index). Direct source grep found and reused
`SheafOfModules.homObj` and `ringedSiteOrdinaryHomComparison`. It also found the
upstream `SheafOfModules.bidual`, whose signature imposes equal site object,
morphism and coefficient universes. The helper here supplies its identical slice
evaluation characterization at independent universes; it does not restrict the
pro-etale site to fit that specialized signature. Mathlib's sheaf-module directory
had no bidual or ordinary-to-derived single-Hom comparison.

Source reread: Stacks sites-cohomology.tex, `lemma-dual-perfect-complex` and
`lemma-Rhom-complex-of-direct-summands-finite-free`, and the node's ordinary-dual
clause and steps 2--5. The latter explicitly identify ordinary Hom into the ring
with its derived Hom, which the previous Lean packet had omitted.

## Second reading by NV

Self-check against the node and repaired file: the original hypothesis list and
local predicates are retained, including rank zero and localized splittings.
The H3/H4 defect was real: all earlier clauses referred only to derived Hom.
It is repaired by the two `FiniteProjectiveOrdinaryDual.Formula` conjuncts, whose
first clauses concern actual module arrows with ordinary `homObj` on both duals,
and whose second clauses concern the specific evaluation-normalized comparison.
The map is explicitly constructed from the normalized (0,0) Hom factor and the
published augmentation, with all presentation and unit transports displayed.
No new hypothesis or natural-language node correction was used.

Consumer self-check: `lem-zl-lisse-cohomology-derived-dual` proof step 2 needs
`D(P) ≅ Hom(P,R)[0]` normalized by evaluation. The new integral comparison supplies
exactly that map for each lisse integral degree-zero presentation; scalar
localization and the retained common-stage conventions carry its evaluation
formula to its two field stages. `thm-sf-hom-ctf` retains its finite-free/direct-
summand calculation and the sharper site-perfect bound. Neither citer is edited.

No independent second agent was started, in accordance with the dispatched brief;
the maintainer's independent review remains the independent mathematical review.

Validation: `scompile.py` compiled sandbox and library forms cleanly (21.2 s and
28.0 s). The required delivery dry run is rerun after updating the verbatim record.
