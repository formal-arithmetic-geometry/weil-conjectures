## Worker report

The module `Sheaf.Paper.IntegralCoefficientPresentationComparison` states
`WeilConjectures.IntegralCoefficientPresentation.comparison`, with its proof `sorry`.
The auxiliary declarations are real definitions of compatibility conditions and
composites of already published canonical functors and isomorphisms. They introduce
no alternative coefficient ring, site, tensor functor, or derived category.

Hypotheses and clauses, read against the node:

- The section binders `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`, and `T : Scheme.{u}`
  are exactly the prime, finite extension and arbitrary scheme. There is no
  characteristic, invertibility, Noetherian, dimension, constructibility or
  completeness hypothesis. The coefficient convention fixes its uniformizer;
  `PbcIntegralRing`, `pbcIntegralDatum.ideal` and `ULift.ringEquiv` are the
  already recorded lifted valuation ring, uniformizer ideal and down equivalence.
  Site objects remain in universe u+1 and morphisms in u; the coefficient ring
  and modules live in u+1. Every positive exponent appears as n+1, including 1.
- The first conjunct is `∀ n, ∃! q : P_n ≃+* Q_n, ...`, with the exact quotient
  representative formula `q (Ideal.Quotient.mk _ x) = ULift.up (... x.down)`.
  The next conjunct gives the equality of ring homomorphisms for every a≤b;
  the right quotient factor uses the identity on the original valuation ring.
  This includes equal indices and nonadjacent transitions.
- `pbcLevelConstantComparison` is the existing isomorphism κ_n.
  The equality of its hom with `AdicCoefficients.constantComparison` identifies
  precisely the sheafification of constants-to-functions, rather than an
  unspecified isomorphism. The next conjunct gives its transition square for
  every arrow of ℕᵒᵖ. `level` is exactly κ_n inverse followed by the constant
  sheaf functor applied to the existing normalized quotient equivalence.
- `detailedSystem` is the actual lifted quotient-transition diagram with
  commutativity retained; forgetting commutativity recovers
  `integralCoefficientSheafSystem`. Its objects are the recorded constant
  sheaves, not a function-sheaf replacement. The `level` naturality conjunct
  identifies both finite coefficient systems.
- The `∃! e` conjunct quantifies over isomorphisms from `pbcAdicCompletion`
  to `completedIntegralCommRingSheafUnrestricted`. Its condition is exactly
  `e.hom ≫ π_det = π_pbc ≫ (level ...).hom` at every positive level.
  `purCoefficientIso` is the already published CommRing lift of this same
  normalized comparison, not a newly chosen ring isomorphism.
- Both actual restrictions `pbcRestrict e.hom` and `pbcRestrict e.inv` are
  asserted to be equivalences, to preserve finite limits and finite colimits,
  and to have both composite identity isomorphisms. The derived restrictions
  are asserted to be inverse equivalences in both orders as well. These are
  the existing termwise exact-functor descents on unbounded derived categories.
- The two quantified cohomological-bound clauses assert preservation AND
  reflection of `DerivedCategory.IsLE` and `IsGE` at every integer, separately
  for each direction. Thus all intervals and one-sided bounds are covered.
- `DerivedCompatible` quantifies an identity-on-sections restriction-square
  isomorphism r_n, and natural isomorphisms α_n between the two finite derived
  reductions. `derivedSquare` is its exact termwise descent.
  `restrictedComparison` restricts α_n to the completed ring and applies that
  square. The first equation uses precisely `pbcDerivedScalarAdjunction.unit`,
  not an arbitrary morphism from K. The next equation compares every a≤b
  transition, using `pbcReductionTransition`, the adjunct of the smaller
  quotient unit and the canonical restriction-composition isomorphism.
  This is the recorded map id tensor quotient after localization.
- The final clause in `DerivedCompatible` asserts existence of BOTH products
  for every unbounded K. `RoosCompatible` asserts a product isomorphism z fixed
  by all projections and equations for the first arrow (`Pi.lift` of the units)
  and second arrow (`towerTransitionEndomorphism`, the actual 1-s). The
  equivalences are invertible, so these equations identify the diagrams in
  both directions. No triangle or derived-completeness membership is asserted.

Dependency interfaces read and used (their source signatures and docstrings were
opened, including the reexports in each recorded module):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the `Padic` coefficient
  extension constructions and positive-level finiteness, with their imports
  from `CoefficientExtension` and `ExtensionIntegersDvr`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficients.constantComparison`,
  `reductionQuotientMap`, and the quotient/function coefficient constructions.
  The shared `BoundedConstructibleTower` interface supplies `pbcAdicRings`,
  `pbcAdicCompletion`, `pbcAdicProjection`, `pbcAdicQuotient`,
  `pbcLevelConstantComparison`, `pbcRestrict`, `pbcDerivedRestrict`,
  `pbcDerivedExtend`, `pbcDerivedScalarAdjunction`, `pbcReductionTransition`,
  and `pbcDerivedRestrictComp`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `ProEtale.finiteCoefficientPresheaf` and `finiteCoefficientRingSheaf`, as used
  by the recorded AdicCoefficients interface.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, used by `pbcRestrict`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, and the existing standard localization instances.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its imported
  `CompletedIntegralCoefficients`: `integralCoefficientCommRingSheaf`,
  `completedIntegralCommRingSheafUnrestricted` and its projections.
- `Sheaf.Paper.IntegralReductionTowerCanonical`:
  `canonicalIntegralReductionTower`, its map and cone; the source formulas
  are [q] inverse followed by [x maps to 1 tensor x], with the recorded
  id-tensor-quotient transitions. The scalar reduction functors were also
  checked against the pbc functors by temporary definitional-equality probes;
  these passed and were removed from the delivery.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`, whose
  global/slice definitions use the augmented reduction tower and Roos triangle.
  It is imported for the node's recorded vocabulary, but no membership result
  is substituted for the required diagram comparison.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `IsDerivedLimitTriangle`, with `towerTransitionEndomorphism` from its import.
- Existing normalized quotient and limit comparisons are reused from
  `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralCoefficientULift`, `integralDetailedLevelComparison`,
  `integralDetailedCoefficientComparison` and their existence theorems;
  `CompletedCoefficientPresentationTransport.purCoefficientIso` retains
  commutativity and the same projection normalization.

All stated proof dependencies with usable modules are imported; the current
`lem-sfb-ring-isomorphism-tensor-transport` node has neither a Lean record nor
Mathlib match, so no module can be imported for that proof-only prerequisite.
Its role is retained explicitly in the proof docstring. No proof of that
prerequisite is needed to type this statement.

Import-cycle note for the maintainer: the existing quotient/limit constructors
live in the parent `IntegralStratifiedPerfectCharacterization` module, imported
through `CompletedCoefficientPresentationTransport`. Do not add an import of
this consumer back into that parent under the blanket proof-dependency-import
rule: that would be an import cycle. The existing canonical constructors are
reused, without re-recording the parent node or adding a cyclic DAG dependency.

Edge cases checked before and after drafting: n=0 is exponent 1, never exponent
0; equal and nonadjacent quotient indices; T empty; zero complex; disconnected
and non-quasicompact site objects (the quotient topology on connected components
makes factorization valid without qcqs); arbitrary unbounded complexes and
nonflat quotient maps. Empty schemes and zero objects are admitted by the
published sheafification, scalar and product constructions. No finite index
assumption, completeness condition, or boundedness is hidden in the binders.
The paper's Lemma 4.2.12 and Section 6.5 coefficient convention were read in the
local PDF; the arbitrary-scheme discrete clause is used, rather than imposing
its separate qcqs clause for general totally disconnected target spaces.

Searches made:

- msearch.py leanfinder: "Normalized comparison of completed integral coefficient
  sheaves identifies derived reductions adjunction units and Roos diagrams".
  Eight results concerned scheme normalization; none stated this comparison.
- msearch.py loogle: `"Ideal.quotientEquiv"`. Twelve results included
  `Ideal.quotientEquiv` and its representative formulas, but not the normalized
  sheaf system, derived units, or Roos diagrams.
- msearch.py grep: `quotientEquiv|quotientEquiv_mk` in
  `RingTheory/Ideal/Quotient`. Six source hits supplied the quotient primitive.
- rg in `lean/WeilConjectures` for the exact item id and
  `integralCoefficientULift|integralDetailedCoefficientComparison`: no match.
- rg in `lean/Sheaf/Paper` for normalized coefficient comparisons found the
  existing quotient/limit constructors and completed transport. They are
  reused. No existing theorem covers all the item clauses. Source/declaration
  searches found no collision for the new namespace or declaration names.
- DAG searches read the item and every statement dependency, and checked the
  transport and parent nodes. The item has no repair note or blueprint update.

No statement correction, dependency repair, or independent new notion/node is
needed. No STATEMENT-DISPUTED flag is raised. The proof docstring carries all
11 natural-language steps and names their tools. Every definition has actual
data; the only postponed theorem is `comparison`, matching this DAG item.

## Second reading by NR

Clause-by-clause rereading by the dispatched worker; no other agent was started,
as required by the dispatch brief. The maintainer supplies the independent
review after delivery. The rereading checked every clause listed above against
the actual Lean file. It found and repaired the need to state raw quotient
transition compatibility explicitly, and checked that the actual Roos arrows
are expressed, including product existence for arbitrary unbounded K. It also
checked direction: restriction along e goes from detailed modules to pbc
modules, the inverse restriction goes back, and the finite comparison runs
from the pbc reduction to the restricted detailed reduction. Exactness is
preservation of finite limits and colimits in each direction. No extra
geometric assumptions were added.
