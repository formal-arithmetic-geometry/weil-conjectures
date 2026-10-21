## Worker report

The module states `SheafOfModules.derived_tensor_shift_descent`, with its proof
postponed by `sorry`. No theorem is proved. Its four helpers have real data:
`tensorShiftTotal` transparently abbreviates Mathlib's total tensor, and
`tensorResolvingShiftCompatible` and `tensorFixedComparisonsShiftCompatible`
spell out this node's normalization and universal fixed-comparison clauses.
`tensorShiftComparisonsUnique` spells out uniqueness for arbitrary competing
natural isomorphisms, without coherence assumptions on the competitor.
There is no second derived tensor, resolving comparison, flatness, or K-flatness definition.

Hypotheses and conclusions, in order:

- The site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`.
  `[EssentiallySmall.{r} C]` expresses smallness relative to the coefficient/module
  universe, without identifying object, morphism and coefficient universes.
  `R : Sheaf J CommRingCat.{r}` is the specified commutative ring sheaf.
- The module category is the dependency's `ringedSiteModules.{r}` of the
  underlying ring sheaf. `[HasDerivedCategory.{w} ...]` supplies the unbounded
  derived category at the chosen morphism size; `w` remains independent.
- `TensorFlatRepresentative (R := R) P` is exactly
  `CochainComplex.IsKFlatIndependentCoefficients P` and
  `∀ i : ℤ, SheafOfModules.IsFlatOnSite (P.X i)`. The `stable` argument explicitly
  assumes closure under every integer shift.
- `siteRestrictionDerivedTensor` is precisely the curry of
  `siteDerivedTensorIndependentCoefficients J R`, the published chosen bifunctor.
  `tensorDescentPair P S hP hS` is the existing comparison obtained from the
  SAME descent theorem's chain-to-homotopy comparison and resolving comparison.
  Its source is localized ordinary total tensor and its target is this T.
- The witness `s : ...CommShift₂Int` supplies both natural shift isomorphisms.
  Its `commShiftFlipObj` gives t¹ and `commShiftObj` gives t². Each has the
  zero and addition identities by `Functor.CommShift`. Its `comm` field is the
  mixed sign (-1)^(ab), with the canonical `shiftComm` identification.
- `tensorResolvingShiftCompatible stable s` gives BOTH representative equations,
  for every resolving P,S and integer n. The left side is c at the shifted pair,
  followed by T applied to the localization shift comparison, then t. The right
  side is Q of the signed chain comparison, then the localization shift
  comparison of the total tensor, then shifted c. Multiplying by the inverses
  of the first two left-side isomorphisms gives exactly the node's conjugation
  formulas δ¹ and δ². The first chain comparison is
  `mapBifunctorShift₁Iso`, the second `mapBifunctorShift₂Iso`.
- The separate clause `tensorShiftComparisonsUnique s` quantifies for EACH n
  over every natural isomorphism α between the shifted-input tensor bifunctor
  and the shifted-output tensor bifunctor, in each variable separately.
  If α agrees with the prescribed component on every resolving pair, it agrees
  on every derived pair M,N. Since the prescribed component has the c/λ
  normalization above, this is exactly uniqueness with the given normalization.
  No zero/addition/mixed coherence assumption is imposed on a competitor.
  In particular the coherent bifunctor structure itself is uniquely determined.
- `CommShift₂Int.commShift_map` and `.commShift_flip_map` range over ALL derived
  morphisms, giving exactly the requested squares for T(f,-) and T(-,g).
  Morphisms represented by chain maps, inverse quasi-isomorphisms, and arbitrary
  localization words are included. Equal localization words are equal morphisms,
  so no auxiliary choice of words is present.
- `tensorFixedComparisonsShiftCompatible s` quantifies over every resolving A,
  assumes the two fixed tensor functors preserve quasi-isomorphisms, and then
  quantifies over EVERY natural isomorphism eL and eR with components on every
  resolving B exactly `tensorDescentPair A B` and `tensorDescentPair B A`.
  Its conclusion `NatTrans.CommShift eL.hom ℤ` (respectively eR) is the complete
  signed shift square at every B and every integer. The source functor has the
  chain shifts from Mathlib; the target has the composite Q/t shift structure.
  Thus these equations say precisely that the derived shifts have the
  one-variable descended characterization. Uniqueness of transformation descent
  identifies them with the one-variable descended shifts, as in proof Step 8.
- All complexes have index ℤ and no boundedness, flat-cohomology, or restrictions
  on the varying B are imposed.

Why the chain-level presentation is the same homotopy-level statement:
`HomotopyCategory.quotient` is full, essentially surjective, and surjective on
objects; whiskering along it is full and faithful. Total tensor factors through
that quotient by `bifunctorMapHomotopyCategory`. `DerivedCategory.quotientCompQhIso`
is the canonical shift-compatible identification of quotient followed by Qh
with Q. Consequently a normalized natural comparison on K pulls back uniquely
to the eL/eR quantified here, and every such chain-natural comparison descends
uniquely to K. The representative equations transport through those same
isomorphisms. They neither omit a homotopy comparison nor assume arbitrary
additional comparison data. The real `tensorDescentPair` formula already inserts
all the necessary `quotientCompQhIso` factors.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `Qh`, `quotientCompQhIso`, and their
  additive and shift instances.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` (exactness of the existing sheaf tensor).
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients` and
  `siteDerivedTensorIndependentCoefficients`; their chosen comparisons, resolving
  localization equivalence, and arbitrary-transformation bijection are retained.
- `Mathlib.Algebra.Homology.BifunctorShift`: `Functor.map₂CochainComplex`,
  `CochainComplex.mapBifunctorShift₁Iso`, `mapBifunctorShift₂Iso`, their signed
  summand formulas, both fixed-argument `CommShift` instances, fixed-map
  `NatTrans.CommShift` instances, and the final `CommShift₂Int` instance.
- `Mathlib.CategoryTheory.Shift.CommShiftTwo`: `Functor.CommShift₂Int`, including
  its four fixed-argument fields and its mixed-sign `comm` field. Read the actual
  definition: its sign is p*q (despite the stale p+q in its module introduction).
- `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated` and
  `DerivedCategory.Basic`: the exact shift-compatible homotopy localization.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` (proof import).
- `Mathlib.CategoryTheory.Localization.Predicate`: `Localization.lift`, `fac`,
  `liftNatTrans`, `liftNatTrans_app`, `liftNatIso`, `natTrans_ext` (proof import).
- `Sheaf.Paper.SiteDerivedTensorRestriction`: existing helpers
  `SiteTensorComplexFunctor`, `TensorFlatRepresentative`,
  `siteRestrictionDerivedTensor`, and `tensorDescentPair`, with the supporting
  `tensorDescentClass`, `tensorDescentComplexIso`, and `tensorDescentDerivedIso`.
  The new definition node `def-weil-pbc-tensor-descent-representative-comparison`
  owns these seven existing definitions. The restriction theorem is absent from
  stmt_deps: its projection-formula conclusion is not used. The `.choose` terms
  select the already-cited site-derived-tensor-descent datum.
  The downstream `KFlatFixedTensorTriangulated` module is deliberately not imported:
  its node already depends on this item, and importing it would close a cycle.

Edge cases checked before drafting: shifts zero and negative integers; both
orders with a=b=1 (the minus sign); a=0 or b=0 (sign +1); characteristic two
(the sign becomes identity); the zero ring and zero complex; unbounded complexes;
nonflat varying B such as ℤ/2 on the one-point ringed site. The fixed comparison
clause assumes no flatness of B. No empty-site case is excluded. Site universes
u,v and coefficient universe r are independent; the derived morphism universe
w is independently bound. No statement fault or STATEMENT-DISPUTED claim remains.

Searches (2026-10-21):

- msearch.py leanfinder, query: "Descend signed shifts in both variables of
  derived tensor normalized on flat K-flat representatives and every fixed-factor
  natural comparison". Eight hits: general derived exact-functor shifts,
  the chain mixed-shift identity, chain shift isomorphisms, and the
  quotientCompQhIso shift instance; no theorem on this published tensor with
  uniqueness and every normalized fixed comparison.
- msearch.py loogle, query: "Functor.CommShift₂Int,
  Functor.commShiftOfLocalization". Zero hits, unknown identifier
  `Functor.CommShift₂Int` in that service index. Local source confirms the class.
- msearch.py grep, query: "commShift₂OfLocalization|commShiftOfLocalization|CommShift₂Int"
  in CategoryTheory/Shift. Ten hits: one-variable shift localization and the
  class definitions; no full normalized conclusion.
- msearch.py leansearch, query: "The derived tensor bifunctor admits unique
  signed integer shift comparisons normalized on K-flat representatives,
  compatible with every normalized fixed factor comparison". Eight hits:
  chain mixed sign, derived shifts, exact-functor shifts; none is this statement.
- rg in lean/WeilConjectures and lean/Sheaf for CommShift₂Int,
  siteDerivedTensorIndependentCoefficients, shiftDescent and normalized shifts:
  found the general monoidal derived shift construction and the downstream
  fixed-tensor theorem. They do not assert this item's unique normalization and
  every normalized comparison for the specified siteDerivedTensor functor.
  The latter was read to identify and avoid its dependency cycle.
- rg for the item's blueprint id in lean/WeilConjectures: no existing declaration.
  Searches of the four new declaration names in both roots and
  dag/lean_names_upstream.json found no collisions.

## Second reading by Q29

Self-review under the dispatcher's instruction not to start other agents;
the maintainer performs the independent review. I reopened the node and the
module and checked each clause against the mappings above. The initial draft
used the opaque `SiteTensorComplexFunctor` where typeclass synthesis needed
Mathlib's total-tensor shift instances; it now uses the definitionally identical
transparent abbreviation. The first compile also caught missing parentheses
around a shifted representative in a function application; these are repaired.
I checked the orientation of both representative equations by cancelling c and
T(λ), and checked that uniqueness quantifies over arbitrary natural isomorphisms
without assuming the coherence identities or the fixed-comparison conclusion.
The eL/eR quantifiers are universal and their normalization uses equalities of
isomorphisms, not merely existence of an unspecified comparison. No requirement
that an arbitrary varying complex be flat or K-flat was introduced.

Compilation review additionally caught an implicit-site inference ambiguity;
all site-dependent wrapper calls now bind J explicitly. The final module uses
no profiler, tracing, diagnostic lines, or increased heartbeat/time limit.

Previous packet validation: `scompile.py` checked the sandbox module and its library
module name cleanly, with no warnings (16.1 s and 16.2 s). On this repair retry,
the saved packet first passed `deliver2.py --no-push` (commit 4c87ccb9d55).
That mechanical success does not resolve the independent H2 return; the ownership
repair below changes the packet before delivery. The recorded main signature is
verbatim, and the Lean module remains byte-for-byte unchanged (SHA256
`dcd98fb9c43b10d562012d2534f95d266bce5d3b222ce93759b3d2a02884a683`).


## New nodes

`def-weil-pbc-tensor-descent-representative-comparison` is an `existing: true`
definition node on `Sheaf.Paper.SiteDerivedTensorRestriction`; no new Lean module
or copy of a construction is introduced. It owns exactly the seven published
helpers needed to expose flat-term K-flat representatives, the ordinary total
tensor functor, the selected resolving predicate and its two comparisons, the
curried published derived tensor, and the resulting two-factor computation
isomorphism. The main recorded signature is the source's `def tensorDescentPair`
verbatim, including its full domain and codomain. The seven declarations are
listed in `lean.declarations`.

Source: Stacks, `sites-cohomology.tex`, Tag 06YS (`lemma-K-flat-resolution`)
and Tag 06YU (`definition-derived-tor` and its preceding construction), together
with the already-recorded two-factor descent datum. I reopened that source and
the ancestor blueprint's perfect projection formula proof, first paragraph,
where tensor's shift comparisons enter the thick-subcategory argument.

Clause correspondence for the new node:

- General ringed site and modules: `C : Type u`, `Category.{v} C`,
  `EssentiallySmall.{r} C`, `J`, `R`, and `ringedSiteModules.{r}` in the existing
  source. `HasDerivedCategory.{w}` retains independent derived morphism size.
- Ordinary total tensor: `SiteTensorComplexFunctor` uses the recorded monoidal
  sheaf tensor and `map₂HomologicalComplex` on three copies of `ComplexShape.up ℤ`.
- Flat-term K-flat: `TensorFlatRepresentative P` is the conjunction of the
  recorded independent-coefficient K-flat predicate and `∀ i, IsFlatOnSite (P.X i)`.
- Selected predicate and comparisons: `tensorDescentClass` is `d.choose`,
  `tensorDescentComplexIso` is `d.choose_spec.2.2.1.choose_spec.1.some`, and
  `tensorDescentDerivedIso` is
  `d.choose_spec.2.2.1.choose_spec.2.choose_spec.some`, for the SAME descent
  theorem `d` at universes `u,v,r,w,0,0`. Thus the use of a theorem here is the
  actual selection of its datum, not an unused restriction-theorem dependency.
- Curried derived tensor: `siteRestrictionDerivedTensor` is exactly
  `Functor.curry.obj (siteDerivedTensorIndependentCoefficients J R)`.
- The comparison formula: `tensorDescentPair` first applies the inverse
  `quotientCompQhIso` at the total tensor, next `Qh.mapIso` of the inverse
  chain-to-homotopy comparison, next the resolving comparison at the two
  representatives, and finally the derived bifunctor applied to the product of
  the two `quotientCompQhIso` comparisons. These are exactly the four factors
  in the new node's displayed formula. The resolving witnesses come from
  `(d.choose_spec.1 _).2 hP` and its counterpart for the other factor.

Searches on 2026-10-21, preserved in the new node as returned by the services:
`msearch.py leansearch` for "Flat term K flat representatives and the canonical
two factor total tensor comparison with the published derived tensor on a
ringed site" returned eight ordinary module-flatness results; `leanfinder`
for "Curried derived tensor with canonical comparison from total tensor of two
K flat complexes with flat terms" returned eight homological-complex tensor
results. Neither supplies these site comparison wrappers. `msearch.py grep`
for the seven declaration names in `Algebra/Homology` returned zero Mathlib
hits. Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` locate the
exact declarations only in the published restriction module; the existing
DAG name matches are theorem records, not definition owners.
`tools/blueprint_refs.py search 'flat-term K-flat'` found the completed exchange
map and the general Weil tensor-product definition, neither this notion.
`tools/blueprint_refs.py ancestor` gives
`lemma-weil-pbc-perfect-projection-formula`, as used in the new node's ancestry.
No new mathematical notion or theorem is asserted: the definition node records
the exact existing interface, as the maintainer requested.

## Repair of return H2

The independent review of immutable head `11346db0c65e` found that
`lem-trf-site-derived-tensor-restriction` was added only to cite plain definitions.
Removed that theorem from the item's added stmt_deps and substituted the new
definition node above. The original eight stmt_deps are unchanged. Its descent
theorem remains the actual source of all `.choose` terms. The item's statement,
proof, proof_deps, helper predicates and theorem signature are unchanged; there
is no statement correction and no dependency-module repair. The import of the
existing restriction module stays because it provides the seven actual defs.

Self-review with both the new node and its source open verified all seven
names, the comparison orientations and the universes. The source's choices
come solely from the already-cited descent theorem. Zero and unbounded
complexes, zero rings, negative shifts and nonflat varying complexes remain
covered exactly as in the original packet; the new owner excludes no case.
Only the item's `lean` and `stmt_deps`, the new definition node and this report
change. The maintainer's substantive Lean review is retained.

Repair validation: the prescribed `scompile.py` checked the unchanged module
cleanly as both sandbox and library module (16.1 s and 16.2 s), with no warnings.
A separate metadata self-check verified both signatures verbatim against their
source, all seven definition names, the exact new-node citation set, the original
eight statement dependencies plus the new definition owner, and the unchanged
Lean SHA256. A signature-extraction bug in the new node record was caught and
repaired before the final dry run: named-argument `:=` is not a body delimiter.
