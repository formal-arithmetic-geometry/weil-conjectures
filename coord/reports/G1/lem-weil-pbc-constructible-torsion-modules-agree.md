## Reviewer fix (R-ctm1135, stage 2)

The delivery re-recorded the dependency def-weil-pbc-constructible-torsion at a second
definition `CurveCoefficientPair.IsAbelianConstructible` (new module
CurveCoefficientPairAbelianConstructible), although K1's `CurveCoefficientPair.IsConstructible`
(d2af24026) is the reviewed record of that notion: two definitions of one notion (H4/H12), and
the bridge would not have been usable by the citers, which hold `P.IsConstructible`
(prop-weil-pbc-algebraically-closed-extension step 10). Fix: the dependency node is reverted to
the sheaf-dag record, the extra module is dropped, and clause (i) is the recorded
`P.IsConstructible`. The same-partitions clause now quantifies over the recorded
`Scheme.Stratification C` (constructible locally closed parts with immersions, the partitions
of `IsConstructibleEtaleSheafOfSets`) and states, on each fixed stratification, set-sheaf finite
local constancy (the stratum condition of `P.IsConstructible`) iff the node's abelian
condition (abelian `upperStar` locally constant with finite geometric stalks), and the abelian
condition iff the module condition (the stratum body of `IsConstructibleEtaleModuleSheaf`).
The rest of the statement (hypotheses, torsion, curve coefficient pair, unique module lift) is
unchanged.

## Worker report

The item is stated by `AlgebraicGeometry.Scheme.constructible_torsion_modules_agree` in
`lean/Sheaf/AlgebraicGeometry/ConstructibleTorsionModulesAgree.lean`. The proof is `sorry`.
Its docstring carries all six node proof steps and the named proof ingredients.
No item statement correction and no new nodes are needed.

Hypothesis and clause correspondence:

- Algebraically closed field k: `{k : Type v} [Field k] [IsAlgClosed k]`.
- Separated finite-type k-scheme C of dimension at most one: `{C : Scheme.{v}}`,
  `f : C ⟶ Spec (.of k)`, `[IsCurve f]`. Its recorded source class extends
  `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`, and has
  `topologicalKrullDim C ≤ 1`. No connectedness, nonemptiness or properness is imposed.
- Integer n at least one: `(n : ℕ) (hn : 0 < n)`, the same positive integers.
  `NeZero n` is derived from hn in the conclusion, not added as a hypothesis.
- Abelian etale sheaf F: `Sheaf C.smallEtaleTopology AddCommGrpCat.{v + 1}`.
- Multiplication by n vanishes: `(hF : n • 𝟙 F = 0)` in the abelian sheaf category.
- Torsion: `∃ hT : C.IsTorsionAbelianSheaf F`, the recorded colimit-of-kernels predicate.
- Curve coefficient pair: `let P : CurveCoefficientPair k :=
  ⟨C, f, inferInstance, F, hT⟩`, with precisely the original C, F and structure morphism.
- Module structure extending the abelian structure: `R := ULift.{v + 1} (ZMod n)`,
  a universe lift of the cyclic ring, and `M : Sheaf C.smallEtaleTopology (ModuleCat R)`
  with `e : U.obj M ≅ F`, where U is `sheafCompose` of `forget₂ ModuleCat AddCommGrpCat`.
  This is the constant-coefficient encoding expressly allowed by def-weil-pbc-etale-sheaves.
- Exactly one structure: for every other lift N and identification eN, there exists exactly
  one module isomorphism a with `U.mapIso a ≪≫ eN = e`. Transport via e/eN fixes the
  underlying abelian sheaf. Existence of this lift of the identity is uniqueness of the
  transported scalar action; conversely the unique action yields exactly this lift.
  Equality of arbitrary bundled carriers would not express uniqueness of scalar action.
- (i) versus (ii): `P.IsAbelianConstructible ↔ IsConstructibleEtaleModuleSheaf M`.
  The dependency repair below provides the exact abelian interpretation requested by (i).
- The same finite partitions and immersions serve: the final `∀ S : LocallyClosedStratification C`
  gives an iff for each fixed S, retaining its domains and immersion morphisms on both sides.
  This structure is a finite pairwise-disjoint locally-closed partition with the image of each
  immersion equal to its part. Both sides also require `Topology.IsConstructible (S.stratum i)`.
- Abelian restriction: `Etale.upperStar AddCommGrpCat (S.immersion i)`.
  Abelian local constancy: `IsLocallyConstantSheaf G`, whose recorded LocallyConstantDatum
  consists of an etale cover and constancy in AddCommGrpCat on each localized site.
- Finite geometric stalks: for every algebraically closed field Ω and point
  `s : Spec Ω ⟶ S.domain i`, `Finite ((pointSmallEtale s).sheafFiber.obj G)`.
  The fiber is explicitly instantiated with `A := AddCommGrpCat`, not Type or a finite-generation
  predicate. It is the recorded colimit over pointed etale neighborhoods.
- Module restriction: `Etale.upperStar (ModuleCat R) (S.immersion i)`.
  Module local constancy with finite values: `∃ d : LocallyConstantDatum G`, and for each
  cover member `∃ A : ModuleCat R, Finite A ∧ Nonempty (G.over (...) ≅ constantSheaf.obj A)`.
  This is literally the body of the recorded module constructibility definition on the fixed S.
- The ingredients in parentheses are proof guidance, carried in steps 3--6 of the docstring.
  The argument for the fixed-partition comparison does not use the curve hypotheses; they
  provide the curve coefficient pair in the conclusion.

Dependency declarations read and used:

- Mathlib.CategoryTheory.Sites.Sheaf: `CategoryTheory.Sheaf`, `sheafCompose`.
- Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.smallEtaleTopology`.
- Sheaf.AlgebraicGeometry.TorsionEtaleSheaf: `Scheme.IsTorsionAbelianSheaf`.
- Sheaf.AlgebraicGeometry.CurveCoefficientPair: `AlgebraicGeometry.CurveCoefficientPair`.
- Sheaf.AlgebraicGeometry.EtaleSheaves (record read): its note authorizes ModuleCat-valued
  constant-coefficient sheaves; none of its set-local-constancy predicates are substituted here.
- Sheaf.AlgebraicGeometry.CurveCoefficientPairAbelianConstructible:
  `CurveCoefficientPair.IsAbelianConstructible` (dependency module of this delivery).
- Mathlib.Topology.Constructible: `Topology.IsConstructible`.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: `Etale.upperStar`.
- WeilConjectures.ConstructibleSheaf.Defs: `Scheme.IsLocallyConstantSheaf`,
  `Scheme.LocallyConstantDatum`, `Cover.etalePrecoverageToEtale`.
- Mathlib.CategoryTheory.Sites.Point.Basic: `GrothendieckTopology.Point.sheafFiber`;
  Mathlib.AlgebraicGeometry.Sites.EtalePoint: `Scheme.pointSmallEtale`.
- Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf:
  `Scheme.IsConstructibleEtaleModuleSheaf`.
- The fixed partition is the already recorded `Scheme.LocallyClosedStratification` from
  Sheaf.AlgebraicGeometry.LocallyClosedStratification; it is also used inside the module predicate.

Edge cases checked before writing: C may be empty, zero-dimensional, disconnected or nonreduced;
IsCurve permits all of these. A partition can have zero parts when C is empty. Empty strata
and empty trivializing members do not force their constant values finite or killed by n;
step 5 discards empty members without changing the cover. A finite module trivialization exists
on an empty stratum using the zero module. At n=1 the cyclic ring is the zero ring, and hF forces
F to be zero; uniqueness and constructibility still hold. n=0 is excluded exactly as in the node.
The zero sheaf is included, and there is no condition that n be invertible in the field.
The coefficient universe is one above the scheme universe, following the dependency conventions;
ULift raises ZMod n without changing the ring. No hypothesis is vacuous or newly introduced.

Searches, run with /home/ubuntu/weil-launcher/msearch.py:

- leanfinder, `constructible abelian etale sheaf killed by n agrees with constructible Z/n module sheaf`:
  eight condensed-module hits, none about this etale constructibility comparison.
- loogle, `CategoryTheory.Sheaf, ZMod`: zero hits.
- leansearch, `constructible abelian sheaf killed by n equivalent constructible ZMod n module sheaf`:
  service unavailable (Internal Server Error); recorded as unavailable, not a no-match verdict.
- grep, `constructible.*(forget|ZMod)|ZMod.*[Ss]heaf|[Ss]heaf.*ZMod`: zero Mathlib hits.
- rg on WeilConjectures/ConstructibleSheaf and lean/Sheaf/AlgebraicGeometry for killed, ZMod,
  zmod and forgetting/constructibility: found coefficient conventions and finite-etale-trace
  discussion, no statement of this comparison. A node-id search of all WeilConjectures gave no hit.
- rg for ConstructibleTorsion, IsConstructibleAbelian and IsConstructible.*Abelian in both
  project libraries found no exact abelian finite-stalk constructibility definition.
  Source IsConstructibleSheaf uses finite generation of stalks (incorrect for literal finite
  abelian stalks), so cannot supply this dependency specialization.

The literature checkout is absent locally; the cited source places were opened directly:
https://stacks.math.columbia.edu/tag/03RW (abelian and module clauses),
https://stacks.math.columbia.edu/tag/03RU (constancy in the appropriate coefficient category),
and https://stacks.math.columbia.edu/tag/095E (global finite partition on qcqs schemes).
No mathematical dispute or item statement fault was found.

Validation: both delivery modules compiled together with scompile.py on the server, without
errors or warnings. The dependency's original set-valued formulation is retained in its original
module for other users; the new record points to the exact abelian formulation instead.

## Dependency modules

`def-weil-pbc-constructible-torsion`: the original recorded
`CurveCoefficientPair.IsConstructible` tests local constancy after forgetting to sets.
This item's (i) explicitly specifies abelian local constancy and finite abelian geometric stalks.
Its usable replacement is `CurveCoefficientPair.IsAbelianConstructible`, in
`lean/Sheaf/AlgebraicGeometry/CurveCoefficientPairAbelianConstructible.lean`.
It states the node's notion on the same curve coefficient pair, using the existing finite
partition, abelian inverse-image, abelian local-constancy, and geometric-stalk declarations.
Its data is fully written; there is no sorry in the definition. Only this dependency's lean
record changes, with the required note; its statement and all other fields stay unchanged.
A separate module/name leaves the old declaration available and avoids changing other users.

## Second reading by G1

I did not write these modules. I read the item and every statement-dependency node,
both delivery modules, and the recorded declarations. I independently opened Stacks
03RW, 03RU and 095E, and downloaded `etale-cohomology.tex` into the item's scratchpad
because the literature checkout is absent. In the TeX, 03RW assumes a scheme and,
for modules, a Noetherian coefficient ring. Here Z/n is finite, hence Noetherian.
095E assumes qcqs; the curve is finite type over a field and separated, hence qcqs.
03RU distinguishes constancy as sets, abelian groups and modules. No characteristic
or invertibility hypothesis occurs in these sources.

Object/hypothesis/conclusion checklist, made from the node and checked against Lean:

- Algebraically closed field k: `{k : Type v} [Field k] [IsAlgClosed k]`. PASS.
- Separated finite-type k-scheme C with dimension at most one: `{C : Scheme.{v}}`,
  `(f : C ⟶ Spec (.of k)) [IsCurve f]`. I read `IsCurve` in upstream
  AlgebraicGeometry/Curve.lean: its parents are IsSeparated, LocallyOfFiniteType and
  QuasiCompact, and its field is `topologicalKrullDim C ≤ 1`. These are exactly the
  requested hypotheses, with no connectedness or properness. PASS.
- Integer n at least one: `(n : ℕ) (hn : 0 < n)`. Positive natural numbers represent
  exactly these integers. The conclusion derives NeZero; it is not assumed. PASS.
- Abelian sheaf F on the small etale site: `Sheaf C.smallEtaleTopology
  AddCommGrpCat.{v + 1}`. Mathlib's Sheaf is the full subcategory satisfying the sheaf
  condition, and smallEtaleTopology is the recorded scheme site. PASS.
- Multiplication by n vanishes: `(hF : n • 𝟙 F = 0)`. This is equality of abelian
  sheaf morphisms, not merely a condition on selected stalks. PASS.
- F is torsion: `∃ hT : C.IsTorsionAbelianSheaf F`. I read its kernel diagram,
  transition maps and canonical colimit map; this is the recorded definition. PASS.
- The same C and F form a curve coefficient pair: `P := ⟨C, f, inferInstance, F, hT⟩`.
  I read all five fields of CurveCoefficientPair; none replaces C or F. PASS.
- Exactly one sheaf-of-Z/n-module structure extending F: `R := ULift (ZMod n)`,
  `U := sheafCompose ... (forget₂ ... AddCommGrpCat)`, and `∃ M e` with `U.obj M ≅ F`.
  The universal clause `∀ N eN, ∃! a : M ≅ N, U.mapIso a ≪≫ eN = e` fixes the
  underlying abelian identification. Transporting the actions along e and eN shows
  existence of such a forces equality of the actions on F; conversely equal actions
  give that lift, unique since U is faithful. Thus this is uniqueness of structure,
  including existence, rather than uniqueness only up to an arbitrary isomorphism.
  The lifted ring is ring-isomorphic to Z/n, and the etale-sheaves dependency expressly
  permits ModuleCat-valued constant-coefficient sheaves. PASS.
- Clause (i): `P.IsAbelianConstructible`. I read the replacement dependency in full:
  a finite locally closed constructible partition, abelian upperStar on its immersions,
  abelian `IsLocallyConstantSheaf`, and literal `Finite` geometric fibers. PASS.
- Clause (ii): `IsConstructibleEtaleModuleSheaf M`. I opened that recorded definition:
  the same partition notion, constructible strata, module upperStar, an etale
  LocallyConstantDatum, and constant module values A with `Finite A`. PASS.
- Equivalence: `P.IsAbelianConstructible ↔ IsConstructibleEtaleModuleSheaf M`. PASS.
- The same finite partitions and immersions serve: the final `∀ S` compares the
  two conditions for each fixed LocallyClosedStratification C. I read both this
  structure and its upstream Topology.Stratification parent: Fin S.n indexing,
  locally closed subsets, union equal to univ, pairwise disjointness, domain schemes,
  immersion morphisms and exact image equality. Each side separately asks all parts
  to be constructible. PASS.
- On every fixed stratum, (i) is abelian upperStar local constancy and finite stalks
  `((pointSmallEtale s).sheafFiber (A := AddCommGrpCat)).obj G`; (ii) is module
  upperStar with constant finite values on each cover member. I read upperStar's
  sheafified inverse-image construction, LocallyConstantDatum's cover and IsConstant
  fields, pointSmallEtale's fiber of lifts, and sheafFiber's colimit construction.
  The coefficient categories, points, restrictions and quantifier order match. PASS.

Dependency-module review (H13): `def-weil-pbc-constructible-torsion` is the sole
additional node copy; there are no new nodes and no statement correction. Its original
record points to IsConstructible, which explicitly forgets to sets. The item's expanded
clause (i) explicitly requires abelian local constancy. The replacement
IsAbelianConstructible states that clause on the unchanged CurveCoefficientPair and
uses recorded notions throughout. Its lean.note explains this replacement. I also
opened upstream IsConstructibleSheaf and IsFiniteSheaf: their abelian specialization
requires finitely generated abelian stalks, not finite stalks, so it is not this
notion on arbitrary torsion curve coefficient pairs. No hollow definition occurs.

Edge cases: IsCurve includes the empty scheme (dimension bottom), dimension zero,
disconnected and nonreduced curves. Fin S.n permits an empty partition exactly when
C is empty. Empty strata and empty cover members impose no nonemptiness condition;
the zero module supplies a finite constant value there. The zero sheaf is allowed.
For n=1, hF makes F zero and the zero ring still has its unique module structure.
n=0 is excluded exactly as in the node. No prime-to-characteristic condition was
added. The universe v is arbitrary; the scheme/field and geometric-point universes
follow the recorded dependency signatures, and coefficients live in v+1. Every
point of a v-small scheme has an algebraic closure of its residue field in Type v,
so the stalk condition is not vacuous. Larger geometric fields give the same etale
stalks. ULift changes universe, not the coefficient ring's mathematics. All variables
and universes are explicitly bound.

Independent searches (different wording from the worker): msearch leanfinder,
`forgetful functor from sheaves of modules over finite cyclic ring detects local
constancy and finite stalks`, returned eight condensed-module declarations, none
this comparison. Loogle `CategoryTheory.Sheaf, ModuleCat, AddCommGrpCat` returned
twelve sheaves-of-modules limits/presentation declarations, none this comparison.
LeanSearch `locally constant abelian sheaves with finite stalks and sheaves of
modules over ZMod have equivalent constructibility` was unavailable (Internal
Server Error), not a no-match result. Direct rg in Mathlib, WeilConjectures and
lean/Sheaf for constructibility with ZMod/forget, and for cyclic/killed/forget in
the constructible-sheaf modules, found no exact statement or exact replacement
definition. I inspected the existing set-valued constructibility and upstream
finite-generation alternatives described above. The item-id and
IsAbelianConstructible searches found no existing declaration. Search-service
results are recorded in searches.jsonl.

No mismatch needing a Lean or node edit was found; I retained both modules and
records. The theorem docstring follows all six proof steps with sources and named
ingredients, including discarding empty trivializing members and lifting geometric
points. Every delivered declaration has its source and blueprint tag. The only
proof is the named theorem's sorry; the dependency definition contains no sorry.
Lines and imports meet the conventions. Both lean.statement records agree verbatim
with their signatures. Both modules compiled together through scompile.py in
 dependency order, with no errors or warnings (2.3 seconds). Changes in this second
reading: this independent review section only.
