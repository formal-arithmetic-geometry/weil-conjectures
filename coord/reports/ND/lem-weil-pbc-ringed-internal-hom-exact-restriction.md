## Worker report

The module `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction` states the three
clauses of the node in `CategoryTheory.ringedInternalHom_tensor_adjunction`,
`CategoryTheory.ringedInternalHom_restriction` and `CategoryTheory.ringedInternalHom_exact`.
All nine theorem bodies are `by sorry`; no data or mathematical notion is redefined.
The other six statements supply the additive, finite-limit and finite-colimit instances
for the existing `SheafOfModules.overFunctor` and `SheafOfModules.overMap`.
These supporting facts let the restriction clause use the actual induced exact derived
functors, rather than making an assumption of exactness or accepting arbitrary functors.
Their statements and proof plans belong to the slice-restriction part of this node.

Hypotheses and clauses, matched individually:

- A small site: `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`.
  This uses the associated Grothendieck topology of the coverings in
  `def-weil-pbc-sites-and-cohomology`, as does `derivedInternalHom` itself. Ringed-site
  calculus depends only on that topology, with no extra assumption about pullbacks in C.
- A sheaf of commutative rings: `(R : Sheaf J CommRingCat.{u})`.
  `ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)` is
  the recorded module category; the composition merely forgets commutativity for
  Mathlib's module-category input. It does not change the coefficient sheaf.
- Unbounded derived category: `DerivedCategory` of this module category, with
  `[HasDerivedCategory.{w} ...]` recording the localization size choice. The restriction
  statement also records the same size choice for every slice using `[hDCU : ∀ U, ...]`.
  The explicit application `@derivedInternalHom ... (hDCU U)` supplies this instance
  across the definitionally equal slice/composition presentations of the ring sheaf.
- The specified derived tensor: `P : ObjectProperty (CochainComplex ... ℤ)` and
  `hP : ∀ X, P X ↔ X.IsKFlat` name precisely the K-flat representative subcategory.
  The functor `T` with natural comparison `r` is total tensor of those representatives
  after localization. The total tensor is the existing `curriedTensor` for
  `SheafOfModules.monoidalCategory R`, lifted by `map₂HomologicalComplex` with
  all three shapes `ComplexShape.up ℤ`. This is the existing general-site
  derived-tensor-descent interface, using all K-flat complexes; no additional object,
  finite-generation, flat-term or boundedness hypothesis is imposed on K, L, M.
  `P`, `hP`, `T`, `r` are parameters specifying this already introduced tensor,
  not a conditional replacement for the asserted Hom isomorphism. Such a comparison
  determines derived tensor up to natural isomorphism since K-flat resolutions present
  the whole derived category.
- For every K, L, M, tensor--Hom currying: the existential family `e` has components
  `H(K,H(L,M)) ≅ H(T(K,L),M)`, using the recorded `derivedInternalHom J R` throughout.
- Naturality in all three variables: the subsequent equation quantifies simultaneously
  over `a : K' ⟶ K`, `b : L' ⟶ L`, `c : M ⟶ M'`. On the first side it uses
  `H.map ((T.map (a,b)).op,c)`; on the second it uses `H.map (a.op,H.map (b.op,c))`.
  Thus this is natural for arbitrary derived morphisms, not just for representative maps.
- For each object U, restriction: the family `e U` in the restriction theorem is an
  isomorphism of bifunctors `H ⋙ restriction_U ≅ (restriction_U.op.prod restriction_U) ⋙ H_U`.
  Here `H_U` is the same `derivedInternalHom` at `J.over U`, `R.over U`;
  `restriction_U` is the actual `SheafOfModules.overFunctor ... U |>.mapDerivedCategory`.
  An isomorphism of bifunctors includes naturality in both arguments.
- Successive slice restrictions: `s U V f` is the same Hom comparison for the existing
  `overMap ... f`, for each arrow `f : V ⟶ U`. The displayed equality says that mapping
  `e U` under this derived restriction, then applying `s`, and transporting its arguments
  along the canonical derived `overFunctorMap`, equals direct `e V` after the same
  canonical transport of its source. This explicitly identifies successive and direct
  comparisons; the equation is not merely an assertion of unrelated objectwise isomorphisms.
- Distinguished triangles in the second variable: the first conjunct of
  `ringedInternalHom_exact` gives, for each L, a `CommShift ℤ` structure on
  `(Functor.curry.obj H).obj (op L)` and its `IsTriangulated` property.
- Distinguished triangles contravariantly in the first variable: the second conjunct
  does the same for `(Functor.curry.obj H).flip.obj M`, whose source is `D(O)ᵒᵖ`.
  The existing `CategoryTheory.Pretriangulated.Opposite` structure has shift by n equal
  to the opposite of shift by -n on D(O). Thus `CommShift` here encodes the required
  negative source-shift convention; the covariant conjunct encodes the positive target shift.
  `IsTriangulated` uses these shift comparisons on the connecting maps of the triangles.
- No boundedness or finite-generation condition: all complex indices are ℤ and every
  derived input is arbitrary. There is no perfectness, constructibility, compactness,
  finite-generation, boundedness or scheme/topological-space assumption.

Dependency declarations used:

- `def-weil-pbc-sites-and-cohomology`: the `CategoryTheory.GrothendieckTopology` / `Sheaf`
  site encoding underlying its recorded Precoverage and sheaf declarations. Cohomology
  itself is not used in this statement.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q` (`Mathlib.Algebra.Homology.DerivedCategory.Basic`).
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`
  (`Sheaf.CategoryTheory.RingedSiteModules`), transparently Mathlib `SheafOfModules`.
- `def-pur-derived-internal-hom`: `CategoryTheory.derivedInternalHom`
  (`Sheaf.Algebra.Homology.DerivedInternalHom`). Its full source definition and
  representative comparisons were read; it is a genuine localization of Hom complexes
  after functorial K-injective replacement, for arbitrary small ringed sites.
- `def-pc-tensor-complex-sheaves`: `CochainComplex.mapBifunctor`,
  `HomologicalComplex.mapBifunctor`, and the bifunctorial `map₂HomologicalComplex`
  (`Mathlib.Algebra.Homology.BifunctorShift` and `Bifunctor`); the monoidal tensor is
  `SheafOfModules.monoidalCategory` from the recorded framework.
- `def-pc-kflat-complex`: `CochainComplex.IsKFlat` (`Sheaf.Algebra.Homology.KFlat`).
  Its predicate tests acyclicity of total tensor against every acyclic complex.

The proof dependency modules are imported, including K-flat resolutions, general-site
K-injective resolutions, Hom complexes, K-flat-to-K-injective Hom, quasi-isomorphism
invariance, tensor and sheaf Hom, localized K-injective restriction, both signed shift
comparisons, homotopy/derived triangulations and the K-injective derived-Hom comparison.
The generic triangulated/triangle-morphism facts are in the imported Mathlib modules.
The module docstrings give the three proof steps of the node, including the currying
and cone differential signs and the identity-on-local-families coherence argument.

Edge cases checked before writing:

- Empty site: the universal U/f restriction clauses can be empty; the tensor and triangle
  clauses still concern the zero module category. No object or nonempty hypothesis is added.
- Zero ring sheaf or zero input: all isomorphisms remain zero-object isomorphisms and
  the formulas do not require a unit to be nonzero or any characteristic assumption.
- All unbounded complexes are allowed, including arbitrarily negative degrees. The Hom
  complex uses products and total tensor uses direct sums; no interchange of infinite
  products with cokernels or unjustified infinite-product exactness is claimed.
- Shift by zero and by negative integers: `CommShift ℤ` covers both, and the opposite
  structure has the required sign reversal.
- Identity arrows and compositions of restrictions: `overFunctorMap` gives the canonical
  source/argument transport, and the coherence equation applies also when f is an identity.
  Iterating this equation handles a longer composable chain of slice restrictions.
- Arbitrary small-site universe u and derived morphism universe w remain explicit.

Searches for existing statements and interfaces:

- `msearch.py` LeanFinder, query “Derived internal sheaf Hom tensor adjunction slice
  restriction distinguished triangles”: eight results, including underived closed sheaf
  structures and `SheafOfModules.PullbackConstruction.adjunction`; no matching derived
  general-site tensor/Hom/restriction/triangle statement.
- `msearch.py` Loogle, query `"derived", "Hom"`: twelve results, including instances and
  single-functor comparisons for `DerivedCategory.Qh`; none is the node's statement.
- `msearch.py` grep, regex `derivedInternalHom|RHom|derivedTensor` in `CategoryTheory`:
  results concern functor Hom and monoidal localization, not this calculus theorem.
- `msearch.py` LeanSearch, query “Derived internal sheaf Hom commutes with slice
  restriction and sends distinguished triangles to distinguished triangles”: unavailable,
  Internal Server Error. This is recorded as service unavailability, not a negative search.
- `rg` of `WeilConjectures` for derived Hom/tensor and the node id found no declaration
  stating the node. `rg` of `lean/Sheaf` found `DerivedInternalHom`, the two shift
  comparisons, `SiteDerivedTensorDescent`, and `DerivedInternalHomRestrictOpen`.
  The latter is only for opens of a ringed topological space, so cannot state this node.
  `SiteDerivedTensorDescent` supplies the representative interface but not the asserted
  tensor--Hom adjunction. These existing notions are used rather than copied.
- `rg` of Mathlib, upstream, and `lean/Sheaf` for every proposed declaration name found
  no collision. The upstream declaration-name index was searched for the expected names.

No statement correction, new definition node, dependency replacement, or
STATEMENT-DISPUTED flag is needed. Only the item's `lean` record changes.

Validation: the full module compiled cleanly with `scompile.py` on the server under
nice 19, two threads, the 60-second per-file limit (7.9 seconds before the final explicit
proof-import pass). The final delivery dry run recompiles the complete delivered file.


## Earlier second reading (a previous round; superseded)

I independently read the sandbox node and all nine declarations, the six statement
 dependency nodes and their recorded source declarations, and Stacks
`sites-cohomology.tex` around `lemma-internal-hom`, `lemma-restriction-RHom-to-U`
and `lemma-RHom-triangulated` (Tags 08J9, 08JB, 08JC), including the preceding
construction of derived Hom and K-flat-to-K-injective Hom lemma. The source assumes
an arbitrary ringed site throughout; it imposes no boundedness, finiteness,
Noetherian, field, or characteristic hypothesis.

The node's objects, hypotheses and conclusions, matched separately:

1. Small site C: `{C : Type u} [SmallCategory C]` and
   `(J : GrothendieckTopology C)` in each main theorem. Verdict: matches the topology
   governing the node's sheaves. The dependency records `Precoverage.toGrothendieck`;
   using its resulting topology loses none of these sheaves or slice constructions.
   The result also holds for arbitrary Grothendieck topologies, as does the recorded
   `derivedInternalHom`; no finite-limit condition on C is needed for the statement.
2. Commutative coefficient sheaf O: `(R : Sheaf J CommRingCat.{u})`. The
   `sheafCompose ... (forget₂ CommRingCat RingCat)` expression only forgets
   commutativity to provide the coefficient object to Mathlib's module category.
   Verdict: the same ring sheaf, with no nonzero-ring or field assumption.
3. Unbounded D(O): `DerivedCategory (ringedSiteModules.{u} ...)` with
   `HasDerivedCategory.{w}`. I opened `ringedSiteModules`: it transparently abbreviates
   `SheafOfModules`, including its actual linear morphisms and abelian structure.
   Mathlib `DerivedCategory.Basic` localizes all integer-indexed cochain complexes.
   Verdict: the specified derived category; the instance chooses localization size.
4. H: every occurrence is `derivedInternalHom.{u,w} J R`. Its definition is
   `Localization.lift` of the actual Hom complex after functorial K-injective
   replacement, not an unconstrained bifunctor. Its representative-comparison
   signatures allow arbitrary complexes in the first variable and arbitrary
   K-injective representatives in the second. Verdict: precisely the dependency.
5. Derived tensor: `P`, `hP : ∀ X, P X ↔ X.IsKFlat`, `T` and the natural isomorphism
   `r` specify total tensor of K-flat representatives after `DerivedCategory.Q`.
   I checked `IsKFlat`, `SheafOfModules.monoidalCategory`, and
   `Functor.map₂HomologicalComplex`: the latter's object is `mapBifunctor`, the
   direct-sum total complex of the termwise tensor. Verdict: no replacement tensor
   or flat-term hypothesis. Restricting Q to all K-flat complexes presents D(O),
   so this natural comparison determines T up to natural isomorphism. The binders
   specify the tensor already introduced in the node; they do not assume the
   conclusion or constrain K, L, M.
6. All K, L, M and the currying isomorphism: the existential family in
   `ringedInternalHom_tensor_adjunction` has exactly
   `H(K,H(L,M)) ≅ H(T(K,L),M)`. Verdict: correct order, variance and objects.
7. Naturality: after that family, the equation quantifies over arbitrary
   `a : K' ⟶ K`, `b : L' ⟶ L`, `c : M ⟶ M'`. It equates currying followed by
   `H((T.map (a,b)).op,c)` with `H(a.op,H(b.op,c))` followed by currying at
   K', L', M'. Verdict: natural in all three derived variables simultaneously.
8. Every object U and O_U: `ringedInternalHom_restriction` quantifies `e : ∀ U : C`;
   its target uses `J.over U`, `R.over U`, and the explicit localization instance
   `hDCU U`. The common w is a size choice, available for the small family of slice
   sites. Verdict: all objects and the actual restricted coefficient sheaf.
9. Natural restriction comparison: `e U` is a natural isomorphism of bifunctors
   between H followed by the induced `overFunctor` and the two restricted arguments
   followed by slice H. Verdict: both arguments natural, actual exact derived
   restriction, and the same orientation as the node (the source's equality is
   symmetric). No arbitrary restriction functor is substituted.
10. Successive restrictions: `s U V f` is the bifunctor comparison for
    `SheafOfModules.overMap ... f`. The equation maps `e U` under that derived
    functor, composes with s, and transports arguments by the canonical derived
    `overFunctorMap`; this equals transporting H itself and applying `e V`.
    I opened Mathlib's `overMap` and `overFunctorMap` and the induced composition
    interface. The argument transport uses inverse in the contravariant slot and
    forward map in the covariant slot. Verdict: genuine compatibility, not unrelated
    objectwise isomorphisms.
11. Triangles in the second variable: the first conjunct of
    `ringedInternalHom_exact` supplies `CommShift ℤ` and `IsTriangulated` for
    `(Functor.curry.obj H).obj (op L)`, for every L. Mathlib's `IsTriangulated`
    sends all distinguished triangles, including their connecting arrows, to
    distinguished triangles using that shift comparison. Verdict: exact clause.
12. Triangles contravariantly in the first variable: the second conjunct supplies
    these structures for `(Functor.curry.obj H).flip.obj M`, for every M.
    I checked `Triangulated.Opposite.Pretriangulated`: shift by n on the opposite
    is shift by -n on D(O), with its reversed distinguished triangles.
    Verdict: the node's negative first-variable shift and contravariant exactness.
13. No bounds or finite generation: all inputs are unrestricted objects of D(O),
    with complex shape `up ℤ`; there is no perfectness or constructibility premise.
    Verdict: all unbounded objects covered.

The six supporting `ringedSite_overFunctor_*` / `ringedSite_overMap_*` theorems
supply additivity and preservation of finite limits and colimits, rather than
asking for extra exactness hypotheses in clause 9. All are public named theorems
with `sorry`, source, blueprint tag and proof plans. No new definition node or
dependency module is delivered. No data definition, hidden instance, local notation,
private copy, or completed proof occurs in the delivered module. The three main
docstrings carry the node's currying differential, identity-on-local-families
restriction argument, and both signed cone arguments and K-injective-cone reasoning.

Edge cases: an empty C makes the U/f clauses vacuous but does not remove the other
clauses; zero rings and zero derived objects are allowed. Empty schemes are included
when their sites are used. No index set, characteristic, nonempty object, or nonzero
integer is assumed. `CommShift ℤ` covers shift zero and negative shifts. Identity
arrows and successive arrows are included in the coherence equation. Site and
coefficient universe u can be enlarged together to include any small ringed site;
w is explicit for derived morphisms. All variables and universes are bound.

Independent searches used different terms from the worker:

- LeanFinder: “Closed derived module category internal Hom currying tensor and
  localization at an object”: eight results, involving Gabriel-Popescu tensor
  adjunctions, Ext, and Tor. None states these unbounded internal-sheaf-Hom clauses.
- Loogle: `"overFunctor"`: seven results. I read the relevant Mathlib declarations
  `SheafOfModules.overFunctor` and `overFunctorMap`; these are the restriction
  constructions already used, not derived Hom calculus.
- LeanSearch: “Internal derived Hom is an exact bifunctor and commutes with
  localization of a ringed site”: unavailable (Internal Server Error), not a
  negative mathematical search result.
- `rg` in Mathlib, upstream `WeilConjectures`, the upstream name index, and
  `lean/Sheaf`, using `internalHom`, `RHom`, `rhom`, `derivedHom`,
  `derivedInternalHom` and restriction/additivity/finite-limit terms. Upstream
  `HomotopyCategory.tensorHomAdjunction` is an adjunction on the homotopy category
  with a monoidal-closed hypothesis, not this localized sheaf bifunctor.
  `Sheaf.Paper.DerivedInternalHomRestrictOpen` applies to opens of a ringed space;
  its existing signature does not cover arbitrary small sites or this coherence
  equation. The six `moduleOverFunctor_*` / `moduleOverMap_*` facts in
  `DerivedHomMayerVietoris` likewise take a ringed space. Existing
  `localized_restriction_adjunction` has a zero-preservation hypothesis and a
  bundled exact-left-adjoint conclusion, rather than the six direct instance
  signatures. No exact duplicate or name collision was found.

One report clarification: `site_derived_tensor_descent` uses K-flat flat-term
objects in the homotopy category, whereas this module uses all K-flat complexes
in the complex category. I opened that theorem; its existence/descent result is
not literally the same interface. Both describe total tensor after K-flat
replacement, and this does not change this item's statement. No Lean repair or
node correction was necessary; the second reading changes the report only.
The node's primary `lean.statement` was checked byte-for-byte against the theorem
signature. There are exactly nine named theorem sorries and no overlength lines.

Validation: `scompile.py` compiled the delivered module cleanly on the server
(7.9 seconds; nice 19, two threads, 60 seconds per file), also compiling the
required side-only `RingedSiteModules` import (1.0 second). Delivery preflight
and its server compile are run again below through `deliver2.py`.

Worker continuation check (2026-10-15): reread the three Stacks source lemmas and
all six statement-dependency records and the relevant definitions. The prior module
needs no change. Fresh `msearch.py` LeanFinder query “Derived internal Hom tensor
currying exact restriction to slice ringed site” returned eight underived sheaf or
light-condensed closed-structure results, none matching. Loogle query
`SheafOfModules.overFunctor, derivedInternalHom` returned no hits (unknown identifier
`derivedInternalHom`); grep `derivedInternalHom|ringedInternalHom` in Mathlib's
`Algebra/Homology` returned no hits. Project/upstream `rg` confirmed the existing
Hom definition, shift comparisons and ringed-space-only restriction result rather
than this general-site calculus statement. The server compilation completed cleanly
in 8.0 seconds, at nice 19 with two threads and the 60-second file limit. The dry run
passed preflight and compilation; nothing was pushed. The independent second-reading
section above is retained from the earlier sandbox attempt for the next reader.


## Second reading by ND

Fresh independent reading, 2026-10-15. I read the current sandbox node and the
whole module, the six statement dependencies and their Lean records, their actual
source declarations, and Stacks sites-cohomology.tex at lines 8840–8970 (Tags
08J9, 08JB, 08JC and the preceding construction). The source assumes a ringed
site, not a scheme or a Noetherian space. No statement_change is present or needed.

Object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. A small site: `{C : Type u} [SmallCategory C]` and
   `J : GrothendieckTopology C`. Matches the topology underlying the dependency's
   `Precoverage.toGrothendieck`; the Hom construction and slice restrictions use
   that topology. No extra existence of fibre products is required by these clauses.
2. A commutative ring sheaf: `R : Sheaf J CommRingCat.{u}`. Matches exactly.
   `sheafCompose J (forget₂ CommRingCat RingCat)` forgets commutativity only for
   the existing module-category input; it does not change the rings or sections.
3. The unbounded module derived category: `DerivedCategory (ringedSiteModules …)`
   with `HasDerivedCategory.{w}`. I opened RingedSiteModules: this is transparently
   `SheafOfModules.{u}`, with its actual module objects and linear morphisms.
   Mathlib DerivedCategory.Basic localizes all integer-indexed complexes at
   quasi-isomorphisms; the instance only fixes the localization morphism size.
4. Derived internal Hom H: every occurrence uses `derivedInternalHom J R` from
   the recorded dependency. Its actual body is Localization.lift of the Hom
   complex after functorial K-injective replacement; its comparison and object
   comparison signatures allow the representatives required by this node.
   Matches; there is no arbitrary bifunctor standing in for H.
5. Derived tensor: `P`, `hP : ∀ X, P X ↔ X.IsKFlat`, `T`, and `r` specify
   localization of total tensor on all K-flat representatives. I read IsKFlat:
   it tests total tensor against every acyclic complex. Mathlib's
   map₂HomologicalComplex has mapBifunctor as its object, the direct-sum total
   tensor with the cochain signs. Thus these binders specify the node's tensor,
   up to natural isomorphism, without imposing conditions on K, L, M. Matches.
6. All K, L, M and currying: `ringedInternalHom_tensor_adjunction` supplies
   `∃ e : ∀ K L M, H(K,H(L,M)) ≅ H(T(K,L),M)`. Same order, objects and variance.
7. Naturality in three variables: the following equality quantifies arbitrary
   `a : K' ⟶ K`, `b : L' ⟶ L`, `c : M ⟶ M'`. Its two paths use respectively
   `H.map ((T.map (a,b)).op,c)` and `H.map (a.op,H.map (b.op,c))`.
   Matches simultaneous naturality for all derived morphisms.
8. Every U, restricted coefficients and arguments: `ringedInternalHom_restriction`
   supplies `e : ∀ U : C` using `J.over U`, `R.over U`, the existing
   `SheafOfModules.overFunctor`, and its induced mapDerivedCategory. The `hDCU`
   family selects localization sizes for the slices, explicitly passed to H_U.
   Matches actual slice restriction, with no arbitrary restriction operation.
9. Natural comparison: each `e U` is an isomorphism of bifunctors from H followed
   by restriction to H_U on the restricted arguments. Matches naturality in
   both variables and the displayed restriction isomorphism in the node.
10. Successive restrictions: `s U V f` supplies the comparison along the actual
    `overMap f`. The coherence equation maps `e U`, composes with `s`, then
    transports by derived `overFunctorMap`; it equals direct `e V` after source
    transport. I opened overFunctorMap: its component is the identity on local
    sections. The inverse in the opposite argument and forward map in the
    covariant argument have the correct directions. Matches compatibility.
11. Second-variable triangles and shifts: the first conjunct of
    `ringedInternalHom_exact` gives CommShift ℤ and IsTriangulated for H(L,-),
    for every L. Matches all distinguished triangles, including the shifted
    connecting maps, and positive shifts.
12. First-variable triangles and shifts: the second conjunct gives the same
    structures for H(-,M) from the opposite triangulated category, for every M.
    I read Opposite.Pretriangulated: distinguished triangles are reversed and
    the opposite shift reverses the integer. Matches contravariance and the
    negative first-variable shift.
13. No boundedness or finite generation: all inputs above are arbitrary derived
    objects; no perfectness, flat-term, boundedness, nonzero or finite-generation
    premise occurs. Matches the final sentence of the node.

Edge cases: the empty site is allowed (the U and f clauses are then empty);
zero ring sheaves and zero complexes are allowed. Empty schemes are included
through their small sites. No field, characteristic, nonempty index set or
positive degree is assumed. Integer shifts include zero and negative shifts.
Identity f and every composable restriction are covered by the coherence equation.
The universe u is arbitrary for small sites and coefficients; w is an explicit
localization size, including a common choice for the small family of slices.
All variables and universes are explicitly bound.

Independent searches with fresh terms: LeanFinder query "Internal Hom derived
currying localization slice triangulated bifunctor" returned eight generic
triangulated-localization facts, no matching theorem. Loogle query `"overMap"`
returned twelve slice/topology and sheaf-pushforward comparisons, not these
Hom clauses. LeanSearch query "Unbounded internal sheaf Hom exact in both
variables and compatible with localization at an object" was unavailable
(Internal Server Error); this is not a negative search. Direct rg searches of
Mathlib, upstream WeilConjectures and project Sheaf used ringedInternalHom,
ringedSite_over, derivedInternalHom, tensorHomAdjunction and overFunctor/overMap.
I opened upstream DerivedCategory.Monoidal.Closed.tensorHomAdjunctionQhObj:
its adjunction uses its own closed-category derived Hom, not this internal Hom
calculus with coherent slice restriction. Project DerivedInternalHomRestrictOpen
is restricted to ringed topological spaces; it does not state this general-site
result. No exact duplicate was found. Existing dependency notions are reused.

The six auxiliary exactness instance theorems have named sorry proofs, source
and blueprint docstrings, and local section/sheafification proof plans. The three
main docstrings include the currying differential, the identity-on-local-families
restriction argument, both cone calculations and the K-injective cone argument.
There are no new definition nodes, dependency modules, hollow definitions,
private copies, local notation or completed proofs in this delivery.

No mathematical mismatch was found. I changed only this report, retaining the
Worker report and earlier review history. The primary lean.statement matches
the file signature byte for byte; all lines are at most 100 characters and all
nine theorem proofs are sorry. Fresh server compilation and delivery validation
are recorded by the commands following this reading.
