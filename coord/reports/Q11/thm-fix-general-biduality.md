## Worker report

The module `Sheaf.Paper.FiniteStageVerdierBiduality` states
`WeilConjectures.finite_stage_verdier_biduality`, with proof `sorry`.
The statement is the conjunction of the small-etale and small-pro-etale conclusions.
The original node statement, source, dependency lists and proof are unchanged.
No statement correction, new independent definition node, disputed statement, ambient
exceptional-adjoint hypothesis or boundary-duality hypothesis is introduced.

Hypotheses and clauses, matched individually:

- The standing field `k = Fbar_q` is `D : WeilConjectures.FiniteFieldDatum.{u}`,
  and the base is `Spec (.of D.k)`. The recorded datum includes the prime p,
  positive exponent a, q = p^a, finite field k0 with q elements, and its fixed
  algebraic closure k. The theorem does not require Y to descend to k0.
- The standing prime different from the characteristic is `(l : ℕ) [Fact l.Prime]`
  and `_hl : l ≠ D.p`. It is not replaced by a coefficient-field assumption.
- A finite extension E/Q_l is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Both conclusions use precisely
  `Padic.coefficientExtensionRing l E n`, the recorded quotient by the chosen
  uniformizer to exponent n. `ULift.{u+1,u}` is its canonical ring lift for the
  existing ModuleCat coefficient universe, not a new ring or a field quotient.
- The positive finite stage is `(n : ℕ) (hn : 1 ≤ n)`. The helper definitions
  install the recorded `Padic.finite_coefficientExtensionRing l E n hn`, rather
  than requiring Finite of this ring as an additional theorem hypothesis.
- Y is `(Y : Scheme.{u})`, with its named structure morphism
  `(aY : Y ⟶ Spec (.of D.k))`. Separated is `[IsSeparated aY]`; finite type is
  `[LocallyOfFiniteType aY] [QuasiCompact aY]`. No properness, smoothness,
  connectedness, dimension bound, nonemptiness or compactification choice is added.
  The existing Nagata instance supplies the compactification used by the operations.
- The etale site is `Y.smallEtaleTopology` on `Y.Etale`; its ambient category
  is `Etale.DerivedCategoryModule (ULift ... A) Y`. The pro-etale site is
  `Scheme.ProEt.topology Y` on `Y.ProEt`, in the existing fixed-scalar
  `DerivedCategory (Sheaf ... (ModuleCat (ULift ... A)))` presentation.
- Etale `D^b_ctf` is `finiteTorConstructibleEtale l E n hn Y`: the recorded
  `Etale.DerivedCategory.isBoundedConstructible` intersected with existence of
  one ordered interval for `Etale.DerivedCategory.hasTorAmplitudeIn`. The latter
  tests every module sheaf in degree zero, not just constructible test sheaves.
- Pro-etale `D^b_ctf` is `finiteTorConstructibleProEtaleModule l E n hn Y`:
  apply the existing exact `finiteCoefficientIntrinsicRealization` termwise,
  then use precisely `finiteTorConstructible l E n hn Y`. Thus both intrinsic
  cohomological constructibility and finite Tor amplitude are retained. This
  does not redefine pro-etale constructibility as etale origin or assume a
  descent theorem. The original ringed-site object universe u+1 and morphism
  universe u remain unchanged.
- On the etale site omega is exactly `Etale.dualizingComplex (ModuleCat ... A) aY`;
  on the pro-etale site it is `ProEtale.finiteCoefficientDualizingComplex ... aY`.
  I read their definitions: each applies exceptional inverse image to the unit.
  The pro-etale exceptional functor is the specified `Rnu_* ⋙ aY^times ⋙ nu^*`,
  not an ambient pro-etale right adjoint or an arbitrary supplied object.
- The etale Verdier functor is the existing `Etale.verdierDual`. The pro-etale
  functor uses `MonoidalClosed.internalHom.flip.obj omega`, exactly the definition
  of upstream `ProEtale.derivedHom.flip.obj omega` with that wrapper unfolded.
  These use the existing closed derived tensor-Hom adjunction. The imported
  general `derivedInternalHomOfUniverses` is the K-injective Hom-complex
  presentation of the same derived internal Hom; no new Hom functor is supplied.
- Contravariance is the actual functor type `Cᵒᵖ ⥤ C`, not an object assignment.
  `IsExactAntiEquivalenceOn` first asserts direct preservation of the object
  property; next it asserts an equivalence `P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory`
  together with a natural isomorphism of its composite with inclusion to the
  specified ambient D. This identifies its map action, not just its object values.
- Exactness is the last clause of `IsExactAntiEquivalenceOn`: one coherent
  `D.CommShift ℤ` sends every ambient distinguished opposite triangle with its
  three objects in P to a distinguished triangle. Its connecting map is
  `D.map T.mor₃ ≫ (s.commShiftIso 1).hom.app T.obj₁`. The opposite category uses
  Mathlib's pretriangulated opposite, in which shift n means shift -n on C.
  This is exactness for the full triangulated subcategory with its inherited
  distinguished triangles; no independent triangulated structure is chosen.
- The natural map delta is `h.bidualityMap K` for the canonical
  `AmbientDualityPairing` of the dependency. That predicate fixes the tensor
  symmetry by HEq to descended Koszul symmetry, evaluation by its tensor-Hom
  adjunct being the identity, and delta by transposition of that evaluation.
  Its compatibility predicate includes naturality, all integer shifts, and
  the three squares of distinguished triangles. The new extraction definitions
  choose only these uniquely determined maps; no mere existence of an arbitrary
  double-dual isomorphism defines data. The theorem concludes that such a proof
  witness h exists, then asserts `IsIso (h.bidualityMap K)` for every K in P.
  No h is an input hypothesis. Its target is the actual covariant double-Hom
  functor `dualityDoubleFunctor` of the same internal Hom and omega applied to K.
- The absence of boundary input is literal: the sole theorem has only the field,
  coefficient, level, scheme and separated-finite-type binders listed above.

Dependency declarations read and used:

| Node | Module and declarations |
| --- | --- |
| def-weil-finite-field-fiber | `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public `CoefficientExtension`: `Padic.finite_coefficientExtensionRing`, `Padic.coefficientExtensionRing`, chosen integers and uniformizer |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; `QuasiCompact` from the recorded companion module |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the recorded `IsSeparated` convention; properness is not assumed |
| def-weil-pbc-etale-site | `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale` |
| def-weil-pbc-proetale-site | `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`; the fixed-scalar realization preserves this category and this small site |
| def-weil-pbc-constructible-complexes | `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`: `Etale.DerivedCategory.isBoundedConstructible` |
| def-weil-finite-torsion-constructibility | `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`: `Scheme.intrinsicFiniteTorsionConstructible`, used through `finiteTorConstructible` |
| def-weil-finite-tor-amplitude | `Sheaf.Paper.FiniteTorAmplitude` and delivered `FiniteTorAmplitudeSites`: original predicates plus the two explicit site presentations |
| lem-sf-flat-model | `Sheaf.Paper.FiniteCoefficientFlatModel`: four recorded declarations, imported for the existing finite-Tor/flat-model interface |
| def-pur-derived-internal-hom | `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: `CategoryTheory.derivedInternalHomOfUniverses`, public through DualityPairing; actual etale/pro-etale derivedHom is the existing right adjoint of derived tensor |
| def-weil-exceptional-inverse-image | delivered `Sheaf.Paper.FiniteExceptionalInverseImage`: `ProEtale.finiteCoefficientExceptionalInverseImage`, `ProEtale.finiteCoefficientDualizingComplex`; the factors are existing `ProEtale.comparisonLowerStar`, `Etale.rightDerivedUpperShriek`, `ProEtale.comparisonUpperStar` |
| lem-weil-duality-pairing | delivered `Sheaf.Paper.DualityPairing`: all five original declarations from Q29, two normalized-map extraction definitions, and two generic invertibility predicates |

The already stated proof dependency `lem-sf-proetale-constructible-origin` is imported
as `Sheaf.Paper.ProEtaleConstructibleOrigin`. The other four proof dependencies have
no current lean record, so their proof imports await their own statements. None is
used as a hypothesis. The theorem docstring retains all five proof steps, including
finite-Tor reflection and the evaluation-compatible double-dual comparison composite.

Edge cases checked against the definitions: the empty scheme and zero objects are
allowed; P is never assumed inhabited or nonzero. The zero complex has an ordered
Tor interval and zero cohomology. Level n=1 and nonreduced higher quotient rings are
included, so finite Tor amplitude is an additional condition and is not inferred from
bounded constructibility. Arbitrary positive n, all finite extensions including the
base field, arbitrary separated finite-type Y over k (without descent to k0), and all
integer shifts are included. Characteristic l is excluded exactly by the standing
l != p hypothesis. A field datum has no empty field or characteristic-zero loophole.
The coefficient ULift is the same quotient ring with its canonical ring structure;
the site object and morphism universes are not identified. The conclusion introduces
no bound on the Tor interval or the dimension of Y.

Searches performed:

- msearch LeanFinder, `finite coefficient Verdier biduality exact contravariant
  anti-equivalence on bounded constructible finite Tor complexes`: 8 generic
  opposite-triangle, derived representative and t-structure hits; no matching statement.
- msearch Loogle, `verdierDual, bidual, derivedHom`: 0 hits, unknown identifier verdierDual.
- msearch grep, `verdierDual|bidual|dualityPairing` in Mathlib CategoryTheory: 0 hits.
- msearch LeanSearch, `Verdier duality is an exact anti-equivalence on bounded
  constructible finite Tor complexes`: service unavailable, Internal Server Error;
  this is recorded only as unavailable.
- msearch LeanFinder, `Restriction of contravariant triangulated functor to full
  subcategory is an exact anti equivalence`: 8 generic triangulated equivalence and
  localization hits. Mathlib Equivalence.IsTriangulated presupposes triangulated
  structures on both input categories; the helper here expresses the inherited
  full-subcategory triangle condition directly and reuses Equivalence and CommShift.
- Direct rg in all Mathlib, upstream WeilConjectures and project lean/Sheaf found
  no collision with the six new main/site declaration names. Searches for
  thm-fix-general-biduality in upstream gave no occurrence. Broader Verdier/bidual
  searches found upstream Etale.Derived.Dualizing: its preservation and unspecified
  Nonempty double-dual isomorphism use a different constructibility predicate, omit
  the exact anti-equivalence and canonical-arrow conclusion, and cover only etale.
  The trace-formula GeometricOperations.bidualityMap presupposes an operations
  package whose hypotheses already include biduality, so cannot state this theorem.
- The resumed inspection used scompile --source on
  Sheaf.Paper.FiniteTypeExceptionalInverseImage and Sheaf.Paper.DualityPairing.
  Both are now published: the former uses the legacy UpperShriek import closure,
  and the latter uses the legacy pro-etale Hom import closure. The adaptations
  below retain their mathematical constructions while using compatible smaller
  imports. No agent was started or contacted.

Verification: each delivered module is compiled with scompile.py under the standard
60-second per-file limit, in both sandbox and library views. The required deliver2.py
--no-push dry run performs its own preflight and file compiles. Final outcomes are
checked by the final dry-run output. The first combined compile exposed two
argument-order errors in the map extraction calls; these were repaired by passing
the coefficient category, scheme, pairing witness and complex explicitly. Every theorem proof remains sorry;
all new definitions have explicit data. No shared source or local Git command was used.

## Dependency modules

`def-weil-finite-tor-amplitude`: the current record points to upstream
`ProEtale.DerivedCategory.constructibleFiniteTor`. Its constructibility predicate is
etale origin, rather than the recorded intrinsic finite-stratification condition; the
comparison is a theorem, not a definition. It also imports the legacy operations
closure. The delivered module instead retains the original intrinsic ringed-site
predicate and supplies the two fixed-scalar presentations needed by the Verdier functors.
`FiniteTorAmplitudeSites` imports all original declarations unchanged and adds just
those two presentations. It reuses the intrinsic pro-etale predicate through the
canonical exact module realization, and the recorded etale constructibility and Tor
predicates. The node copy changes only lean, with this reason in lean.note.

`lem-weil-duality-pairing`: the now-published Q29 module imports legacy
`ProEtale.Derived.Hom`, which conflicts with the intrinsic finite-coefficient
framework. I read and reused its full module and six-step proof docstring. The
combined compile revealed a collision between legacy `ProEtale.UpperLowerStar.Defs`
imported by `ProEtale.Derived.Hom` and `FiniteCoefficient.UpperLowerStar.Defs` imported
by the recorded intrinsic constructibility. I removed the legacy Hom wrapper import
and unfolded its pro-etale wrappers to the existing generic `curriedTensor` and
`MonoidalClosed.internalHom`, with `internalHomAdjunction₂.adj` for its adjunction.
These are definitionally the same tensor and Hom, with the same K-flat-derived
monoidal structure and Koszul symmetry. No declaration is proved or hypothesis
changed. The added two extraction definitions expose its uniquely normalized delta
for IsIso. The node copy changes only lean and records all nine declarations.

`def-weil-exceptional-inverse-image`: the current recorded
`finiteTypeExceptionalInverseImage` uses upstream `ProEtale.rightDerivedUpperShriek`.
Its import closure causes the same legacy/finite-coefficient declaration collision. The delivered dependency module
`FiniteExceptionalInverseImage` uses only the smaller compatible Comparison.Defs
and ordinary etale-adjoint imports and writes its specified three-factor composite:
`comparisonLowerStar.rightDerivedFunctor ⋙ Etale.rightDerivedUpperShriek ⋙
comparisonUpperStar.mapDerivedCategory`. Its second definition applies this functor
to the actual derived monoidal unit. No new arbitrary map, arbitrary right adjoint,
noncanonical site equivalence, or pro-etale ambient-adjoint datum is supplied. This
also avoids an irrelevant bounded-below-preservation interface merely to construct
the composite on ordinary categories. The node copy changes only lean and notes the
import fault and repair. As for the original existing finite interface, this delivery
records the finite-coefficient construction needed here; the node's other coefficient
stages are not used or constructed by this module.

The initial explicit map applications reached the standard 60-second elaboration limit.
The final representation factors each existential pairing witness and its pointwise
IsIso assertion through `Etale.HasInvertibleBidualityOn` or its pro-etale counterpart.
These generic predicates are definitions of exactly that same assertion, with the
specified W and object property as arguments; they add no hypothesis or weaker map.

Resumed source and search checks (2026-10-16): read the original blueprint theorem
and pairing source in the launcher literature archive, then reran LeanFinder on
`finite-stage Verdier duality exact anti-equivalence canonical double dual map
constructible finite Tor` (eight generic exactness, opposite-category and duality
hits, no matching statement), Loogle on `verdierDual, biduality` (zero hits, unknown
identifier verdierDual), and Mathlib CategoryTheory grep on
`verdierDual|biduality` (zero hits). Refreshed all node copies from the read-only
current DAG, preserving only each delivery lean record.

The resumed four-file scompile.py invocation completed with exit 0: every file
passed separately in both sandbox and library views, without errors or warnings.
All four primary signature records also passed stage2_delivery.check_lean_text.
The wrapper retained its prescribed 60-second Lean limit; elapsed summaries include
compiler slot waits. No compilation limit or tool setting was changed.


## Earlier second reading (a previous round; superseded)

I independently read the current DAG node, its thirteen statement dependencies,
the four delivered modules, and the master blueprint source at order 2136 in
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/`.
The source statement is verbatim the node's statement. Its standing coefficient
conventions are the global finite-field datum, prime l different from p, finite
E/Q_l, and positive n, not arbitrary field coefficients. I also read the pairing
source at order 2122 and Stacks `sites-cohomology.tex`, the internal-Hom section
(Tags 08J9, 08JA, 08JC) and Tor-dimension definition (08FZ). These assume a ringed
site and arbitrary derived objects; no constructibility is required for evaluation.

The object/hypothesis/conclusion inventory, with the Lean file open:

| Node item | Lean rendering and independent verdict |
| --- | --- |
| Global k = algebraic closure of F_q, q = p^a | `D : FiniteFieldDatum.{u}` and `Spec (.of D.k)`. Read `FiniteFieldFiber`: prime p, positive a, cardinality q, finite field k0 and `IsAlgClosure k0 k` are its fields/instances. Same datum; no requirement that Y descend to k0. Pass. |
| Prime l unequal to characteristic p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`. The prime is explicit and the excluded characteristic is precisely the one determined by D. Pass. |
| Finite extension E/Q_l | `E : Type u`, `Field E`, `Algebra (Padic l) E`, `FiniteDimensional (Padic l) E`. Read `CoefficientExtension` and its finiteness interface: the integers, uniformizer ideal power, and quotient are those of this extension. Pass. |
| Positive finite stage A = O_E/(varpi_E^n) | `(n : ℕ) (hn : 1 ≤ n)` and every site predicate and dualizing object uses `Padic.coefficientExtensionRing l E n`. `ULift.{u+1,u}` is the canonical ring lift needed by ModuleCat, and the finite instance comes from `finite_coefficientExtensionRing`; it is not an extra assumption. Pass. |
| Arbitrary separated finite-type k-scheme Y and its structure map | `(Y : Scheme.{u}) (aY : Y ⟶ Spec (.of D.k))`, `[IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]`. Read Mathlib's diagonal/locally-finite-type/quasi-compact definitions. Together these are precisely separated finite type. Compactifiability is supplied by Nagata, not a theorem binder. Pass. |
| Both small sites | The theorem conjoins `FiniteEtaleVerdierBiduality` and `FiniteProEtaleVerdierBiduality`. Their categories are derived module sheaves on `Y.smallEtaleTopology` and `Scheme.ProEt.topology Y`, respectively. Read the recorded small-site encodings and exact canonical coefficient realization. Neither site is replaced by a big site. Pass. |
| Full domain D^b_ctf on etale site | `finiteTorConstructibleEtale` is recorded `isBoundedConstructible` intersected with existence of integers `a ≤ b` satisfying the existing `hasTorAmplitudeIn`. Read `BoundedConstructibleComplexes` and `EtaleTorAmplitude`/upstream Coefficients: cohomology is constructible and bounded; all degree-zero module sheaves are tensor tests. Pass. |
| Full domain D^b_ctf on pro-etale site | `finiteTorConstructibleProEtaleModule` applies the existing exact `finiteCoefficientIntrinsicRealization.mapDerivedCategory`, then `finiteTorConstructible`. Read `FiniteTorAmplitude`, `IntrinsicFiniteTorsionConstructibility`, `ProEtaleTorAmplitude`, and `ProEtaleFiniteModuleIntrinsicComparison`: intrinsic constructible cohomology plus one Tor interval, with every degree-zero module tested. It does not substitute etale origin for intrinsic constructibility. Pass. |
| omega_Y = Ra_Y^! A on etale site | `Etale.dualizingComplex ... aY`, whose upstream definition is ordinary etale `rightDerivedUpperShriek` applied to the derived tensor unit. Read `Etale.Derived.Dualizing` and the exceptional-adjoint interface. Pass. |
| omega_Y = Ra_Y^! A on pro-etale site | `ProEtale.finiteCoefficientDualizingComplex ... aY`. Read its two definitions: exactly `Rnu_* ⋙ Etale.rightDerivedUpperShriek ⋙ nu^*` applied to the tensor unit. The transported exceptional functor is the node's functor; no ambient pro-etale right-adjoint assumption enters. Pass. |
| D_Y = RHom(-,omega_Y), including maps and contravariance | The etale functor is `Etale.verdierDual`; upstream it is `(derivedHom ...).flip.obj omega`. Pro-etale uses `MonoidalClosed.internalHom.flip.obj omega`. Read both upstream Hom definitions: `derivedHom` is definitionally this same internal Hom. They are actual functors `Cᵒᵖ ⥤ C`, with the existing derived closed monoidal structures. Pass. |
| Preservation and anti-equivalence | `IsExactAntiEquivalenceOn` asserts preservation of P and an equivalence `P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory` whose functor composed with inclusion is naturally isomorphic to the specified ambient D after inclusion. The natural isomorphism fixes the map action as well as the objects; an arbitrary object assignment would not satisfy this clause. Pass. |
| Exactness | The final clause supplies one coherent `D.CommShift ℤ` and requires every distinguished opposite triangle with its three objects in P to have distinguished image, with third map `D.map T.mor₃ ≫ (s.commShiftIso 1).hom.app T.obj₁`. Read the Mathlib pretriangulated-opposite import: its shifts reverse the integer shift on C. This is inherited triangulated exactness on the full domain, not merely preservation of object membership. Pass. |
| Natural delta_K: K -> D_Y D_Y K is an isomorphism for every domain object | Both `HasInvertibleBidualityOn` predicates assert existence of the canonical ambient pairing witness and `∀ K, P K → IsIso (h.bidualityMap K)`. Read the projections in `DualityPairing`: symmetry is fixed by HEq to the descended Koszul braiding, evaluation by the adjunct identity, and delta by its prescribed transpose. The selected data are determined by these equations. Compatibility includes naturality, all integer shifts, and all three triangle squares. The witness is an output, not a hypothesis. The target is the actual double internal-Hom functor. Pass. |
| No boundary duality hypothesis | The complete theorem signature ends after the three geometric property instances. Neither a boundary datum nor any arbitrary exceptional-operation/duality package is a binder. Pass. |

Edge cases: the empty scheme and zero complexes remain allowed; no `Nonempty`,
positive dimension, smoothness, properness, connectedness or projectivity is assumed.
There is no indexed-family binder, hence no hidden inhabited-index restriction.
The source excludes n=0, exactly as `hn` does. Level n=1 and all higher positive
levels, including nonreduced quotient rings, occur; finite Tor is not inferred from
bounded constructibility. All finite extensions, including Q_l itself, occur.
Characteristic l is excluded explicitly and no additional characteristic is excluded.
The shared universe u is a common ambient universe for the scheme, base field and
extension; lifting to a common universe does not remove a mathematical case. The
small pro-etale site's object universe u+1 and morphism universe u remain distinct;
ModuleCat and the canonical scalar ULift use the required u+1 coefficient universe.
No universe variable, structure map, complex or integer is left auto-implicit.

Independent H4 searches (recorded by msearch in this sandbox):

- LeanFinder: `duality on constructible torsion complexes double internal Hom
  evaluation gives equivalence of categories`. Eight generic rigid-category,
  tensor-Hom and ModuleCat hits; none is the finite-stage two-site theorem.
- Loogle: `"dual", "evaluation"`. Zero hits, with no search error.
- Wrapper grep: `bidual|reflexiv|dualizing|antiEquivalence`. Twenty-five mostly
  unrelated reflexivity hits; I did not treat the capped result as exhaustive.
- Direct rg over Mathlib CategoryTheory/Monoidal and Algebra/Homology for
  `bidual|duality|dualizing|anti.equivalence` found bibliographic references and
  ordinary generic duality, not this theorem. Direct rg over upstream
  WeilConjectures and project lean/Sheaf for Verdier, bidual, dualizing and the
  delivered names found the upstream etale Dualizing theorem and the project
  `DeltaProperPushforward` constructions; I opened those declarations.
  Upstream `nonempty_iso_verdierDual_verdierDual` concludes an unspecified
  object isomorphism on a different constructibility predicate and covers only
  etale; it does not supply the canonical-arrow and two-site exact-equivalence
  statement. `GeometricOperations.bidualityMap` is relative to an operations
  package already assuming duality. `ambientDoubleDualMap` is a direct etale
  presentation of the same normalized transpose used by a proper-pushforward
  consumer, not this theorem. The pairing-witness projection here only exposes
  the existing pairing's determined map; it introduces no alternative Hom or
  evaluation construction. No existing declaration replaces this item's module.

Dependency-module reading (H12/H13): there are no new independent definition
nodes and no `statement_change`. `FiniteTorAmplitudeSites` imports the original
finite/integral/field definitions and adds only their recorded etale and canonical
fixed-scalar finite presentations. I checked its owning node at order 1464 against
the blueprint and Stacks 08FZ: the interval is uniform over all test modules.
The published record's etale-origin predicate is not the intrinsic stratification
definition, so the repair is needed rather than an unrecorded private predicate.
`FiniteExceptionalInverseImage` supplies the same finite-stage comparison composite
of its owning node at order 1489 using compatible smaller imports; the old recorded
finite-type module also gives only the finite-stage interface needed here. Neither
repair claims to construct the later coefficient-stage theorems. `DualityPairing`
retains the five published declarations and their theorem signature/proof outline;
its pro-etale wrappers are unfolded to their exact generic definitions to avoid
the legacy/finite-coefficient import collision. The four added declarations are
projections or predicates about that determined pairing. No definition has sorry
data, no theorem was proved, and the two theorem bodies remain exactly `by sorry`.
All declarations have source/blueprint docstrings; both theorem docstrings retain
the node's proof steps. The main docstring includes finite-Tor reflection, the
second internal-Hom input check, and the ordered evaluation-compatible composite.

Mismatches and changes: no mathematical mismatch was found, so I left the four Lean
modules and all mathematical node fields unchanged. Two dependency copies had
stale maintainer `reviewed_lean` metadata compared with the current shared DAG.
I refreshed all node copies from the current read-only DAG and retained only the
delivery's intended lean records, ensuring that each dependency changes only lean.
I appended this independent reading without changing `## Worker report`.

Validation: the required four-file scompile.py invocation compiles every sibling
separately in the private overlay, in both sandbox and library views, under the
unchanged default 60-second Lean limit. The dry-run and delivery wrapper outcomes
are recorded below after they complete. Primary `lean.statement` text is unchanged
and checked verbatim against each file's declaration by preflight.

Current-source confirmation: the pro-etale site node now records upstream
`AlgebraicGeometry.ProEtale.ModuleDerivedCategory`. It is absent from the older
local upstream checkout, so I read it with the authorized `scompile.py --source`
command. Its body is exactly the fixed-scalar `DerivedCategory (Sheaf
(Scheme.ProEt.topology Y) (ModuleCat.{u+1} A))` already used here. Thus the refreshed
dependency record introduces no change of category or universe. All four primary
signature strings were checked verbatim against their Lean files, and every
Lean line is at most 100 characters.

Second-reader compile result: the complete four-file scompile.py invocation exited
0. Every sibling passed individually in both sandbox and library views, with no
errors or warnings. One elapsed summary includes a compiler-slot queue wait; the
wrapper's per-invocation Lean timeout was unchanged at 60 seconds.

Dry-run result: deliver2.py --no-push exited 0 and printed
`OK (dry run): commit e72771b512 passes the preflight and compiles; nothing pushed`.
The wrapper excluded concurrently updated maintainer review metadata, as required;
only the intended lean records are delivered on dependency nodes.


## Repair of immutable-head compilation return

The return reports that the immutable compile could not resolve
`finiteTorConstructibleEtale`, `finiteTorConstructibleProEtaleModule`, or
`ProEtale.finiteCoefficientDualizingComplex` in the main theorem. The sandbox
contains all three declarations, in the two dependency modules explicitly imported
by the main module. The final validation below compiles the complete sibling set;
a main-file-only invocation cannot supply these unpublished declarations.

I also read the current server source with `scompile.py --source`. The published
`FiniteExceptionalInverseImage` module now contains Q09's intrinsic
`Scheme.finiteExceptionalInverseImage`. The previous delivery replaced that
module with its two fixed-scalar helper definitions. The repaired module retains
Q09's complete published construction and imports verbatim, adds the required
etale Dualizing import, and appends the two helper definitions. The dependency
lean record lists the preserved declaration as well as both helpers. This is a
concrete source change, preserving existing users while supplying every name
used in the theorem. No mathematical statement, hypothesis, or conclusion changes.
All node copies were refreshed from the current read-only DAG, retaining only
their intended lean records. Prior verification entries describe the returned
delivery; fresh compile and dry-run results for this repair are recorded below.

Current-source follow-up: `lem-sf-comparison-tor-amplitude` now has the
published module `Sheaf.Paper.ComparisonTorAmplitude`. I read its full source
with `scompile.py --source` and added its required proof-only import. Three
proof dependencies remain unstated; they are not needed as theorem hypotheses.
The finite-Tor dependency note now refers to the current intrinsic declaration
and its missing fixed-scalar presentation, rather than the superseded upstream
etale-origin record. The original finite/integral/field definitions are retained
by public import.

Repair searches actually rerun: LeanFinder on “finite coefficient Verdier
duality canonical biduality map exact anti equivalence bounded constructible
finite Tor complexes” returned eight generic derived-category, Ext, and
opposite-triangle hits, none the requested theorem. Loogle `verdierDual,
biduality` returned zero hits with unknown identifier verdierDual; it is not
evidence of mathematical absence. Wrapper grep for the delivered predicate,
dualizing-object and theorem names in Mathlib CategoryTheory returned zero hits.
Direct rg of upstream WeilConjectures and the shared Lean source found only two
proof-docstring citations to this item, and no collision with the new names.
I reread the blueprint theorem at order 2136: its hypotheses, two sites, exact
anti-equivalence and canonical delta conclusion agree with the unchanged Lean.
The isolated Tor-module compile exited 0 in both sandbox and library views.

Repair validation: the complete four-file compile performed by the required
`deliver2.py Q11 thm-fix-general-biduality --no-push` finished with exit 0.
Every module passed in sandbox and library views, including the main theorem
with all previously unresolved identifiers visible, with no errors or warnings.
The server preflight passed. The wrapper printed:
`OK (dry run): commit 757e588e05 passes the preflight and compiles; nothing pushed`.
The default 60-second per-file limit was retained. No delivery was pushed.


## Earlier second reading (a previous round; superseded)

I reread the source node at blueprint order 2136 and matched its statement against
`finite_stage_verdier_biduality` and the two helper predicates in
`Sheaf.Paper.FiniteStageVerdierBiduality`.

- The global field (k=\overline{\mathbf F}_q) is `D : FiniteFieldDatum.{u}` and
  the structure map is `aY : Y ⟶ Spec (.of D.k)`. Verdict: same fixed datum and
  geometric base; no descent of `Y` is imposed.
- The prime ℓ and ℓ different from the characteristic are `(l : ℕ) [Fact l.Prime]`
  and `_hl : l ≠ D.p`. Verdict: exact source hypothesis.
- The finite extension (E/\mathbf Q_\ell) is `E : Type u` with `Field E`,
  `Algebra (Padic l) E`, and `FiniteDimensional (Padic l) E`. Verdict: same
  coefficient extension; no stronger field assumption.
- The finite stage (A_{E,n}), with (n\ge1), is `(n : ℕ) (hn : 1 ≤ n)` and
  `Padic.coefficientExtensionRing l E n` in both site definitions. Verdict: all
  positive levels, including `n = 1`, are included.
- (Y) separated and finite type is rendered by `[IsSeparated aY]`,
  `[LocallyOfFiniteType aY]`, and `[QuasiCompact aY]`. Verdict: exact finite-type
  condition; no properness, smoothness, connectedness, or dimension assumption.
- The two small sites are `Y.smallEtaleTopology` and `Scheme.ProEt.topology Y`,
  through the recorded etale and fixed-scalar pro-etale derived categories.
  Verdict: neither site is replaced by a big site.
- The etale domain (D^b_{ctf}(Y,A)) is
  `finiteTorConstructibleEtale l E n hn Y`, combining bounded constructibility
  with one Tor-amplitude interval tested against all degree-zero modules.
  Verdict: exact finite-Tor constructible domain.
- The pro-etale domain is `finiteTorConstructibleProEtaleModule l E n hn Y`,
  using the canonical intrinsic realization and the recorded intrinsic finite
  constructibility/Tor predicate. Verdict: intrinsic pro-etale constructibility
  is retained; it is not replaced by etale origin.
- The dualizing objects are `Etale.dualizingComplex ... aY` and
  `ProEtale.finiteCoefficientDualizingComplex ... aY`. Verdict: each is the
  recorded exceptional inverse image of the derived unit, with the pro-etale
  comparison composite; no ambient exceptional-adjoint hypothesis is added.
- The dual functors are `Etale.verdierDual` and
  `MonoidalClosed.internalHom.flip.obj ...`. Verdict: actual contravariant
  internal-Hom functors with the prescribed dualizing objects.
- `CategoryTheory.IsExactAntiEquivalenceOn` asserts preservation of the object
  predicate, an equivalence of the opposite full subcategory with the full
  subcategory together with a natural comparison to the specified ambient
  functor, and preservation of every distinguished opposite triangle with the
  coherent shift comparison. Verdict: exact anti-equivalence including maps and
  triangles, not merely objectwise equivalence.
- `Etale.HasInvertibleBidualityOn` and
  `ProEtale.HasInvertibleBidualityOn` assert existence of the canonical pairing
  witness and `IsIso (h.bidualityMap K)` for every domain object. Verdict: the
  natural evaluation-transpose map (K\to D_YD_YK) is the conclusion; an
  arbitrary isomorphism is neither assumed nor substituted.
- The theorem concludes the conjunction of the etale and pro-etale clauses and
  has no boundary-duality binder. Verdict: every source conclusion is present and
  no extra hypothesis occurs.

Edge cases checked: the empty scheme and zero complex are allowed; no nonempty,
proper, smooth, connected, or positive-dimensional condition is present. The
zero object has the required trivial Tor interval. `n = 0` is correctly excluded
by `hn`, while `n = 1` and all higher nonreduced quotient levels are included.
The characteristic exclusion is exactly `_hl`; no additional characteristic
condition appears. The finite extension may be the base field. The common
universe and the `ULift` coefficient presentation preserve the distinct pro-etale
site object/morphism universes and do not identify them.

For H4 I reran the prescribed searches: LeanFinder for finite-coefficient
Verdier biduality and exact anti-equivalence, Loogle for `verdierDual`/`bidual`,
LeanSearch (unavailable with an internal server error), and direct `rg` over
Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`. Results were
only generic tensor-Hom, opposite-triangle, and upstream etale duality
material; no declaration states this two-site finite-stage theorem. The existing
upstream etale double-dual result has an unspecified isomorphism, a different
predicate, and no pro-etale clause, so it does not replace this node.

I read the dependency records and delivered modules for the finite-field datum,
coefficient ring, finite-type/separated morphisms, both sites, constructibility,
finite Tor amplitude, flat models, derived internal Hom, exceptional inverse
image, and duality pairing. The two dependency repairs add canonical fixed-scalar
presentations required by the recorded interfaces; they do not alter the
mathematical node statement or add hypotheses. No hollow definition or private
notion was introduced, and all postponed theorem bodies remain `sorry` with
source and blueprint docstrings.

No mismatch was found in the node, source, or Lean statement, so no mathematical
change was made. The only delivery content remains the existing four-module
statement/dependency set and its synchronized Lean records. The full four-file
`scompile.py` invocation passed in all views under the standard 60-second limit.

## Second reading by Q11

This is the current independent second reading, against the shared DAG and current
server sources on 2026-10-16. It supersedes the earlier delivery-shape and validation
entries above. The final delivery has three modules: FiniteStageVerdierBiduality,
FiniteTorAmplitudeProEtaleModule, and DualityPairing. It has two dependency records and no
new node or mathematical statement correction. The Worker report is retained above.

I read the original blueprint node at order 2136, its unit at order 2113, the global
finite-field and coefficient conventions, and all thirteen statement-dependency
nodes. This node has a blueprint source, not a Stacks theorem source. For its Tor
and pairing definitions I also read the local Stacks TeX: Tags 08FZ (one ordered
interval, every module), 08J9 (derived tensor-Hom), and 08JC (triangles). No source
assumes properness, smoothness, a boundary datum, or an ambient pro-etale adjoint.

The statement inventory and its item-by-item Lean match are:

| Object, hypothesis, or conclusion in the node/source | Lean rendering and verdict |
| --- | --- |
| Fixed k = algebraic closure of F_q, with p prime and q = p^a | `D : FiniteFieldDatum.{u}`; its fields include `prime`, `exponent_pos`, `cardinality_eq`, finite `k₀` of cardinal q, and `IsAlgClosure k₀ k`. Exact; Y is not required to descend to k₀. |
| Prime l different from p, standing throughout the source | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`. Exact. |
| Arbitrary finite extension E/Q_l | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Exact; no topology or extra completeness binder is added. |
| A = A_(E,n), positive finite stage | `(n : ℕ) (hn : 1 ≤ n)` and `Padic.coefficientExtensionRing l E n`. I read the coefficient definition: quotient of the valuation ring by the nth uniformizer ideal. The canonical `ULift` preserves that ring; finiteness is supplied internally by the recorded named theorem. Exact. |
| Arbitrary separated finite-type Y over k and its structure map | `(Y : Scheme.{u}) (aY : Y ⟶ Spec (.of D.k))`, with `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on aY. I read these signatures and the diagonal definition; this is precisely separated finite type. No further geometric instance is a theorem hypothesis. |
| Both small sites | The final conjunction is `FiniteEtaleGeometricBiduality ... ∧ FiniteProEtaleVerdierBiduality ...`. Their categories use `Y.smallEtaleTopology` and `Scheme.ProEt.topology Y`. Exact. |
| Etale domain D^b_ctf | The existing etale conclusion uses `finiteTorConstructibleEtale`: recorded `isBoundedConstructible` intersected with one ordered interval for `hasTorAmplitudeIn`. I opened both definitions; every degree-zero module sheaf is tested. Exact. |
| Intrinsic pro-etale domain D^b_ctf | `finiteTorConstructibleProEtaleModule` applies the canonical exact `finiteCoefficientIntrinsicRealization.mapDerivedCategory`, then the existing intrinsic `finiteTorConstructible`. I read intrinsic cohomological constructibility and `HasFiniteProEtaleTorAmplitude`; all module sheaves and all integer degrees are tested with one uniform interval. Exact; no etale-origin condition replaces intrinsic constructibility. |
| Etale omega = RaY^! A | The existing etale conclusion uses `Etale.dualizingComplex`, literally the ordinary etale exceptional adjoint applied to the derived tensor unit. Exact. |
| Pro-etale omega = RaY^! A | `(ProEtale.sfFiniteExceptionalFixed A (NagataCompactification aY)).obj (𝟙_ _)`. I opened the currently recorded module: it is exactly `Rnu_* ⋙ Etale.rightDerivedUpperShriek ⋙ nu^*`. The existing Nagata construction supplies the compactification; none is assumed as an input. Exact. |
| D_Y = RHom(-,omega_Y), with contravariant action on arrows | Etale uses the published `FiniteEtaleGeometricBiduality` and its `Etale.verdierDual`. Pro-etale uses `MonoidalClosed.internalHom.flip.obj omega`. I opened upstream Hom/Tensor definitions: these are precisely the existing derived Hom and tensor, with their adjunction, not a supplied abstract duality functor. Exact. |
| Preservation and anti-equivalence on the full domain | Etale's published predicate states these clauses explicitly. Pro-etale `IsExactAntiEquivalenceOn` requires preservation and an equivalence of `P.FullSubcategoryᵒᵖ` with `P.FullSubcategory`, naturally identified after inclusion with the specified D. This fixes morphisms as well as objects. Exact. |
| Contravariant exactness | Both predicates require a coherent `D.CommShift ℤ` taking every distinguished opposite triangle with vertices in P to a distinguished image triangle, with connecting map `D.map T.mor₃ ≫ (s.commShiftIso 1).hom.app T.obj₁`. The opposite pretriangulated shift reverses integers. Exact inherited triangulated exactness. |
| Canonical natural delta_K is invertible for every K in the domain | Etale's published predicate and pro-etale `HasInvertibleBidualityOn` use the existing `AmbientDualityPairing.bidualityMap`. I read its extraction and normalization: descended Koszul symmetry, evaluation as adjunct identity, and delta as its transpose determine the arrow. A pairing witness is concluded, never assumed. Its compatibility includes naturality, every integer shift, and all three triangle squares. Exact; no unspecified isomorphism substitutes for delta. |
| No boundary-duality input | The complete final theorem signature has only the field, coefficient, level, scheme, structure-map, and separated-finite-type binders listed above. Exact. |

Edge cases: the empty scheme and the zero complex are allowed. There is no
nonempty index, nonzero object, dimension, smoothness, properness, connectedness,
or projectivity restriction. There is no indexed-family binder. The source's
n ≥ 1 excludes n = 0 exactly, includes n = 1, and includes all higher nonreduced
quotient rings. Finite Tor is an extra condition at those levels. E may equal Q_l.
The characteristic exclusion is precisely l ≠ p. A common ambient universe for
E, k and Y loses no mathematical case; no universe equality is imposed between
site objects (u+1) and morphisms (u). Module values and the canonical scalar lift
are in u+1. All variables and universes are explicitly bound (`autoImplicit false`).

Independent searches rerun during this reading:

- msearch LeanFinder, `Verdier dual induces involutive exact equivalence
  constructible complexes torsion coefficients`: eight generic opposite-triangle,
  exact functor and Ext hits; no two-site finite-coefficient theorem.
- msearch Loogle, `"dual", "iso"`: twelve order-duality hits; no matching statement.
- msearch LeanSearch, `canonical biduality morphism for Verdier duality on
  constructible sheaves`: eight ordinary module/continuous-double-dual hits;
  the service answered successfully, with no sheaf-duality theorem.
- msearch grep for the exact finite-stage predicates and biduality: zero Mathlib
  hits. Direct rg over Mathlib CategoryTheory, upstream WeilConjectures, and
  shared lean/Sheaf found the current pairing projections, the existing etale
  conclusion, and `sfFiniteExceptionalFixed`. I opened and reused all three.
  Searches for `IsExactAntiEquivalenceOn`, `HasInvertibleBidualityOn`,
  `FiniteProEtaleVerdierBiduality`, and `finiteTorConstructibleProEtaleModule`
  found no existing declarations. The upstream etale
  `nonempty_iso_verdierDual_verdierDual` only asserts an unspecified object
  isomorphism on its different constructibility predicate; it does not replace
  this canonical-map, exact-equivalence, two-site theorem.

Dependency review (H12/H13): there are no new definition nodes.
`def-weil-finite-tor-amplitude` is read against blueprint order 1464 and Stacks
08FZ. Its new dependency module is `FiniteTorAmplitudeProEtaleModule`. The existing
`FiniteTorAmplitudeSites` file and its etale-only import closure remain unchanged;
the added fixed-scalar pro-etale presentation uses the existing intrinsic predicate
through its canonical exact realization. The original etale, finite, integral and
field interfaces remain public imports.
`lem-weil-duality-pairing` is read against blueprint order 2122 and Stacks
08J9/08JC. All seven current declarations and the complete six-step theorem
proof docstring are retained. The only change unfolds existing pro-etale tensor,
Hom and adjunction wrappers to their exact generic definitions, avoiding the
legacy/finite-coefficient notation import collision. No pairing equation or
normalization changes. The owning dependency note explains this necessary
compatibility repair. The main module owns its pro-etale invertibility predicate.

Mismatches found and repairs:

1. H4/current-source mismatch: the sandbox's etale conclusion duplicated the now
   published `FiniteEtaleGeometricBiduality`. I removed the duplicate, reused that
   predicate and imported its module, also satisfying the newly available proof
   dependency import. Its explicit clauses match the node item by item above.
2. H4/current-source mismatch: the sandbox's fixed-scalar exceptional functor
   duplicated the now recorded `sfFiniteExceptionalFixed`. I removed the entire
   exceptional dependency module/record from this delivery and use that existing
   functor and the existing Nagata compactification directly on the tensor unit.
3. The sandbox proposed two generic invertibility predicates in the pairing
   dependency. Only the pro-etale one remains needed; it is now in the main
   module with the main node's blueprint docstring. The current published
   bidualityMap projections are retained rather than introduced again.
4. I tested using the pairing module completely unchanged. Local compilation
   failed on the duplicate `AlgebraicGeometry.ProEtale.«term(_)_*[_]»` imported
   from legacy and finite-coefficient UpperLowerStar modules. Therefore its
   definitionally identical import adaptation remains an authorized §1(B)
   dependency repair. This is a concrete compiler failure, not a hypothetical
   reason to replace an otherwise usable interface.
5. I refreshed node copies from the current shared DAG, retaining only intended
   lean records, and copied primary signatures verbatim from each delivered file.
   No mathematical node statement, source, dependency list, or proof was changed.

Every delivered definition has real data. The only delivered theorem bodies are
`by sorry`, with source/blueprint and full natural-language proof docstrings.
No theorem was proved. Every Lean line is at most 100 characters. Compilation,
preflight and delivery results follow below after completion.

Validation before the final module-layout repair: the explicit three-file scompile.py invocation
exited 0. DualityPairing, FiniteTorAmplitudeSites, and FiniteStageVerdierBiduality
all compiled individually in both sandbox and library views, with no errors or
warnings, under the unchanged default 60-second limit. Primary node signatures
were checked verbatim against all three files. A closer empty-scheme check found
that intrinsic constructibility asks for a positive number of strata, but its
stratification allows empty strata: the one empty stratum covers the empty scheme.
Thus this convention does not silently exclude that edge case.

Final source-compatibility repair: the server confirmation for the unchanged-pairing
experiment also rebuilt EtaleGeometricBiduality and exposed how adding intrinsic
pro-etale imports to its existing etale Tor dependency can create the same legacy
notation collision inside that source. I therefore deliver only the new pro-etale
presentation in `Sheaf.Paper.FiniteTorAmplitudeProEtaleModule`, publicly importing
the existing `FiniteTorAmplitudeSites` unchanged. Its owning node's lean record
points to this extension. No published etale source or its imports are overwritten.
This fixes source compatibility without changing any mathematical definition or
raising a timeout. The final module names are those at the start of this section.
The earlier successful dry run (dff0f57804) predates this layout repair; fresh
validation and the final dry run are recorded below.

The compile after the layout change accepted all three modules; its snapshot caught
one long docstring line before I wrapped that line. The current files all meet the
100-character limit. The required final dry run recompiles the corrected files and
must reject every warning. I also explicitly recompile the published etale-biduality
consumer source with the adapted pairing as siblings, to test source compatibility
rather than relying on that consumer's cached artifact. No extra file is delivered.

Source compatibility check: scompile.py with the final adapted DualityPairing and
the current published EtaleGeometricBiduality source exited 0. Both files passed
individually in sandbox and library views with no errors or warnings, under the
standard 60-second limit. This explicitly validates the affected published consumer
without changing or delivering its source, and confirms the separate Tor-presentation
module avoids the source-rebuild collision.

Final dry run: deliver2.py --no-push exited 0 and printed
`OK (dry run): commit 24b26add5f passes the preflight and compiles; nothing pushed`.
It compiled all three corrected delivery modules without errors or warnings and
passed current server preflight. No Lean invocation exceeded the unchanged default
60-second limit. The following normal deliver2.py invocation performs the required
final recheck and pushes the reviewed delivery.
