## Worker report

This is an existing-declaration attachment for the whole finite-coefficient derived-functor
package. No Lean module is delivered and no declaration is duplicated. The source read is
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-finite-derived-functors/_section.md`,
including its five Lean references and all three numbered clauses. The node replaces the
old umbrella underived reference with its two actual definition nodes; its mathematical
statement agrees with this source. No statement correction is needed.

The primary module is
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek`.
It publicly imports `FiniteCoefficient.Derived.UpperLowerStar`, so its public import
closure exports the three generic constructions and all five component declarations in
`lean.declarations`. The primary declaration is the final bounded below adjunction.
Its recorded signature is verbatim from OpenLowerShriek.lean, lines 80–81. The node is an
umbrella definition, not a single theorem asserting the conjunction of all the clauses;
the declaration list records each component explicitly.

Hypothesis and clause correspondence (notation is the existing scoped notation):

- A Grothendieck abelian coefficient category is `(A : Type u') [Category.{u + 1} A]
  [Abelian A] [IsGrothendieckAbelian.{u + 1} A]`. The object universe `u'` is unrestricted.
  This is the universe convention of the dependency interfaces: a scheme in `Scheme.{u}`
  has small pro-etale site object universe `u+1` and morphism universe `u`.
- An arbitrary scheme morphism is `{Z Y : Scheme.{u}} (g : Z ⟶ Y)`. There is no proper,
  smooth, weakly etale, finite-type, or nonempty assumption on g.
- The sheaf category is exactly `Sheaf (Scheme.ProEt.topology X) A`. The unbounded derived
  category is `DerivedCategory` of this category; its bounded below full subcategory is
  `DerivedCategory.Plus` of the same category, not a new carrier.
- `Rg_* := R(g_*)` is `CategoryTheory.Functor.rightDerivedFunctor (ProEtale.lowerStar A g)`.
  UpperLowerStar.lean, lines 106–116, displays its complete source and target in a typed
  example. The generic definition is in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`, lines 171–175.
  Its unit is invertible on K-injectives. In the separate existing KInjective module,
  `Functor.rightDerivedFunctorObjQIso` expresses this as R(F)(Q I) ≅ Q(F I) for
  K-injective I (that auxiliary module is not claimed in the exported declaration list).
  For a resolution K → I, apply R(F) to the localized resolution isomorphism first.
  No monoidal structure is needed in this first part of the file.
- `R⁺g_*` is `Functor.rightDerivedFunctorPlus (ProEtale.lowerStar A g)` from
  `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`, lines 28–39,
  with the typed pro-etale example at UpperLowerStar.lean, lines 118–125. Its construction
  localizes the bounded below homotopy category using injective resolutions.
  `Functor.rightDerivedFunctorPlusIsoInjectiveObject`, in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
  lines 198–210, states the termwise formula through K⁺(Inj) ≌ D⁺.
- The additional assumptions are exactly `[MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]`,
  as read at UpperLowerStar.lean, lines 173–180, and OpenLowerShriek.lean, lines 58–61.
  These render closed, symmetric, additive tensor and functorial flat resolutions.
  The Grothendieck, closed, symmetric assumptions supply the sheaf tensor-colimit and
  flat-resolution infrastructure through the imported instances; none is an extra binder.
- `Lg^* := L(g^*)` is `Functor.leftDerivedFunctor (ProEtale.upperStar A g)`, the generic
  total left derived construction on the K-flat derivability structure in
  `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`.
  UpperLowerStar.lean, lines 184–200, describes this construction and gives its type.
- Clause 1 is exactly `ProEtale.leftDerivedUpperStarIsoMapDerivedCategory`,
  UpperLowerStar.lean, lines 202–215: `L((g)^*[A]) ≅ D((g)^*[A])`.
- Clause 2, unbounded, is `ProEtale.derivedUpperStarLowerStarAdjunction`,
  UpperLowerStar.lean, lines 332–349: `L((g)^*[A]) ⊣ R((g)_*[A])`.
  Its bounded below clause is `ProEtale.derivedUpperStarLowerStarAdjunctionPlus`,
  lines 351–359: `D+((g)^*[A]) ⊣ R+((g)_*[A])`.
- Clause 3 introduces `{U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]`.
  `ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction`,
  OpenLowerShriek.lean, lines 63–72, has type `D((j)_!open[A]) ⊣ D((j)^*[A])`.
  Its `Plus` companion, lines 74–82, has type `D+((j)_!open[A]) ⊣ D+((j)^*[A])`.
  These use precisely the exact underived extension by zero and pullback of the
  dependency nodes. There is no constructibility or Tor-amplitude condition.

Dependency interfaces read and reused:

- `def-sp-grothendieck-abelian`: `CategoryTheory.IsGrothendieckAbelian` in
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`; its docstring and fields
  give locally small, AB5 and generator, with small colimits supplied by the standard
  instance. This is the recorded Mathlib match.
- `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology` in
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: weakly etale objects with pro-etale topology.
- `sk-def-sfb-derived-categories`: read the complete
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` module and its universal
  pair, unit and object comparison. Its node's lean.note explicitly allows the existing
  generic upstream derived functor on these Grothendieck sheaf categories. The imported
  upstream construction uses that same localization and K-injective resolution formula;
  this attachment does not create a competing functor or convention.
- `def-sfb-finite-lower-star` and `def-sfb-finite-upper-star`: read the compatibility
  module `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` and the full canonical
  `FiniteCoefficient.UpperLowerStar.Defs` it re-exports. `ProEtale.lowerStar` is restriction
  along opposite base change, while `ProEtale.upperStar` is the sheafified left Kan
  extension; `upperStarLowerStarAdjunction` is their adjunction. The derived package uses
  these exact declarations through their scoped notation.
- `sk-def-sfb-finite-lower-shriek`: its recorded Proper module's closure defines
  `ProEtale.openImmersionLowerShriek` and its underived adjunction and exactness. Read
  `FiniteCoefficient.LowerShriek.Open.Defs`, including `localizationLowerShriek_eq` and
  the open immersion specialization. The derived package uses this extension by zero,
  not an independently chosen left adjoint or a compactification pushforward.

Edge cases checked by reading the binders and constructions: arbitrary g, including the
identity; empty schemes and the empty open immersion; the zero coefficient category;
zero complexes; complexes bounded below at any integer (not just zero); and genuinely
unbounded complexes. No finite generation, nonzero ring, characteristic, boundedness or
finite Tor hypothesis is added. The right-derived constructions remain available without
the additional tensor assumptions. Clause 3 retains precisely the additional coefficient
assumptions in the source, even though more general exact-derived adjunctions may exist.

Searches actually run:

- msearch.py leanfinder: "Derived pushforward and pullback adjunction unbounded and bounded
  below derived categories of pro etale sheaves". Eight hits, headed by
  `SheafOfModules.pushforwardPushforwardAdj` and `SheafOfModules.pullbackPushforwardAdjunction`;
  these are not the complete arbitrary-coefficient pro-etale package.
- msearch.py loogle: "CategoryTheory.Adjunction.derived,
  CategoryTheory.Functor.rightDerivedFunctorPlus". Zero hits for this combined query.
- msearch.py grep: "rightDerivedFunctorPlus|mapDerivedCategoryAdjunction" in
  `Algebra/Homology`. Five returned hits in Mathlib's RightDerivedFunctorPlus.lean,
  including the definition at line 36 and its unit.
- Direct rg searches of `lean/WeilConjectures/SixFunctors` for the five blueprint names
  located the exact finite-coefficient UpperLowerStar and OpenLowerShriek modules.
  The corresponding module-object and etale declarations concern different categories.
- Direct rg for the node id in `lean/WeilConjectures` returned no match: this aggregation
  has no individual blueprint-tagged declaration, but its five named components exist.
- Direct rg in `lean/Sheaf` for the component names located consumers (including
  OpenClosedRecollement and CompactSupportFiniteTorsion), not a new implementation.
  Searches of `lean/Sheaf/CategoryTheory` found no competing pro-etale package.

No node fault or STATEMENT-DISPUTED issue was found. The existing constructions can
rest on postponed infrastructure theorems; this attachment claims exact statement
coverage, not that their axiom closure is already free of sorry.

## Second reading by Q85

This section records a separate second pass by the same dispatcher-started worker;
the brief prohibits starting another agent. I reopened the node and the two canonical
source files. I checked the initial Grothendieck hypotheses separately from the later
monoidal hypotheses: the two pushforward examples precede the monoidal section, so
recording the package does not silently strengthen their assumptions. I matched the
five numbered components in lean.declarations against clause 1, both adjunctions in
clause 2, and both in clause 3. I checked in particular that the Plus pullback is D⁺(g*)
and not an invented bounded below K-flat functor. I also checked that the open functor
is the finite-coefficient `_!open[A]` construction on A-valued sheaves. The generic
R, R⁺ and L definitions supply the three introductory construction clauses. The
primary OpenLowerShriek module publicly exposes UpperLowerStar and all those generic
definitions, so its declaration list is a public package rather than declarations
asserted to occur in a file that does not export them. No mathematical mismatch was
found and no node statement was changed. No new nodes or dependency repairs are needed.

## Validation

On this resumed attempt, I reread the current node, all six dependency records, the
blueprint unit, and the existing finite-coefficient UpperLowerStar and OpenLowerShriek
sources. All five component signatures and the coefficient hypotheses still match;
the initial pushforward constructions still precede the monoidal assumptions. There
is no repair note for this item. No new declaration or node-field change is needed.

The first required deliver2.py --no-push run reproduced the earlier missing
WeilConjectures.Mathlib.Algebra.Homology.Localization.olean failure in upstream KFlat,
including current-server confirmation. The prescribed scompile.py --source command
successfully returned the current Localization source. A minimal import-only scratch
probe was then submitted through scompile.py, and the complete dry run was retried.
The retry passed both preflight and compilation, reporting:

    OK (dry run): commit 54cef0d9a5b passes the preflight and compiles; nothing pushed

Thus the previous shared compiler-artifact failure no longer prevents delivery. The
report was updated to record this successful validation; the attachment itself did
not require a mathematical or interface repair. The library, its artifacts, and all
launcher scripts remain unmodified by this worker. No global build was run.
