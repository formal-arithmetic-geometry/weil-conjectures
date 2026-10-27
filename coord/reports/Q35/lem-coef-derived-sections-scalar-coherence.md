## Worker report

The module `Sheaf.CategoryTheory.DerivedSectionsScalarCoherence` states
`CategoryTheory.CoefficientDerivedSections.derivedSectionsScalarCoherence` with one
postponed proof. All other declarations are concrete abbreviations or definitions
for the objects occurring in this node. No statement correction, new DAG node,
dependency repair, axiom, additional mathematical hypothesis, or proved theorem is
introduced.

Source read: `literature/stacks-project/sites-cohomology.tex`, lines 4011–4030,
`lemma-derived-pushforward-composition` (0D6E); `sites.tex`,
`definition-global-sections`, lines 10603–10616; the current blueprint
`sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
paragraph 2 and its first/last mapping-complex comparisons. Also read the complete
seven-step node proof and every statement-dependency node, its recorded interface,
and each corresponding source signature/docstring.

Clause-by-clause rendering:

* A small site in the coefficient universe is `{C : Type u} [SmallCategory C]`
  and `{J : GrothendieckTopology C}`. The standard sheafification and
  locally-bijective classes are the existing Mathlib interface to its abelian
  category; they hold for this small site and coefficients in `u`. There is no
  terminal-object assumption on C. The two universes `u w` are explicit; the
  quantified HasDerivedCategory instances specify the chosen localization
  universe and can always be supplied with the standard size convention.
* Each commutative coefficient is `R : Sheaf J CommRingCat.{u}`.
  `coefficientModules R` is transparently the dependency's `ringedSiteModules`,
  and thus exactly `SheafOfModules` on the associated RingCat sheaf. It is not
  a second category or a chosen abelian structure.
* `coefficientSections R` is `SheafOfModules.toSheaf _ ⋙ Sheaf.Γ J AddCommGrpCat`.
  Mathlib's global-sections adjunction and `ΓNatIsoCoyoneda` identify its
  underlying elements with maps from the terminal set sheaf, as in 06UN.
  The group operations are those of the existing abelian global-sections
  functor. `coefficientComplexSections` applies this same construction degreewise.
* The first conjunct constructs the specified `g_R` as a `RingedToposMorphism`.
  `sectionsPoint` is `Discrete PUnit`, lifted to universe u solely to fit that
  dependency's site universes; `sectionsPointTopology = ⊥` has exactly the
  maximal covering sieve. `sectionsPointIntegers` is the actual constant
  presheaf `ULift ℤ`, with its bottom-topology sheaf proof. Evaluation followed
  by forgetting integer scalars is `sectionsPointAbelian`. This is the same
  singleton-site evaluation of the dependency, transported through the unique
  equivalence of its singleton presentation with the universe-sized singleton.
  No new module/sheaf notion is introduced. The existential isomorphism `e`
  identifies `g.inverse` with singleton evaluation followed by `constantSheaf`.
  The next two isomorphisms identify its set and module direct images with
  global sections. The final equation specifies its structural ring map on
  every integer generator via `toSheafify`, as the integer cast `n.down` in R(U).
* `H R` and `η R` have the required unbounded derived types.
  `(H R).IsRightDerivedFunctor (η R) (HomologicalComplex.quasiIso ...)` is
  Mathlib's universal total right-derived pair (left Kan extension along Q),
  the exact universal property in def-sfb-right-derived-functor. The next
  conjunct requires its unit invertible on every K-injective complex. Choosing
  universal pairs existentially is the same formulation as the recorded
  ringed-topos composition theorem; universal uniqueness identifies them with
  any fixed universal pairs. Nothing is defined by a bare existence choice.
* `coefficientRestriction a` is the recorded `SheafOfModules.restrictScalars`
  along the ring-sheaf map. `coefficientComplexRestriction a` applies it
  degreewise. The family `r a`, together with its natural isomorphism
  `ν a : Q ⋙ r a ≅ C(r_a) ⋙ Q`, specifies its descent through localization,
  rather than introducing any arbitrary map. Q's universal property determines
  this pair uniquely up to its normalized isomorphism.
* `σ a : H S ⟶ r a ⋙ H R` is a natural transformation. `IsIso (σ a)` supplies
  invertibility as a transformation, rather than only degreewise cohomology.
  The displayed equation `(η S).app M ≫ (σ a).app (Q.obj M) = ...`
  is exactly the node's derived-unit normalization, with `H R` applied to
  `ν.inv` to change the target from `H_R(Q(rM))` to `H_R(r(QM))`.
* The clause quantifying `τ` says that EVERY natural transformation with this
  unit equation equals `σ a`. Thus uniqueness applies before assuming τ
  invertible; it is not merely uniqueness among isomorphisms.
* For every S-K-injective I, every R-K-injective K and every quasi-isomorphism
  `j : C(r_a) I ⟶ K`, the statement requires
  `QuasiIso ((coefficientComplexSections R).map j)`. The accompanying equation
  is the canonical representative formula, written without inverse units:
  `η_S ≫ σ_QI ≫ H_R(ν.hom) ≫ H_R(Qj) = QΓ(j) ≫ η_R,K`.
  All conjugating factors are invertible by the previous clauses. This is
  precisely the normalization of the canonical composition comparison in the
  dependency 0D6E theorem, specialized to the coefficient morphism and g_R
  under the singleton evaluation. Its unit uniqueness consequently identifies
  σ with that canonical comparison, not just with some isomorphism. This
  formula also retains arbitrary choices of the resolution j and K.
* For every composable a,b, the isomorphism `c : r (a ≫ b) ≅ r b ⋙ r a`
  is normalized by its equation with ν on EVERY complex. This is the explicit
  localization transport of the identical ordinary scalar actions; it is not
  an unconstrained comparison. The following equation on every derived X is
  `σ_RT` transported by `H_R(c)` equals `σ_ST ≫ σ_RS` evaluated at r_ST X,
  exactly the stated cocycle under those scalar identifications.
* For every R, the isomorphism `i : r (𝟙 R) ≅ 𝟭 _` is normalized by ν on
  every complex. `σ_id ≫ H_R(i) = 𝟙 _` on every derived object is exactly
  the identity law. All families and comparisons in these equations are
  natural transformations/isomorphisms, so naturality in the derived argument
  is retained throughout.
* There is no flatness, boundedness, injective-preservation, terminal-object,
  nonzero-ring, or nonempty-site assumption. K-injective resolutions are the
  dependency theorem used in the proof plan, not an extra hypothesis.

Dependency declarations (sources opened):

* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the actual site topology
  and sheaves use its retained Mathlib `GrothendieckTopology` and `Sheaf`.
* `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, a transparent Mathlib abbreviation.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and its localization instance.
* `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its unit,
  universal theorem and K-injective unit theorem, used in the proof plan;
  `Mathlib.CategoryTheory.Functor.Derived.RightDerived` supplies the same
  universal pair predicate on complexes used in the signature.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, including its additive instance.
* `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, including its
  unique unit-normalized comparison and arbitrary K-injective-resolution formula.
* `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, including `inverse`, `direct`, `ringMap`,
  `modules` and the operation/scalar-action conditions.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
* `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, exactly the acyclic-source homotopy condition.
* `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
* `Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage`:
  `CategoryTheory.restrictionRingedToposModuleDirectImage_exists`.
* `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`:
  `CategoryTheory.singleton_site_module_comparison`, `singletonSite`,
  `singletonTopology`, `singletonRingSheaf`, and `singletonEvaluation`.
* `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `sheafificationAdjunction`, `toSheafify`, and its finite-limit-preservation
  instance (the remaining proof dependency is this exact Mathlib leaf).
* `WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections`:
  `CategoryTheory.Sheaf.Γ_additive`; Mathlib's underlying `Sheaf.Γ`,
  `constantSheafΓAdj`, `ΓNatIsoLim`, and `ΓNatIsoCoyoneda` supply existing Γ.

Edge cases checked mathematically: empty C (unique compatible section and zero
abelian section group), the zero ring, the zero complex, identity coefficients,
a singleton site, and the nonflat map ℤ → ℤ/2. None is excluded by the signature.
The identity law uses a normalized localization isomorphism because arbitrary
chosen localization functors need not have definitional identity descent. The
same issue explains c in the cocycle; its equation prevents arbitrary twisting.
Temporary compiler probes confirmed that ordinary scalar composition, scalar
identity and restriction/underlying sections are definitionally identical; all
probe commands were removed. The site need not have a terminal object.

Searches actually run with msearch.py:

* leanfinder: `unbounded derived global sections restriction of coefficient rings
  unique natural isomorphism compatible derived units` — eight hits including
  `Scheme.restrictFunctorΓ`, `Functor.mapDerivedCategorySingleFunctor`,
  `DerivedCategory.singleFunctorIsoCompQ`; none states this theorem.
* loogle: `"restrictScalars", "rightDerived"` — zero hits.
* leansearch: `derived global sections restriction of scalars coefficient
  independence canonical natural isomorphism` — eight hits on ordinary
  restriction, including `ModuleCat.restrictScalarsCongr`,
  `PresheafOfModules.restrictScalarsObj`; none states the unbounded comparison.
* grep: `restrictScalars.*[Dd]erived|[Dd]erived.*restrictScalars|[Rr]ightDerived.*[Ss]ection`
  in CategoryTheory — zero hits.
* grep: `globalSections|sectionsFunctor` in Algebra/Category/ModuleCat/Sheaf.lean
  — `SheafOfModules.sectionsFunctor`, which is Type-valued and not derived Γ.
* Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: node id; derived/restrictScalars patterns;
  derived sections/scalar/coherence patterns; all introduced declaration names.
  Only scheme-specific, degree-zero, ordinary scalar, or per-degree comparisons
  occur. No declaration states the full site-general unit-normalized unbounded
  scalar comparison with its representative formula and cocycle. General Γ,
  scalar restriction, derived categories and the universal-pair predicate are
  reused directly; all helper declarations are transparent instantiations or
  singleton presentation data belonging to this node.

Validation: scompile.py compiled the delivered module separately in sandbox
and library module modes, with no error or unexpected warning (19.1 s and
31.6 s in the successful check). Every universe and variable is explicit;
`autoImplicit` is disabled. The only postponed proof is the node theorem,
whose docstring contains the complete seven-step proof plan. No node fault
or STATEMENT-DISPUTED concern remains.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
