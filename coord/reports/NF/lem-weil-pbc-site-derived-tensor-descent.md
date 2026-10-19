## Worker report

The module `Sheaf.Algebra.Homology.SiteDerivedTensorDescent` states the single theorem
`SheafOfModules.site_derived_tensor_descent`, with proof `by sorry`. It makes no new
definitions. The node's natural-language statement and dependency lists are unchanged.
The theorem states the resolving-subcategory equivalence, descent of total tensor, and
full faithfulness on natural transformations for the product of the resolving functors.

Hypothesis and clause correspondence:

- The small site is `{C : Type u} [Category.{u} C] (J : GrothendieckTopology C)`.
  The coefficient and module universe is `u`, so this is the usual small-site encoding
  relative to module sheaves. `R : Sheaf J CommRingCat.{u}` is the given sheaf of
  commutative rings. There are no geometric, boundedness, nonzero-ring, or flat-ring
  assumptions. Small-site sheafification and the abelian structure are inferred.
- `SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)` is
  precisely the category of R-module sheaves. Forgetting commutativity here just supplies
  the input ring sheaf to Mathlib's module-sheaf carrier; the tensor still uses R.
- `HomotopyCategory ... (ComplexShape.up ℤ)` is K(R). `DerivedCategory ...` under
  `[HasDerivedCategory.{w} ...]` is D(R), with its chosen morphism universe w.
  `DerivedCategory.Qh` is Q_R, the localization from K(R).
- The existential object property P is completely specified by
  `∀ X, P X ↔ CochainComplex.IsKFlat X.as ∧ ∀ n : ℤ, SheafOfModules.IsFlat (X.as.X n)`.
  Mathlib's quotient keeps the complex as its object (`X.as`), so this tests the actual
  complex's K-flatness and all its terms' flatness, without requiring those properties
  to be invariant under arbitrary homotopy equivalences. P is uniquely determined as
  a predicate by this equivalence. `P.FullSubcategory` and `P.ι` are Mathlib's full
  subcategory and inclusion. No private definition of K-flatness or flatness is used.
- W_R is `(HomotopyCategory.quasiIso ... (.up ℤ)).inverseImage P.ι`. Its
  `.Localization` is the constructed localization W_R^{-1} P_R. The first existential
  functor F has `F.IsEquivalence`, and the natural isomorphism
  `W_R.Q ⋙ F ≅ P.ι ⋙ DerivedCategory.Qh` specifies precisely the induced functor.
  It is not an unrelated equivalence between the categories.
- The existential bifunctor B on K(R) × K(R) is specified by a natural isomorphism
  after precomposition with the product of the homotopy quotient functors. Its other
  side is `Functor.uncurry.obj ((@curriedTensor ... (monoidalCategory R)).
  map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ HomotopyCategory.quotient ...`.
  This is exactly the functorial total complex of the tensor double complex, with
  Mathlib's signed total differential, not an arbitrary objectwise tensor operation.
- The existential `T : D(R) × D(R) ⥤ D(R)` is the derived tensor bifunctor.
  `Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ Qh ≅ ((P.ι ⋙ Qh).prod (P.ι ⋙ Qh)) ⋙ T)`
  gives the displayed representative comparison Q_R Tot(P tensor Q) ≅
  Q_R(P) tensor^L Q_R(Q). Composing its components with the comparison specifying B
  gives the complex-level displayed isomorphisms. Both comparisons are natural
  isomorphisms of bifunctors, so naturality is in both homotopy-category variables.
  For a denominator s, the same naturality square implies the square for s^{-1}
  by multiplication with the inverse images of s; this is the node's compatibility
  with inversion, rather than an extra assumption or a selected class of maps.
- `∀ (E : Type e) (_ : Category.{z} E) (U V : D(R) × D(R) ⥤ E),
  Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft ((P.ι ⋙ Qh).prod
  (P.ι ⋙ Qh)) τ)` is exactly the final clause. Injectivity is unique determination,
  and surjectivity is extension of every transformation on the restriction. No
  transformation is assumed invertible. The universes e and z are independent
  and arbitrary.

The existential P is the fully specified predicate in the statement, not a definition
selected from an undetermined existence assertion. The statement does not introduce
any new data-valued constants or any substitute framework. The existential B records
the intermediate descent through homotopy already used by the node's proof, and T
records the asserted existence of the descended bifunctor.

Dependency declarations read and used:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, `SheafOfModules.Hom`.
  This is the general-site carrier explicitly allowed by the note/mathlib_match on
  `def-weil-sheaf-of-modules-category`. Its headline `AlgebraicGeometry.Scheme.Modules`
  (`Mathlib.AlgebraicGeometry.Modules.Sheaf`) is only the scheme specialization and
  is not used to restrict the site.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` and its public upstream
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`:
  `SheafOfModules.monoidalCategory`, `tensorObjIsoSheafification` give the actual
  sheafified tensor. The tensor-power and change-of-rings declarations in the node
  are not needed for this item.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`; its zero-morphism and
  sheafification-monoidality instances supply the total complex's infrastructure.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`: `SheafOfModules.IsFlat`, defined
  as exactness of right tensor with the sheaf.
- `Mathlib.Algebra.Homology.BifunctorShift` (public through KFlat) and Bifunctor:
  `CochainComplex.mapBifunctor`, `Functor.map₂HomologicalComplex`, with
  `CategoryTheory.MonoidalCategory.curriedTensor`. The functorial version has the
  node's recorded total tensor as its objects.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Qh`, and the quotient comparison.
- Mathlib `ObjectProperty.FullSubcategory`, `ObjectProperty.ι`,
  `MorphismProperty.Localization`, `MorphismProperty.Q`, `Functor.uncurry`,
  `Functor.prod`, and `Functor.whiskerLeft` express the standard categorical
  constructions without duplicating them.

The proof-only imports cover all stated proof dependencies: KFlatResolution
(`CochainComplex.exists_isKFlatResolution`), DerivedCategory.Fractions (the two
quasi-isomorphism calculus instances), Localization.CalculusOfFractions
(`Localization.exists_rightFraction`, `MorphismProperty.RightFraction.map_eq_iff`),
and upstream HomotopyCategory.Acyclic (`CochainComplex.mappingCone.quasiIso_iff_acyclic`).
Localization.Predicate, available through the derived-category imports, supplies
`Localization.lift`, `fac`, `liftNatTrans` and `natTrans_ext`. The docstring follows
all six node proof steps, including the signed tensor homotopies, cone argument,
roof refinements, and two successive localizations.

Edge cases checked mathematically before writing: zero ring and zero complexes do
not require exclusions; an empty site gives the corresponding zero module category;
unbounded complexes retain the direct-sum totalization and all integer degrees;
flat terms remain required independently of K-flatness. Over the one-object site
with ring Z, Z/2 in degree zero is excluded from P by the flatness clause. Arbitrary
U, V and arbitrary (including noninvertible and zero) transformations are included.
No empty-family or nonemptiness assumptions are introduced. Category universes and
the chosen derived morphism universe are explicit. No counterexample or statement
correction was found.

Searches for an existing statement (msearch.py with group NF and this item):

- leanfinder, query "Localization of K-flat complexes with flat terms on a ringed
  site gives derived tensor bifunctor and unique extension of natural transformations":
  eight hits, including CategoryTheory.Tor', Tor, their object/map lemmas, and
  Functor.mapDerivedCategoryFactorsh_hom_app. None states this site-level unbounded
  resolving-subcategory localization and two-variable transformation descent.
- loogle, query `"KFlat"`: one hit `Lean.mkFlatCtorOfStructCtorName`, unrelated.
- grep, query `KFlat|derivedTensor`, subdirectory CategoryTheory: zero hits.
- leansearch, query "Derived tensor bifunctor on a ringed site computed by localization
  of flat term K-flat complexes": unavailable, Internal Server Error, zero hits.
- Direct source rg for `KFlat|kFlat|derivedTensor` finds the FromJoel generic
  quasi-isomorphism-preserving KFlat machinery and specialized etale tensor functors,
  with a different K-flat predicate. They do not state this theorem for R-module
  sheaves and flat-term representatives. The node-id grep in WeilConjectures has
  no match.
- Direct project rg for `site_derived_tensor_descent|tensor.*descent|derived.*tensor.*descent`
  finds scheme-specific and module-ring descent/associator statements, not this one.
  MixedTotalTensorAssociatorDescent was inspected: it concerns ModuleCat over rings,
  uses the generic FromJoel KFlat, and does not supply the ringed-site statement.
- Upstream name-table rg for `site_derived_tensor_descent|derived_tensor_descent|KFlat.*[Ll]ocalization`
  has no match. The declaration name is new.

Validation: scompile.py reports a clean compile of the module in 2.7 seconds,
nice 19, two threads, limit 60 seconds. No local compiler or global build was used.
The only postponed proof is the theorem named above. Delivery dry-run follows.


## Second reading by NF

I independently read the item node, its six statement-dependency nodes and their
recorded source declarations, the module, and the Stacks source text. No statement
correction, dependency module, or new definition node is needed. The Lean statement
and node record are unchanged; this reading adds the review evidence below.

Object/hypothesis/conclusion inventory and correspondence (H3):

1. A site small relative to the module universe: `{C : Type u} [Category.{u} C]`
   and `J : GrothendieckTopology C`. Verdict: matches. Smallness is relative, since
   `u` is arbitrary; a site in a smaller universe can also be regarded in the module
   universe by cumulativity. The small-site abelian/sheafification instances are
   inferred, not extra hypotheses. I checked the small-site instance explanation
   in Mathlib's module-sheaf Abelian file.
2. A sheaf of commutative rings: `(R : Sheaf J CommRingCat.{u})`.
   Verdict: matches, including the zero ring and every characteristic. The carrier
   `SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)`
   forgets only commutativity in order to use Mathlib's existing module-sheaf
   category. I opened `SheafOfModules` and `SheafOfModules.Hom`: these are module
   presheaves whose underlying additive presheaves are sheaves, with module-linear
   morphisms. The dependency's note explicitly supplies this general-site carrier;
   its scheme-specialized headline declaration is not substituted for it.
3. Integer-indexed complexes, their homotopy category, and localization Q_R:
   `HomotopyCategory ... (ComplexShape.up ℤ)`, `DerivedCategory ...`, and
   `DerivedCategory.Qh`. Verdict: matches. I opened HomotopyCategory (a quotient
   of morphisms by homotopy, retaining the complex as object) and DerivedCategory.Basic
   (`Qh` and `quotientCompQhIso`). `[HasDerivedCategory.{w} ...]` is precisely the
   chosen localization/morphism-size structure of the recorded derived-category
   dependency; it adds no geometric or finiteness assumption.
4. The full subcategory of K-flat complexes with flat terms:
   `∃ P : ObjectProperty ...`, fixed by
   `∀ X, P X ↔ CochainComplex.IsKFlat X.as ∧ ∀ n : ℤ, SheafOfModules.IsFlat (X.as.X n)`.
   Verdict: matches exactly. `X.as` is the actual underlying complex, not an arbitrary
   chosen homotopy-equivalent replacement. I read IsKFlat: acyclic F implies acyclic
   total tensor F tensor K. I read IsFlat: exactness of right tensor with that module.
   Thus both independent conditions are present. `P.FullSubcategory` and `P.ι` are
   the existing full-subcategory constructions; the existential predicate is uniquely
   specified, not an undetermined data-valued definition.
5. W_R and the induced equivalence: `(HomotopyCategory.quasiIso ...).inverseImage P.ι`,
   its `.Localization`, the functor `F`, `F.IsEquivalence`, and
   `Nonempty (W_R.Q ⋙ F ≅ P.ι ⋙ DerivedCategory.Qh)`.
   Verdict: matches; the last comparison ties F to the induced functor. An unrelated
   equivalence of categories would not satisfy this clause. I read the localization
   construction, which inverts exactly the supplied morphism property.
6. Total tensor induces a derived bifunctor: `∃ B` on the product of homotopy
   categories, its natural comparison after the product quotient functor with
   `Functor.uncurry.obj ((curriedTensor ...).map₂HomologicalComplex ... )`, and `∃ T`
   on the product derived category. Verdict: matches. I opened map₂HomologicalComplex:
   its objects are the existing mapBifunctor total complexes and its maps are the
   functorial tensor maps. The total-complex shape has degree p+q, first sign 1 and
   second sign (-1)^p. The explicitly supplied `SheafOfModules.monoidalCategory R`
   is the dependency's sheafified sectionwise tensor, checked against its source
   `tensorObjIsoSheafification`. There is no second tensor definition here.
7. The representative isomorphisms, naturality, and inverse denominators:
   `Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
   ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙ T)`.
   Verdict: matches. Composing with the preceding B comparison gives precisely the
   complex-level representative formula. A natural isomorphism on the product gives
   simultaneous naturality, hence naturality in each homotopy variable. For a
   quasi-isomorphism between representatives both its image under Qh and the
   corresponding tensor map after Qh are invertible; rearranging the naturality
   equation gives the equation for the inverse denominator. No extra compatibility
   assumption is needed.
8. Every category E, bifunctors U,V, and arbitrary natural transformations:
   `∀ (E : Type e) (_ : Category.{z} E) (U V : D(R) × D(R) ⥤ E),
   Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft (L.prod L) τ)`,
   where the displayed L is literally `P.ι ⋙ DerivedCategory.Qh` in the file.
   Verdict: matches. Injectivity is determination/uniqueness, surjectivity gives
   extension of every transformation on the restriction. There is no isomorphism
   hypothesis on τ. Both E universes are arbitrary and independent. The predicate
   P is fixed before F, B, T and the final clause, as required.

Sources and proof plan (H8): Stacks sites-cohomology.tex, section-flat, assumes
only a ringed site throughout. I read lemma-K-flat-resolution (06YS), including
flat terms and its termwise-surjective conclusion; lemma-factor-through-K-flat
(0G7D), including preservation of flat terms; lemma-derived-tor-exact (06YM);
definition-K-flat (06YN); lemma-K-flat-quasi-isomorphism (06YP);
lemma-derived-tor-quasi-isomorphism-other-side (06YT); and the construction before
and definition-derived-tor (06YU). The source introduces no boundedness or ring
finiteness assumption. In categories.tex I read the right-roof representation,
equality and localization universal property (04VI, 04VJ, 04VK). The docstring
retains all six node steps: resolving Ore and cancellation witnesses; refining
roofs for full faithfulness and resolving objects for essential surjectivity;
signed tensor homotopies; acyclic cones and signed symmetry; two-variable
localization; and extension/uniqueness of arbitrary natural transformations.
Imports include the recorded resolution, fraction-calculus, localization and cone
proof dependencies. No theorem other than the single named `by sorry` statement
is introduced, and no data-valued definition or local notation is introduced.

Edge cases: the empty site and zero ring are allowed; no Nonempty, Nontrivial,
field, characteristic, or geometric hypothesis appears. Zero complexes satisfy
both resolving conditions. Over the one-object Z site, Z/2 concentrated in degree
zero fails the flat-term condition, as it should; flatness was not silently
replaced by K-flatness. All integer degrees, including 0 and negative degrees,
and unbounded complexes use direct-sum totalization. There is no external index
set to require inhabitedness. Empty target categories and noninvertible/zero
transformations are covered by the unrestricted functor-category clause.
Universes u,w,e,z are explicitly bound, and all category/complex variables are
bound. No pro-etale or unsynced framework is imported or substituted.

Independent searches (H4), using different queries from the first worker:

- msearch leanfinder: "Localization of resolving subcategory of complexes induces
  equivalence and fully faithful restriction of functors in two variables".
  Eight hits include LocalizerMorphism.isLocalizedEquivalence_of_functorial_right_resolutions
  and HasLeftResolutions/HasRightResolutions. I inspected the resolution API:
  these are generic localization tools, not the site-level flat-term resolving
  subcategory, total tensor descent, and full transformation statement together.
- msearch loogle: `"map₂HomologicalComplex"`. Four hits: the functor and its
  object/map formulas. I read its source and confirmed its use above; none states
  the localization theorem. A preliminary two-string Localization/prod query was
  rejected by Loogle syntax and was replaced by this valid query.
- msearch grep: `resolving|localization.*tensor`. Twenty-three hits, including
  generic monoidal localization and commutative-algebra localization, no match.
- Direct rg on Mathlib and on upstream/project sources for resolving classes,
  localizerMorphismKFlat and tensor/derived-tensor descent found generic upstream
  derived monoidal machinery and specialized project statements. I opened
  HasMonoidalDerivedCategory: it requires monoidal closed Grothendieck categories
  with functorial flat resolutions and uses the FromJoel KFlat predicate, not
  this flat-term subcategory. I also opened KFlatBifunctorIsoDescent (schemes and
  isomorphisms only) and MixedTotalTensorAssociatorDescent (module categories over
  rings, mixed tensor associators). Neither states this general-site theorem or
  its arbitrary-transformation clause. The upstream name table has no match for
  site_derived_tensor_descent or derived_tensor_descent.

Mismatch/repair verdict: no mismatch found; no Lean or node change made. There are
no new nodes or dependency modules to review under H12/H13, and no statement_change
or corrected citers under H7. I verified by exact text comparison that lean.statement
is the module's complete signature verbatim. Independent server validation through
scompile.py passed cleanly in 2.6 seconds, nice 19, two threads, 60 seconds per file.
