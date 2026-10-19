## Worker report

This node reuses `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`
in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, lines 97–101 of the
read-only slopmaster2 source. No Lean module, theorem, proof, or definition is added.
The same declaration was recorded on dependency
`def-weil-pbc-projection-compactification` on master; it is now also present on
slopmaster2. The node's explicit `blueprint.same_as` agrees with this reuse.

The recorded signature is verbatim from the source, before `:=`. Its section
parameters are `A : Type u'`, `[Category.{u + 1} A]`, `[Abelian A]`,
`[IsGrothendieckAbelian.{u + 1} A]`, `{X Y : Scheme.{u}}`, `{f : X ⟶ Y}`,
and `(c : Compactification f)`. Although the enclosing section also mentions
`HasSmallSiteSheafify A`, the declaration does not retain that unused parameter,
as the server's `#check @...` confirms. Here the source's category parameter `A`
is specialized to `ModuleCat.{u + 1} Λ` for the node's commutative coefficient
ring `Λ : Type (u + 1)` with `[CommRing Λ]`.

Clause-by-clause correspondence:

- The coefficient ring is `Λ` with `[CommRing Λ]`. The coefficient category is
  `ModuleCat.{u + 1} Λ`; its required Grothendieck abelian instances synthesize.
- Schemes and their morphism are `{X S : Scheme.{u}}` and `{f : X ⟶ S}`.
  The existing definition works for arbitrary schemes, so applies in particular
  under the node's Noetherian assumptions, without imposing extra hypotheses.
  No new declaration extending or changing the node's scope is introduced.
- The chosen factorization is `c : Compactification f`. Its `Z`, `i`, and `g`
  are the node's ambient scheme, `j`, and `r`. Its `isOpenImmersion`, `isProper`,
  and `comm : f = i ≫ g` give exactly the required three conditions.
  This structure does not impose density or any unmentioned condition.
- Both categories are the ordinary unbounded
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`,
  definitionally `Etale.DerivedCategoryModule Λ T`. This is the recorded
  six-functor encoding of constant-ring module sheaves, not pro-etale sheaves.
- The first factor of the body is `D((c.i)_!open[ModuleCat Λ])`, namely
  `openImmersionLowerShriek` followed by `Functor.mapDerivedCategory`.
  It is induced by exact extension by zero, not a new choice of functor.
  Its localization compatibility supplies the normalization
  `Q_X ⋙ Dj_! ≅ j_! on complexes ⋙ Q_Z` (or its inverse in the node's orientation).
- The second factor is `R((c.g)_*[ModuleCat Λ])`, the generic
  `Functor.rightDerivedFunctor` of `Etale.lowerStar`. Inspection of
  `CategoryTheory/DerivedCategory/RightDerivedFunctor/Defs.lean`, lines 162–195,
  shows its body is
  `(F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
  DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))`.
  It is explicitly the unbounded total derived construction on the homotopy
  category, with its right-derived unit and an invertible unit at every
  K-injective complex. It is not `rightDerivedFunctorPlus`.
- Consequently a complex is extended degreewise by zero, resolved by a
  K-injective complex `I`, and evaluated as `Q_S(r_* I)` up to the canonical
  derived comparison. The localizer construction through K-injectives sends
  a representing homotopy class by termwise pushforward. Additivity is the
  existing prerequisite for `mapHomotopyCategory`; shifts and cones are the
  standard ones, with no extra triangulation chosen by this node.
- Lean's `⋙` composes in application order, so the exact body
  `D((c.i)_!open[A]) ⋙ R((c.g)_*[A])` is precisely `Rr_* ∘ Dj_!`.
  Its object and morphism maps are the composite functor's maps.
- Refinement comparisons, coherence, and invertibility are not defining data
  in this node. No such assertion or pro-etale identification is introduced.
  There is no boundedness, torsion, or constructibility restriction.

Dependency declarations inspected and reused, including full source signatures
and docstrings:

- `WeilConjectures.Compactification.Refinement`:
  `AlgebraicGeometry.Compactification.Refinement`, `Compactification.category`;
  the factorization structure itself is in `Compactification.Defs`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology` and its recorded
  existing carrier `Etale.DerivedCategoryModule` (defined in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`). Torsion is not imposed.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`. The node itself explicitly avoids the
  old bounded-below-only record for its unbounded interpretation; the actual
  total right derived construction was inspected as above.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`, its additive instance and
  `Etale.preservesFiniteLimits_openImmersionLowerShriek`.
- `Mathlib.CategoryTheory.Localization.Predicate`:
  `CategoryTheory.Localization.lift`, `fac`, `liftNatTrans`, `liftNatIso`,
  and `natTrans_ext` express descent and uniqueness.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`:
  `CochainComplex.IsKInjectiveResolution` is `QuasiIso f ∧ I.IsKInjective`.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`:
  `CochainComplex.etale_kinjective_resolutions_exist`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`; the existing
  construction already realizes this universal property, so no second chosen
  witness is extracted from that existence theorem.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective` and `quasiIso_iff`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Qh`;
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated`;
  `Mathlib.CategoryTheory.Triangulated.Triangulated`: `IsTriangulated`;
  `Mathlib.CategoryTheory.Triangulated.Functor`: `Functor.IsTriangulated`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`
  (dependency `def-weil-pbc-projection-compactification`).

Edge cases: empty schemes and empty open immersions remain allowed by
`Compactification`; no density or nonemptiness is imposed. The zero ring and
zero complex are allowed. There is no lower or upper cohomological bound.
For a proper map, `Compactification.ofIsProper` has `i = 𝟙 X`, as required
by the shared chosen-compactification construction. On Noetherian schemes the
open immersion is automatically quasi-compact, so the shared node's
quasi-compact formulation excludes no case here. Universe `u` is arbitrary,
and coefficient modules use the same `u + 1` convention as the dependency.

Searches (2026-10-15):

- `msearch.py ... leanfinder`: "unbounded etale compact support functor extension
  by zero followed by total derived direct image" returned eight results on
  homological complexes/local cohomology, none defining this functor.
- `msearch.py ... loogle`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` returned
  unknown identifier (the remote index is Mathlib, not this project).
- `msearch.py ... leansearch`: "derived direct image with compact support chosen
  compactification" was unavailable with Internal Server Error.
- `msearch.py ... grep`: `rightDerivedLowerShriekOfCompactification|compact.support`
  returned 25 unrelated Mathlib hits on compactly supported functions.
- `rg` on `WeilConjectures/SixFunctors/Etale` found the exact existing
  declaration in `Derived/LowerShriek.lean`. Its complete declaration and body
  were opened, together with the generic right-derived-functor definition.
- `rg` on `lean/Sheaf` found no duplicate declaration. `rg` on
  `dag/lean_names_upstream.json` found the same full name (line 475).
- `rg` for the exact node id on `WeilConjectures` found no blueprint-id tag;
  this does not override the exact match by content.

Source checked: the node's cited blueprint file, order 1560, and the upstream
module docstrings and definitions. No statement correction, new node, or
unusable dependency module is needed; no statement is disputed.

Validation: the sandbox scratchpad probe `ExistingCompactSupport.lean` was
compiled using `scompile.py NE def-amb-etale-compact-support` on the server.
It checks the full existing signature and the specialization
`rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :
DerivedCategoryModule A X ⥤ DerivedCategoryModule A S` with every binder and
universe explicit. It compiled without warnings in 1.8 seconds, nice 19,
two threads, limit 60 seconds. This scratchpad probe is not a delivered module.

## Second reading by NE

I independently opened the node, its cited blueprint definition (order 1560),
the upstream declaration and body, and every statement-dependency node and its
recorded declarations. The cited source here is the blueprint markdown, not a
Stacks tag: it assumes Noetherian schemes, a fixed compactification, and ordinary
etale derived categories. The node's expansion specifies the unbounded meaning
of that formula; it preserves the source's scope and leaves comparisons to the
separate comparison lemma. No statement correction is present or needed.

Objects, hypotheses, and defining clauses, in node order:

1. A commutative coefficient ring: specialize upstream `A` (a coefficient
   category) to `ModuleCat.{u + 1} Λ`, with `Λ : Type (u + 1)` and `[CommRing Λ]`.
   Verdict: exact module-coefficient instance, including the zero ring; all
   required abelian and Grothendieck instances synthesize in the server probe.
2. A morphism `f : X ⟶ S` of Noetherian schemes: upstream takes
   `{X Y : Scheme.{u}} {f : X ⟶ Y}`. Verdict: this existing general definition
   restricts to exactly the node's objects; it needs no added finiteness,
   separation, characteristic, base field, or compactifiability instance.
   Reusing a general definition on these objects does not assert a new theorem
   with the Noetherian hypotheses omitted.
3. Chosen ambient scheme, open immersion, proper map, and factorization:
   `c : Compactification f` has fields `Z`, `i`, `g`, `isOpenImmersion`,
   `isProper`, and `comm : f = i ≫ g`. Verdict: exactly the datum `(j,r)`;
   no density condition. I read `Compactification.Defs` and `Refinement`, not
   merely the dependency's similarly named refinement declaration. Refinements
   are not an argument of the candidate.
4. Ordinary unbounded module derived categories: the displayed signature is
   `DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
   DerivedCategory (Sheaf Y.smallEtaleTopology A)`. The coefficient specialization
   is definitionally `Etale.DerivedCategoryModule Λ X ⥤
   Etale.DerivedCategoryModule Λ S`, as read in `Derived.Coefficients` and
   `Sheaf.AlgebraicGeometry.DerivedCategories`. Verdict: the recorded dependency
   encoding, with no torsion, constructibility, or boundedness condition.
5. Degreewise extension by zero and descent: the first factor is
   `D((c.i)_!open[A])`. I opened `openImmersionLowerShriek`, its adjunction,
   additive instance, and finite-limit-preservation instance. The left adjoint
   preserves finite colimits; the resulting exact functor uses
   `Functor.mapDerivedCategory`. Mathlib's `mapDerivedCategoryFactors` has
   `Q ⋙ F.mapDerivedCategory ≅ F.mapHomologicalComplex (.up ℤ) ⋙ Q`, precisely
   the node's normalization. Verdict: exact localization descent, on maps too.
6. Direct image: the second factor uses `Etale.lowerStar A c.g`, whose body
   is sheaf pushforward by base change on small etale sites. Its objectwise
   formula is evaluation on `V ×_S c.Z`. Verdict: the dependency's module-sheaf
   direct image, not pushforward on another site or topological space.
7. Total unbounded right derivation: `R((c.g)_*[A])` expands to
   `Functor.rightDerivedFunctor`, defined by total right derivation of
   `F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh` along `Qh`.
   I checked its unit, `IsRightDerivedFunctor` instance, and invertibility
   of the unit on K-injectives. Verdict: exactly the unbounded construction;
   the bounded-below direct-image record is not being substituted for it.
8. Resolution computation and morphisms: `IsKInjectiveResolution` is
   `QuasiIso f ∧ I.IsKInjective`. I read its module, the resolution existence
   declaration, `exists_rightDerived_of_enough_isKInjective`, and Mathlib's
   `IsKInjective.Qh_map_bijective` and `quasiIso_iff`. They give the same
   K-injective computation and homotopy-class map rule used by the existing
   total derived construction. Verdict: no arbitrary functor or unresolved
   existence choice is substituted for this construction.
9. Composition and evaluation: upstream's exact body is
   `D((c.i)_!open[A]) ⋙ R((c.g)_*[A])`. Lean composition applies extension by
   zero first and right derived direct image second. Verdict: both object
   and morphism assignments are precisely `Rr_* ∘ Dj_!`, so a complex is
   extended, resolved on the ambient scheme, then pushed forward.
10. Refinement comparison, coherence, and independence: absent from this
    definition's data, just as the node explicitly requires. Verdict: no extra
    assertion, pro-etale identification, or compactification choice added.

Edge cases: the empty scheme and empty open immersion are valid inputs;
`Compactification` imposes neither density nor nonemptiness. The identity
compactification of a proper map is `Compactification.ofIsProper`, with
`i = 𝟙 X`. The zero ring, zero sheaf, and zero complex are allowed. All degrees
are indexed by `ℤ`, so degree zero and arbitrarily unbounded complexes are
included. There is no characteristic restriction or index-set assumption.
The universe `u` is arbitrary; the coefficient/module universes agree with
`DerivedCategoryModule` and the recorded dependency convention. Smaller rings
can be viewed in `Type (u + 1)` by cumulativity, and the ambient universe can
be enlarged. Every binder in the specialization probe is explicit under
`autoImplicit false`; the printed upstream type confirms there is no retained
`HasSmallSiteSheafify` hypothesis.

Independent searches, with different wording from the first worker:

- LeanFinder, "Derived functor of proper pushforward after exact open immersion
  extension on sheaves": eight hits, all generic sheaf pushforward or its
  comparison isomorphisms, not this composite.
- Loogle, `CategoryTheory.Functor.rightDerivedFunctor`: unknown identifier in
  the Mathlib-only search index; the upstream source was opened directly.
- LeanSearch, "Unbounded compactly supported direct image of sheaves from a
  fixed compactification": unavailable, HTTP 521; no search verdict inferred.
- `rg` on upstream and `lean/Sheaf` for declarations of
  `rightDerivedLowerShriekOfCompactification`, `mapDerivedCategory`, and
  `DerivedCategoryModule`: the etale declaration is the exact match;
  the pro-etale sibling has a different coefficient site and was excluded.
  `rg` for `compactification|lowerShriek` on Mathlib's algebraic geometry and
  homology directories found no competing definition. No private copy exists
  in this delivery, and the shared chosen-compactification dependency already
  names this same construction.

No mismatch found. No Lean, node signature, natural-language statement, or
statement-dependency change was necessary. No new nodes or dependency modules
are delivered, no theorem is proved, and no hollow definition is introduced.
Existing upstream docstrings describe the two factors and the unbounded
interpretation; the new-module docstring rules require no duplicate module.
The JSON signature was checked programmatically against the source substring
from `noncomputable abbrev` through the text before `:=`: verbatim equal.

Validation repeated independently: `scompile.py NE
 def-amb-etale-compact-support .../scratchpad/ExistingCompactSupport.lean`
passed without warnings, 1.8 seconds, server nice 19, two threads, 60-second
limit. Its output checks both the full upstream signature and the exact
module-coefficient specialization. The scratchpad is not part of delivery;
there are no delivered Lean files requiring another compile.
