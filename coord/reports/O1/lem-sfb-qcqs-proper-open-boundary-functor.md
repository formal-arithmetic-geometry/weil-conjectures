## Worker report

The module `Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryFunctor` states
`AlgebraicGeometry.ProEtale.CondensedRing.qcqs_proper_open_boundary_functor`.
Its single theorem has proof `sorry`; no definition or auxiliary theorem is introduced.
The node is unchanged except for `lean`.

Hypotheses and conventions, clause by clause:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The commutative condensed coefficient ring is
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, with `MonObj` and
  `IsCommMonObj`; `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ` uses the recorded
  coefficient convention, including discrete finite power-of-ℓ torsion rings,
  ℤ_ℓ, ℚ_ℓ, finite intermediate fields in the fixed PadicAlgCl and their valuation
  rings, and the two recorded algebraic-closure coefficient conventions. No new
  topology, scalar ring, or coefficient predicate is substituted.
- `S X Y V C : Scheme.{u}` and `Ab.{u+1}` use the published small pro-etale site
  (objects in u+1, morphisms in u), and the existing ordinary `DerivedCategory` of
  `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj Λ T)`.
  `condensedRingObj Λ T` is exactly p_T^*Λ. The fixed small indexing universe is
  u+1, as in the recorded proper-coproduct dependency, with no universe equality
  imposed on the site's object and morphism levels.
- S qcqs is `[CompactSpace S] [QuasiSeparatedSpace S]`.
- The two proper morphisms are `(q : Y ⟶ S) [IsProper q]` and
  `(f : X ⟶ Y) [IsProper f]`. The result is independent of q except for its stated
  proper-base context, which is retained in the signature.
- The quasi-compact open immersion is `(e : V ⟶ X) [IsOpenImmersion e]
  [QuasiCompact e]`.
- The closed immersion with quasi-compact open complement is `(c : C ⟶ Y)
  [IsClosedImmersion c] (hc : IsCompact (Set.range c)ᶜ)`. Closed immersion makes
  this complement open; compactness of that subset is its quasi-compactness.
  No relation of this subset to e is assumed.

Conclusions, in their order in the conjunction:

1. `PreservesFiniteLimits (upperStar Λ e)` and `PreservesFiniteColimits ...`
   say that the actual extension-of-scalars module pullback e* is exact.
   `Nonempty (upperStar Λ e ⋙ Mod.forget ... ≅ Mod.forget ... ⋙
   ProEtale.upperStar Ab.{u+1} e)` identifies its entire underlying functor,
   objects and arrows, with ordinary abelian inverse image. The corresponding
   three clauses for c render the identical assertion for c*.
2. `(openImmersionLowerShriek Λ e).mapDerivedCategory.IsTriangulated` and
   `(upperStar Λ c).mapDerivedCategory.IsTriangulated` state triangulatedness
   of J=D(e_!) and D(c*), using their canonical termwise shifts.
3. The next two universal quantifiers `∀ I : Type (u+1),
   PreservesColimitsOfShape (Discrete I) ...` state preservation of all small
   ambient coproducts by J and D(c*) on the full ordinary derived categories.
4. The universal K implication maps membership in
   `localizingClosureOfSize.{u+1} (constantModelBoundedConstructible Λ V ⊓
   fun L ↦ DerivedCategory.finiteTorAmplitude _ L)` into the corresponding X
   property after J. These are precisely the recorded replete triangulated,
   ambient-sum-closed hulls of the finite constant scalar-model D_ctf predicates.
5. The existential `P.IsTriangulated`, where P is that source hull, supplies the
   inherited triangulated category structure; `(... P.ι ⋙ J ⋙ Rf_* ⋙ D(c*)).
   IsTriangulated` states exactness of the restriction to the source hull.
   Here `(lowerStar Λ f).rightDerivedFunctor` is definitionally the recorded
   `moduleObjectDerivedPushforward Λ f`, not a different derived construction.
   Its explicit unfolded spelling exposes the published canonical K-injective
   shift instance to elaboration; no auxiliary shift structure is chosen.
6. For every I and ambient family K with each K t in that same source hull,
   `PreservesColimit (Discrete.functor K) (J ⋙ moduleObjectDerivedPushforward
   Λ f ⋙ D(c*))` says that the canonical comparison induced by coprojections
   is invertible. This formulation uses ambient colimits directly, so it also
   states preservation of the ambient sum used to form the source hull. It
   avoids replacing that comparison with an arbitrary isomorphism. Ambient
   sums exist by the Grothendieck/K-injective interfaces used by the recorded
   proper theorem. No common bound or derived-completeness premise occurs.

No field, characteristic, Noetherian, finite-dimensional-base, image-disjointness
or vanishing hypothesis or conclusion occurs.

Recorded statement dependency declarations read and used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`,
  `CategoryTheory.localizingClosureOfSize`, `IsLocalizingSubcategoryOfSize`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, transported
  monoid/commutative structures, accessed through the public framework imports.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`,
  whose body is exactly `(lowerStar Λ f).rightDerivedFunctor`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`, with the imported existing
  `DerivedCategory.finiteTorAmplitude` (testing every degree-zero module).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `openImmersionLowerShriek` and its exactness and adjunction interfaces.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  actual `upperStar` and `lowerStar`, pulled in through the framework above.
- Mathlib `AlgebraicGeometry.IsProper`, `QuasiSeparated`, `IsOpenImmersion`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsClosedImmersion` in the modules
  recorded by the corresponding geometric nodes. Only the needed geometric
  notions occur; a second finite-type hypothesis is not added to properness.
- `def-weil-size-convention` is metatheoretic; its recorded binding has no
  declaration, and the explicit universes here implement it.

Proof imports include the recorded proper-coproduct theorem, exact derived
coproduct theorem, generic derived resolution interface, cartesian coefficients,
K-injective triangulatedness, module-object Grothendieck theorem, sheaf
Grothendieck interface, Mathlib exact derived functors and adjoint colimits.
The K-injective triangulatedness import is public because its canonical CommShift
instance occurs in the elaborated statement. No imports are added from unstated
`lem-sfb-qc-open-extension-ctf`. The recorded proof-only
`det-proper-image-localizing-principle` module was deleted as dead on 2026-10-20;
its source is also unavailable through `scompile.py --source`. Its import is
therefore omitted; the elementary inverse-image-of-a-localizing-property argument
is retained in the theorem's complete five-step proof docstring. This is a
proof-plan interface fault, not a missing statement dependency of this delivery.

Edge cases checked before writing: I empty is allowed (no Nonempty binder), so
preservation includes zero; V empty and C empty are allowed; e or c may be an
identity; the images may overlap without restriction; residue characteristic ℓ
is allowed; unbounded families and ordinary non-complete sums are allowed.
Zero rings and zero complexes are not excluded. Proper q/f ensure the qcqs
geometric situation without a field or dimension binder. A nonreduced closed
source C is allowed; only its actual closed immersion and compact complement
are specified.

Searches for an existing statement:

- msearch LeanFinder: “Closed pullback after proper derived pushforward after open
  extension by zero preserves all coproducts on the localizing hull of constructible
  finite Tor complexes”: eight generic condensed AB and monoidal hits, no match.
- msearch Loogle: `CategoryTheory.Functor.IsTriangulated,
  CategoryTheory.Limits.PreservesColimit`: zero hits.
- msearch grep of Mathlib: `proper.*localizing|openImmersionLowerShriek`: five
  irrelevant stochastic-localizing or Verdier-localization hits, no match.
- msearch LeanSearch: “The composition of closed inverse image, proper derived
  pushforward and open extension by zero preserves all small coproducts on the
  localizing hull of constructible complexes”: eight generic finite coproduct,
  sheaf pushforward, proper-composition and localization hits, no match.
- rg of WeilConjectures and Sheaf for `qcqs_proper.*boundary`,
  `proper_open_boundary`, the item id, and `qcqs_proper.*Coproduct`: the existing
  proper-coproduct theorem and boundary-vanishing statements are different
  assertions. No theorem states the present continuity and typing conjunction.
  A separate search found existing shift wrappers on derived pushforward; the
  present statement instead unfolds the already recorded definition and uses
  its original published shift instance, avoiding a duplicate wrapper.

Validation: scompile compiled sandbox and library module separately with no
errors or warnings, 24.6 s and 24.7 s. All variables and universes are explicitly
bound and `autoImplicit` is false. No statement correction or disputed
mathematical assertion is made.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
