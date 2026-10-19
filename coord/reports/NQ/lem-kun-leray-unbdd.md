## Worker report

This delivery completes the existing-declaration record for `lem-kun-leray-unbdd`.
It introduces no module or declaration. The existing declaration is
`AlgebraicGeometry.Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`
in `WeilConjectures.SixFunctors.Etale.Derived.GlobalSections`, lines 57–65.
I read its signature, docstring and construction in the read-only source, and checked
that the current published source returned by `scompile.py --source` agrees.
The pre-existing attachment had only branch, declarations and an incomplete note;
this delivery supplies the complete stage-2 record, without changing any other node field.

The declaration, in its source namespace and notation, has this signature:

```lean
noncomputable def rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((f)_*[A]).rightDerivedFunctor ⋙ rightDerivedGlobalSections A Y ≅
      rightDerivedGlobalSections A X
```

Its section parameters are `(A : Type u') [Category.{u + 1} A] [Abelian A]`
and `[IsGrothendieckAbelian.{u + 1} A]`; the file also supplies
`[HasSmallSiteSheafify A]`, which does not occur in the elaborated declaration.
For the node use `A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))`.
The coefficient lift uses the canonical `ULift.ringEquiv : ULift (ZMod n) ≃+* ZMod n`,
not a new coefficient ring or extra mathematical hypothesis. This is the coefficient
universe convention of `def-weil-pbc-derived-categories`.

Hypothesis and conclusion correspondence:

- Schemes `X,Y` and their morphism `f : X → Y` are exactly `{X Y : Scheme.{u}}`
  and `(f : X ⟶ Y)`, for arbitrary universe `u`.
- Quasi-compact and quasi-separated mean `AlgebraicGeometry.QuasiCompact f` and
  `AlgebraicGeometry.QuasiSeparated f`, as collected by the convention dependency.
  The existing isomorphism is available for every morphism, so it applies in particular
  to every morphism with both these properties. The node's hypotheses are unchanged.
- `cd(f) < ∞` is the finiteness hypothesis of `def-kun-cd`, i.e. a common natural
  vanishing bound for higher direct images of torsion abelian sheaves. The existing
  isomorphism does not require this bound, so its restriction to this domain directly
  supplies the node's conclusion. No hypothesis is replaced by another condition.
- `n ≥ 1` is `n : ℕ` with `1 ≤ n`. The construction works at each such `n` with
  coefficients `ULift (ZMod n)`. No invertibility, characteristic or primality condition
  is introduced. Its additional availability at `n = 0` does not change the node.
- Every `E ∈ D(X_et, Z/n)` is an arbitrary object of
  `DerivedCategory (Sheaf X.smallEtaleTopology A)`. There is no boundedness,
  constructibility, finite Tor amplitude, or further condition on `E`.
- `Rf_*E` is `((lowerStar A f).rightDerivedFunctor).obj E`, the total right derived
  functor of the recorded direct image, not a bounded-below replacement.
- The canonical isomorphism with the node's orientation is precisely
  `((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).app E).symm`.
  Its source is `(rightDerivedGlobalSections A X).obj E`; its target is
  `(rightDerivedGlobalSections A Y).obj (((lowerStar A f).rightDerivedFunctor).obj E)`.
  This is an isomorphism in `DerivedCategory A`, with naturality in `E` supplied by the
  natural isomorphism itself, not merely an existential choice of an isomorphism.

The construction in the source is
`Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompGlobalSectionsIso A f)`.
The underived comparison identifies sections on `Y` of `f_*F` with sections on `X`
of `F`. Direct image preserves K-injective complexes because it is right adjoint to
exact inverse image (`preservesKInjectiveComplexes_lowerStar`). Thus computing on a
K-injective representative gives the asserted unbounded comparison canonically.
This also explains why the stronger upstream result is usable without duplicating it.

Dependency declarations read and used:

- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories` records
  `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. Its full definition is
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  I also read the recorded `DerivedCategory.torsionCohomology` definition; that predicate
  is not needed because `E` here is an arbitrary complex of fixed finite-ring modules.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` is the continuous sheaf
  pushforward induced by base change, with the objectwise formula specified by the node.
  Its total unbounded right derived functor is used in the existing Leray signature.
  The additionally recorded `rightDerivedLowerStarPlus` is defined in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; it is the
  bounded-below restriction and is not substituted for the unbounded functor.
- `def-weil-pbc-scheme-conventions` explicitly fixes no independent notion or declaration.
  Its relevant Mathlib properties are `QuasiCompact` and `QuasiSeparated` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- Global sections are the existing `AlgebraicGeometry.Etale.rightDerivedGlobalSections`
  in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, the total right derived
  functor of `Sheaf.Γ` at the terminal object of the small etale site.

Edge cases checked: `n = 1` gives the zero coefficient ring and zero module category;
the same natural comparison applies. No characteristic condition is required. Empty
schemes, identity morphisms, zero complexes, arbitrary shifts and genuinely unbounded
complexes are included because the comparison is defined on the entire unbounded
category for every morphism. The scheme universe is arbitrary, with module objects and
coefficient lifts in universe `u + 1`; the site universe is not forced to shrink.

Searches made with `msearch.py` (receipts in `searches.jsonl`):

- LeanSearch: `Derived global sections of the derived direct image of an unbounded etale
  sheaf complex are canonically isomorphic to derived global sections on the source`.
  The service returned Internal Server Error; recorded as unavailable, with no verdict.
- LeanFinder: `Leray isomorphism derived global sections of derived pushforward unbounded
  complexes`. Eight Mathlib hits concerned underived pushforward or exact localization
  comparisons, including `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`
  and `Functor.mapDerivedCategoryFactorsh_hom_app`; none was this etale Leray declaration.
- Loogle: `CategoryTheory.Functor.rightDerivedFunctor`, `Sheaf.Γ`, and
  `Functor.rightDerivedFunctorCompIso'`. The service returned unknown-identifier or
  unknown-constant responses, no match; these are project interfaces.
- Mathlib grep: `rightDerivedFunctorCompIso|[Ll]eray` under `Algebra`, and
  `rightDerivedFunctorCompIso|rightDerived.*GlobalSections|[Ll]eray` under
  `CategoryTheory`: no hits for the sought comparison.
- Direct `rg` in `WeilConjectures` for
  `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso` located the definition in
  `SixFunctors/Etale/Derived/GlobalSections.lean` and its uses. Searching the node id
  in that source tree found no id annotation. `dag/lean_names_upstream.json` was also
  checked; the node's existing audit already identifies this exact source declaration.
- Direct `rg` in `lean/Sheaf` found many callers of the same upstream comparison,
  including `Paper/EtaleKInjectiveUnitLeray.lean` and `Paper/DerivedLerayComp.lean`;
  no additional definition is needed. The shared `lean/WeilConjectures` source agrees.

Node fault (proof only; statement not disputed): the imported proof says
`R^q f_* E = 0` for `q > cd(f)` for arbitrary unbounded `E`, and consequently claims
finitely many columns. This is false for shifted complexes: take the identity morphism
(cohomological dimension zero) and a nonzero sheaf placed in degree one. Finite
cohomological dimension bounds higher images of sheaves, not arbitrary complexes.
The statement is true, and the existing K-injective construction above proves it;
the proof field is left unchanged because this delivery only completes the lean record.
No statement correction or new/dependency node is required.

Validation: `scratchpad/ExistingSpecialization.lean` is a non-delivered `#check` probe.
It checks the coefficient-specialized component and its exact source and target, under
`set_option autoImplicit false`, through `scompile.py`. The initial small unlifted-ring
probe lacked the universe-matched Grothendieck instance; the standard coefficient lift
above repairs it without restricting scheme universes. `#print axioms` on the existing
construction reports only `propext`, `Classical.choice`, and `Quot.sound`.
The delivery wrapper also compiles its independent existing-declaration probe.

## Second reading by NQ

I independently read the node copy, the recorded upstream declaration and its
construction, and all three statement-dependency records and their relevant source
declarations. The blueprint Markdown is absent from this machine's literature
directory, so I read the node's exact source place and its enclosing `_section.md`
read-only on the project server. The source statement agrees verbatim with the node.
It has no separate Stacks tag. The enclosing Künneth proposition assumes a separably
closed field and an invertible coefficient order, but this auxiliary lemma explicitly
quantifies over schemes and morphisms as stated; the existing construction verifies
that no field, characteristic or invertibility assumption is needed here.

My object/hypothesis/conclusion checklist, in source order:

1. Schemes `X`, `Y` and their morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
   Verdict: the same objects, with arbitrary scheme universe `u`.
2. The morphism is quasi-compact and quasi-separated: `QuasiCompact f` and
   `QuasiSeparated f`, the properties fixed by `def-weil-pbc-scheme-conventions`.
   Verdict: the existing declaration can be applied to every morphism in this
   restricted domain; it introduces no substitute or extra geometric assumption.
3. Finite torsion étale cohomological dimension: the meaning is
   `f.torsionEtaleCohomologicalDimension < ⊤`, from `def-kun-cd`, whose actual
   definition takes `[QuasiCompact f] [QuasiSeparated f]` and bounds higher images
   of torsion **sheaves** placed in degree zero. Verdict: this hypothesis can be
   retained when applying the declaration, which needs no such bound. Its absence
   from the more general existing API does not restrict the node's domain.
4. Coefficient order `n ≥ 1`: `n : ℕ` and `1 ≤ n`, with the fixed coefficient
   category `A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))`.
   Verdict: exactly the finite coefficient ring, using its canonical universe lift
   `ULift.ringEquiv`; no primality, nonzero characteristic, or field hypothesis.
   The declaration also works for `n = 0`; the node only asserts its restriction
   to positive orders.
5. Every unbounded complex `E ∈ D(X_et, Z/n)`: an arbitrary
   `E : DerivedCategory (Sheaf X.smallEtaleTopology A)`.
   Verdict: this is definitionally the `DerivedCategoryModule` of the dependency
   with the lifted ring, not `DerivedCategory.Plus` and not a category of bare
   abelian sheaves that forgets the coefficient action. No boundedness,
   constructibility or Tor-amplitude predicate is supplied.
6. `Rf_*E`: `((lowerStar A f).rightDerivedFunctor).obj E`.
   Verdict: `lowerStar` is the recorded base-change direct image, with its actual
   objectwise formula `F(W ×_Y X)`. I separately read `rightDerivedLowerStar` and
   `rightDerivedLowerStarPlus` in `UpperLowerStarCoherence`: the former is exactly
   this total functor; the latter is the bounded-below functor and is not used.
7. The conclusion in the stated orientation:
   `((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).app E).symm`.
   Its source is `(rightDerivedGlobalSections A X).obj E` and its target is
   `(rightDerivedGlobalSections A Y).obj
   (((lowerStar A f).rightDerivedFunctor).obj E)`, in `DerivedCategory A`.
   Verdict: precisely both clauses of the displayed comparison, with the
   coefficient-module structure retained.
8. Canonicity for every `E`: the recorded object is a natural isomorphism of
   functors, whose components supply clause 7. I read its construction as
   `Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompGlobalSectionsIso A f)`
   and the underlying comparison of sections at the terminal object.
   Verdict: canonical and natural, rather than a chosen abstract isomorphism.
   Quantifiers specialize in the required order: choose `n`, `X`, `Y`, `f`,
   then take the component at any `E`.

The dependency interfaces are usable without repairs. I opened
`Sheaf.AlgebraicGeometry.DerivedCategories` and upstream `Derived.Coefficients`
to check the actual `DerivedCategoryModule` abbreviation and coefficient universe.
I opened `UpperLowerStar.Defs` for the direct-image functor, and
`Derived.LowerShriek` for `rightDerivedGlobalSections`, which is the total right
derived functor of `Sheaf.Γ`. The scheme-conventions node expressly introduces no
new notion. For the numerical hypothesis I also read the landed definition in
`Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`; for unbounded
sections I checked the existing record of `def-kun-rgamma-unbounded` against the
same source definition. There are no new nodes, dependency modules, private copies,
hollow definitions or postponed theorems in this delivery.

Edge cases: empty source or target schemes, identity morphisms, the zero complex,
arbitrary shifts and complexes unbounded in both directions are included by the
unrestricted morphism and derived-object binders. `n = 1` is allowed, including
its zero coefficient ring; `n = 0` is outside the assertion and requires no special
case. There is no index set to assume inhabited. There is no characteristic
restriction. The arbitrary `u` uses modules in universe `u + 1`, with the ring
lifted into that same universe, so the coefficient Grothendieck instance is
available without equating site object and morphism universes or imposing an
additional mathematical condition. The full elaborated declaration has only
`Category`, `Abelian`, and `IsGrothendieckAbelian` coefficient instances; the
source section's `HasSmallSiteSheafify` is not an additional parameter.

My independent searches used different phrases from the first reader:

- LeanFinder: `total derived functors commute with composition when pushforward
  preserves K injective complexes`. Eight hits included
  `Functor.mapDerivedCategoryFactorsh` and derived natural-transformation
  composition laws, not another étale unbounded Leray construction.
- Loogle: `CategoryTheory.Functor.sheafPushforwardContinuous`. Twelve hits give
  the underlying sheaf pushforward and its underived composition laws, not this
  derived global-sections comparison.
- LeanSearch: `The derived functor of global sections after derived sheaf
  pushforward is canonically isomorphic to derived global sections`. The service
  returned Internal Server Error; recorded unavailable, without a search verdict.
- Mathlib grep: `global.*sections.*push|push.*global.*sections|PreservesKInjective`
  under `CategoryTheory` returned no hits. Direct `rg` of the upstream derived
  functor and étale directories locates the existing generic composition theorem
  and the recorded `Derived.GlobalSections` definition. Direct `rg` of project
  `lean/Sheaf` locates callers in `EtaleKInjectiveUnitLeray` and
  `DerivedLerayComp`; I opened these to confirm they use this same canonical map.
  The source declaration is present in both read-only upstream source copies.
  Thus H4 requires reusing it; adding a renamed specialization would duplicate it.

Mismatches and changes: I found no mismatch between the node's assertion and the
specified specialization of the existing declaration, and retained the worker's
Lean record and all mathematical node fields. I confirm the worker's separate
proof-field fault: for `f = id`, a nonzero sheaf placed in degree one has nonzero
`H^1(Rf_*E)` even though `cd(f) = 0`. Thus the claimed finite columns for arbitrary
`E` do not follow. This is a faulty imported proof, not a false statement; the
actual existing construction instead uses preservation of K-injectives by the
right adjoint to exact inverse image. I read that instance and the generic
composition construction. The fault remains reported here for the maintainer;
this existing-record delivery does not silently alter the proof or unit route.
No statement correction or citer audit is needed. This second-reading section is
the only change I made.

Validation: I reran `scompile.py NQ lem-kun-leray-unbdd` on the scratch probe
`ExistingSpecialization.lean`. It completed successfully, with no warnings, and
checked the component against the exact source/target type in clause 7 with
`autoImplicit false`. The universe `u`, `n`, schemes, morphism and `E` are all
explicitly bound. `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`. There is no delivered module requiring another file compile.
