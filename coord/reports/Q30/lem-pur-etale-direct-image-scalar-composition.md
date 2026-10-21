## Worker report

The module `Sheaf.Paper.EtaleDirectImageScalarComposition` states the two clauses of
`lem-pur-etale-direct-image-scalar-composition`: the composition equality as
`AlgebraicGeometry.Etale.scalarMate_directImage_composition` and its identity clause as
`AlgebraicGeometry.Etale.scalarMate_directImage_identity`. Both proofs are `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The source was read in `literature/stacks-project/sites-cohomology.tex`,
`remark-compose-base-change` (Tag 0E46): the coefficient-change identity-topos squares
are its two pasted squares. The node's seven proof steps are supplied in the two
proof docstrings, steps 1–6 for composition and step 7 for identity.

Hypotheses and objects, clause by clause:

- A and B are `{A B : Type (u + 1)} [CommRing A] [CommRing B]`; their stipulated
  finiteness is `[Finite A] [Finite B]`. `φ : A →+* B` is a unital ring homomorphism.
  This includes zero rings and does not require either ring to be a field.
- The arbitrary schemes are `{X Y Z : Scheme.{u}}`, and their arbitrary morphisms
  are `(r : X ⟶ Y) (s : Y ⟶ Z)`. The composite sr in the mathematical notation is
  `r ≫ s`. Neither theorem has a geometric hypothesis.
- `D_A(X)` is exactly `DerivedCategoryModule A X`, the ordinary unbounded derived
  category of `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`. The binder
  `(M : DerivedCategoryModule A X)` covers every derived object, without bounds.
  The coefficient universe is the published u+1 convention for the small etale site;
  its distinct object/morphism universes are not identified by an extra assumption.
- `Q_T` is the existing `scalarExtension φ T`, an abbreviation for the canonical
  derived scalar extension `ProEtale.pbcFixedScalarExtension`.
- `Ru_{*,R}` is `R(lowerStar (ModuleCat.{u + 1} R) u)`. The geometric pullback is
  `L(upperStar (ModuleCat.{u + 1} R) u)`, canonically identified with the exact
  termwise inverse image by `leftDerivedUpperStarIsoMapDerivedCategory`.
- The specified lambda is the existing `scalarPullbackIso φ u`. Its unique
  K-flat normalization was read in `scalarPullbackIso_existsUnique`.
- The specified chi is the existing `(scalarMate φ u).app E`, defined using
  `mateEquiv` and `derivedUpperStarLowerStarAdjunction`. Its transpose is
  `(scalarPullbackIso φ u).hom.app (Ru_* E)` followed by scalar extension of the
  A-geometric counit, exactly the definition in the node. It is not an arbitrary map
  or a map defined by an invertibility assertion. The already landed owning node
  `def-pur-etale-scalar-mate` is cited in `stmt_deps` as the owning definition node
  for this exact declaration; its dependency lists do not reach the current item.
- The specified kappa is the inverse of
  `Functor.rightDerivedFunctorCompIso' (lowerStar ... r) (lowerStar ... s)
  (lowerStarComp ... r s)`. This is the canonical right-derived comparison built
  from the composite resolution unit and the ordinary direct-image compositor.
  It is normalized on K-injective representatives, rather than selected as an
  arbitrary natural isomorphism. Exact inverse image implies that lowerStar
  preserves K-injectives; the existing instance supplies this automatically.
  Thus this constant-coefficient specialization has the normalization of
  `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: on a K-injective I,
  using a resolution j of r_*I, it is represented by s_*j under the resolution maps.
- The left side of the first theorem is chi for sr followed by kappa_B at Q_X M.
  The right side is `Q_Z.map kappa_A` followed by chi_s at Rr_* M followed by
  `Rs_*.map chi_r`. Lean's `≫` is first the left arrow then the right arrow,
  so this is exactly the node's displayed equation in functional-composition order.
- The identity clause is stated for every `(T : Scheme.{u})` and
  `(M : DerivedCategoryModule A T)`. Its equation is
  `chi_id ≫ e_B(Q_T M) = Q_T.map (e_A(M))`, where e_R is the canonical identity
  direct-image comparison. Explicitly e_R is right derivation of `lowerStarId`,
  followed by `rightDerivedFunctorIsoMapDerivedCategory` for the identity exact
  functor and `mapDerivedCategoryIdIso`. Since these are isomorphisms, the equation
  says precisely that chi becomes identity after identifying both direct images
  with the identity. No identity case is discarded.
- There is no properness, Noetherian, boundedness, coefficient-flatness, or
  invertibility-of-chi hypothesis or conclusion in either theorem.

Recorded dependencies and declarations read and used (the generic dependencies
also supply the proof plan through imports):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-derived-categories`:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`, publicly reexporting
  `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `lem-pur-derived-change-of-rings`:
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.
  The existing constant-coefficient specialization `scalarExtension` is read from
  `Sheaf.Paper.EtaleDerivedScalarTensor`, publicly imported by the mate module.
- `prop-weil-pbc-inverse-image-modules-exact`:
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
  `AlgebraicGeometry.etaleInverseImageModulesExact`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`:
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `def-kun-projection-formula-map`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`,
  `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`, together with the
  canonical `derivedUpperStarLowerStarAdjunction` of its public UpperLowerStar import.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`:
  `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
  `CategoryTheory.ringedToposDerivedPushforwardComposition`. The concrete canonical
  compositor is the existing `Functor.rightDerivedFunctorCompIso'` from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `def-pur-etale-scalar-pullback-iso` and the added landed
  `def-pur-etale-scalar-mate`: `Sheaf.Paper.PurEtaleScalarMateProjection`,
  `AlgebraicGeometry.Etale.scalarPullbackIso_existsUnique`, `scalarPullbackIso`,
  and `scalarMate` (all in the namespace `AlgebraicGeometry.Etale`).
- `lem-sfb-ringed-derived-monoidal-comparisons`:
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`,
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`.
- `lem-sf-scalar-pullback-composition`: `Sheaf.Paper.ScalarPullbackComposition`,
  `AlgebraicGeometry.Etale.scalarPullback_composition`.
- `lem-weil-pbc-adjunct-counit-identity`: Mathlib match
  `CategoryTheory.Adjunction.eq_unit_comp_map_iff`, in
  `Mathlib.CategoryTheory.Adjunction.Basic`; no Lean record is needed on that node.
- `lem-pc-kflat-resolution`:
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.

Edge cases checked by inspecting the actual binders and arrow types: empty schemes;
zero complexes; zero coefficient rings; nonflat finite ring maps such as
Z/4 to Z/2; either or both scheme morphisms identities; arbitrary unbounded complexes.
The two theorem signatures admit all these cases. A map from the zero ring to a
nonzero ring is not a unital homomorphism and correctly supplies no φ. Finiteness is
retained exactly as in the item, although the underlying constructions are general.

Searches made through msearch.py and read-only rg:

- LeanFinder: "Counit mate of derived scalar extension commutes with composition of
  derived direct images of etale sheaves" returned 8 hits, including ordinary
  `SheafOfModules.pushforwardPushforwardAdj_counit_app_val_app`, not this statement.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Functor.rightDerivedFunctorCompIso`
  returned 0 hits and reported the second identifier unknown in Mathlib. A further
  `CategoryTheory.Adjunction.homEquiv` query returned 12 generic adjunction hits,
  including `homEquiv`, `homEquiv_unit` and `homEquiv_counit`; none is this theorem.
- LeanSearch: "The mate of a natural transformation commutes with composition of
  adjunctions" returned 8 generic hits, including `mateEquiv_hcomp`, `mateEquiv_vcomp`
  and `conjugateEquiv_mateEquiv_vcomp`. These can assist the later proof, but do not
  supply the normalized etale scalar-extension statement or its identity clause.
- msearch grep of Mathlib/CategoryTheory for
  `scalarMate|scalarPullback|rightDerivedFunctorCompIso` returned 0 hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for `scalarMate` and the item id found
  the existing mate definition and consumers but no statement of its direct-image
  composition or identity. Further searches for
  `scalarMate.*[Cc]omp|scalarMate.*[Ii]d|scalarMate.*composition|rightDerivedLowerStarComp.*scalar`
  found no existing exact statement. `rightDerivedLowerStarComp` is a canonical
  conjugate compositor; the present signature directly uses the K-injective universal
  construction instead. No second definition of the mate or compositor was written.

Validation: scompile.py compiled both the sandbox module and its actual library module
name cleanly (21.5 s and 19.1 s), with no errors or warnings. Every universe and variable
is explicitly bound and `autoImplicit` is false. The module has no line over 100 characters.
The only two postponed proofs are the named theorems listed above. No statement dispute
or node fault was found.


## Repair of return H2 (2026-10-21)

Replaced `lem-pur-etale-scalar-mate-projection` in `stmt_deps` with the live
`def-pur-etale-scalar-mate` definition node (NS, 2026-10-21, `existing: true`).
Read its full statement and Lean record and the source definition at
`Sheaf.Paper.PurEtaleScalarMateProjection`, lines 162–172: `scalarMate` is the plain
`mateEquiv` construction applied to `scalarPullbackIso.hom` under the two canonical
derived adjunctions. It does not choose data from the scalar-mate/projection theorem.
The worker report's ownership references above now name the definition node.
The Lean module is retained byte for byte; its import already supplies that definition.
No mathematical statement, proof plan, or other dependency is changed.

Self-check against the returned review: the finite ring binders, arbitrary schemes
and morphisms, unbounded M, normalized inverse compositor, composition equation,
and identity comparison clause are unchanged. The node's `lean.statement` still
matches the composition signature verbatim. The shared main node and retained
packet differ only in `lean` and the permitted added definition dependency.
The initial saved-packet dry run passed (commit 4066b8cfcdc); the explicit H2
repair above is nevertheless applied before the final compile and delivery.

## Second reading by Q30

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
