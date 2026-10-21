## Worker report

The target is already stated by
`AlgebraicGeometry.ProEtale.isMonHom_condensedPushforwardHom` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, line 608.
This delivery records `existing: true`; no module or duplicate theorem is written.
The live source was read with `scompile.py --source`, as well as the shared read clone.
The original blueprint lemma and its coefficient-morphisms unit were opened in
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`.
No repair note for this item is present.

The recorded signature, verbatim before `:=`, is:

```lean
instance isMonHom_condensedPushforwardHom : IsMonHom (condensedPushforwardHom Λ f)
```

Hypothesis and clause correspondence:

- An arbitrary condensed ring Λ is the section variable
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]`.
  `Profinite.CondensedRing` is exactly the bundled `Mon` of this sheaf category;
  its underlying object with its MonObj instance gives this unbundled presentation.
  No topological-ring presentation or commutativity is required.
- Arbitrary schemes and a morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  There is no finiteness, properness, weakly-etale or other property binder.
- Λ_X and Λ_Y are `condensedRingObj Λ X` and `condensedRingObj Λ Y`.
  Their definition is `(upperStarFromPoint X).obj Λ`, and the Obj-scoped
  `Functor.monObjObj` instance transports the ring structure. The bundled
  counterpart is `coefficientRing X (Mon.mk Λ)`, defined using `mapMon.obj`.
- The specified strong monoidal pullback is `ProEtale.monoidal_upperStar`,
  built by `.ofOplaxMonoidal` from the mate oplax structure of the same adjunction.
  The specified lax pushforward is `ProEtale.laxMonoidal_lowerStar`.
  These are the instances imported by Basic, not arbitrary alternative structures.
- The ring structure on `f_* Λ_X` is `Functor.monObjObj` for that pushforward:
  its unit is `Functor.LaxMonoidal.ε F ≫ F.map MonObj.one`, and multiplication
  is `Functor.LaxMonoidal.μ F R R ≫ F.map MonObj.mul`.
  These are precisely the two structure maps stipulated by the transport node.
- The arrow η_f is literally `condensedPushforwardHom Λ f`, whose body is
  `(upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom (condensedRingObj Λ Y)`
  followed by `(f)_*[Ab.{u + 1}].map (condensedPullbackHom Λ f)`.
  `unitAlgHom` is the adjunction unit component, so this is the canonical mate.
- The conclusion `IsMonHom (condensedPushforwardHom Λ f)` has both defining
  fields `one_hom` and `mul_hom` in Mathlib: unit preservation and multiplication
  preservation, respectively. Ambient morphisms of abelian sheaves already
  preserve addition. This is exactly a morphism of ring objects in the node's
  tensor-monoid convention, rather than a cartesian ring-object convention.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj`, `isCommMonObj_condensedRingObj`, `condensedPushforwardHom`;
  the same namespace supplies the exact existing conclusion above.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`:
  `AlgebraicGeometry.ProEtale.monoidal_upperStar`, `laxMonoidal_lowerStar`,
  and `laxBraided_lowerStar`.
- `Mathlib.CategoryTheory.Monoidal.Mon`: `CategoryTheory.MonObj`, `Mon`,
  `IsMonHom`, `Mon.Hom`, `Mon.id`, `Mon.comp`, `Mon.instCategory`, `Mon.forget`,
  `Mon.forget_faithful`, `IsCommMonObj`, `Functor.monObjObj`, `Functor.mapMon`,
  `Functor.map.instIsMonHom`, `Functor.mapMonNatTrans`, and `Functor.mapMonNatIso`.
- `Mathlib.CategoryTheory.Monoidal.CommMon_`:
  `CategoryTheory.Functor.isCommMonObj_obj` and `Functor.mapCommMon`.
  The generic transport and monoid nodes are Mathlib leaves and need no lean repair.

The existing proof also follows the DAG route: the monoidal adjunction gives a
ring morphism for the unit, alpha is a ring morphism, lax monoidal pushforward
preserves it, and composition preserves the two ring-morphism equations.
No proof or definition is added or changed in this statement-stage delivery.

Edge cases checked against the full signature and construction: empty schemes
are allowed, identity and arbitrary morphisms are allowed, the zero condensed
ring is allowed, and noncommutative condensed rings are allowed. No invertibility
of η_f is asserted. The universe is the framework convention: Profinite.{u},
Scheme.{u}, and Ab.{u + 1}; it retains the actual small pro-etale sites and does
not impose equality of site object and morphism universes.

Searches for an existing statement:

- msearch.py LeanSearch: “The adjunction unit and the pushforward of a morphism
  of monoid objects are monoid morphisms”; 8 hits, including
  `CategoryTheory.Adjunction.IsMonoidal.instIsMonoidalUnit`, generic infrastructure.
- msearch.py LeanFinder: “The mate of the canonical pullback morphism of condensed
  coefficient rings is a morphism of monoid objects”; 8 hits about light condensed
  internal Hom and monoidal categories, no scheme-specific result.
- msearch.py Loogle: `CategoryTheory.IsMonHom, CategoryTheory.Functor.mapMon`;
  0 hits.
- msearch.py grep: `isMonHom|unitAlgHom` in `CategoryTheory/Monoidal`;
  25 returned hits including Mathlib's IsMonHom and preservation infrastructure.
  The full signatures and transport formulas were read in Mon.lean and CommMon_.lean.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  `isMonHom_condensedPushforwardHom` finds the exact upstream Basic.lean instance
  at line 608. The upstream-name index and Sheaf source give no duplicate.
- grep of `lem-sfb-eta-ring-hom` in `lean/WeilConjectures`: no literal blueprint-tag
  hit. Searching the declaration name, then opening its surrounding section and
  docstring, identifies the exact match despite the absent tag.
- `scompile.py --source WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
  confirms the live source has the same section binders, canonical definition,
  target structure and exact instance.

Only the item's `lean` field changes. No statement correction, new node,
dependency module, or STATEMENT-DISPUTED issue is needed. The delivery wrapper
compiles its generated existing-declaration probe and runs server preflight.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
