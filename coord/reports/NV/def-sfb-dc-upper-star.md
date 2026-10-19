## Worker report

Attach the existing declarations
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar` and
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarCompatibility`
in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
There is no new Lean module, definition, proof, dependency module, or definition node.
The item's only changed field is `lean`.

Read the item and all four statement-dependency nodes, their recorded declarations,
the compact-object example and its node, the stage-2 contract, and
`coord/pefw-upstream-framework.md`. Read the current blueprint item's definition and
its parent `sk-def-sfb-dc-restricted-functors/_section.md`. Read the side framework
module and then the authoritative published source using
`scompile.py --source WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
The published version has the bundled `Over` interface (the local copied framework
still has the earlier unbundled scheme-over-base parameters). The record follows
the current published declaration verbatim. No repair note exists for this item.

Hypotheses and clauses, individually:

- A commutative condensed ring is
  `(Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]`.
  The object is an internal commutative ring in condensed abelian groups, not a
  discrete ordinary coefficient ring or a finite-coefficient realization.
- The setting's prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. Its field and characteristic are
  `{k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`.
  Prime ring characteristic gives positive characteristic, with the stated inequality.
- The schemes and their structure maps are `{X Y : Over (Spec (.of k))}`.
  For each of `X.hom` and `Y.hom` the assumptions are `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated`. Locally finite type together with
  quasi-compactness is exactly finite type. There is no properness, smoothness,
  finiteness, or invertibility assumption on `f` or the coefficient ring.
- The morphism is `(f : X ⟶ Y)` in that over-category. Thus it is a morphism of
  k-schemes; its underlying scheme morphism is `f.left`.
- The displayed domain and codomain are exactly
  `Dᵇc(Y.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧`. The module's scoped notation expands to
  `AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj Λ T)`.
  The general recorded `BoundedConstructible` is the full subcategory on
  `boundedConstructible R`; that predicate is boundedness of the ordinary derived
  object together with constructibility of all its cohomology modules. There is
  no derived completeness restriction. This is the same general ring-object
  constructibility used by `sk-def-sfb-bounded-constructible`.
- The ambient functor in the definition's body is `L((f.left)^*⟦Λ⟧)`.
  As explained and defined in the dependency's `Derived.UpperLowerStar` module,
  this is `Functor.leftDerivedFunctor` applied to the entire underived module
  pullback composite. It is not a derived functor of only its abelian-sheaf factor.
- Restriction to the full subcategories is literally
  `(boundedConstructible _).lift ((boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧))`.
  Its membership proof on an object `K` is
  `boundedConstructible_leftDerivedUpperStar_obj Λ ℓ f K.obj K.property`,
  exactly the recorded preservation dependency, with no extra coefficient hypothesis.
  Mathlib's `ObjectProperty.lift` sends an object to the image with that proof and
  a morphism to the same ambient functor's map. Hence objects, morphisms,
  identities and composition are precisely those of the required restriction.
- The final inclusion clause is the companion existing definition
  `boundedConstructibleUpperStarCompatibility`, with type
  `boundedConstructibleUpperStar Λ ℓ f ⋙ (boundedConstructible _).ι ≅
  (boundedConstructible _).ι ⋙ L((f.left)^*⟦Λ⟧)`.
  Its body is `ObjectProperty.liftCompιIso _ _ _`, whose body is `Iso.refl _`:
  the composites agree definitionally on objects and morphisms. This is precisely
  commuting with the inclusions; it introduces no arbitrary comparison map.

Dependency declarations used (all source signatures and docstrings read):

1. `sk-def-sfb-dc-setting`: the same `Derived.BoundedConstructible` module's
   field-setting binders and `CondensedRing.compactificationOverField`; its
   source uses `Over (Spec (.of k))`. Compactification data are not inputs of
   upper star, so the chosen compactification is neither replaced nor required
   as an additional parameter here.
2. `sk-def-sfb-module-derived-pushpull`:
   `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`,
   `CondensedRing.derivedUpperStarLowerStarAdjunction`, with ambient
   `Functor.leftDerivedFunctor`, and the accompanying `leftDerivedUpperStarIso`
   and `leftDerivedUpperStarIsoMapDerivedCategory`. The published source was read
   with `scompile.py --source`; the new dependency record's exact aggregate is used.
3. `lem-sfb-dc-upper-star-preserves`: the same `Derived.BoundedConstructible`
   module's `CondensedRing.boundedConstructible_leftDerivedUpperStar_obj`.
   The published source now proves it using exact pullback on cohomology and
   `isConstructibleModuleObject_upperStar`; this delivery does not change it.
4. `sk-def-sfb-bounded-constructible`:
   `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible` records a mixed binding;
   its actual object predicate, full subcategory, and cohomological characterization
   are the unchanged `AlgebraicGeometry.ProEtale.boundedConstructible`,
   `BoundedConstructible`, and `mem_boundedConstructible_iff` of
   `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
   Read both the recorded Sheaf module and the current published defining module.
   Its conditional triangulatedness theorem is not needed for this restriction.

Edge cases checked against the construction: the zero coefficient ring is admitted
(no `Nontrivial` coefficient hypothesis); any bounded cohomological interval and
the zero complex are admitted; the empty scheme and empty strata are not excluded;
identity maps and arbitrary morphisms of the setting use the same formula.
The restriction does not assume nonempty schemes, a fixed degree range, derived
completeness, constructible closure under kernels, or special ell-adic coefficients.
The full-subcategory inclusion preserves exactly the ambient Hom sets even for
these degenerate cases. The site universe remains `Scheme.{u}` with sheaves in
`Ab.{u + 1}`, as in the dependency interfaces; no universe equality is added.

Searches (2026-10-18):

- `msearch.py ... leansearch` query:
  `Derived inverse image functor restricted to bounded constructible complexes of condensed module sheaves on the pro-etale site`.
  Eight hits including `SheafOfModules.pullback`, its adjunction, site pullback,
  condensed locally constant sheaves and scheme-module restriction. None is the
  specialized bounded constructible internal-module restriction.
- `msearch.py ... leanfinder` query:
  `Derived pullback restricted to bounded constructible complexes of modules over a commutative condensed ring on the pro-etale site`.
  Eight hits including `Condensed.profiniteSolid`, explicit condensed module
  constructions, `SheafOfModules.pullback` and `pullbackComp`. No entire-item match.
- `msearch.py ... loogle` query:
  `CategoryTheory.ObjectProperty.lift, CategoryTheory.ObjectProperty.liftCompιIso`.
  Found `liftCompιIso` and its shift compatibility. Read Mathlib's
  `CategoryTheory/ObjectProperty/FullSubcategory.lean`, lines 153--171:
  `lift` supplies the elementary full-subcategory construction, and
  `liftCompιIso` is `Iso.refl`. These do not supply the specialized ambient functor.
- `msearch.py ... grep` query `boundedConstructibleUpperStar|liftCompιIso`,
  subdirectory `CategoryTheory`: nine generic inclusion-comparison hits.
- `rg -n 'boundedConstructibleUpperStar|def-sfb-dc-upper-star'` on
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's
  `lean/Sheaf`: no matching definition in the older source checkout, and uses
  (not new definitions) in `CondensedQbarBaseChangeCompatibility.lean` and
  `CondensedERealization.lean`. A node-id search has no source hit.
- The corresponding `dag/lean_names_upstream.json` search found no entry.
  Reading the mandated newer framework at
  `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean`
  found both exact declarations; `scompile.py --source` confirmed their live
  current signatures and real `ObjectProperty.lift`/`Iso.refl` bodies.

No `STATEMENT-DISPUTED`, source error, or statement correction applies.

Validation: the sandbox-only `scratchpad/UpperStarProbe.lean` imports the published
module with `autoImplicit false` and checks the full signatures of both attachment
names, preservation, setting, ambient adjunction, object predicate, full subcategory,
and cohomological membership. It is a probe, not a delivered module.
The probe passed with exit code 0 and no errors or warnings, against both the
server sandbox overlay and published library. The full elaborated signatures
confirmed all binders listed above and the absence of a finiteness-coefficient
condition. `deliver2.py NV def-sfb-dc-upper-star --no-push` also passed server
preflight and compilation (dry-run commit `3b09212610`), staging exactly the
node record and report. The dry run is repeated after this validation note.

## Author self-check

Author's self-check under the dispatcher brief (no other agents were started;
the maintainer supplies independent review). Re-read the item alongside the
published source, including the surrounding binders and the actual definition
bodies. Each coefficient, prime, characteristic, scheme, and morphism assumption
is matched above. Both the restriction and final inclusion sentence are covered:
the latter required recording the companion compatibility declaration as well
as the functor. No mathematical mismatch was found. The stale local framework's
unbundled `Scheme.Over` interface was not copied into the record; the published
bundled `Over` signature is recorded verbatim. No statement, dependency, or proof
field was changed.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
