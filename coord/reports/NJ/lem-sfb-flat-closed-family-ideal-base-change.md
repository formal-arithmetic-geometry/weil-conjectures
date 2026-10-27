## Worker report

The module `Sheaf.AlgebraicGeometry.FlatClosedFamilyIdealBaseChange` states
`AlgebraicGeometry.Scheme.Modules.flatClosedFamily_ideal_baseChange`, with `sorry`
as its only theorem proof. Three fully constructed helper maps belong to this node
and are listed in `lean.declarations`: the induced morphism of fibre products,
the pulled-back ideal inclusion, and the canonical structure-sheaf quotient.
There are no new DAG nodes, dependency repairs, or statement corrections.

The previous worker's reason for stopping confused a stage-1 review with a stage-2
attachment. The live node has Q23's reviewed split but no `lean` record. This packet
adds that record and the actual statement module; it is not the unchanged node
that previously failed preflight.

Sources read: Stacks `morphisms.tex`, lemma-finite-presentation-permanence
(02FV), especially (2), and lemma-closed-immersion-finite-presentation (01TV);
`algebra.tex`, lemma-flat-tor-zero (00HL). The node's eight proof steps are
rendered in the theorem docstring, combining the two finite-presentation steps
and the final localization/kernel argument. No mathematical assertion was changed.

### Hypotheses and conclusions

- The scheme objects are `{T X Z : Scheme.{u}}`. The structure map is
  `(f : X ⟶ T)`, and the closed immersion is `(i : Z ⟶ X)` with
  `[IsClosedImmersion i]`. The structure map of Z is written `i ≫ f`.
  Every closed immersion over T has this form, by its defining commutativity;
  using the composite avoids a redundant structure map and equality binder.
- Finite presentation of X over T is exactly the three assumptions
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
- Finite presentation of Z over T is exactly
  `[LocallyOfFinitePresentation (i ≫ f)] [QuasiCompact (i ≫ f)]
  [QuasiSeparated (i ≫ f)]`.
- Flatness of Z over T is `[Flat (i ≫ f)]`. Neither `Flat f` nor flatness of
  the later morphism g is assumed.
- The ideal is the recorded ideal-sheaf construction `i.ker.toModules`, with
  inclusion `i.ker.toModulesι`. Mathlib's `Scheme.Hom.ker_apply` identifies its
  affine ideal with the kernel of `i.app`. The upstream module bridge identifies
  its sections with those ideals (`range_toModulesι_app`) and realizes the
  ideal as a kernel module of the associated closed subscheme. For a closed
  immersion this is precisely the ideal `ker(O_X → i_* O_Z)` in the node.
  This reuses the established ideal notion rather than defining a second one.
- The first conclusion is
  `LocallyOfFinitePresentation i ∧ QuasiCompact i ∧ QuasiSeparated i`, namely
  finite presentation in the node's explicit convention.
- The ideal assertion is `i.ker.toModules.IsQuasiCoherentFiniteType`.
  The recorded definition expands to
  `SheafOfModules.IsQuasicoherent i.ker.toModules ∧
  SheafOfModules.IsFiniteType i.ker.toModules`; it does not require finite
  presentation or coherence of the module.
- Arbitrary base change is `∀ (T' : Scheme.{u}) (g : T' ⟶ T)`.
  The fibre products are `Limits.pullback f g` and
  `Limits.pullback (i ≫ f) g`; their projection to X is
  `Limits.pullback.fst f g`.
- The induced map i' is `flatClosedFamilyBaseChangeImmersion f i g`, constructed
  with `Limits.pullback.map` from i and two identity maps. Its two square proofs
  use `simp`. `IsClosedImmersion` of this very map is a conclusion.
- The arrow a is `flatClosedFamilyIdealBaseChangeMap f i g`: the image of
  `i.ker.toModulesι` under `tensorPullback` of the projection, followed by
  the existing `tensorPullbackObjUnitToUnit`. That structure-sheaf comparison
  is adjoint to g-sharp under `exists_tensorPullbackAdjunction`, whose unit is
  the actual section `1 ⊗ m`. Thus this is the specified canonical inclusion.
- The arrow b is `flatClosedFamilyBaseChangeQuotient f i g`, literally
  `SheafOfModules.unitToPushforwardObjUnit` for i'. Its target is
  `(pushforward i').obj (SheafOfModules.unit Z'.ringCatSheaf)`.
  By the definition of module pushforward, its sections on U are the structure
  sections on the inverse image of U, with their induced O_X'-module structure.
  Affine pushforward base change and the structure-sheaf comparison identify
  this arrow with the pulled-back quotient arrow, as detailed in proof step 3.
- The existential proof `w : a ≫ b = 0` packages the canonical arrows as a
  short complex. `(ShortComplex.mk a b w).ShortExact` says exactly
  `0 → g_X^* I → O_X' → i'_* O_Z' → 0` is short exact, including both ends.
  This proof binder is a conclusion, not an assumed annihilation relation.
- Finally, `∃ e : g_X^* I ≅ kernel b, e.hom ≫ kernel.ι b = a` states that the
  canonical map to the specified kernel is an isomorphism. The compatibility
  equation uniquely determines e.hom by the kernel universal property; this
  is not an arbitrary isomorphism of the two objects. Its target is the literal
  kernel of the actual restriction map for i', exactly as in the node.

### Dependency declarations

All nine statement-dependency records and their source declarations were read.
The public imports use these recorded interfaces:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; its docstring and `Flat.iff_flat_stalkMap` identify
  the affine and stalkwise flatness notions.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and
  `pullback.map`, together with scheme pullbacks from
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, publicly importing
  the existing `AlgebraicGeometry.Scheme.Modules.tensorPullback` and its
  normalized adjunction interface. The structure-sheaf comparison is reused
  from `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated`.

The ideal bridge is
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`,
`Scheme.IdealSheafData.toModules` and `toModulesι`; the ideal data itself is
the `Scheme.Hom.ker` recorded on `def-sbc-closed-immersion-ideal-sheaf`.
The modules of all stated proof dependencies are also imported. In particular,
the proof plan retains `quasicoherent_finite_type_affine`,
`closedSubscheme_baseChange_ideal_image`, `affinePushforward_baseChange`,
`exists_tensorPullback_affine_sections`, and
`quasiCoherent_affine_section_baseChange`, as well as the Mathlib finite
presentation, flat tensor, and localization lemmas named by their nodes.

### Edge cases

- Identity i: I is zero and b is the structure-sheaf identity under the
  canonical comparisons. Both exactness and the canonical kernel isomorphism
  specialize correctly.
- Empty Z: I is the unit ideal/O_X, the final term is zero, and a is the
  structure-sheaf pullback isomorphism. Empty X or T' gives the zero sequence.
  There are no nonemptiness assumptions.
- Nonflat base change and nonflat ambient family are included. For example,
  take T = Spec Z, X = Spec(Z[x]/(2x)), Z = Spec Z cut out by x, and
  T' = Spec F_2. Z is flat over T while X and the base change are not flat.
  The claimed sequence becomes the ideal sequence for (x) in F_2[x], which
  is exact. This checks that the flat quotient, rather than the ambient ring,
  is the needed hypothesis.
- Flatness of Z cannot simply be deleted: for Spec F_2 inside Spec Z over
  Spec Z, base changing along Spec F_2 kills the map from the nonzero module
  `(2) ⊗ F_2` into F_2. This excluded example confirms the role of the
  supplied flatness hypothesis.
- All schemes use the same arbitrary explicit universe u, as in the recorded
  scheme and module APIs. No independent test universe makes the quantifier
  vacuous. There are no implicit variables, private definitions, local
  notation, or auxiliary hypotheses about canonical maps.

### Searches and validation

Searches actually run through `batch2/msearch.py` for this group/item:

- LeanFinder: "A closed immersion between finitely presented schemes over a
  base with flat source has a finite type ideal sheaf whose short exact
  sequence remains exact after arbitrary base change". Eight hits, including
  `IsClosedImmersion.isStableUnderBaseChange`, flat monomorphisms, and finite
  closed immersions. None states the full item.
- Loogle: `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.Flat`.
  Zero hits.
- Mathlib grep: `baseChange|base_change|ShortExact` in
  `AlgebraicGeometry/IdealSheaf`. Zero hits.
- LeanSearch: "The ideal sheaf of a flat closed subfamily of finitely
  presented schemes is finite type and its short exact sequence is preserved
  under arbitrary base change". Eight hits on ideal-sheaf data, their
  functoriality, and stability of flatness/closed immersions under base
  change; none supplies the theorem.

Direct ripgrep searches in `lean/WeilConjectures` and `lean/Sheaf` examined
flat/closed/ideal base-change names. The existing
`ClosedSubschemeBaseChangeIdealImage` supplies only the image formula, and
`ClosedImmersionConormalFlatBaseChange` concerns conormal modules with a flat
ambient base-change map. Neither is this theorem. Searches for the exact item
ID in `lean/WeilConjectures` found nothing. Searches for `flatClosedFamily`,
`flat_closed_family`, and `FlatClosedFamily` in both source trees and
`dag/lean_names_upstream.json` found no declaration collision.

The first server compile exposed the existing module-pullback name shadowing
the category-theoretic fibre-product name inside `Scheme.Modules`. Using
`Limits.pullback` explicitly repaired this. The next `scompile.py` run compiled
both the sandbox probe and the final module cleanly (11.3 s and 13.7 s).
Only comments were then corrected. The prescribed delivery dry run recompiles
the final text and runs the maintainer's preflight. Independent review is by
the maintainer, as directed by the dispatcher; no independent worker review
is claimed here.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
