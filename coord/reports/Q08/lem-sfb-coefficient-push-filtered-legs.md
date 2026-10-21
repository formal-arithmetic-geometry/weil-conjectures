## Worker report

The module `Sheaf.Paper.CoefficientPushFilteredLegs` states
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientPush_isIso_of_filtered_flat_legs`.
The sole postponed proof is the theorem's `sorry`. The helpers `filteredCoefficientRestriction`, `filteredCoefficientExtension`,
`filteredCoefficientTensorIso`, `filteredCoefficientRestrictPushIso`,
`filteredCoefficientPushHom` give the existing
functors and maps explicitly typed endpoints. Each body is exactly its existing
recorded construction. The projection mate is the existing `internalProjection` directly.
This avoids repeatedly re-inferring large derived-functor structural arguments.
`filteredCoefficientPullIso` exposes the total derived pullback endpoint of the
existing `residueRestrictedRegularPullIso`; its data are that existing canonical
comparison, not an existence choice or an arbitrary comparison map.

Source read: current blueprint
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md`,
paragraph (1), localization, finite scalar extensions and the final filtered
extension to the algebraic closure. The DAG node expands the argument to a
filtered flat module presentation and specifies the precise cocone maps.

Hypothesis and conclusion correspondence:

- Prime, positive characteristic and distinct primes: `(ℓ p : ℕ) [Fact ℓ.Prime]`,
  `(k : Type u) [Field k] [CharP k p]`, `_hp : 0 < p`, `_hne : p ≠ ℓ`.
- Separated finite-type schemes over the field and a morphism over that field:
  `X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on both structure maps,
  and `f : X ⟶ Y`. The chosen compactification of the setting is not used in
  either conclusion, so no compactification datum is requested from the caller.
- The additional qcqs condition on f is `[QuasiCompact f.left] [QuasiSeparated f.left]`.
- Arbitrary commutative condensed rings are the sheaves `R S` with `MonObj` and
  `IsCommMonObj`; `a : R ⟶ S` and `IsMonHom a` specify the ring map. The
  all-schemes exact scalar-extension assumption is the instance
  `∀ Z, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))`.
  Extension of scalars already preserves colimits; this is exactly exactness.
- The ordinary unbounded category is `DerivedCategory (internalModules R X.left)`.
  These are the existing internal modules, with the imported normalized
  module/ringed-topos equivalence. No completed or constructible replacement is used.
- Small nonempty filtered index: `I : Type (u + 1)`, `SmallCategory I`, `IsFiltered I`.
  `IsFiltered` itself includes nonemptiness. This is the coefficient-sheaf size
  used by the existing qcqs continuity theorem (same scheme universe u).
- Diagram of flat modules: `P : I ⥤ internalModules R Y.left` and `_hP` using
  `ObjectProperty.flat`. This is exact tensor in both variables, the existing
  braided-category flatness predicate. `_hfP` asserts flatness of the ordinary
  `upperStar R f.left` images, as in the node.
- The actual linear cocone legs are `v.app i` of the natural transformation
  `v : P ⟶ (Functor.const I).obj ((Mod.comap (coefficientMap a Y.left)).obj
  (Mod.regular (condensedRingObj S Y.left)))`. Its colimit property is
  `_hv : IsColimit (Cocone.mk _ v)`; no chosen colimit identification replaces v.
- Bounded below is `_hK : ∃ n : ℤ, K.IsGE n`. K remains an object of the full
  unbounded derived category, so this imposes no upper bound.
- The stage maps δ_i are exactly `internalProjection R f.left K (single(P_i))`, the geometric adjoint of tensor pullback followed by the
  counit tensor identity. `_hδ` says these actual maps are invertible.
- The first conclusion is `IsIso ((filteredCoefficientPushHom a f.left).app K)`, definitionally the actual
  recorded coefficient mate γ, not an arbitrary map with the same endpoints.
- For every i, the second conclusion starts with `Rf_* K ◁ single.map (v.app i)`.
  It then applies the inverse of the existing `Mod.residueDerivedTensorIso` on Y (named `filteredCoefficientTensorIso`),
  the derived restriction of γ, and `derivedComapLowerStarIso.hom` at `T_X K`.
  This is the restricted γ composed with `1 ⊗ v_i` and with the canonical
  restriction/pushforward identification, using the right-tensor symmetry.
- The right side starts with that same δ_i and then applies `Rf_*` to
  `K ◁ Lf*.map(single.map(v.app i))`, followed by `K ◁ filteredCoefficientPullIso.hom`
  and the inverse scalar-tensor presentation on X. The existing coefficient
  pullback comparison identifies `Lf*(U_Y S_Y[0])` with `U_X S_X[0]`.
  Thus this is precisely `Rf_*(1 ⊗ f* v_i) ∘ δ_i`, with the node's identifications.

Dependency interfaces read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the field setting and `compactificationOverField` (the setting is explicit in binders).
- Mathlib `AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`, `.QuasiSeparated`:
  `LocallyOfFiniteType`, `QuasiCompact`, `QuasiSeparated`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, transparently
  the `Mon` encoding of the sheaves used here.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` and `.ChangeOfCoefficients`:
  `condensedRingObj`, `condensedPullbackHom`, `coefficientPullbackIso`,
  `condensedPushforwardHom`, `coefficientMap`, `derivedPushHom`,
  `derivedComapLowerStarIso`, `comapUpperStarIso`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`, which are exactly
  the full-composite total right/left derived functors. The statement uses their
  definitionally identical `ModuleRingedComparison.internalDerivedPushforward`
  and `internalDerivedPullback` names, already used by `internalProjection`.
- Mathlib `CategoryTheory.Limits.HasLimits` and `CategoryTheory.Filtered.Basic`:
  `Cocone`, `IsColimit`, `IsFiltered`; the cocone is specified explicitly, so
  no arbitrary `colimit` object is needed in the statement.
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`: `internalProjection`,
  `internalModules`, and the tensor, adjunction and projection comparisons.
  Its public import `Sheaf.Paper.ProjectionMateExact` supplies the ringed mate.
- `Sheaf.Paper.IntegralResidueTensorPresentation`: the completely general
  `CategoryTheory.Mod.residueDerivedTensorIso`; despite the module/name, its
  binders are arbitrary commutative ring objects and arbitrary ring maps.
- `Sheaf.Paper.IntegralResidueTensorPullPresentation`: the completely general
  `residueRestrictedRegularPullIso R S a f`. Its construction uses exact
  pullback/single, `comapUpperStarIso.symm` and the regular-module monoidal unit.
  Both owning nodes already have landed Lean records and are added to stmt_deps
  under the standing permission to cite landed nodes. No new notion or node is added.

All stated proof-dependency modules are imported directly or reexported by the
public statement imports. The seven-step proof plan is in the theorem docstring.
The underived scalar adjunction is reexported from the coefficient modules;
the node `def-sfb-modobj-extend-restrict-adjunction` has no separate Lean record.

Edge cases checked against the mathematical statement and definitions: empty
schemes and zero modules give zero derived objects and identity zero morphisms;
zero coefficient rings are admitted. The index cannot be empty by `IsFiltered`.
A one-object filtered diagram recovers the projection map for its coefficient.
Identity a and identity f retain the actual units and comparison maps. K can
have arbitrarily high cohomology and any lower bound; no uniform upper bound is
introduced. The P_i need not be algebras, monomorphisms, finite or finitely generated;
only their linear maps to the restricted regular S-module are required. The
argument uses cohomology of strict uniformly bounded diagrams and does not assert
arbitrary colimits in the triangulated derived category.

Searches actually run:

- msearch LeanFinder, `Flat coefficient scalar extension pushforward comparison is an
  isomorphism for a filtered colimit of flat coefficient modules with invertible
  projection maps`: eight hits about flat modules and flat Kan extensions; none
  states the coefficient mate or its filtered cocone-leg formula.
- msearch Loogle, `Mod.IsFlat, Mod.extendScalars, DerivedCategory.singleFunctor`:
  zero hits; the service reports the unknown identifier `Mod.IsFlat`. Source
  inspection instead locates `ObjectProperty.flat` in the upstream flat API.
- msearch grep, `derivedPushHom|pushHomOfComapIso|projection.*[Ff]iltered`:
  zero Mathlib hits.
- msearch LeanSearch, `The derived coefficient extension pushforward comparison is
  invertible for a filtered presentation with invertible projection maps`: eight
  hits concerning ordinary pushforward composites and algebra presentations;
  none is the node's assertion.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  `filtered.*[Pp]rojection|[Pp]rojection.*filtered`: unrelated filtered complexes,
  cohomology and algebra; no existing statement. Upstream node-id grep likewise
  has no match. Further `extend.*[Tt]ensor|[Tt]ensor.*[Ee]xtend|comap.*[Tt]ensor`
  searches found the reused generic scalar-tensor presentations. Searches for
  all seven delivered declaration names in both libraries and `dag/lean_names_upstream.json`
  found no collisions.

No statement correction or statement dispute was needed.

## Second reading by Q08

This is the author's second pass; the prescribed maintainer review supplies the
independent reading. I reread the full node and the declaration with particular
attention to the direction of γ, the tensor symmetry, and each cocone leg. The
left composite goes from `Rf_*K ⊗ P_i[0]` to `Rf_* U_X T_X K`, using inverse
right-tensor presentation, then restricted γ, then the restriction/push isomorphism.
The right composite has exactly the same source and target: δ_i first, then
pullback of v_i, the canonical pulled regular coefficient, and inverse tensor
presentation. In particular no arbitrary choice of coefficient identification,
no arbitrary comparison map, and no algebra structure on P_i has been inserted.
The flatness hypotheses are on ordinary modules, whereas projection uses their
single-degree derived objects; the exact geometric inverse image identifies
these with the corresponding ordinary pullbacks. The characteristic and
finite-type setting is explicit. Nonemptiness and the lower-bound condition
were checked in the existing definitions. The helper is real existing data.

The typed endpoint helpers were introduced after diagnostic compiles localized
expensive repeated unification to raw derived restriction and the internal/total
derived pullback endpoint. These are definitional wrappers, with no additional
mathematical hypotheses, axioms, or postponed helper theorems.

The scalar-tensor helper specializes the existing generic natural isomorphism
with explicitly typed endpoints. Its target is `(derivedTensor R Z).flip.obj C_Z`,
the existing right tensor functor.
The scalar-extension wrapper extracts the actual left functor from the existing
`Mod.derivedExtendMapDerivedCategoryAdjunction`. It returns that functor itself;
it does not select a left adjoint by existence. This is the same computational
endpoint-extraction method as the comparison dependency uses for its derived
geometric functors.

The generic scalar-tensor comparison is specialized with an explicit symmetric
structure whose braiding is `ProEtale.sheafBraidedCategory` and whose symmetry
proof is `ProEtale.sheafSymmetricCategory.symmetry`. These are the existing
canonical data. This keeps the generic comparison's braiding identical to that
of the geometric functors. The isolated typed component of this specialization
compiled on the server; no existence theorem or new postponed helper is used.

The equation writes left tensoring as `((derivedTensor R Z).obj K).map g`,
rather than the notation `K ◁ g`. These are the same operation; using the
already specialized bifunctor avoids repeated synthesis of monoidal structures.

Validation: the delivered module compiled separately through `scompile.py` in
both sandbox and module modes (34.0 s and 39.4 s), within the unchanged 60-second
limit. There were no errors or non-sorry warnings. `autoImplicit` is disabled.
There is no repair note for this item. The source and node signatures were
checked verbatim, and all delivered Lean lines are at most 100 characters.
