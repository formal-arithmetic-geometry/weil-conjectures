## Worker report

The module `Sheaf.AlgebraicGeometry.FlatteningAmbientModulePreparation` states
`AlgebraicGeometry.exists_flattening_ambient_module_preparation`. Its only theorem
has proof `sorry`; there are no new definitions, auxiliary theorems or node corrections.
The original node is copied unchanged except for `lean`.

Source read: `literature/stacks-project/flat.tex`, Tag 081R,
`lemma-flat-after-blowing-up`, lines 9122–9166 (the affine-cover and ambient-module
paragraphs); `morphisms.tex`, `lemma-quasi-affine-finite-type-over-S`, lines
9372–9410. The node refines the source's affine cover by affine charts on the
base, so its conclusion does not require the whole morphism `g` to be
quasi-separated. The source's quasi-separatedness assumption is used later for
the global strict transform and is not added to this local preparation lemma.

Hypotheses, one by one:

- Schemes T and W: `{T W : Scheme.{u}}`, with explicitly declared universe `u`.
- T quasi-compact and quasi-separated: `[CompactSpace T] [QuasiSeparatedSpace T]`.
- The quasi-compact open U: `(U : T.Opens) (hU : IsCompact (U : Set T))`.
- The morphism g: `(g : W ⟶ T)`.
- Finite type of g: `[LocallyOfFiniteType g] [QuasiCompact g]`, exactly the
  conjunction recorded by `def-weil-finite-type-morphism`.
- Flatness of W ×_T U → U: `[Flat (pullback.snd g U.ι)]`.
- Local finite presentation of that same morphism:
  `[LocallyOfFinitePresentation (pullback.snd g U.ι)]`.

Conclusions, one by one:

- A finite affine open covering of W is `(r : ℕ) (O : Fin r → W.Opens)`,
  `(⨆ i : Fin r, O i) = ⊤`, and `∀ i, IsAffineOpen (O i)`.
- The nonnegative integers n_i are `(n : Fin r → ℕ)`.
- Open subschemes V_i of the relative affine spaces are
  `V : ∀ i, (AffineSpace (ULift.{u} (Fin (n i))) T).Opens`.
  The coordinate index has exactly n_i elements; the lift only places it in the
  universe required by the recorded `AffineSpace` definition.
- Each open V_i is quasi-compact by the clause
  `IsCompact (V i : Set (AffineSpace (ULift.{u} (Fin (n i))) T))`.
- The morphisms j_i are existentially chosen with type
  `(O i).toScheme ⟶ (V i).toScheme`, and satisfy `IsClosedImmersion (j i)`.
- They are over T by the equation
  `j i ≫ ((V i).ι ≫ (AffineSpace ... T ↘ T)) = (O i).ι ≫ g`.
- The ambient map p_i is the fixed map `(V i).ι ≫ (AffineSpace ... T ↘ T)`;
  the two separate clauses `QuasiCompact p_i` and
  `LocallyOfFinitePresentation p_i` give precisely its two required properties.
- The module is literally
  `(Scheme.Modules.pushforward (j i)).obj
    (SheafOfModules.unit (O i).toScheme.ringCatSheaf)`.
  It is not an arbitrary module. `Modules.pushforward_obj_obj` identifies its
  sections on H with the structure-module sections on `(j i) ⁻¹ᵁ H`
  definitionally. `SheafOfModules.unit` is the sheaf of rings as its own module;
  `Modules.pushforward` uses `j_i.toRingCatSheafHom`, hence exactly the scalar
  action from j_i. No separate section-identification hypothesis is necessary.
- Quasi-coherence and finite type of this module are the exact dependency
  predicate `Scheme.Modules.IsQuasiCoherentFiniteType` (its two conjuncts are
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`).
- Its restriction over U is `M.restrict (p_i ⁻¹ᵁ U).ι`. The canonical
  `pullbackRestrictIsoRestrict p_i U` identifies this open model with V_i ×_T U.
  `SheafOfModules.IsFinitePresentation` applied to that restriction is the
  module finite-presentation clause, with its ambient structure sheaf.
- `Scheme.Modules.IsFlatOver` applied to the same restriction and the fixed
  map `p_i ∣_ U` is its flatness over U. `morphismRestrict` is the pullback
  projection after the preceding canonical identification, rather than an
  independently chosen morphism. Thus the fibre-product language and the open
  model denote the same restriction and base scalar action.
- Empty W is allowed: `r = 0`, the empty supremum is bottom, which is top on
  the empty scheme, and every per-index condition is vacuous.

Recorded statement-dependency declarations read and used:

| Node | Module | Declaration/interface |
| --- | --- | --- |
| def-weil-pbc-scheme-conventions | convention record, no module | compact and quasi-separated scheme conventions |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType | AlgebraicGeometry.LocallyOfFiniteType; QuasiCompact in Morphisms.QuasiCompact |
| def-weil-quasi-separated-morphism | Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated | AlgebraicGeometry.QuasiSeparated; scheme form QuasiSeparatedSpace |
| def-weil-flat-morphism | Mathlib.AlgebraicGeometry.Morphisms.Flat | AlgebraicGeometry.Flat |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | AlgebraicGeometry.LocallyOfFinitePresentation |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | CategoryTheory.Limits.pullback, pullback.snd |
| def-nagata-relative-affine-space | Mathlib.AlgebraicGeometry.AffineSpace | AlgebraicGeometry.AffineSpace; AffineSpace.over |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion | AlgebraicGeometry.IsClosedImmersion |
| pqf-def-coherent | Sheaf.AlgebraicGeometry.CoherentFiniteType | AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType |
| def-weil-pbc-module-finite-type-presentation | Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators and .Quasicoherent | SheafOfModules.IsFiniteType; IsFinitePresentation |
| def-pc-scheme-module-flat-over | WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic | AlgebraicGeometry.Scheme.Modules.IsFlatOver |

Canonical module operations were read in Mathlib's
`AlgebraicGeometry/Modules/Sheaf.lean` (`pushforward`, `pushforward_obj_obj`,
`restrict`), `Algebra/Category/ModuleCat/Sheaf.lean` (`unit`) and
`AlgebraicGeometry/Restrict.lean` (`pullbackRestrictIsoRestrict`,
`morphismRestrict`). All statement imports are public. The recorded proof
modules are imported privately, including the relative-spec theorem, closed
pushforward stalks, affine finite-type module criteria, and smooth affine space.
`lem-a1-map-over-base-finite-presentation` has neither Lean record nor Mathlib
match in the node copy read, so there is no recorded module to import for that
proof dependency. It is not needed to type the statement.

Edge cases checked before and after writing: empty W (empty family); empty T
(which forces W empty); U empty (the two base-change hypotheses and the two
restricted-module conclusions concern empty schemes); U = T (the restrictions
are the canonical whole-scheme models); n_i = 0 (a zero-variable relative affine
space is allowed); zero quotient modules (finite type, finite presentation and
flatness include zero). Neither the theorem nor its finite-cover encoding
assumes a nonempty index set, nonempty scheme or positive affine dimension.
No Noetherian or quasi-separatedness condition on W or g has been inserted.

Searches actually run on 2026-10-24:

- `msearch.py ... leanfinder`, query:
  "A finite type morphism over a quasi compact quasi separated scheme has a
  finite affine open cover embedded into open subsets of relative affine
  spaces with pushforward structure modules finitely presented and flat over
  a good open". Eight hits, including `IsFinite.finite_app`,
  `Scheme.Hom.finiteType_appLE`, `isFinite_iff`, and
  `Scheme.exists_isOpenCover_and_isAffine`. None states the full preparation
  theorem with its ambient modules and good-open clauses.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.LocallyOfFinitePresentation`.
  Successful search, zero hits.
- `msearch.py ... grep`, query:
  `quasiAffine.*[Ii]mmersion|immersion.*[Aa]ffineSpace|pushforward.*[Ff]inite[Pp]resentation|finitePresentation.*pushforward`.
  Four hits in Mathlib/AlgebraicGeometry/QuasiAffine.lean, all concerning
  quasi-affineness and immersions, no matching preparation statement.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`, query:
  `flattening.*[Aa]mbient|ambient.*[Mm]odule|lem-trf-flattening-ambient-module-preparation`.
  Only unrelated ambient-module occurrences, no existing statement or name.
- Targeted `rg` searches for pushforwards of the structure module and for
  `IsFlatOver`, `restrict`, `unit`, `AffineSpace` and `morphismRestrict` located
  the exact existing definitions used above. No private copies were introduced.

There is no statement dispute, correction, missing notion or dependency-interface
repair. The theorem docstring includes the entire seven-step natural-language
proof from the DAG, including the cited dependency IDs.

## Second reading by Q77

This is the author's final clause-by-clause rereading; the maintainer supplies
the independent review under the dispatcher brief. The node and final file
were checked together. The base and good-open hypotheses use the original
objects; `pullback.snd g U.ι` has target U, so flatness is over U, not over T.
The cover only asserts affine opens, not a stronger affine condition on V_i.
The over-T equation fixes the ambient structure maps. Both finite-presentation
and flatness clauses use the same literal canonical direct image, restricted
along the same inverse-image open, and flatness uses `p_i ∣_ U`. The compactness
of V_i and quasi-compactness of its structure map are separate clauses. The
finite index allows zero. No mismatch with the node remains.

Compilation initially exposed a field-notation parse issue, repaired by writing
`SheafOfModules.IsFinitePresentation` and `Scheme.Modules.IsFlatOver` explicitly.
This changed no mathematical clause.
