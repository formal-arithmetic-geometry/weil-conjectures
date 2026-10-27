## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothFreeSequenceTransformFlatness` states
`AlgebraicGeometry.Scheme.Modules.smoothFreeSequence_transform_flatness`, with a
single `sorry`. The new companion module defines the basis-normalized free pullback
isomorphism with real data and no postponed theorem. The
node statement is unchanged. The actual object `cokernel α` is used throughout,
with its canonical quotient `cokernel.π α`.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Affine base S, affine smooth f:X→S | `{S X : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsAffineHom f] [Smooth f]`; affineness of X follows from the affine morphism over the affine base. |
| Fibres integral after every residue-field extension | `[GeometricallyIntegral f]`, Mathlib's quantification over all field-valued points and their scheme-theoretic pullbacks. |
| Quasi-compact open U | `(U : S.Opens) (hU : IsCompact (U : Set S))`. |
| Finite-type quasi-coherent F | `(F : X.Modules) [hF : F.IsQuasicoherent] [F.IsFiniteType]`. No finite-presentation assumption is imposed. |
| Integer r≥0 and α:O_X^r→F | `(r : ℕ)` and `α` from `SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))`. ULift only places the finite basis in the sheaf's universe. |
| Open W, W→S surjective, α restricted to W an isomorphism | `(W : X.Opens) (hW : Surjective (W.ι ≫ f))` and `hαW : IsIso ((restrictFunctor W.ι).map α)`. |
| H=coker α and original sequence short exact | H is literally `cokernel α`; `hα : Mono α` is equivalent to short exactness of α followed by its canonical cokernel quotient in this abelian category. There is no arbitrary quotient object or map. |
| Remains exact after every T→S | `hbase` quantifies over every `(T : Scheme.{u}) (t : T ⟶ S)` and asserts `ShortExact` of the tensor-pulled-back α and `cokernel.π α`. Its existential `w` supplies only the proof of zero composite. |
| Every U-admissible blowup, retaining its finite-type ideal | `∀ B : IsAdmissible S U`; the ideal is always `B.I`, the blowup `B.I.blowup`, and its morphism `B.I.blowupMap`. `hI` is returned as a conclusion; admissibility already supplies finite type. |
| X^b and W^b are the indicated base changes | `Limits.pullback f B.I.blowupMap`, projections `pullback.fst` and `pullback.snd`, and the canonical base-change open `(pullback.fst f B.I.blowupMap) ⁻¹ᵁ W`. This open subscheme is W×_S S^b. |
| Strict free term is ordinary pullback | `IsIso (cokernel.π (kernel.ι (moduleStrictTransformRestriction f B.I free)))` for the actual quotient map. The new definition-owned `tensorPullbackFreeBasisIso` identifies this ordinary pullback with the free sheaf of rank r on X^b. Its normalization on each basis summand is fixed by the structure-sheaf tensor comparison. |
| Induced short exact sequence 0→O_(X^b)^r→F^b→H^b→0 | Existential `αb`, `βb`, and zero-composite witness `w`, followed by `(ShortComplex.mk αb βb w).ShortExact`. All transformed objects use `moduleStrictTransform f B.I` on the original modules. |
| Compatibility with ordinary pullback quotients | First equation: `tensorPullbackFreeBasisIso.hom ≫ αb = (tensorPullback p).map α ≫ cokernel.π (kernel.ι (moduleStrictTransformRestriction f B.I F))`. Second equation: `cokernel.π (kernel.ι (moduleStrictTransformRestriction f B.I F)) ≫ βb = (tensorPullback p).map (cokernel.π α) ≫ cokernel.π (kernel.ι (moduleStrictTransformRestriction f B.I (cokernel α)))`. These fix the induced maps, with the canonical free identification. |
| W^b→S^b surjective and α^b restricted to W^b is an isomorphism | The next two conjuncts assert `Surjective` of the inverse-image open immersion followed by the second projection, and `IsIso` of the restriction of `αb` to that open. |
| Flatness equivalence at every y with image t | `∀ y : Limits.pullback f B.I.blowupMap, Module.Flat (...) (...) ↔ Module.Flat (...) (...)`; t is explicitly `(pullback.snd f B.I.blowupMap) y`. Both stalks are constructed by `RingedSpace.moduleStalkFunctor` and restricted along the actual second-projection stalk map using `ModuleCat.restrictScalars`. Thus the base ring is exactly O_(S^b,t), rather than the source stalk ring or the original base ring. |
| H^b flat over S^b iff F^b flat over S^b | Final conjunct uses the recorded `Scheme.Modules.IsFlatOver` on the two strict transforms through `pullback.snd f B.I.blowupMap`, in the node's order. |

The existential witnesses `hfree` and `hH` are proofs of quasi-coherence, returned
before the blowup quantifier. They permit the existing strict-transform API to be
used for the free module and the actual cokernel. They are not extra hypotheses,
choices of module data, or replacements for those modules.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  `pullback.fst`, `pullback.snd`, reexported by the scheme pullback imports.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the upstream
  `Scheme.Modules.tensorPullback` and its section-normalized adjunction interface.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`; the
  convention node defines no additional object, and no unnecessary qs hypothesis
  is added to the affine base.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: Mathlib's `IsQuasicoherent` and
  `IsFiniteType`, with the recorded coherence module publicly exposed.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and `.Quasicoherent`:
  `SheafOfModules.IsFiniteType`, `IsFinitePresentation`, and `free`; the statement
  uses finite type and free modules, without assuming finite presentation of F.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, with its full affine-local definition read.
- `WeilConjectures.Blowup.AdmissibleBlowup`: `IsAdmissible`, with the actual `I`,
  `finiteType`, and `disjoint_support` fields read.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform`: `moduleStrictTransform`,
  `moduleStrictTransformRestriction`, and its kernel/cokernel construction read.
- `Sheaf.AlgebraicGeometry.ModuleAdmissibleBlowupCalculus`: proof-only import
  for `moduleAdmissibleBlowupPermanence` and `moduleAdmissibleBlowupCalculus`.
  Its quotient helper is inlined using the defining cokernel.π of kernel.ι.
- `Sheaf.AlgebraicGeometry.TensorPullbackFreeBasisIso`:
  `tensorPullbackFreeBasisIso`, constructed from Mathlib `mapFreeIso` and
  the pinned `tensorPullbackObjUnitToUnit`. The old Picard theorem module
  and its helper are no longer used by this item.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`, including its underlying stalk construction.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`,
  whose definition quantifies over field-valued points, as required.

The item retains the added geometric-properties and module-stalk definition nodes.
The two theorem nodes named in the return have been removed from `stmt_deps`.
The new `def-trf-tensor-pullback-free-basis-iso` supplies the definition-owned free
comparison and cites `def-sfb-tensor-pullback-structure-sheaf-map` and
`def-pc-module-pullback`. There is no dependency module or statement correction.
Every stated proof dependency is imported, with blowup calculus proof-only;
the full six-step proof plan remains in the theorem docstring.

Edge cases checked against the source and signature: r=0 is included by Fin 0;
then the cokernel is F and the flatness equivalence has its expected meaning.
The empty base is allowed and yields vacuous pointwise conditions. No Nonempty
assumption is used. U=S includes the identity blowup and its canonical quotients;
U=∅ is not excluded. No density, Noetherian, nonzero-ring, characteristic,
finite-presentation-of-F, or fixed-relative-dimension hypothesis is added.
The basis open need not avoid the exceptional divisor. All universal scheme
base changes in the ambient universe are quantified over; universes are bound
explicitly with autoImplicit disabled.

Searches actually run:

- `msearch.py`, LeanFinder: “Strict transforms of a universally exact generically
  free sequence under an admissible blowup have equivalent relative flatness for
  the middle and quotient terms”: eight hits about flat tensor products and weakly
  regular sequences, no strict-transform statement.
- `msearch.py`, Loogle: `"strictTransform"`: zero hits.
- `msearch.py`, grep of Mathlib: `strictTransform|strict_transform|moduleStrictTransform`:
  zero hits.
- `msearch.py`, LeanSearch: “Strict transforms of a generically free universally
  exact sequence compare the relative flat loci of the middle term and the
  cokernel”: eight hits about tensor exactness, localization and flat morphisms;
  none is the item.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for strict-transform names found
  the existing strict-transform, universal-exactness, and blowup-calculus modules,
  but no existing theorem giving all clauses of this item.
- `grep -rn` for the item ID in `lean/WeilConjectures`: no hits.
- Further `rg` searches for free pullback comparisons found
  `WeilConjectures/AlgebraicGeometry/PicardTensorFrameCoordinates.lean` and its
  public `picardTensorFreeIso`; the private LocalKoszul implementation is not used.
- `rg` for the proposed full declaration name in Mathlib/project naming records
  and project sources: no collision.

Source reading: `flat.tex` theorem-flatten-module proof paragraph 3 and
lemma-induction-step; `divisors.tex` lemma-strict-transform-universally-injective.
No disputed statement or source fault was found.

## Second reading by Q49

A separate second pass by the same dispatched worker reread the node and the
complete signature; no other agent was started, as required by the dispatch brief.
The independent delivery review remains with the maintainer.

The pass checked that the cokernel is literal, that the initial exactness is Mono
plus canonical cokernel and that hbase includes both endpoint conditions through
ShortExact. It checked that no proof of quasi-coherence or finite type of the
cokernel became an input, that the free term uses the same rank including zero,
and that both quotient equations use the correct order of composition. It checked
the basis-normalized free comparison and the inverse-image open, including its
surjectivity and the restriction isomorphism. Finally it reread the two stalk
expressions: both use the new base stalk at the image under snd, with scalar
restriction along snd.stalkMap; the final global equivalence uses the recorded
IsFlatOver predicate. The first delivery had the H2 ownership mismatch described in the return: two
statement edges pointed to theorem nodes solely for their helper definitions.
The repair removes those edges, inlines all quotient maps, and uses the new
definition-owned normalized isomorphism. This second pass reread the new node and
its implementation: I is unrestricted in Type u including empty, the canonical
structure-sheaf map fixes each summand, and the inverse is constructed by
mapFreeIso. The helper agrees with the previous normalization. No hypothesis,
stalk expression, open, or flatness clause changed. Compiler feedback
identified a name collision between the scheme fibre product and Modules.pullback;
all object occurrences of the fibre product were qualified as Limits.pullback.


## Repair of returned delivery 2f2ba59f814d

H2 is repaired exactly at the two inappropriate statement-dependency edges.
`lem-sc-picard-tensor-frame-map` and `lem-trf-module-admissible-blowup-calculus`
are removed from `stmt_deps`. The latter stays in `proof_deps` and as a plain
proof-only import because the six-step proof uses its flat-transform theorem.
The Picard module import is removed entirely. The actual quotient in all three
occurrences is now `cokernel.π (kernel.ι (moduleStrictTransformRestriction ...))`,
which is the defining quotient of `def-trf-module-strict-transform`.
`tensorPullbackFreeBasisIso` replaces `picardTensorFreeIso`, with the same
normalization. The item node differs from current main only in `lean` and
`stmt_deps`; all source text, proof steps, and other fields are preserved.
The authorized delivery wrapper refreshes and rebases the packet on current main.

## New nodes

`def-trf-tensor-pullback-free-basis-iso` owns the basis-normalized isomorphism
`(tensorPullback g).obj (free I) ≅ free I` in the new module
`Sheaf.AlgebraicGeometry.TensorPullbackFreeBasisIso`. Its definition constructs
`mapFreeIso` from the inverse of `asIso (tensorPullbackObjUnitToUnit g)` and takes
its inverse. The pinned canonical adjunction supplies preservation of coproducts;
the existing isomorphism theorem supplies only the proof needed by asIso. No
object, map, inverse, or proof is sorry, and no arbitrary isomorphism is chosen.
On the i-th pulled-back summand the forward map is the pinned structure map
followed by the i-th inclusion. This is the labelled-basis identification used
in the strict-transform quotient square, for arbitrary I, including empty I.

The new node cites exactly `def-pc-module-pullback` and
`def-sfb-tensor-pullback-structure-sheaf-map`, as requested by the return.
Its sources are sheaves.tex Tag 0096 (the canonical tensor adjunction) and
modules.tex Tag 01C8 (pullback of locally free modules). The tag mapping was
checked in literature/stacks-project/tags/tags. Blueprint ancestor is
`lem-trf-local-term-locality`; the free-term identification in its flattening
expansion is the place this comparison serves.

Searches for this new node: LeanSearch “Canonical basis normalized isomorphism
between tensor pullback of a free sheaf and the free sheaf on the source scheme”
returned eight results including `SheafOfModules.pullbackObjFreeIso` for the
abstract Mathlib pullback, not the tensorPullback functor used here. Loogle
`SheafOfModules.mapFreeIso` returned eleven results, including the generic
coproduct construction used in the definition. Mathlib grep
`pullbackObjFreeIso|mapFreeIso` in Algebra/Category/ModuleCat/Sheaf returned sixteen
hits, again the generic construction and abstract-pullback comparison.
`blueprint_refs.py search 'pullback free'` returned zero blueprint nodes.
DAG searches found no definition node owning this normalized tensor comparison.
Project searches found `picardTensorFreeIso` in the existing theorem module and
its consumers, but no `tensorPullbackFreeBasisIso`. The requested module exposes
the same canonical construction through definition-node ownership instead of
creating a statement edge to the unrelated Picard theorem. The explicit return
authorizes this new definition module; it introduces no different normalization.
The actual search logs are recorded in the new node's mathlib_searches.
