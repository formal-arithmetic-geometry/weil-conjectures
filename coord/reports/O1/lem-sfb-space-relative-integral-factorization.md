## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeIntegralFactorization` states
`AlgebraicGeometry.AlgebraicSpace.exists_relative_integral_factorization`. Its sole proof
is `sorry`. It introduces no definitions, helper theorems, new nodes, or dependency repairs.
The node's natural-language statement and all existing dependencies remain unchanged.

The source was read in `literature/stacks-project/spaces-morphisms.tex`,
Definition `definition-normalization-X-in-Y` and Lemma `lemma-characterize-normalization`
(Tags 0822 and 0823, including the proof). The node is precisely the existence and initiality
part of that lemma, specialized to separated f. The extra assertion there that the mediator
is itself a normalization is not part of this node and is not added to its conclusion.

Hypotheses and clauses, matched against the node:

- The base scheme is `{S : Scheme.{u}}`. The explicitly declared universe `u` and the
  existing `AlgebraicSpace S` and `Over S` interfaces retain the project's size convention.
  There is no additional size or smallness hypothesis.
- The spaces and morphism are `{Y X : AlgebraicSpace S} (f : Y ⟶ X)`. They are full
  subcategory objects of fppf sheaves and their actual natural transformations, not schemes.
- Quasi-compactness is `hqc`. It quantifies over every `T : Over S` with
  `CompactSpace T.left`, and every `t : yoneda.obj T ⟶ X.obj.obj`. Its conclusion is an
  actual map `a : yoneda.obj U ⟶ Limits.pullback f.hom.hom t`, with
  `CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`. These are exactly a quasi-compact
  scheme atlas and representable surjective etaleness for the required sheaf fibre product.
  `CompactSpace` means quasi-compact, without a Hausdorff requirement. This hypothesis is
  expanded because `IsQuasiCompactPresheafMap` in the pushforward proof dependency only
  explicitly tests affine schemes; this statement retains all quasi-compact tests verbatim.
  There is no second named quasi-compactness predicate. Restriction of `hqc` to affine
  tests supplies that proof dependency's hypothesis, since affine schemes are quasi-compact
  and a map to the pullback is precisely a compatible pair of maps to its factors.
- Separatedness is `hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
  (Limits.pullback.diagonal f.hom.hom)`. This is the existing scheme-test representability
  predicate applied to the actual relative diagonal, with the recorded closed-immersion
  notion on the underlying scheme morphism. No representability assumption on f is added.
- The factorization is `∃ (N : AlgebraicSpace S) (i : Y ⟶ N) (n : N ⟶ X)` and
  `i ≫ n = f`. Composition in Lean is in diagram order, so this is n composed with i.
- Integrality of n is `IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) n.hom.hom`.
  It asserts representability and the scheme integral property on every scheme test.
- The universal target is every `T : AlgebraicSpace S`, with every `q : T ⟶ X` satisfying
  that same integral scheme-test condition, every `a : Y ⟶ T`, and `a ≫ q = f`.
  In particular a has no finiteness, representability, or surjectivity hypothesis.
- The conclusion `∃! h : N ⟶ T, i ≫ h = a ∧ h ≫ q = n` asserts existence and uniqueness
  among all morphisms satisfying both triangles, exactly h composed with i equals a and
  q composed with h equals n. There is no supplementary condition on h.
- The sheaf fibre products are the existing `Limits.pullback`; their algebraic-space
  interpretation is supplied by the imported fibre-product node. The point topology is
  imported from its recorded module; no topological predicate or substitute topology is
  introduced, since the node states its actual hypotheses via scheme atlases and diagonals.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`. Their full definitions
  express scheme-valued pullback squares. These render the object category, atlas
  hypotheses, diagonal property, and integral properties directly.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` (and its recorded covering declarations).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace` (and the existing point-image construction).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: the recorded finite/integral interface;
  its public import `Mathlib.AlgebraicGeometry.Morphisms.Integral` provides
  `AlgebraicGeometry.IsIntegralHom`. The latter's full signature extends `IsAffineHom`
  with integral section maps on every affine open; it is exactly the node's integral notion.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used by the
  existing `IsEtale` scheme-test predicate.
- `def-weil-size-convention` is the recorded metatheoretic convention and has no module
  or declaration; explicit universe polymorphism implements it here.

The remaining proof dependencies are imported without `public`, as required for stage 3:

- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence`:
  `AlgebraicSpace.space_relative_spec_correspondence`, with `RelativeSpecData` and its
  `StructureAlgebraModel`, chart formula, and normalized tensor base-change data.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `AlgebraicSpace.moduleDirectImage`, `moduleTensorPullback`, `moduleTensorAdjunction`,
  and their normalized compatible-chart-section universal properties.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicSpace.QCoh`, using `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward`:
  `AlgebraicSpace.isQuasicoherent_moduleDirectImage_of_quasiCompact_separated`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIntegralClosure`:
  `AlgebraicSpace.existsUnique_quasiCoherent_integralClosure`, whose subobject records
  the sectionwise inclusion and monic-polynomial integral-element condition.

All four node proof steps are included in the declaration docstring: the mapping
correspondence, the quasi-coherent integral-closure construction, existence of the
mediator via monic equations and descent, and uniqueness via injectivity and faithfulness.

Edge cases were checked before writing: if f is integral, N = Y and i = identity has
exactly this initial property. If f is identity, N = X and both structure maps are
identities. For empty Y, the zero algebra has empty relative spectrum, an integral map
to X, and a unique map into every integral target over X. Empty scheme tests and empty
atlases are allowed. A nonempty Y cannot map to empty X, consistently with the binders.
There is no finite-type, reducedness, characteristic, nonemptiness, or field hypothesis.

Searches for an existing declaration:

- `msearch.py`, `leanfinder`: "Every quasi compact separated morphism of algebraic spaces
  admits a universal factorization through an integral morphism". Eight results included
  `Scheme.Hom.instIsIntegralHomFromNormalization`, `instIsIntegralHomNormalizationDesc`,
  and scheme postcomposition/permanence instances. These quantify over schemes and do not
  state this algebraic-space theorem.
- `msearch.py`, `loogle`: `AlgebraicGeometry.Scheme.Hom.normalizationDesc`. Six results:
  `normalizationDesc`, `instIsIntegralHomNormalizationDesc`,
  `toNormalization_normalizationDesc`, `normalizationDesc_comp`, and the two assoc forms.
  All are scheme-only.
- `msearch.py`, `grep`: `relative.*[Nn]ormalization|normalizationDesc|IsIntegralHom` in
  `AlgebraicGeometry/Normalization.lean`. Five text hits, all on relative normalization
  of schemes; none is a space theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `relative.integral.factor|relative_integral_factor|normalizationDesc`: scheme
  normalization applications, and a blueprint reference in `SpaceEtaleFiniteFpEnvelope`;
  no existing declaration of this assertion. `grep -rn` of this node id in
  `lean/WeilConjectures` returned no match. The proposed declaration name was also checked
  in both source roots and `dag/lean_names_upstream.json`, with no match.
- `rg` for the scheme-test quasi-compactness and separatedness predicates located
  `SpaceQCSeparatedEtaleLocal`; its full predicate signatures were read and compared as
  described above. The existing relative-Spec integral test already uses precisely
  `IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left)`.

No statement correction or disputed statement was found.

## Second reading by O1

No separate worker was started: the dispatcher brief forbids starting agents and provides
for the maintainer's independent review. A self-check of the written signature against
the node confirms all quasi-compact scheme tests, representable surjective etale atlases,
the closed relative diagonal, integral scheme tests, arbitrary targets and arrows, and
both triangles inside unique existence. It found no mismatch and changed no statement.
