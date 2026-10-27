## Worker report

`Sheaf.AlgebraicGeometry.RegularStrictLocalModel` states
`AlgebraicGeometry.regular_strict_local_model`. Its only proof is `sorry`.
No definition, helper theorem, new node, dependency module or statement correction
is introduced. Only the item's `lean` record changes. The former declaration was
removed with its unused module, as recorded by `lean_removed`; the current library
contains no surviving declaration of this result. The node's earlier Q70 review
and report were read, but the statement and its dependencies were checked against
the current sources and compiled afresh.

Hypothesis and clause correspondence:

- `X Y : Scheme.{u}`, `[IsNoetherian X]`, `[IsNoetherian Y]` give the two
  Noetherian schemes. `hX` and `hY` require `IsExcellent Γ(X,U)` and
  `IsExcellent Γ(Y,V)` on every affine open. These use the recorded excellent-ring
  predicate directly, without defining a second scheme-excellence predicate.
- `h : Y ⟶ X`, `[Flat h]`, and `hreg` are precisely the regular-morphism
  hypothesis in the node: for every `x : X`, every field `L : Type u`, every
  `Algebra (X.residueField x) L` and `[Module.Finite (X.residueField x) L]`,
  the pullback of `h.fiberToSpecResidueField x` along the spectrum of that
  algebra map is `IsRegularScheme`. There is no finite-type or separability
  assumption on `h` or on the finite field extensions.
- `ΩX`, `ΩY`, their field and `IsAlgClosed` instances, and `barX`, `barY`
  are the two geometric points in the dependency's inline encoding.
  `e : ΩX →+* ΩY` is their specified map of fields. The equation `hbar`
  expresses the commutative geometric-point square. Distinct fields are allowed.
- The strict localizations are exactly `Scheme.strictHenselizationScheme barY`
  and `Scheme.strictHenselizationScheme barX`, the spectra of the recorded
  coordinate-ring colimits. The conclusion gives their induced morphism as `∃! H`.
  The structural square uses `strictHenselizationStructuralMap`; the second square
  uses `strictHenselizationPointEvaluation` and `e`. These characterize the
  specified pointed morphism rather than an arbitrary map. `IsLocalHom
  H.appTop.hom` says its coordinate-ring map is local. For these affine local
  schemes this is the local condition in the node.
- `Flat H` and the following universal finite residue-field extension test state
  regularity of the induced morphism, with exactly the same test as `hreg`.
- The following four conjuncts say that both strict localizations are Noetherian
  and every affine coordinate ring of each is excellent.
- For every source point `v`, the equality with left side
  `ringKrullDim ((H.fiber (H v)).presheaf.stalk (H.asFiber v))` gives the
  dimension of the local ring of the strict-local fibre at `v`. The right side
  is the local ring of the original fibre at
  `y = Scheme.strictHenselizationStructuralMap barY v`, lying above `h y`.
  The structural square identifies that base point with the image of `H v`.
  These are local fibre dimensions, not whole-fibre or ambient dimensions.
- The closed-subscheme clause quantifies over every `C : Scheme.{u}` and
  `i : C ⟶ Scheme.strictHenselizationScheme barX` with `[IsClosedImmersion i]`.
  Its base-changed map is the actual projection `pullback.snd H i`.
  Flatness and the same finite-field fibre test give its regularity; the remaining
  conjuncts state Noetherianity and excellence of `pullback H i` and `C`.
- The final clause gives the ordinary-localization analogue for every `y₀ : Y`.
  The compatible base point is `h y₀`. The ordinary localizations are the spectra
  of the two stalk rings and their induced map is `Spec.map (h.stalkMap y₀)`.
  Its flatness and finite-field test express regularity, followed by both
  Noetherianities and both excellence conditions. The final equality applies to
  every point `v` of the source localization. Its image in the original scheme
  is `Y.fromSpecStalk y₀ v`; both sides again use fibre stalks via `asFiber`.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, defined as
  `IsQuasiExcellent R ∧ IsUniversallyCatenary R`, with the Noetherian, G-ring,
  J-2 and chain conditions read in that module.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, the
  affine-open flatness predicate, equivalent to stalkwise flatness by
  `Flat.iff_flat_stalkMap`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  defined as `IsLocallyNoetherian X ∧ IsRegular X`. The upstream scheme class
  `IsRegular` tests every stalk with Mathlib's `IsRegularLocalRing`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, and `asFiber`. `fiber` is the chosen pullback along
  `fromSpecResidueField`; `asFiber` is the point determined by `fiberHomeo`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField` explains
  the dependency's inline geometric-point encoding and its residue-field map.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, `strictHenselizationScheme` and
  `strictHenselization_properties`, including the small representative diagram,
  its coordinate-ring colimit and its spectrum. The upstream module replaces the
  withdrawn Sheaf twin and is imported directly.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `Scheme.strictHenselizationStructuralMap`, the common structural composite
  characterized by `exists_strictHenselizationStructuralMap`.
- `Sheaf.Paper.StrictHenselizationPointEvaluation`:
  `Scheme.strictHenselizationPointEvaluation`, constructed by `colimit.desc`
  from the compatible geometric-point evaluation cocone.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, valued in
  `WithBot ℕ∞` without truncation to natural numbers.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber`. Ordinary
  scheme localizations use the existing stalks, canonically prime localizations
  on an affine neighbourhood, and `Mathlib.AlgebraicGeometry.Stalk` supplies
  `Scheme.fromSpecStalk`. No localization is copied.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, with the existing scheme pullback instances.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, used by the excellent
  and regular ring predicates; `Mathlib.AlgebraicGeometry.Noetherian`:
  `IsNoetherian`, which includes local Noetherianity and compactness.

Statement imports are public. The recorded, already stated proof dependencies
are imported privately, including the affine-neighbourhood/triple comparison,
localized strict henselization, functoriality, excellence ascent, Noetherianity,
ind-etale stability, regular local maps, smooth colimits, composition, separable
fibres, flat tensor comparison, height formula, fibre-stalk quotient and regular
base change. The theorem docstring explains all ten proof steps of the node,
including the finite-product decomposition and dimension cancellation.

Source checks: I read the ILO PDF at Exposé XVII the project server, the project server and the project server,
printed pp. 283–285, including its reductions to local strictly henselian
schemes. I also read Stacks `more-algebra.tex`, definition-regular,
lemma-regular-local (07C0), lemma-regular-base-change (07C1),
lemma-henselization-noetherian (06LJ), and lemma-henselization-regular (06LN).
The full local-model package is the node's explicit algebraic argument, not a
claim that ILO states that entire package verbatim. The current blueprint
`literature/blueprint/latest/` ancestor was consulted for provenance.

Edge cases: identity morphisms and the identity field extension are included;
finite inseparable extensions are included; no finite-type condition is added.
Every point, including nonclosed points, occurs in both dimension equalities.
Zero-dimensional fibre stalks use dimension zero in the extended dimension type.
The empty closed subscheme is permitted: its pullback is empty and the regular
fibre tests are vacuous. Empty original schemes have no such geometric point;
the quantification adds no artificial nonemptiness assumption. Ordinary compatible
point pairs are specified by arbitrary `y₀`. The universe `u` is explicit and
shared by schemes and the fields tested, so no independently smaller field
universe makes a regularity test vacuous. All variables are explicitly bound.

Searches, performed through the prescribed wrapper and local source searches:

- LeanFinder: “A regular morphism of excellent Noetherian schemes induces a
  regular morphism on strict localizations with equal local fibre dimensions”:
  eight hits about standard smooth localizations and smooth relative dimension;
  no exact statement.
- Loogle: `AlgebraicGeometry.Flat, IsRegularLocalRing`: zero hits.
- LeanSearch: `regular morphism strict henselization local fiber dimension`:
  eight hits about formal unramifiedness, henselian rings, etale and smooth
  morphisms; no exact statement.
- Wrapper Mathlib grep: `strict.*[Ll]ocal|[Rr]egular.*[Mm]orphism` in
  `AlgebraicGeometry`: six hits about constructors, regular epimorphisms,
  affine localization and ideal sheaves; none the theorem.
- Direct `rg` for `regular_strict_local_model`, the node id,
  `IsRegularMorphism` and `RegularMorphism` in `lean/WeilConjectures`,
  `lean/Sheaf` and Mathlib's `AlgebraicGeometry`: no surviving declaration;
  a downstream proof docstring names this DAG node. The prescribed `grep -rn`
  for the node id under `lean/WeilConjectures` also found nothing.
- Source search found the existing `Orgogozo.IsExcellentScheme` definition, but
  this statement applies the recorded ring predicate inline on every affine open,
  as the earlier reviewed statement did; it introduces no competing predicate.

No `STATEMENT-DISPUTED` issue or node correction is needed. There is no repair
note for the item. Compilation uses `scompile.py` only. The initial compile
identified one 101-character line; it was wrapped, and the final file is checked
again by both single-file compilation and the delivery dry run.

## Second reading by N8

No separate worker was started, as the dispatcher explicitly forbids it. The
maintainer's independent delivery review supplies the independent reading.
I reread the node and final signature clause by clause: regularity retains every
finite residue extension, the two geometric-point squares specify the induced
map, both dimensions are actual fibre stalks, the ordinary clause uses the
canonical stalk map at every compatible pair, and the closed-subscheme clause
retains both Noetherian and excellent schemes without excluding the empty case.
No mathematical mismatch was found; the sole formatting warning was repaired.
