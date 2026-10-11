## Worker report

Existing declaration: `AlgebraicGeometry.IsLocallyNoetherian`, in
`Mathlib.AlgebraicGeometry.Noetherian` (source lines 56–59). No new Lean module,
definition, theorem, or proof is delivered. Only the item's `lean` record changes.

The source was checked at [Stacks Tag 01OV](https://stacks.math.columbia.edu/tag/01OV),
Definition 28.5.1: each point has an affine neighbourhood with Noetherian coordinate
ring. This is the node's existence-of-an-affine-open-cover formulation. The remark's
sources were also opened: [01T5](https://stacks.math.columbia.edu/tag/01T5) states that
immersions are locally of finite type; [01T6](https://stacks.math.columbia.edu/tag/01T6)
states locally finite type permanence over a locally Noetherian target. The local
literature files are absent on this machine; these primary-source pages were used.

Clause-by-clause correspondence:

- The object is an arbitrary scheme `X : Scheme`, with the ambient universe `u` of
  Mathlib. No field, characteristic, separatedness, finite type, nonemptiness, or
  quasi-compactness assumption is imposed.
- An affine open family is `S : ι → X.affineOpens`; the covering clause is
  `(⨆ i, S i : X.Opens) = ⊤`. Its Noetherian sections clause is
  `∀ i, IsNoetherianRing Γ(X, S i)`. The full signature of
  `isLocallyNoetherian_of_affine_cover` takes exactly those two hypotheses and
  concludes `IsLocallyNoetherian X`.
- Conversely, `IsLocallyNoetherian.component_noetherian` gives
  `IsNoetherianRing Γ(X, U)` for each `U : X.affineOpens`. Applying this to the
  ranges of the canonical affine cover supplies a covering of the node's form.
  `Scheme.isAffine_affineCover` in `Mathlib.AlgebraicGeometry.AffineScheme` verifies
  that these charts are affine. Thus the apparently stronger every-affine-open
  presentation has exactly the same truth conditions as the node's existential
  covering presentation. This is a proved equivalence, not a definitional equality.
- Mathlib also packages the equivalence for an actual affine open cover as
  `isLocallyNoetherian_iff_of_affine_openCover (𝒰 : Scheme.OpenCover.{v, u} X)
  [∀ i, IsAffine (𝒰.X i)] : IsLocallyNoetherian X ↔
  ∀ i, IsNoetherianRing Γ(𝒰.X i, ⊤)`. Its proof uses `IsOpenImmersion.ΓIsoTop`
  to identify chart sections with sections on their open images. The variant
  `isLocallyNoetherian_iff_of_iSup_eq_top` directly uses opens inside `X`.
- For an open subscheme `U : X.Opens`, Mathlib's instance at lines 158–159 takes
  `[IsLocallyNoetherian X]` and concludes `IsLocallyNoetherian U`, by applying
  `isLocallyNoetherian_of_isOpenImmersion U.ι`. The latter's full signature is
  `{X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] [IsLocallyNoetherian Y] :
  IsLocallyNoetherian X`.
- The justification via finite type is already available: the immersion instance
  in `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, line 190, gives
  `[IsImmersion f] → LocallyOfFiniteType f`; and
  `LocallyOfFiniteType.isLocallyNoetherian`, in the recorded Noetherian module,
  takes `{X Y : Scheme} (f : X ⟶ Y) [LocallyOfFiniteType f]
  [IsLocallyNoetherian Y]` and concludes `IsLocallyNoetherian X`.
- The final sentence is a convention about the target, not a further property of
  a morphism: for `f : X ⟶ Y`, it is rendered as `[IsLocallyNoetherian Y]`.
  It imposes no local Noetherian condition on `X` or finite type condition on `f`.

Dependency declarations read in full:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`. Scheme is a locally ringed space locally
  isomorphic to spectra, and scheme morphisms are locally ringed space morphisms.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, from
  `Mathlib.RingTheory.Noetherian.Defs`. It abbreviates `IsNoetherian R R`;
  `isNoetherianRing_iff_ideal_fg` explicitly identifies it with every ideal
  being finitely generated. The Noetherian scheme class uses this declaration,
  not a private ring predicate. Both dependencies are Mathlib leaves.

Edge cases checked against the source and the existing declarations: the empty
scheme satisfies the condition, including an empty covering (the covering equation
then forces `⊥ = ⊤`). No nonempty or finite index requirement appears in the
cover theorem; its index is a general Sort. An affine spectrum has the expected
condition `IsLocallyNoetherian (Spec R) ↔ IsNoetherianRing R`, as proved by
`isLocallyNoetherian_Spec` in the same module, including the zero ring. An arbitrary
open, including the empty open, is covered by the open-subscheme instance. The
scheme universe is unrestricted and there is no independently smaller universe
of test schemes. Local Noetherianness is not confused with the separate
quasi-compact condition in `IsNoetherian`.

Searches made on 2026-10-11:

- `msearch.py E1 pqf-def-locnoeth leanfinder` with query
  "A scheme is locally Noetherian if it admits an affine open covering with
  Noetherian rings of sections": eight hits, including the existing class,
  `isLocallyNoetherian_of_affine_cover`, both cover equivalences and
  `IsLocallyNoetherian.component_noetherian`. Signatures were verified locally;
  the search service's paraphrased docstring is not used instead of the source.
- `msearch.py ... loogle` with query
  "AlgebraicGeometry.IsLocallyNoetherian,
  AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover": one hit, the
  affine open cover equivalence in `Mathlib.AlgebraicGeometry.Noetherian`.
- `msearch.py ... grep` with expression
  `class IsLocallyNoetherian|isLocallyNoetherian_of_affine_cover|isLocallyNoetherian_iff_of_affine_openCover|isLocallyNoetherian_of_isOpenImmersion`
  in `AlgebraicGeometry`: six hits, locating the class and cover results.
  Direct reading of `Noetherian.lean` located and verified the open-immersion
  lemma and open-subscheme instance as well.
- `rg -n 'pqf-def-locnoeth'` in the upstream `WeilConjectures` source: no hits.
  `rg -n 'IsLocallyNoetherian|LocallyNoetherian'` there finds many uses of Mathlib's
  class, including its finite type permanence theorem, but no competing definition.
- `rg -n 'pqf-def-locnoeth|IsLocallyNoetherian|LocallyNoetherian'` in
  `lean/Sheaf` finds a blueprint citation in `FiniteSurjectiveAffineTarget.lean`;
  no alternative local Noetherian predicate is defined. A declaration-pattern
  search `class IsLocallyNoetherian|def .*LocallyNoetherian|abbrev .*LocallyNoetherian`
  in the upstream source, project modules and `dag/lean_names_upstream.json`
  has no hits.

The stage-1 candidate says the two formulations agree theorem-level rather than
by reduction. That equivalence is already proved in Mathlib; stage-2's one-definition
rule therefore calls for the existing class and its supporting declarations, not
another cover predicate. No statement correction, new node or dependency module
is needed. No statement is disputed. Existing declarations require no delivered
module to compile (brief-stage2 §1 and §5).

## Second reading by E1

I independently read the sandbox node and its `lean` record, both dependency
nodes, and the actual declarations in Mathlib's `Scheme.lean`,
`RingTheory/Noetherian/Defs.lean`, `AlgebraicGeometry/Noetherian.lean`,
`AffineScheme.lean`, and `Morphisms/Immersion.lean`. There is no delivered module,
new definition node, dependency module, or statement correction to review.

Source reading: the local Stacks checkout is absent, so I read the primary-source
pages for [01OV](https://stacks.math.columbia.edu/tag/01OV),
[01T5](https://stacks.math.columbia.edu/tag/01T5), and
[01T6](https://stacks.math.columbia.edu/tag/01T6), then independently read the raw
Stacks `.tex` files at
[properties.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex)
(labels `section-noetherian`, `definition-noetherian`,
`lemma-locally-Noetherian`) and
[morphisms.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex)
(labels `lemma-immersion-locally-finite-type`, `lemma-finite-type-noetherian`).
The surrounding section adds no field, separation, finiteness, or nonemptiness
hypothesis. The characterization explicitly equates the pointwise definition,
the every-affine-open formulation, and existence of one Noetherian affine cover.

The node's object/hypothesis/clause list, matched with Lean:

1. An arbitrary scheme X: `class IsLocallyNoetherian (X : Scheme) : Prop`.
   Verdict: exact object, with no added hypotheses. The recorded scheme dependency
   is `Scheme`, whose `local_affine` field supplies affine neighbourhoods in a
   locally ringed space; its `Hom` is a locally ringed-space morphism.
2. Existence of an affine open family covering X: in
   `isLocallyNoetherian_of_affine_cover`, `{S : ι → X.affineOpens}` and
   `(hS : (⨆ i, S i : X.Opens) = ⊤)` render the family and covering equation.
   Verdict: exact. Conversely every scheme has `X.affineCover`, its charts are
   affine by `Scheme.isAffine_affineCover`, and the class field supplies the
   Noetherian rings on their affine open images. Thus using the class does not
   change existence into a stronger assumption: the two implications are already
   proved in Mathlib.
3. Each ring of sections is Noetherian: `(hS' : ∀ i, IsNoetherianRing Γ(X, S i))`.
   Verdict: exact same section rings. `IsNoetherianRing` is the dependency's
   self-module Noetherian predicate; `isNoetherianRing_iff_ideal_fg` identifies it
   with every ideal being finitely generated. The class field
   `component_noetherian : ∀ (U : X.affineOpens), IsNoetherianRing Γ(X, U)`
   and `isLocallyNoetherian_iff_of_iSup_eq_top` give the reverse direction.
   `isLocallyNoetherian_iff_of_affine_openCover` also handles actual open-cover
   charts, using `IsOpenImmersion.ΓIsoTop` to identify their rings with these
   sections. No second ring or Noetherian predicate is introduced.
4. Open subschemes preserve the property: the existing lemma
   `isLocallyNoetherian_of_isOpenImmersion {Y : Scheme} (f : X ⟶ Y)
   [IsOpenImmersion f] [IsLocallyNoetherian Y] : IsLocallyNoetherian X`
   specializes to `U.ι`; the instance at Noetherian.lean:158–159 does precisely
   that for every `U : X.Opens`. Verdict: exact open-subscheme consequence, with
   no quasi-compactness or affine hypothesis on U.
5. The remark's justification: Immersion.lean:190 provides
   `(f : X ⟶ Y) [IsImmersion f] : LocallyOfFiniteType f`.
   `LocallyOfFiniteType.isLocallyNoetherian` takes `(f : X ⟶ Y)` with
   `[LocallyOfFiniteType f] [IsLocallyNoetherian Y]` and concludes
   `IsLocallyNoetherian X`. Verdict: the two cited Stacks implications are present;
   finite type is only used in this implication, never as an assumption in the
   definition or the target convention.
6. A locally Noetherian morphism situation means its target is locally
   Noetherian: for `f : X ⟶ Y`, this is `IsLocallyNoetherian Y`.
   Verdict: exact convention, not a new morphism predicate or an assertion that
   an arbitrary source X is locally Noetherian.

Edge cases: an empty index family is allowed by the arbitrary Sort index of the
cover theorem; its covering equation forces the scheme to be empty. The class
then holds, as for the spectrum of the zero ring. The equivalence
`isLocallyNoetherian_Spec {R : CommRingCat} :
IsLocallyNoetherian (Spec R) ↔ IsNoetherianRing R` includes the zero ring.
The empty open subscheme is included by the unrestricted Opens instance.
Infinite covers are permitted; `IsNoetherian` (which additionally requires
`CompactSpace X`) is not used as a replacement. The scheme universe is arbitrary;
`Scheme.OpenCover.{v, u}` and the arbitrary Sort index do not impose a small
universe restriction. There is no characteristic, natural-number parameter,
module, or zero-object condition to exclude further cases.

Independent searches, using different wording from the worker (2026-10-11):

- LeanFinder via `msearch.py`: "Every affine chart of a scheme has a Noetherian
  coordinate ring, equivalently one covering does". Eight hits, including
  `component_noetherian`, both affine-cover equivalences, and
  `isLocallyNoetherian_of_affine_cover`; verified against actual source.
- Loogle via `msearch.py`:
  `AlgebraicGeometry.IsLocallyNoetherian, AlgebraicGeometry.Scheme.OpenCover`.
  Three hits: the chart instance, `isLocallyNoetherian_iff_openCover`, and the
  affine-cover equivalence. Again the source signatures were read.
- LeanSearch via `msearch.py`: "A scheme admitting a cover by affine opens with
  Noetherian sections is locally Noetherian". Service unavailable (Internal
  Server Error), recorded without a mathematical verdict; the other searches
  independently locate the exact declarations.
- Direct `rg` for `class .*Noetherian|def .*Noetherian|abbrev .*Noetherian|
  isLocallyNoetherian_iff|component_noetherian` in Mathlib's Noetherian module,
  upstream `WeilConjectures`, and the project's `lean/Sheaf`: the class and
  equivalences are in Mathlib; upstream occurrences use that same class, and
  project hits introduce no competing locally Noetherian scheme definition.

No mismatch was found. The class signature recorded in `lean.statement` is
verbatim the source signature before `where`; all supporting declarations in
`lean.declarations` are in the recorded module. The theorem-level equivalence
is sufficient for H4 and avoids a duplicate predicate. I changed only this
report by appending the independent reading; the worker's Lean record is kept.
H5/H6/H8/H9 introduce no new obligations here: no new definition, proof, module,
or declaration is delivered. Compilation is not applicable to an existing-only
record (brief-stage2 §1); the delivery preflight checks the existing declaration.
