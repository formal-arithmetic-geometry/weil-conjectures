## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothDVRGenericLineExtension` states
`AlgebraicGeometry.exists_invertible_extension_of_smooth_dvr`, with one named
`sorry` and no definitions or additional theorems. The accepted stage-1 split,
source, statement and dependency lists are unchanged. No repair note exists.
The inherited refusal concerned re-splitting at stage 1, whereas the current
assignment and queue entry are stage 2 and the item has no Lean record.
The stage-handoff paragraph of brief-stage2 explicitly permits this work.

Hypotheses and clauses, matched individually:

- A discrete valuation ring R: `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. The last class is the recorded Mathlib local-PID,
  nonfield definition, and requires the explicitly supplied domain instance.
- Its fraction field K: `(K : Type u) [Field K] [Algebra R K]
  [IsFractionRing R K]`. The algebra map supplies the specified canonical map
  `Spec K -> Spec R`, as `Spec.map (CommRingCat.ofHom (algebraMap R K))`.
- A scheme Y and its structural morphism: `(Y : Scheme.{u})
  (f : Y ⟶ Spec (CommRingCat.of R))`.
- Smoothness: `[Smooth f]`, the dependency's affine-local smoothness predicate.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the two
  recorded conditions in def-weil-finite-type-morphism. Although smoothness
  implies the former, spelling out the source's finite-type condition does
  not restrict it further.
- The scheme-theoretic generic fibre Y_K: the actual chosen categorical
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))`.
- An arbitrary invertible module L on Y_K: the binder `L` has that scheme's
  `.Modules` category as its type, with `[L.IsInvertible]`.
- An extension on Y: `∃ M : Y.Modules, M.IsInvertible ∧ ...`.
- The restriction isomorphism: `Nonempty ((Scheme.Modules.pullback
  (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M ≅ L)`.
  The first projection is Y_K -> Y, so its module pullback is exactly M|Y_K.
  This is an isomorphism of sheaves of modules, not merely a stalkwise claim.
- The final sentence of the node imposes no further conditions: the existential
  asserts no uniqueness; there are no properness, excellence, separatedness,
  connectedness, dimension or residue-characteristic hypotheses.

Recorded dependency declarations read and used:

- def-sc-discrete-valuation-ring: `IsDiscreteValuationRing`, in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`; full signature requires
  `[CommRing R] [IsDomain R]` and extends local and principal-ideal-ring classes.
- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`; schemes are locally ringed spaces with
  local affine charts and morphisms are locally ringed-space morphisms.
  This dependency is publicly available through the geometric imports.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `AlgebraicGeometry.QuasiCompact` in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
  The latter is publicly imported by the former.
- def-pc-base-change: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
  especially the documented convention that X_T is `Limits.pullback f T.hom`
  and X_T -> X is `pullback.fst`. Its declaration
  `Scheme.Modules.moduleBaseChange` is module pullback along the canonical
  base-change map; this statement uses the underlying scheme pullback directly,
  as the node's Lean note instructs. No private replacement is introduced.
- def-sc-invertible-module: `AlgebraicGeometry.Scheme.Modules.IsInvertible`, in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, stating local
  isomorphism with the structure sheaf on an open neighbourhood of each point.
  This is exactly local freeness of rank one (hence quasi-coherence).
- Restriction uses the existing `AlgebraicGeometry.Scheme.Modules.pullback`
  from `Mathlib.AlgebraicGeometry.Modules.Sheaf`, whose signature and definition
  as the ringed-sheaf pullback were read. It is the ordinary module pullback,
  available publicly from the invertible-module dependency.

All recorded proof-dependency modules are imported, publicly if also used in the
statement and otherwise privately. These include the DVR dimension theorem
(TFAE), regular schemes (IsRegularScheme), smooth ascent (RegularRingSmoothAscent),
regular-local UFD factorization (RegularLocalUFDBoundaryFactorization), divisor
line bundles (EffectiveCartier), and module gluing (SiteModuleSheafGluing).
Mathlib affine-stalk-localization and open-immersion/base-change inputs are
available through the geometric dependencies, and Noetherian open restriction
is imported from Mathlib.AlgebraicGeometry.Noetherian.
`lem-sfb-quasiaffine-line-effective-divisor` and
`lem-sfb-cartier-extension-factorial-complement` have neither a Lean record nor
a Mathlib match in the live read clone. They are proof-only dependencies, not
notions needed to type this statement; their future module imports are left to
the maintainer when those statements land, per stages/2-statements section 3.7.
Their natural-language uses are included in this theorem's seven-step proof
docstring. No import is omitted to avoid a cycle.

Edge cases checked before writing:

- Empty Y is allowed; the structure sheaf on the empty scheme extends its unique
  module up to isomorphism. No Nonempty or inhabited binder excludes it.
- Nonproper and nonseparated Y, and disconnected schemes, are allowed; the finite
  affine-cover proof uses quasi-affine overlaps and never assumes affine overlaps.
- Arbitrary and mixed residue characteristic are allowed. R is genuinely a DVR,
  so fields are excluded exactly by the source definition, rather than accidentally.
- Relative dimension zero and higher dimensions are allowed with no dimension bound.
- No density or nonemptiness of the generic fibre is assumed as additional data.
- There is no demand that two extensions be equal or uniquely isomorphic.
- Universe `u` is arbitrary. R, K and Y inhabit a common universe required by
  Scheme morphisms, which can always be chosen large enough. The fraction-field
  condition concerns actual rings and no quantification over an independent
  lower universe makes it vacuous. The module category is the project's standard
  `Scheme.Modules`, not a smaller unrelated coefficient category.

Source inspection: read the full Stacks Tag 0BD9 lemma and proof in divisors.tex,
including its affine Cartier-divisor construction and gluing. The statement is
its application to the generic-fibre open in a regular smooth DVR scheme.
The accepted seven-step DAG proof is reproduced in the docstring. In step 3,
r = 0 means that the selected parameter subfamily is empty, rather than that a
positive-dimensional regular local ring has an empty full parameter system.
No mathematical statement change was needed.

Searches made (prescribed msearch wrapper, plus direct source searches):

- leanfinder: "Every invertible sheaf on the generic fiber of a smooth finite
  type scheme over a discrete valuation ring extends to the whole scheme".
  Eight hits concerned ValuativeCommSq, function fields and valuation rings;
  none states a line-bundle extension theorem.
- leansearch: "Extend an invertible sheaf from the generic fiber of a smooth
  scheme over a discrete valuation ring". Eight hits included ModuleCat.tilde,
  ValuativeCommSq.i₁, structureSheafInType, basicOpenIso and Proj valuative
  criteria; none states this theorem.
- loogle: `IsDiscreteValuationRing, IsInvertible`: zero hits, unknown identifier
  IsInvertible (the project definition is not in Mathlib).
- msearch grep: `extend|extension|generic` under AlgebraicGeometry/Modules:
  one hit, Mathlib/AlgebraicGeometry/Modules/Tilde.lean:304,
  `TopCat.Sheaf.extend_hom_app`, an unrelated sheafification calculation.
- Direct rg searches in both `lean/WeilConjectures` and `lean/Sheaf` for
  `generic.*([Ii]nvertible|[Ll]ine)|([Ii]nvertible|[Ll]ine).*generic` found
  generic stalks, principal parts, divisors and generic affine-line points,
  none extending line bundles over a smooth DVR scheme.
- Direct searches for `extend.*invertible|invertible.*extend` found unrelated
  scalar-extension, blowup and generic-stalk results. The proposed declaration
  `exists_invertible_extension_of_smooth_dvr` and the item's blueprint id had
  no existing declaration in either source tree.
- Searched the node's recorded dependencies and read their source interfaces.
  No missing notion, duplicate definition or unusable dependency interface was found.

Validation: the prescribed scompile wrapper compiled the delivered module in
sandbox mode (5.7 s) and at its library module path (4.3 s), both clean.
Every variable and universe is explicitly bound; `autoImplicit` is disabled.
No STATEMENT-DISPUTED issue or node fault is outstanding.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
