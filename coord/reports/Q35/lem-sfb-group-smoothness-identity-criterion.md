## Worker report

Item: lem-sfb-group-smoothness-identity-criterion. The delivery adds
`Sheaf.AlgebraicGeometry.GroupScheme.SmoothnessIdentityCriterion`, containing three
named theorem statements with `sorry` proofs. Their three full names are listed in
`lean.declarations`; together they state every conclusion of the unchanged node.
There are no new definitions, auxiliary axioms, dependency repairs, or statement
corrections. The node copy changes only `lean`.

The source material read is the recorded node and all its statement-dependency
records, together with the declarations in their recorded modules. The locally
available primary-source proof is Stacks `morphisms.tex`,
`lemma-noetherian-finite-type-finite-presentation` (01TX), `definition-smooth`
(01V5), `lemma-smooth-characterize` (01V6), and
`lemma-set-points-where-fibres-smooth` (02V4), plus `groupoids.tex`,
`definition-group-scheme`, `lemma-base-change-group-scheme`, and the
residue-field-point/translation argument in
`lemma-group-scheme-field-geometrically-irreducible`. The BLR places are retained
as the node's source; no local BLR scan was available or claimed to have been read.
The theorem docstrings give the node's argument step by step, divided between
its fibre, open-locus, and Dedekind conclusions.

Hypotheses and clauses, matched to Lean:

* Schemes and an arbitrary base: `{S : Scheme.{u}}` and `G : Over S`; the map
  `G.hom` is the given structure morphism. The universe `u` is explicit and
  unrestricted, not fixed to a small universe.
* Multiplication, identity, inverse, and group diagrams: `[GrpObj G]`, using the
  recorded `CategoryTheory.GrpObj` in the cartesian monoidal slice category. The
  identity section is `η[G].left`, the scheme morphism underlying the group
  object's canonical unit. It has source S, not Spec of an independently chosen
  field, and is not an arbitrary section. No new relative-group predicate is
  needed: the recorded generic group-object declaration applies directly over S.
* Locally Noetherian base: `[IsLocallyNoetherian S]` in the first two statements.
* Flat and locally finite type group scheme: `[Flat G.hom]` and
  `[LocallyOfFiniteType G.hom]`. There is no `QuasiCompact` hypothesis.
* Smooth at a point: membership in the existing `G.hom.smoothLocus`.
  Mathlib defines this open subset for locally finitely presented morphisms;
  the needed instance follows from the recorded local-Noetherian finite-type
  theorem, without adding a local-finite-presentation assumption. The existing
  `exists_smooth_of_formallySmooth_stalk`, `preimage_smoothLocus_eq`, and
  `smoothLocus_eq_top_iff` identify membership with a smooth open neighbourhood.
* Every base point s: `(s : S)` in
  `AlgebraicGeometry.GrpObj.smooth_fiber_iff_smooth_identity`.
  The left side quantifies over `x : G.hom.fiber s` and asserts that
  `G.hom.fiberι s x` belongs to the smooth locus of the original morphism.
  Thus it refers to smoothness of G→S at the points of the fibre, not merely
  smoothness of a different map. The recorded `Scheme.Hom.fiberHomeo` identifies
  these points with all source points over s.
* If and only if smooth at e(s): the right side is exactly
  `η[G].left s ∈ G.hom.smoothLocus`, joined by `↔`.
* The displayed U is open: the first conjunct of
  `AlgebraicGeometry.GrpObj.smooth_identity_locus_open_and_smooth` is
  `IsOpen {s : S | η[G].left s ∈ G.hom.smoothLocus}`.
* G_U→U is smooth: the second conjunct is
  `Smooth (G.hom ∣_ (η[G].left ⁻¹ᵁ G.hom.smoothLocus))`.
  The open inverse image is exactly the displayed set U, equipped with its
  existing open-subscheme structure; restriction is the standard scheme open
  restriction, equivalently the base change along U→S. No arbitrary open or
  arbitrary comparison map is supplied as additional data.
* The Dedekind case is
  `AlgebraicGeometry.GrpObj.finite_nonsmooth_identity_of_dedekind` with
  `(A : Type u) [CommRing A] [IsDedekindDomain A]` and
  `(hdim : ringKrullDim A = 1)`, and `G : Over (Spec (.of A))`.
  Mathlib's class already includes Noetherianness, integral closedness, the
  domain condition, and dimension at most one. The equality retains the node's
  exact dimension-one convention (Mathlib alone also allows fields). The affine
  spectrum is consequently locally Noetherian; no extra base hypothesis is
  imposed. Using the literal spectrum realizes “S is the spectrum of A”.
* Generic fibre smooth: the instance binder is
  `[Smooth (G.hom.fiberToSpecResidueField ⟨⊥, Ideal.isPrime_bot⟩)]`.
  The marked point is precisely the zero prime of the domain. Its residue
  field is canonically the fraction field, so this is the actual generic
  fibre, not an arbitrary field base change.
* S minus U is finite: the first conjunct is
  `{s : Spec (.of A) | η[G].left s ∉ G.hom.smoothLocus}.Finite`.
* Every point of that complement is closed: the second conjunct says
  `∀ s, η[G].left s ∉ G.hom.smoothLocus → IsClosed ({s} : Set (Spec (.of A)))`.
* No commutativity, separatedness, quasi-compactness of G, or Néron mapping
  property is imposed. The node's preliminary explanation of “separated” does
  not state such a hypothesis, and none is added.

The dependency declarations reused, with their modules:

* def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`, and `Scheme.Opens`.
* def-sc-group-scheme: `Mathlib.CategoryTheory.Monoidal.Grp`,
  `CategoryTheory.GrpObj`, extending `MonObj`; the canonical unit is
  `MonObj.one`, written using its public scoped notation `η[G]`.
* def-weil-flat-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` (its stalkwise equivalence was also read).
* def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` and `Scheme.Hom.smoothLocus`.
* def-weil-finite-type-morphism:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`.
* def-weil-closed-immersion:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; its recorded module is imported as
  required by the statement-dependency rule, although no separatedness
  assumption is part of this theorem.
* pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
* def-pc-scheme-fibre: `Mathlib.AlgebraicGeometry.Fiber`,
  `Scheme.Hom.fiber`, `fiberι`, and `fiberToSpecResidueField`.
* pqf-lem-lft-fp-locnoeth has no Lean record and is a Mathlib leaf: its match
  is `LocallyOfFinitePresentation.iff_locallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Noetherian`, whose underlying instance supplies
  local finite presentation here.
* lem-weil-pbc-smooth-local-on-source is likewise a Mathlib leaf, matched by
  `IsZariskiLocalAtSource.iff_of_iSup_eq_top` in
  `Mathlib.AlgebraicGeometry.Morphisms.Basic`. This module is already imported
  through the smoothness module, without another declaration or predicate.
* lem-weil-pbc-morphism-from-spec-field is the Mathlib leaf matched by
  `Scheme.SpecToEquivOfField`,
  `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`, and
  `Scheme.fromSpecResidueField_apply`, in
  `Mathlib.AlgebraicGeometry.ResidueField`, imported for the future proof.
* lem-sfb-scheme-flat-smooth-point-base-change:
  `Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange`,
  `AlgebraicGeometry.smooth_at_point_pullback_snd_iff_of_flat`.
* def-sc-group-scheme-translate and lem-sc-translation-automorphism:
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`,
  `AlgebraicGeometry.GrpObj.mulLeft`, `mulRight`, `conjBy`, `translate`,
  `mulLeftIso`, and `mulRightIso`.
* lem-sc-noetherian-closed-points-finite:
  `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints`,
  `AlgebraicGeometry.finite_of_isClosed_of_closed_points`.
* Dedekind terminology and ring dimension use the existing
  `IsDedekindDomain` in `Mathlib.RingTheory.DedekindDomain.Basic` and
  `ringKrullDim` in `Mathlib.RingTheory.KrullDimension.Basic`.

Searches for an existing exact statement (all msearch calls use group Q35 and
this item; the original machine-readable results are in sandbox searches.jsonl):

* LeanFinder: “For a flat locally finite type group scheme over a locally
  Noetherian base, smoothness of a fibre is detected at the identity section;
  the smooth base locus is open.” Eight hits, chiefly general smooth-locus
  definitions and affine smoothness results. None states this criterion.
* Loogle: `"Smooth", "GrpObj"`. One hit,
  `AlgebraicGeometry.smooth_of_grpObj` in
  `Mathlib.AlgebraicGeometry.Group.Smooth`. Its signature and proof were read:
  it concerns a geometrically reduced group scheme over a field, with global
  smoothness conclusion. It is not this identity-point/family criterion and
  supplies neither the open base locus nor the Dedekind conclusion.
* msearch grep: `smooth.*identity|identity.*smooth|smooth.*unit|unit.*smooth`
  in Mathlib/AlgebraicGeometry: no hits.
* LeanSearch: “Smoothness of a flat group scheme is detected at the identity
  of each fibre, with an open smooth base locus and a finite bad locus over a
  Dedekind domain.” Eight hits, general smoothness definitions and ring facts;
  no exact statement.
* Local rg of the same identity/unit pattern in lean/WeilConjectures and
  lean/Sheaf found unrelated purity, orbit, and tangent-space results; the
  closest tangent-dimension module does not state this assertion. Searching
  for the item id in lean/WeilConjectures and dag/lean_names_upstream.json
  found no existing declaration. Searching the chosen theorem names across
  Mathlib, WeilConjectures, Sheaf and the upstream-name index found no clashes.
* Local rg for smoothLocus and unit-section notation found the existing
  `Scheme.Hom.smoothLocus` and canonical `MonObj.one` construction; these are
  used directly. No helper notion was introduced.

Edge cases checked before writing:

* Empty base: the fibre criterion has no s to check, U is empty, and the
  restriction has empty source and target, so its smoothness is correct.
* An empty fibre over an existing base point cannot occur for a group scheme:
  the identity section provides a residue-field-valued point in that fibre.
  The implication from all fibre points therefore includes the identity.
* U may be empty or the whole base. Standard open restriction admits both.
* A globally smooth group gives an empty finite bad set. Conversely a
  non-smooth finite flat group such as μ_p in characteristic p does not
  satisfy the identity-smooth condition; no false smoothness is forced.
* Non-quasi-compact group schemes are allowed: no finite-type or compactness
  class is assumed for G. Finiteness uses only the Noetherian affine base.
* Noncommutative groups and arbitrary residue fields/characteristics remain
  allowed; the proof uses residue-field-valued points, not closed-point
  density over an algebraically closed field.
* A field is intentionally excluded from the Dedekind clause by `hdim`,
  matching the node's explicit convention. The zero ring is excluded by the
  domain condition. These exclusions do not affect the general-base clauses.

Validation: scompile.py compiled the sole delivered module on the server in
sandbox and library-module modes, 1.7 seconds each, with no errors or warnings.
No local or global library build was run. All theorem bodies are `by sorry`;
there are no data definitions. Every variable and universe is explicitly bound.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
