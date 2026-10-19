## Worker report

States Stacks Project Tag 08R0, lemma-derived-diagonal, as
`Algebra.CotangentResolution.derived_diagonal_cotangent_vanishing` in
`Sheaf.RingTheory.DerivedDiagonalCotangentVanishing`.
Only the theorem proof is postponed (`sorry`). The canonical multiplication helper
has fully specified data and no postponed proof.

Clause-by-clause correspondence:

- Commutative rings and their homomorphism: `{A B : CommRingCat.{u}} (f : A ⟶ B)`.
  The same universe imposes no mathematical size restriction: any two rings can be
  represented in their common maximum universe. Zero rings are allowed.
- The standard cotangent complex of the recorded dependency is
  `cotangentComplex C (Arrow.mk f)`. The datum `C : Coherence.{u}` is the existing
  standard-resolution interface, not a replacement notion. Its existence is the
  recorded `Algebra.CotangentResolution.exists_coherence` theorem. Quantification
  over C makes the statement independent of choices of the specified standard model.
- The canonical multiplication is `derivedDiagonalMultiplication f P`.
  `P : ProjectiveResolution ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B B))`
  is any ordinary projective resolution of B as an A-module. It only chooses a
  representative for the derived tensor product; such resolutions exist for every
  module, by Mathlib's enough-projectives construction for ModuleCat. In each
  nonnegative homological degree apply `ModuleCat.extendScalars f.hom`, i.e.
  B tensor over A. Its augmentation followed by
  `ModuleCat.extendRestrictScalarsAdj.counit.app (ModuleCat.of B B)` sends
  b tensor p to b times the image of p in B. Thus this is the canonical
  multiplication, with its B-linear structure, rather than an arbitrary morphism.
  `HomologicalComplex.singleMapHomologicalComplex` supplies the canonical
  identification of the termwise extension of B[0] with the single complex of the
  ordinary tensor product. `extendMap` along `embeddingDownNat` places degree n
  in cochain degree -n and adds zero in positive degrees. Bounded-above complexes
  of projective modules are K-flat, so the localized source is exactly B tensor
  derived over A B. The target is the extended single complex B[0].
- The sole mathematical hypothesis is
  `hμ : IsIso (derivedDiagonalMultiplication f P)` in D(B). This is equivalent to
  the resolution-level multiplication being a quasi-isomorphism. No flatness of
  B over A, injectivity, finite presentation, or etaleness is assumed.
- The entire conclusion is `IsZero (cotangentComplex C (Arrow.mk f))`, i.e.
  zero-object vanishing of the full standard cotangent complex in D(B), not only
  vanishing of its first two cohomology modules.
- The explicit `HasDerivedCategory.{u + 1}` family chooses the localization
  universe used by the dependency. It adds no ring-theoretic assumption.

Dependencies read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` (the recorded declaration of
  def-weil-abstract-derived-category). This import is re-exported by the
  cotangent-resolution module.
- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Coherence`, `.cotangentComplex`, `.exists_coherence`.
  Read the full interface, its standard polynomial formulas, DifferentialModel,
  and comparison/functoriality requirements.
- Proof-only import `Sheaf.RingTheory.LocalizationCotangentVanishing`:
  `Algebra.CotangentResolution.localization_cotangent_vanishing`.
- The other proof dependency, lem-trf-cotangent-flat-base-change, has no recorded
  module at delivery time. Its node's complete statement is read and the square
  specialization is retained in the proof docstring; there is no module to import.
- Mathlib's `ProjectiveResolution`, `ModuleCat.extendScalars`,
  `ModuleCat.restrictScalars`, `ModuleCat.extendRestrictScalarsAdj`,
  `HomologicalComplex.singleMapHomologicalComplex` and `extendMap` provide
  the concrete canonical multiplication. The helper belongs to this item's
  canonical map and is recorded in lean.declarations, as authorized by the brief.

Source check: read literature/stacks-project/cotangent.tex at
lemma-derived-diagonal (Tag 08R0), including its proof. The node's expanded proof
uses base change to identify L[B/A] with L[B/B], then the identity localization
case to get zero. This full proof is in the theorem docstring.

Edge cases checked: A = B and f the identity gives ordinary derived multiplication
with its unit normalization; arbitrary localizations, including the zero ring,
are allowed; no Nontrivial instance occurs. A non-flat surjection is not silently
accepted merely because ordinary multiplication is an isomorphism: higher Tor in
its projective-resolution tensor remains present, so the IsIso hypothesis still
requires it to vanish. Infinite rings and infinite-rank resolutions are allowed.
The projective resolution can have nonzero terms in arbitrarily large homological
degrees; the construction does not truncate it. No statement correction or
STATEMENT-DISPUTED issue was needed.

Searches (full response digests are retained in sandbox searches.jsonl):

- msearch leanfinder: "derived tensor multiplication morphism cotangent complex
  vanishing"; eight hits concerning ordinary differentials, extension cotangents,
  and base-change tensor formulas, none the full derived criterion.
- msearch loogle: "DerivedCategory, curriedTensor, cotangentComplex"; no hit,
  unknown identifier curriedTensor in the search index.
- msearch grep, RingTheory: "cotangentComplex|curriedTensor|DerivedCategory";
  25 hits, mainly presentation cotangent complexes, no full derived criterion.
- msearch leansearch: "The cotangent complex vanishes when the canonical derived
  multiplication B tensor over A B to B is an isomorphism"; eight hits, including
  formallyEtale_iff, FormallySmooth.subsingleton_h1Cotangent and presentation-level
  cotangentComplex_injective_iff. They address low cotangent homology, not this
  full derived statement.
- rg in Mathlib/RingTheory, upstream WeilConjectures and side lean/Sheaf:
  "cotangent.*[Vv]anish|derived.*[Dd]iagonal|derivedDiagonalMultiplication";
  only neighboring cotangent lemmas and unrelated diagonal constructions.
- grep of the item id in upstream WeilConjectures: no match.
- Exact proposed declaration names checked against dag/lean_names_upstream.json,
  upstream WeilConjectures and side lean/Sheaf: no existing declaration.

Validation: scompile.py compiled the delivered module both as a sandbox file and
at its final module path, cleanly with no errors or warnings. No global build run.

## Second reading by Q95

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
