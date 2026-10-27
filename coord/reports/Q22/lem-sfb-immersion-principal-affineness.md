## Worker report

Stated `AlgebraicGeometry.isAffine_of_isImmersion_of_isAffineOpen_preimage_basicOpen_of_isClosed`
in `Sheaf.AlgebraicGeometry.ImmersionPrincipalAffineness`, with `sorry` as its only proof.
No definitions, extra nodes, dependency repairs, or statement corrections are needed. The item
node differs only in `lean`.

Source read: `literature/stacks-project/more-groupoids.tex`, lines 2770–2802,
Tag 0ABH (`lemma-get-affine`), including its explicit reference to Morphisms 0C3A;
`literature/stacks-project/morphisms.tex`, lines 2075–2103, Tag 0C3A (`lemma-get-affine`).
The node keeps exactly the statement of 0ABH and its accepted split follows the latter proof.
The module docstring records all five steps and their DAG inputs; no theorem is proved here.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| A is a commutative ring | `(A : Type u) [CommRing A]` |
| V is a scheme | `(V : Scheme.{u})` |
| j maps V to Spec A | `(j : V ⟶ Spec (CommRingCat.of A))` |
| j is quasi-compact | `[QuasiCompact j]` |
| j is an immersion | `[IsImmersion j]` |
| f is an element of A | `(f : A)` |
| D(f) consists of primes not containing f | `PrimeSpectrum.basicOpen f` |
| j inverse D(f) is affine | `hprincipal : IsAffineOpen (j ⁻¹ᵁ PrimeSpectrum.basicOpen f)` |
| j(V) intersect V(f) is closed in Spec A | `hclosed : IsClosed (Set.range j ∩ PrimeSpectrum.zeroLocus {f})` |
| V is affine | `IsAffine V` |

`PrimeSpectrum.basicOpen` has carrier `{p | f ∉ p.asIdeal}` (Mathlib
`RingTheory/Spectrum/Prime/Topology.lean:509`); its complement is
`PrimeSpectrum.zeroLocus {f}` by `basicOpen_eq_zeroLocus_compl` (line 521).
`IsAffineOpen U` means the actual open subscheme is affine
(`AlgebraicGeometry/AffineScheme.lean:251`). Thus `hprincipal` asserts affineness of
j's open inverse image, with its restricted structure sheaf, rather than affineness of
a set or an unrelated scheme. `Set.range j` is the image on underlying points;
closedness is in the whole spectrum, without assuming a closed subscheme structure on it.
All universes and variables are explicit; automatic implicit binding is disabled.
There is no domain, nonzero ring, Noetherian, finite-type, separatedness, or nonempty
hypothesis. The common universe is Mathlib's category of schemes; u is arbitrary.

Statement-dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  (line 42) and `Scheme.Hom` (line 74). Affineness uses Mathlib's `IsAffine`
  (`Mathlib.AlgebraicGeometry.AffineScheme:59`) and `IsAffineOpen` (line 251).
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` (line 470); `Spec.map` (line 479) was also read.
- `def-weil-closed-immersion`: its full `mathlib_match` explicitly records the
  immersion clause as `Mathlib.AlgebraicGeometry.Morphisms.Immersion`,
  `AlgebraicGeometry.IsImmersion` (line 45) and
  `IsImmersion.isImmersion_iff_exists` (line 155). The latter gives precisely
  closed-then-open factorization. The primary Lean record names `IsClosedImmersion`
  in `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (line 45), also read and imported.
  The full match is usable, so no duplicate immersion definition or record repair is needed.
- `def-weil-finite-type-morphism`: its recorded `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  is imported; the quasi-compact clause is its listed `AlgebraicGeometry.QuasiCompact`,
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact:43`. Its full signature and the
  `LocallyOfFiniteType` signature (FiniteType:43) were read. Only quasi-compactness is
  assumed here, as the node requires; no finite-type hypothesis was added.

The stated proof dependencies all have Mathlib bindings. Their modules are imported:
`RingTheory.Spectrum.Prime.Topology` for the basic-open basis and localization topology,
`AlgebraicGeometry.OpenImmersion` for localization as an open immersion,
`AlgebraicGeometry.Morphisms.ClosedImmersion`, `.Integral`, `.Separated`,
and `.UniversallyClosed` for the closed-immersion package, `.Affine` for
`IsAffineHom`, `isAffineHom_of_isAffine` and the local target criterion, and
`.Basic` for the open-cover affine-property interface. These proof imports are not public.
The statements' own dependency imports are public.

Edge cases checked before writing:

- Empty V is permitted, with empty image and empty affine inverse image.
- The zero ring A is permitted; its spectrum is empty, forcing V empty for such j.
- f = 1 makes D(f) the whole spectrum; `hprincipal` is the desired affineness of V
  and the complementary image is empty, so this case remains included.
- f = 0, or f nilpotent, makes D(f) empty; closedness is then closedness of the
  entire image. An immersion with closed image is a closed immersion, hence V is affine.
- A closed immersion is included for every f. No reducedness is imposed on V or A.
- The closedness condition matters: for A = k[x,y], V = A² minus the origin,
  j the open immersion, and f = x, the inverse image D(x) is affine but the
  complementary image is the punctured y-axis and is not closed. The condition
  correctly excludes this familiar nonaffine V.

Searches actually run with msearch.py (2026-10-24):

- LeanFinder: “A quasi compact immersion into Spec A is affine if the inverse image
  of D f is affine and the image intersect V f is closed”. Eight hits, including
  `Scheme.IsQuasiAffine.of_isImmersion`, `quasiCompact_iff_forall_affine`, and
  `IsClosedImmersion.hasAffineProperty`; these assert quasi-affineness or separate
  ingredients, not this criterion.
- Loogle: `AlgebraicGeometry.IsImmersion, AlgebraicGeometry.IsAffine`. Zero hits.
- LeanSearch: “An immersion in an affine scheme is affine when the inverse image of a
  principal open is affine and the image in the closed complement is closed”. Eight
  hits, including closed-immersion affineness, `IsImmersion` and the affine-open
  preimage/image lemmas. None is an exact match.
- Grep wrapper: `immersion.*affine|affine.*immersion`, restricted to
  `AlgebraicGeometry`. Twenty-five hits, including `QuasiAffine.lean` and
  `ClosedImmersion.lean`; no exact statement.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and proposed declaration, and concept searches
  `principal.*affine|affine.*principal|closed.*complement|complement.*closed`.
  No declaration for this criterion. In particular, the upstream
  `Mathlib/AlgebraicGeometry/Morphisms/Affine.lean` file was read in full: its
  dimension-at-most-one open-immersion theorem has different hypotheses.
  Upstream `Mathlib/AlgebraicGeometry/AffineScheme.lean` likewise only gives
  affineness of opens over a principal ideal ring, not the node's criterion.

Compilation: prescribed scompile.py passed both the private sandbox check and the
actual module check (2.5 s and 1.7 s after slot acquisition), with exit code 0 and
no warnings. The temporary type-inspection module was removed from the packet.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
