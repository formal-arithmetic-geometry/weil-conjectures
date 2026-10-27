## Worker report

The delivery states `AlgebraicGeometry.isOpen_veryTameLocus` in
`Sheaf.AlgebraicGeometry.VeryTameLocusOpen`, with `sorry` as its entire proof.
It also extends the two recorded definition interfaces under §1(B). No definition
contains postponed data and no theorem is proved.

Source read: the local ILO PDF, Exposé VI 3.1, 3.4--3.7 (printed pp.73--76),
and Exposé VIII 5.3.1, 5.3.2(i), 5.3.6 (printed pp.123--124). VI 3.1 supplies
exactly the three geometric-point tests; VI Corollary 3.6 supplies the local
very-tame neighborhood; VIII 5.3.2(i) obtains openness from its etale image.
The strict inert pullback assertion compares precisely the same stalk objects.
The current node already includes separatedness and explicitly excludes a
separatedness assumption on the source. It is unchanged outside `lean`.
There is no new statement dispute or statement correction in this delivery.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The finite group is `{H : Type v} [Group H] [Finite H]`; its universe is
  independent of the scheme universe.
- The locally Noetherian fs log scheme is `Y : FineSaturatedLogScheme.{u}`.
  Its existing fields `locallyNoetherian` and `fineSaturated` are the recorded
  certificates, not extra assumptions. `a : FSLogGroupAction H Y` supplies
  actual log automorphisms, their group laws, and underlying automorphisms.
- Separatedness is `[Y.scheme.IsSeparated]`. Mathlib defines this by the
  terminal structural morphism's closed diagonal; equivalently it is the
  structural morphism to Spec Z. Log regularity is `hregular : Y.IsLogRegular`,
  whose recorded definition gives regular strict-local stratum quotients and
  the dimension-plus-characteristic-rank equality at every geometric point.
- The set T is `a.toEtaleLogGroupAction.veryTameLocus`. Its definition quantifies
  over every `Ω : Type u` with `Field Ω`, `IsAlgClosed Ω`, and
  `t : Spec (.of Ω) ⟶ Y.scheme`, conditioned by
  `(Scheme.SpecToEquivOfField Ω Y.scheme t).1 = y`. Thus it includes the residue
  embedding and does not replace geometric inertia by an ordinary stabilizer.
- The first test in `IsVeryTameAt` is
  `IsUnit (Nat.card {g : H // t ≫ (a.baseAction g).hom = t} : Ω)`.
  Since the stabilizer is finite, this is invertibility of its order in the
  geometric residue extension, equivalently in the point's residue field.
- The second test is `Associated` for every log section and its pullback in
  every pointed relative etale diagram. Associated germs are exactly the same
  class in the recorded characteristic monoid (the quotient by log units).
- The third test places each difference of pulled-back and original regular
  function germs in `M.nonunitIdeal t`. All germs have section representatives,
  so this is identity on the actual quotient ring, including nilpotents, hence
  identity on its affine spectrum. It is not merely identity on its points.
- Openness is `IsOpen ...`; invariance is the membership iff under every
  `(a.baseAction g).hom`, including both directions.
- For pullback the statement quantifies over an arbitrary `Y' : Scheme.{u}`,
  arbitrary `M' : EtaleLogStructure Y'`, its `EtaleLogGroupAction H M'`, and
  the actual log map `v : EtaleLogMap M' Y.logStructure`.
  `a'.IsEquivariant a.toEtaleLogGroupAction v` asserts equality of both
  composites as scheme and log-sheaf maps. `v.IsStrictEtale` is the recorded
  strictness-plus-etaleness predicate, with bijective section maps on all
  relative etale objects. No source fs, local Noetherianity, log regularity,
  separatedness, surjectivity, or global tameness is assumed.
- For the same acting group, the canonical inertia homomorphism sends an
  element to that same element. Its being an isomorphism is exactly the
  displayed iff for every geometric point and `g : H`: fixing `t'` iff fixing
  `t' ≫ v.base`. This avoids choosing an unrelated isomorphism of groups.
- The conclusion supplies `hln : IsLocallyNoetherian Y'` and
  `hfs : M'.IsFineSaturated`, and asserts
  `(FineSaturatedLogScheme.mk Y' hln M' hfs).IsLogRegular` for these exact data.
  The final set equality is `a'.veryTameLocus = Set.preimage ... T`.
  No log structure is replaced by a chosen isomorphic structure.

Dependency declarations used and read with their signatures/docstrings:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `EtaleLogStructure`, `FineSaturatedLogScheme`,
  `FineSaturatedLogScheme.IsLogRegular`, `EtaleLogHom`, log germs,
  `EtaleLogStructure.nonunitIdeal`, characteristic monoid, and fs charts.
- `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction`, its
  `baseAction`, `logMap`, and group laws; extended as described below.
- `Sheaf.AlgebraicGeometry.VeryTameFSLogAction`:
  `FSLogGroupAction.IsVeryTame`; the original declaration body is preserved
  verbatim. The pointwise helper uses its exact two germ tests.
- `Sheaf.AlgebraicGeometry.LogIdealChartPresentation`: `EtaleLogMap`,
  `EtaleLogHom.toLogMap`, `EtaleLogMap.CompEq`, `EtaleLogMap.IsStrictEtale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` (through Separated):
  `AlgebraicGeometry.Scheme.IsSeparated`, `IsSeparated`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`;
  `IsAlgClosed` is the recorded algebraically closed-field class.

Proof-only imports include the recorded modules of
`lem-trf-ind-etale-strict-local-invariance`,
`lem-trf-closed-immersion-strict-localization-cartesian`,
`lem-weil-pbc-strict-henselization-functoriality`, and
`lem-sbc-strict-local-roots-of-unity`. Their source declarations/docstrings
were read. The other proof nodes have no usable recorded module, or are
Mathlib facts already reached via imports. The pointwise diagonal Kummer
neighborhood node is not yet recorded; no theorem about it is invented here.
The theorem docstring carries all five existing proof steps, with the
strict-local comparison, every-geometric-lift argument, diagonal chart,
stratum calculation, open images, conjugation, and empty-union case.

Edge cases checked: empty Y and empty locus (vacuous point quantification and
empty union); empty Y' (no source point needed); trivial H (order 1 and identity
action); ineffective actions (no faithful-action or generic-freeness hypothesis);
characteristic zero and residue characteristic dividing an inertia order;
nontrivial residue automorphisms (geometric morphism equality, not point
fixing); unit-only/trivial log structure (stratum is the entire strict local
scheme); nilpotent stratum quotient (ring identity test); nonsurjective strict
etale maps; and nonseparated Y' (no separatedness binder). All universes and
variables are explicitly bound, with `autoImplicit false`.

Searches made for the item and interfaces:

- `msearch.py` LeanFinder: “The very tame locus of a finite group action on a
  log regular scheme is open and preserved by strict inert etale maps”. Eight
  hits: algebra etale/unramified/smooth loci, Scheme.Etale, generalizing-map
  openness and IsEtale APIs. None states the logarithmic inertia conditions.
- `msearch.py` Loogle: `"VeryTame"`. Zero hits.
- `msearch.py` grep: `very.?tame|veryTameLocus|logRegular` in AlgebraicGeometry.
  Zero Mathlib hits.
- `msearch.py` LeanSearch: “The very tame locus of a finite group action on a
  log regular scheme is open”. Eight hits: smooth/etale/unramified/free loci
  and properly discontinuous actions. None is this statement or notion.
- `msearch.py` LeanFinder: “An action on an arbitrary logarithmic scheme, its
  inertia at a geometric point, and very tame locus”. Eight hits, all scheme
  etale/formally-unramified/germ/spreading-out APIs; no log action interface.
- Direct `rg`: `very.?[Tt]ame|veryTameLocus|EtaleLogGroupAction` in
  `lean/WeilConjectures` and `lean/Sheaf/AlgebraicGeometry`: only the existing
  FSLogGroupAction/VeryTameFSLogAction and distinct divisorial-action definitions
  and consumers. No locus theorem or arbitrary-log action exists.
- Direct `rg`: `EtaleLogGroupAction|veryTameLocus|IsVeryTameAt` across Mathlib,
  upstream source, project source and `dag/lean_names_upstream.json`: no hits.
- Direct `rg` for the item id in `lean/WeilConjectures`: no hits.
- DAG searches for geometric inertia/stabilizers and very tameness found the
  existing action and very-tame nodes and related theorem nodes. The archived
  inert-etale comparison module is absent from current live source and its
  record explicitly says it was deleted; it is not imported or re-created.

Validation: all three delivered files compiled separately, in dependency order,
through `scompile.py`, with no errors or warnings. The sole postponed theorem
is `AlgebraicGeometry.isOpen_veryTameLocus`.

## Dependency modules

`def-per-fs-log-group-action`: the existing `FSLogGroupAction` requires a
`FineSaturatedLogScheme`; using it for Y' would assume the fs conclusion before
stating it. Its sandbox module keeps every original declaration and adds
`EtaleLogGroupAction` with the identical underlying/section-map group-action
data for arbitrary `EtaleLogStructure`, the data-preserving
`FSLogGroupAction.toEtaleLogGroupAction`, and
`EtaleLogGroupAction.IsEquivariant`. It uses the existing general
`EtaleLogMap` and `CompEq`. No existing definition is changed; the extra import
of LogIdealChartPresentation supplies the required general maps. Only `lean`
is changed in the dependency node, with the required diagnostic note.

`def-per-very-tame-fs-log-action`: its global fs-only predicate cannot express
the pointwise tests or the source locus before fs has been concluded. Its
sandbox module preserves the original `FSLogGroupAction.IsVeryTame` declaration
and adds `EtaleLogGroupAction.IsVeryTameAt` and `.veryTameLocus`. The new tests
are precisely the original tame-order and section-representative conditions,
localized at one geometric point and then quantified over all lifts of an
ordinary point. These are helpers of this existing notion, not a competing
very-tameness definition or a new mathematical notion. Only `lean` changes in
the dependency node, with the required diagnostic note.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
