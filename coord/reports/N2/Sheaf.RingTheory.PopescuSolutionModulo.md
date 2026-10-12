## What changed

Replaced the sole hole in `Sheaf.RingTheory.PopescuSolutionModulo` by a complete Lean proof
combining two strictly smaller parts of the original 07FH argument:

- `Sheaf.RingTheory.PopescuFlatCoordinates` chooses an admissible subalgebra and flat polynomial
  coordinates, including spanning residue differentials. It asserts no smooth quotient map.
- `Sheaf.RingTheory.PopescuEtaleQuotientMap` constructs the local étale quotient map for FIXED
  flat coordinates and an admissible subalgebra. It assumes neither positive characteristic
  nor geometric regularity, and does not assert existence of the coordinates.

The original proof then proves both local/Artinian quotient assertions directly from Mathlib,
constructs `D = ULift A`, transports étaleness along the explicit algebra equivalence, proves
localness and flatness of the inclusion, constructs its essentially smooth presentation using
localization at `{1}`, verifies the factorization equation, and supplies explicit preimages of
all elements of E. No definition chooses an arbitrary witness from an unproved existence claim:
all existential eliminations occur inside a theorem proof, and D is an explicit universe lift.

Added a proved private helper `Algebra.local_artinian_prime_pow`. The item's existing statement,
universes, public imports and docstrings are unchanged. Only proof imports changed. The parent
node's proof and dependency list now describe the actual reduction. Both new nodes contain the
corresponding parts of the source argument, full Lean signatures and search records.

Read the original module, its node, the node's dependency records and signatures, the unit
`sk-thm-p1`, and the source at https://stacks.math.columbia.edu/tag/07FH. The local Stacks TeX
file is absent on this machine, so the authoritative online text supplied the source reading.
The unit's realized statements and proof steps are preserved; this change is below that level.

## Proved and sorry left

Closed the original hole in
`Algebra.exists_essentiallySmooth_artinian_factorization_mod_prime_pow`
(node `lem-weil-pbc-popescu-solution-modulo`). Its complete proof compiles without warnings.
The private helper `Algebra.local_artinian_prime_pow` is also fully proved from Mathlib.

Two new holes, each exactly the whole proof of a public theorem in its own module:

- `Algebra.exists_popescu_flat_coordinates`
  (`lem-weil-pbc-popescu-flat-coordinates`): original steps 1–9, plus retaining coordinate
  values in the admissible subalgebra and their differential span.
- `Algebra.exists_etale_popescu_quotient_map`
  (`lem-weil-pbc-popescu-etale-quotient-map`): original steps 10–15 for fixed input data,
  stopping at algebraic étaleness.

There are no holes in the item's module and no other holes added. This is a decomposition:
one upper hole closed, two lower holes added, net -1 before any effect of import closure.
The target still depends on these unproved results; this is not a sorry-free proof of 07FH.

The new statements were checked on the boundary cases E empty, n=1, q=0 in a field, and m=0
in the second lemma. Empty coordinates require Ω(F/k)=0; this allows precisely the finite
separable residue extension used in the argument. n=0 is excluded, because its quotient is
trivial and therefore not a local ring. The second statement retains the flatness and
maximal-ideal equality needed for descent; it does not infer them from spanning differentials.
These are mathematical checks, not extra executable tests.

## No longer needed

Removed the following proof imports from the item's module:

- `Sheaf.RingTheory.ArtinianFlatSubalgebras`
- `Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian`
- `Sheaf.RingTheory.FlatOverRegular`
- `Sheaf.RingTheory.FlatPermanence`
- `Sheaf.RingTheory.GeometricallyRegularH1Injective`
- `Sheaf.RingTheory.GeometricallyRegularOverFieldFlat`
- `Sheaf.RingTheory.LocalizationOfRegularRing`
- `Sheaf.RingTheory.PolynomialOriginRegularLocal`
- `Sheaf.RingTheory.PopescuSolutionModuloChoose`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`

Their corresponding nodes remain needed inside the two new statements' proof plans: they are
moved below those two items, not claimed as globally unnecessary mathematical work. Likewise
all original Mathlib dependencies except the following remain needed directly or in those plans.

`lem-weil-pbc-etale-ring-map-iff-etale-affine` is unnecessary for this argument: the new second
lemma concludes algebraic `Algebra.Etale`, which directly supplies `Algebra.Smooth`. The original
route through affine-scheme étaleness is eliminated. This is a node pruned from this proof
plan, not a claim that its Mathlib comparison module has no other library users. No unit
statement or unit proof step is pruned.

Removed trial direct imports of `Mathlib.Algebra.Module.ULift` and
`Mathlib.RingTheory.Etale.Basic` after checking that the remaining imports supply the used APIs.
Only `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` and the two new proof modules are added.

Complete parent-node dependency diff (every old `proof_deps` entry absent from the new
parent list):

- `def-weil-pbc-g-ring`
- `def-weil-pbc-kahler-differentials`
- `def-weil-pbc-mv-polynomial-ring`
- `def-weil-pbc-regular-sequence`
- `def-weil-pbc-separable-algebraic-extension`
- `def-weil-pbc-smooth-ring-map`
- `def-weil-regular-scheme`
- `lem-weil-pbc-artinian-finite-over-residue-finite`
- `lem-weil-pbc-criterion-flatness-fibre-noetherian`
- `lem-weil-pbc-etale-ring-map-iff-etale-affine`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `lem-weil-pbc-fg-field-zero-differentials-separable`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-finite-type-noetherian-finite-presentation`
- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-flat-module-base-change`
- `lem-weil-pbc-flat-over-regular`
- `lem-weil-pbc-flat-permanence`
- `lem-weil-pbc-geometrically-regular-h1-injective`
- `lem-weil-pbc-geometrically-regular-over-field-flat`
- `lem-weil-pbc-local-flat-unramified-etale`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-localization-of-regular-ring`
- `lem-weil-pbc-nakayama-local-generators`
- `lem-weil-pbc-polynomial-ring-origin-regular-local`
- `lem-weil-pbc-popescu-artinian-flat-subalgebras`
- `lem-weil-pbc-popescu-solution-modulo-choose`
- `lem-weil-pbc-regular-local-generators-regular-sequence`

Except for `lem-weil-pbc-etale-ring-map-iff-etale-affine`, these dependencies occur in the
new lower proof plans. Definition imports needed by the original signature also stay public;
removal from the parent's proof dependency list does not claim that its statement no longer
uses these definitions. The local/Artinian quotient leaf remains a direct parent dependency
and is realized by the proved private Mathlib helper. No whole-library module-pruning count
is claimed before the maintainer regenerates the dependency imports and runs the ledger.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy or new dispute was found. The corrected enlargement already recorded
in `PopescuSolutionModuloChoose` is retained in the first new node's proof. The original plan
left localization, quotient, residue-field and fibre-flatness glue implicit in its component
signatures; the two new statements isolate that remaining work instead of moving the entire
original theorem under a different name.

LeanSearch was unavailable (Internal Server Error) for both new statements. This is recorded as
unavailable, not as evidence of absence. LeanFinder, Loogle, source searches and whole-blueprint
searches were actually run; they found no exact packaged coordinate/factorization theorem.

## New nodes

`lem-weil-pbc-popescu-flat-coordinates`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-flat-coordinates.json`, is the coordinate
construction through property (1) of 07FH. Its module is
`lean/Sheaf/RingTheory/PopescuFlatCoordinates.lean`. The source proof and corrected enlargement
are recorded step by step. It has no quotient-factorization or smoothness conclusion.

`lem-weil-pbc-popescu-etale-quotient-map`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-etale-quotient-map.json`, is the final
quotient construction and étaleness argument of 07FH, for fixed flat coordinates. Its module is
`lean/Sheaf/RingTheory/PopescuEtaleQuotientMap.lean`. It is independent of the geometric-regularity
and positive-characteristic preparation. No change record is necessary: no existing signature,
definition or public visibility changed.

## Second reading by N2

1. **Interface check: PASS.** Read the repository and sandbox versions of all delivered
   modules and diffed the existing module. The signature of
   `Algebra.exists_essentiallySmooth_artinian_factorization_mod_prime_pow` is byte-for-byte
   unchanged, including universes, every hypothesis, the two quotient-ring instances, the
   localness/flatness clauses and the element preimages. Existing public imports, visibility
   and definitions are unchanged. The only additional declaration there is a private proved
   quotient helper, realizing the existing Mathlib quotient leaf. The other two modules are
   new public statements, each in its own module; no change record is needed.

2. **Proof and axioms: PASS as a decomposition.** Independently compiled all three modules
   with `lcompile.py --all`: no errors or warnings. Opened the complete parent proof: quotient
   locality uses nontriviality (n >= 1), Artinianity uses the radical/minimal-prime lemma,
   the admissible inclusion is flat, its contracted maximal ideal proves it local, and the
   explicit `ULift A` algebra equivalence transports the first map. The smooth presentation
   is D localized at `{1}`; the compatibility and E-preimages are checked explicitly.
   Scratch-copy `#print axioms` checks give only `propext`, `Classical.choice`, `Quot.sound`
   for the private helper and additionally `sorryAx` for the parent and both new statements.
   Exactly the two listed public theorems have whole-proof `sorry`; no definition has one,
   and no axiom, unsafe, opaque, extern, implemented_by or kernel-check bypass occurs.
   No arbitrary witness is chosen by a definition. One original hole is replaced by two
   lower holes, not a sorry-free proof; the report correctly calls this decomposition.

3. **Split statements: PASS.** Read both full Lean signatures, docstrings and JSON nodes
   against [07FH](https://stacks.math.columbia.edu/tag/07FH), label
   `lemma-solution-modulo`, and the existing corrected `PopescuSolutionModuloChoose`.
   The first statement constructs coordinates and an admissible A, without a smooth or
   etale quotient map. Its proof uses geometric regularity for H1 and the first coordinate
   localization, then a regular parameter sequence and the fibre-flatness criterion for
   the extended map. The positive characteristic supplies the corrected enlargement.
   The second fixes those data; factoring evaluation uses the coordinate containment,
   localization uses maximal-ideal contraction, quotienting uses pL=qL, and flatness descends
   through the faithfully flat admissible inclusion. Faithful-flat ideal contraction gives
   pA=m_A; spanning differentials and finite generation give a finite separable residue
   extension by [090W](https://stacks.math.columbia.edu/tag/090W). The Artinian finiteness
   leaf gives module finiteness, Noetherianity gives finite presentation, and
   [00U6](https://stacks.math.columbia.edu/tag/00U6) gives etaleness. These are strictly
   different parts of the argument, not renamed copies of the original conclusion.

   Independently checked E empty, n=1, and q=0 when Lambda is a field; the positive exponent
   keeps the quotients nontrivial. For m=0 in the second statement, spanning means
   Omega(F/k)=0, so the finite-type residue field must be finite separable, and pL=qL forces
   qL=0. A field inclusion alone is flat; inseparable residue extensions are excluded by
   the differential hypothesis. Nonreduced Artinian A is permitted for n>1 and requires
   the retained flatness and maximal-ideal equality. The second argument also works in
   characteristic zero and does not use geometric regularity. Independent searches used
   LeanFinder for adapted local coordinates and the flat Artinian etale criterion, Loogle
   queries `MvPolynomial, RingHom.Flat` and `Algebra.Etale, RingHom.Flat` (both no hits),
   and msearch grep for admissibility, differential spanning, and Artinian etale algebras.
   Repository rg found the existing coordinate-preparation and flatness declarations but
   no packaged replacement for either split. Mathlib standard-smooth and standard-etale
   results assume an already smooth or etale algebra, so do not close these holes directly.
   `SmoothPolynomialFactorization` invokes Popescu smoothing downstream of this argument
   and cannot give a noncircular shorter route here. Neither open part can be closed by a
   few-minute application of a searched theorem.

4. **Route and pruning: PASS after report repair.** The parent combines the two source
   parts in a complete Lean proof; no unit statement or realized step is bypassed.
   Read `dag/units/sk-thm-p1.json`: none of these three nodes is a unit statement or a
   realized step, and the unit file is unchanged. All added parent proof imports are plain
   `import`; public imports of the new modules provide types used in their statements.
   The parent directly uses both new imports and KrullsHeightTheorem. Its removed imports
   are all recorded. Added the exhaustive list of old parent proof dependencies removed,
   distinguishing lower planned dependencies from the eliminated affine-etale comparison.
   No globally unreachable module is claimed without the maintainer's import regeneration
   and sorry ledger. The net hole change remains -1 before import-closure effects.

5. **DAG agreement: PASS.** Compared the parent JSON with the repository: only `proof`,
   `proof_deps` and `proof_origin` changed. Its three proof steps describe the coordinate
   choice, quotient helper/etale map, and explicit universe lift/smooth presentation.
   For all three nodes checked that `proof_deps` is exactly the union of the steps' `uses`
   and that every statement/proof dependency exists. For each new node checked its source,
   self-contained statement, detailed proof, search records, `status: split`, worker/item/
   group/date, blueprint ancestry, chapter/unit, and Lean record. The recorded Lean
   signatures agree with the actual declarations after whitespace normalization. The
   original statement and statement dependencies are unchanged. The new proofs cite the
   existing component lemmas; the named Mathlib leaves supply finite presentation,
   differential separability and the local etale criterion.

Changes made by the second reader: corrected the new etale-map docstring's false assertion
that all polynomial variables map into m_A (only p does), used the direct 090W citation,
made the final local-to-global etaleness step explicit, and replaced the coordinate
lemma's potentially circular localness explanation by the direct proper-contraction and
maximality argument. Completed the parent dependency-pruning list and this review.
No Lean statement or proof term changed; no new hole was closed or added by the second reader.
