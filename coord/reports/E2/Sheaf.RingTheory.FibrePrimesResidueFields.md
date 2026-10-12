## What changed

Proved `PrimeSpectrum.fibre_primes_residue_fields` in
`Sheaf.RingTheory.FibrePrimesResidueFields`, preserving its entire signature and imports.
The order isomorphism is Mathlib's `preimageOrderIsoFiber` inverted; contraction and
kernel clauses are definitional. The residue-field equivalence is the inverse of
`RingEquiv.ofBijective` applied to the canonical map, whose bijectivity follows from
`surjectiveOnStalks_residueField.baseChange′.residueFieldMap_bijective`.
Compatibility follows by injectivity on the B factor, residue-field extensionality on
the A factor, and tensor-product ring-hom extensionality. Updated the existing node's
proof steps and proof origin to record these Lean implementations of its route.

Searches run: LeanFinder for bijectivity of residue-field maps under base change found
`RingHom.SurjectiveOnStalks.residueFieldMap_bijective`; Loogle for
`Ideal.ResidueField.ringHom_ext` found that exact lemma; grep for base change and
residue-map compatibility found `baseChange′` and `Ideal.ResidueField.map_algebraMap`.
Read their Mathlib source signatures and the tensor extensionality lemma.

## Proved and sorry left

Closed the sole original hole: `PrimeSpectrum.fibre_primes_residue_fields`
(node `lem-weil-pbc-fibre-ring-primes-residue-fields`). No holes remain and no holes
were added. This is a complete proof from Mathlib, not a decomposition.
Local single-file compilation succeeded with no errors or warnings.

## No longer needed

None. The sole existing import is needed by both the statement and proof. Both
Mathlib leaf dependencies, `lem-weil-pbc-fibre-ring-primes-bijection` and
`lem-weil-pbc-fibre-ring-residue-field-iso`, remain used, together with
`def-weil-pbc-localization-at-prime`. No Sheaf dependency modules or new modules are
needed. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

None. The DAG's route is directly implementable in Mathlib. Its explicit fraction
argument is encapsulated by `Ideal.ResidueField.ringHom_ext`. Empty fibres are
handled by the universal quantifiers, with no extra nonemptiness assumption.

## Second reading by E2

1. Compared the complete delivered module with the repository version using `diff -u`.
   The only change is the body of `PrimeSpectrum.fibre_primes_residue_fields`: its
   signature, docstring, universes, section, and sole public import are byte-for-byte
   unchanged. No definitions, extra declarations, or change records were added. Pass.
2. Independently compiled the module with `lcompile.py`: clean, 3.7 seconds. Compiled
   a scratch copy with `#print axioms PrimeSpectrum.fibre_primes_residue_fields`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Searched the delivered Lean for holes and forbidden declarations; none. Pass.
3. No split-off statements or new nodes exist, so there are no lower holes to check.
   Inspected Mathlib's `preimageEquivFiber`, `preimageOrderIsoFiber`,
   `SurjectiveOnStalks.baseChange'`, `residueFieldMap_bijective`,
   `ResidueField.map_algebraMap`, and `ResidueField.ringHom_ext` directly.
   Their hypotheses match the arbitrary commutative A-algebra B and prime p here;
   no finiteness, injectivity, or nonempty-fibre assumption enters. In particular,
   if B is the zero ring then both spectra in the correspondence are empty and
   the residue-field clause is vacuous. For A = B a field the correspondence has
   one prime and the construction is the canonical residue-field equivalence. Pass.
4. Read from the existential order isomorphism down to the final extensionality
   argument. The two prime descriptions are the actual defining maps of Mathlib's
   equivalence. The equality `hq` supplies precisely the contraction hypothesis
   required by the canonical map iota. Its bijectivity follows by base change of
   A -> kappa(p). The `hj` calculation proves compatibility on B by applying iota;
   residue-field extensionality reduces the kappa(p) factor to A, where tensor
   balancing and the scalar-tower identity reduce it to `hj`. Tensor-product
   extensionality then proves the full requested equality, not just an abstract
   isomorphism of fields. No shorter missing library step was found in the local
   searches for fibre correspondences and residue-field bijectivity. The sole
   public import supplies `Ideal.Fiber` and the residue-map constructions in the
   statement and must remain public. All three old proof dependencies are used,
   so `No longer needed: None` is complete. Inspected `dag/units/sk-thm-p1.json`:
   no realized statement or step is removed or bypassed. Pass.
5. Compared the existing node JSON with its sandbox version. Only proof-step text
   and proof_origin change; the statement and proof_deps remain unchanged.
   Step 1 records `preimageOrderIsoFiber`; step 2 records the base-changed canonical
   map; steps 3-5 record the two factor calculations and extensionality, matching
   the Lean. The union of step dependencies remains exactly proof_deps. The
   Mathlib-leaf nodes for the prime bijection and residue-field isomorphism describe
   the declarations actually used. Also read Stacks Tag 00E6 at
   https://stacks.math.columbia.edu/tag/00E6, which supplies the fibre diagram and
   correspondence; the local algebra.tex is absent and Tag 0H9M was inaccessible
   online, so the residue-field step was checked against the Mathlib source and
   the node's explicit localization argument. Pass.

Second reading changed only this report: no Lean or DAG repairs were necessary.
The sole original hole is closed and zero holes are added.
