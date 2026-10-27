## What changed

Replaced the proof of `FieldTheory.henselian_krasner_neighbourhood` in
`Sheaf.FieldTheory.HenselianKrasnerNeighbourhood`, preserving its full signature.
The proof imports `Sheaf.FieldTheory.HenselianFiniteExtensionTopology` privately and uses
only its uniqueness clause. Equality of prolongation valuation subrings gives equivalent
valuations after each base-field automorphism. A strict-cycle contradiction using the finite
order of that automorphism upgrades equivalence to exact equality of values. The ultrametric
inequality then shows that every automorphism fixing beta also fixes alpha, and finite Galois
fixed-field theory gives alpha in F(beta).

The neighbourhood is the finite intersection of the basic balls indexed by automorphisms
moving alpha. Each radius is finite because the corresponding difference is nonzero. The
intersection contains alpha, and symmetry of the valuation of a difference gives the required
inequalities for each beta. If alpha belongs to F, there are no moving automorphisms and this
same intersection is the whole field. Updated the item's proof record to describe this
construction. No definition, existing statement, public import, other module, or unit route
was changed.

Searches used `msearch.py` with LeanFinder (arbitrary-rank henselian Krasner), Loogle
(`Valuation.IsEquiv`), and grep (finite order and valuations), together with direct searches
of Mathlib, Sheaf, and the adopted source library. The search returned the normed-field
Krasner theorem, which has stronger hypotheses; the available valuation equivalence and
finite Galois API suffice for the argument above. Read the recorded ILO source at XX 4.4,
printed p.374 (PDF p.380); it refers to Bourbaki's Krasner exercises, and the reconstructed
argument remains explicitly attributed to the agent rather than to unread Bourbaki text.

Validation: `lcompile.py` compiled the complete module without errors or warnings in
4.1 seconds. A source comparison confirms the theorem signature is unchanged; the Lean
file contains no `sorry` and all lines are at most 100 characters. The import-direction
check confirms the added proof dependency introduces no cycle.

## Proved and sorry left

Closed the one local hole: `FieldTheory.henselian_krasner_neighbourhood`
(`lem-per-henselian-krasner-neighbourhood`). Added zero holes; none remain in the item.
The proof uses the existing theorem `Valuation.henselian_finite_extension_topology`, whose
separate proof remains an existing dependency, not a new hole of this delivery.

## No longer needed

Removed the proof-only import `Mathlib.FieldTheory.Galois.Infinite`; the finite theorem
`IsGalois.fixedField_fixingSubgroup`, already available from the unchanged public import
`Mathlib.FieldTheory.Galois.Basic`, suffices. The mathematical fixed-field dependency
`lem-exc-etale-galois-fixed-field-subgroup` remains used via this finite specialization.
No declared dependency node or project module is pruned. The maximum-radius construction
and the proof of existence of a moving conjugate are unnecessary: a finite intersection also
works when its index set is empty. All three original proof dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The neighbourhood step can be simplified as described above.
The proof covers the edge cases N=F, alpha in F, alpha=beta, an empty set of moving
conjugates, higher-rank value groups, and value groups larger than the value image.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
