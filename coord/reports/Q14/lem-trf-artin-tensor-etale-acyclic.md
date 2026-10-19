## Worker report

The delivery defines `AlgebraicGeometry.Scheme.IsEtaleAcyclic` in
`lean/Sheaf/AlgebraicGeometry/EtaleAcyclic.lean` and states
`artin_tensor_etale_acyclic` in `lean/Sheaf/AlgebraicGeometry/ArtinTensorEtaleAcyclic.lean`.
The new definition records that every jointly surjective family of étale objects over a
scheme has a section after coproduct; the affine component equivalence is part of its
source statement. The item binds commutative rings `R`, `B₁`, `B₂`, algebra structures and
`Algebra.IndEtale` hypotheses, assumes étale acyclicity of both spectra, quantifies over a
small-étale torsion abelian sheaf `F`, and concludes `IsZero` of its degree-`q` étale
cohomology for every integer `q` with `0 < q`.

The item uses `Algebra.IndEtale` from `WeilConjectures.RingTheory.ProEtale.IndEtale`,
`AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf` from
`Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`, `AlgebraicGeometry.Etale.cohomology` from
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
`AlgebraicGeometry.Spec` from Mathlib, and
`AlgebraicGeometry.Scheme.smallEtaleTopology` from Mathlib. The new notion is cited by `Scheme.IsEtaleAcyclic`.

## New nodes

Added `def-trf-etale-acyclic-scheme`, the missing predicate used by the item hypotheses. It has a real data definition and no postponed proof. Its statement cites `def-weil-pbc-etale-site`, `def-weil-affine-spectrum`, and `def-weil-pbc-henselian-terminology` exactly where those notions occur.

Edge cases checked: the index type for a cover is `Type u`; the empty coproduct and empty
scheme are allowed by the quantified cover condition; no finiteness of the cover or of the
number of components is imposed; `q` is an arbitrary integer subject only to positivity;
`B₁ ⊗[R] B₂` is allowed to be the zero ring.

Searches made with `msearch.py Q14 lem-trf-artin-tensor-etale-acyclic`: LeanFinder for
“Tensor products of ind-etale etale-acyclic algebras over a ring are etale-acyclic” and
“A tensor product of etale acyclic ind-etale algebras is acyclic for derived global
sections” found only generic `Algebra.Etale`/tensor declarations; Loogle for
`Algebra.Etale, TensorProduct, IsStrictlyHenselianLocalRing` returned zero hits; grep in
Mathlib and `WeilConjectures` for `ind-etale.*acyclic|tensor.*strictly henselian|etale.*acyclic`
found no matching theorem or predicate; LeanSearch returned only generic étale and formal
étale declarations. A separate search for the new predicate likewise found no existing
notion, so it was added as the new definition node `def-trf-etale-acyclic-scheme`.

No statement correction or `STATEMENT-DISPUTED` issue was found. Both files compile cleanly
with the prescribed `scompile.py` command; the theorem proof is intentionally `sorry` for
stage 2.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (NT-cc review, 2026-10-18)

The item module's statement docstring now carries the node's five proof steps (H8), and the
unused import `WeilConjectures.Mathlib.RingTheory.Henselian` was removed from it (H9;
`IsStrictlyHenselianLocalRing` does not occur in the statement, and the parenthetical
henselian characterization is the separate node
`lem-trf-affine-etale-cover-component-criterion`). This report now names the new node by its
real id `def-trf-etale-acyclic-scheme`. The signature, and so `lean.statement`, is unchanged.

