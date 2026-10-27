## What changed

The statement of `CategoryTheory.exists_ringed_cech_koszul_hom_limit_comparison` is
unchanged. Its proof composes the existing augmented colimit identification with a
chain-level finite evaluation/ordinary-limit comparison, applies the fixed internal-Hom
localization factorization and the specified derived-limit comparison on functorial
K-injective coefficients, and descends the resulting natural isomorphism through fully
faithful precomposition by `DerivedCategory.Q`. The unit calculation is explicit: it
uses augmentation compatibility, naturality of the ordinary-limit unit, cancellation
of the K-injective replacement quasi-isomorphism, and the chosen representative
isomorphism appearing in the definition of `D.unit`.

Two supporting statements are in separate new modules, each with its source and full
proof sketch. They concern ordinary cochain complexes and inverse-limit acyclicity,
respectively. Neither asserts the original derived natural-isomorphism statement.
No existing statement, definition, public import, or source-library declaration changes.
The proof locally marks the Cech complex, tensor-tower complex and ordinary-limit unit
irreducible to prevent unnecessary unfolding. A private typed localization factorization and a proved one-step unit equation bound
the largest construction. The assigned file compiled in 57 seconds;
the final delivery checks validate the complete packet.

## Proved and sorry left

The original hole in
`CategoryTheory.exists_ringed_cech_koszul_hom_limit_comparison` is reduced to two
strictly smaller supporting statements. This is a decomposition, not a net hole closure:
one original hole removed, two holes added, zero original obligations fully closed.
The assigned module itself has zero remaining `sorry`.

The two remaining holes are:

- `CategoryTheory.exists_ringedKoszul_colimitHom_ordinaryLimit_iso`, node
  `lem-weil-pbc-ringed-koszul-colimit-hom-ordinary-limit`.
- `CategoryTheory.ringedKoszulTensorTower_limit_comparison_isIso`, node
  `lem-weil-pbc-ringed-koszul-tensor-tower-limit-acyclic`.

Both are public theorems whose complete proof bodies are `by sorry`, in new modules.
Their docstrings give the source and proof in words. No data is selected from either
unproved theorem in a definition: the isomorphism witness is used only inside the
proof of the assigned theorem.

## No longer needed

The assigned module removes the direct proof imports
`Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
`Sheaf.Algebra.Homology.KInjectiveProductsTermwise`,
`Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`,
`WeilConjectures.Algebra.Homology.TelescopeColimit`, and
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
It uses the original small-site internal Hom already publicly available through
`RingedKoszulSystem`. The product, finite split-perfect, telescope and strict Roos
nodes remain dependencies of the new acyclicity node. They are deferred mathematical
work, not globally withdrawn modules. The new modules import only what their public
statements require; their eventual proof dependencies remain recorded in the DAG.

The upper proof needs no uniqueness of completion-normalized maps, slice restriction
comparison, reflector theorem or empty-list normalization theorem. No existing Lean
module or DAG node is withdrawn. The proper-base-change unit route is preserved. The item closure was checked for
dependency cycles after overlaying the three delivered node records; none was found.

## Where the brief, the DAG or earlier work was wrong

The original dependencies supply the colimit identification, telescope quasi-isomorphism,
K-injective product theorem, split-perfect tensor theorem, and strict Roos theorem, but
none directly states finite Koszul evaluation with the ordinary-limit unit or acyclicity
of this particular strict tower. These are the two missing glue steps now stated.
The ordinary-limit comparison is natural on all coefficient complexes and precedes
deriving; the acyclicity assertion assumes only K-injectivity, not injective terms.
The proof sketches handle the empty list, zero generators, invertible generators,
zero ring and empty site. No assertion of exact infinite products is introduced.

## New nodes

`lem-weil-pbc-ringed-koszul-colimit-hom-ordinary-limit` records the natural chain
isomorphism from Hom of the positive Koszul colimit to the ordinary inverse limit of
the actual tensor tower, including its augmentation equation. It has no derived-category
hypothesis and applies to every coefficient complex.

`lem-weil-pbc-ringed-koszul-tensor-tower-limit-acyclic` records invertibility of the
specified ordinary-to-derived inverse-limit comparison on the actual Koszul tensor
tower of a K-injective complex. The source proof uses the telescope, finite evaluation,
products of K-injectives, and the normalized Roos construction. It makes no claim about
Čech completion, naturality in the derived coefficient object, or completion units.

No existing public interface changes. The two new nodes supply the public interfaces
needed only by this reduction.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
