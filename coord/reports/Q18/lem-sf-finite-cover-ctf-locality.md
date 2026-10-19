## Worker report

The item is stated in `lean/Sheaf/SixFunctors/FiniteCoverCTFLocality.lean` as
`AlgebraicGeometry.Scheme.finiteCoverCTFLocality`. It binds a scheme `X`, explicit
Noetherian-space hypothesis, finite commutative coefficient ring `A`, a finite family of
schemes and open immersions covering `X`, the derived object `K`, and integers `a ≤ b`.
The restriction `K_i` is the canonical
`proEtaleConstantRingDerivedPullback A (j i)` object. Cohomology is rendered by
`DerivedCategory.homologyFunctor` in the intrinsic ringed-site module category.

The local finite-support clause is
`Set.Finite {t : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor ... t).obj K_i)}`.
The local finite-stratification and finite-stalk clause is the existing
`IsConstructibleProEtaleModuleSheaf (U i) A` predicate; its definition expands to a
finite locally closed constructible stratification, locally constant pullbacks, and
finite geometric `A`-module stalks. The local Tor clause quantifies every module sheaf
`F` and every degree `t` with `t < a ∨ b < t`, and applies `IsZero` to the cohomology of
`proEtaleDerivedTensor ... K_i ((DerivedCategory.singleFunctor ... 0).obj F)`.
The conclusion has the corresponding global finite support, constructibility for every
cohomology degree, and the global Tor clause for every degree-zero `F`.
The cover is written as `∀ x : X, ∃ i, ∃ y : U i, (j i).base y = x`, so `r = 0`
forces `X` empty exactly as in the node.

The theorem docstring records all six proof steps from Tag 095F: finite affine
refinement from Noetherianity, localization and exact restriction, finite stratification
gluing, transport of local constancy and finite stalks, cover detection of Tor vanishing,
and tensor-unit specialization. Its proof is only `sorry`.

The statement dependencies used are `AlgebraicGeometry.Scheme`, Mathlib
`AlgebraicGeometry.IsOpenImmersion`, `Scheme.proEtaleDerivedCategory`,
`Scheme.proEtaleConstantRingDerivedPullback`, `DerivedCategory.homologyFunctor`,
`Topology.IsConstructible` through the constructibility predicate, and
`Scheme.IsLocallyConstantProEtaleModuleSheaf` through that predicate. The derived tensor
interface is supplied by the dependency repair below.

Edge cases checked: `r = 0` is compatible exactly when `X` is empty; the empty scheme is
handled by the finite-support and constructibility predicates; the zero coefficient ring
is allowed by `[CommRing A] [Finite A]`; `a = b` and intervals with no outside degrees
are accepted; all integer degrees, including negative ones, are quantified; no affine
intersection is assumed affine; and the finite family index is `Fin r` in the scheme's
universe.

Searches for an existing item declaration found no match: `rg -n
"finite-cover-ctf-locality|bounded.*constructible|Tor amplitude"` in both the shared
`lean/Sheaf` tree and `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` returned no
statement of this locality lemma. The recorded node searches (LeanFinder, LeanSearch,
Loogle, and Mathlib/source grep) likewise reported no match. Existing declarations for
schemes, open immersions, pro-etale derived categories, cohomology, constructible subsets,
and locally constant pro-etale module sheaves were inspected and reused.

No `STATEMENT-DISPUTED` flag or statement correction is needed.

## Second reading by Q18

I reread the node statement and the complete module. The hypothesis correspondence is:
`hX` is the underlying topological Noetherian condition; `A`, `Finite A`, `r`, `U`, `j`,
`hj`, and `hcover` give the finite open cover including the empty case; `K`, `a`, `b`,
and `hab` give the derived object and fixed interval; `hlocal` gives finite local
cohomological support; `hconstructible` gives the finite constructible locally constant
stratifications with finite stalks; and `htor` tests every degree-zero local module
sheaf. Every conclusion clause is present globally with the same objects and the same
interval. The only shorthand is `IsConstructibleProEtaleModuleSheaf`, whose inspected
definition is exactly the finite-stratification/local-constancy/finite-stalk clause in
the node. The derived restriction and degree-zero sheaf are canonical declarations,
not arbitrary maps. No mismatch was found.

## Dependency modules

`def-weil-derived-tensor` received a §1(B) interface repair in
`lean/Sheaf/SixFunctors/IntrinsicDerivedTensor.lean`. Its recorded generic
`AlgebraicGeometry.ProEtale.derivedTensor` is a ModuleCat-valued sheaf bifunctor and
cannot accept the intrinsic ringed-site objects of `proEtaleDerivedCategory`. The new
`proEtaleDerivedTensor` uses the canonical `Q.objPreimage` representatives and the
universe-general K-flat resolution theorem to form the same intrinsic derived tensor;
`proEtaleDerivedTensorRing` supplies the ring-map specialization with restriction of
scalars. The module contains real definitions only and no theorem proof beyond the
resolution theorem it invokes.
