## Worker report

The module `Sheaf.Paper.HomUniversalCoefficients` states the canonical
coefficient comparison for constructible derived internal Hom.  It defines
`AlgebraicGeometry.Etale.universalCoefficientHomMap` as the evaluation
transpose, with reassociation and the signed derived tensor symmetry, and
states `AlgebraicGeometry.Etale.hom_universal_coefficients` with proof `sorry`.
The module compiled cleanly with `scompile.py`.

The Lean rendering of the hypotheses is as follows.  `A : Type (u + 1)` with
`[CommRing A] [IsNoetherianRing A]` is the commutative Noetherian coefficient
ring; `X : Scheme.{u}` with `[IsNoetherian X]` is the Noetherian scheme;
`K Y : DerivedCategoryModule A X` are the two derived module sheaves.
`_hK : ∃ r : ℤ, K.IsLE r` gives bounded-above K.  `_hc` is
`DerivedCategory.constructibleHomology (ModuleCat.{u + 1} A) X K`.
`_hY` is finite Tor amplitude of Y.  `_hbounded` supplies `d ≤ e` and, for
every ordinary `ModuleCat.{u + 1} A` module M and every integer i outside
`[d,e]`, the homology object of
`RHom(K, M_X ⊗^L Y)` is `IsZero`; the displayed term uses
`singleFunctor`, `constantSheaf`, `derivedTensor`, `derivedHom`, and
`homologyFunctor` exactly in that order.

The three conclusion clauses are rendered directly.  First,
`DerivedCategory.finiteTorAmplitude ... (((derivedHom ...).obj (op K)).obj Y)`
asserts finite Tor amplitude for H = RHom(K,Y), tested by the dependency
notion.  Second, for every ordinary derived coefficient complex C with
`∃ n : ℤ, C.IsGE n`, `IsIso` is asserted for
`universalCoefficientHomMap ... ((constantSheaf ...).mapDerivedCategory.obj C)`.
Third, the final universally quantified equality has arbitrary
`K' Y'`, coefficient complexes `C C'`, and maps `f`, `g`, `h`; its left and
right sides are the two composites shown in the node, expressing naturality
in K contravariantly, Y, and C.

Dependency declarations used are: `Mathlib.AlgebraicGeometry.Scheme`
(`AlgebraicGeometry.Scheme`); `Mathlib.RingTheory.Noetherian.Defs`
(`IsNoetherianRing`); `Mathlib.AlgebraicGeometry.Sites.Etale`
(`AlgebraicGeometry.Scheme.smallEtaleTopology`);
`WeilConjectures.AlgebraicGeometry.DerivedCategories`
(`AlgebraicGeometry.Etale.DerivedCategoryModule` and derived-category
notations); `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`
(`SheafOfModules.IsLocallyConstantFiniteTypeModules`);
`Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`
(`AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`);
`Mathlib.RingTheory.Finiteness.Defs` (`Module.Finite`);
`WeilConjectures.SixFunctors.Etale.Derived.Tensor`
(`AlgebraicGeometry.Etale.derivedTensor`);
`Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
(`AlgebraicGeometry.Etale.derivedHom` and
`AlgebraicGeometry.Etale.derivedTensorHomAdjunction`);
`Mathlib.CategoryTheory.Sites.ConstantSheaf`
(`CategoryTheory.constantSheaf`); and
`Mathlib.Algebra.Homology.DerivedCategory.Basic` (`DerivedCategory`).

Edge cases checked: the bounded-above witness allows any integer bound; the
interval permits `d = e`; the module quantifier includes the zero module and
arbitrarily large/infinite modules; `IsZero` is imposed only outside the
interval; C may be any bounded-below derived complex and is not assumed
perfect or finite-Tor; K' and Y' in the naturality clause are unrestricted;
and no nonempty, finite-rank, characteristic, or perfectness hypothesis was
introduced.  The signed symmetry in the definition handles the zero and
nonzero degree cases uniformly.

Searches for an existing declaration were recorded in `searches.jsonl`.
`leanfinder` queries for uniform boundedness and coefficient comparison found
only generic derived-category bounds and Tor declarations.  `leansearch`
queries for uniform derived-Hom boundedness found only underived tensor/Hom
adjunctions and generic Ext infrastructure.  `loogle` queries for
`CategoryTheory.MonoidalClosed`, `ModuleCat.ihom`, and derived tensor-Hom
comparisons found no matching theorem (one result was the generic
`MonoidalClosed.ofEquiv_*` API).  Grep of Mathlib `CategoryTheory` and of the
project for `universalCoefficients`, `tensorHomComparison`, and
`finiteTorAmplitude` found no declaration of this proposition.  Thus this is
not an existing Mathlib or project statement.

No statement correction or new definition/dependency module was needed.

## Second reading by NF

I reread the node and the complete module.  The ring, scheme, boundedness,
constructibility, finite-Tor, and uniform `[d,e]` hypotheses each occur once
with the same objects.  The finite-Tor conclusion, bounded-below coefficient
isomorphism, and the full three-variable naturality equation all occur in the
same order and with the same canonical transpose map.  The helper definition
uses evaluation plus signed symmetry rather than an arbitrary isomorphism.
No mismatch was found and no change was required.
