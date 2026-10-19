## Worker report

The new module `Sheaf.AlgebraicGeometry.PrimePowerHomTensorTest` states ILO, Travaux de
Gabber, Expose XVII, Lemma the project server (printed pp. 294–295, PDF pages 300–301).
The node is unchanged except for `lean`. There is one postponed theorem,
`AlgebraicGeometry.Etale.prime_power_hom_tensor_test`, with the complete twelve-step
proof plan in its docstring. Its three small helper definitions have real data.
No independent notion or dependency repair is needed.

Hypotheses and clauses, in the order of the node:

- A Noetherian scheme is `(X : Scheme.{u}) [IsNoetherian X]`.
- A prime ell is `(l : ℕ) [Fact l.Prime]`. The positive exponent n is indexed by
  `r : ℕ`, with `n = r + 1`. Every n ≥ 1 occurs, including n = 1 at r = 0.
- Lambda is literally `ULift.{u+1} (ZMod (l ^ (r + 1)))`, and k is literally
  `ULift.{u+1} (ZMod l)`. These are universe lifts of the stated rings, not different
  coefficient rings. `primePowerResidueMap` is the lifted canonical `ZMod.castHom`.
- K belongs to `DerivedCategory.Bounded` of
  `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Lambda)`. Its underlying object is `K.obj`.
  Thus the hypothesis is bounded cohomology, with no constructibility condition.
- (i) is `∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn Lambda X a b K.obj`.
  The recorded predicate tests every module sheaf in degree zero, not only the residue
  sheaf or finitely generated sheaves. Empty intervals remain allowed.
- (ii) is `DerivedCategory.TStructure.t.bounded` of the recorded `derivedTensor` applied
  to K and `primePowerResidueComplex l r X`. The latter is the constant k module,
  restricted along the quotient and put in degree zero by `singleFunctor`.
  Boundedness is tested after exact, conservative restriction of k scalars to Lambda;
  this is equivalent to boundedness over k because restriction preserves homology and
  detects zero. The last clause also explicitly supplies the k-linear tensor model.
- (iii) is `DerivedCategory.TStructure.t.bounded` of
  `(coextendScalars (primePowerResidueMap l r) X).rightDerivedFunctor.obj K.obj`.
  This object lies in D(X_et,k), with the actual k-action. Ordinary coextension is
  M ↦ Hom_Lambda(k,M), computed objectwise; for a constant first argument it is the
  internal sheaf Hom. Its right-derived value is precisely RHom_Lambda(k_X,K).
  This uses the existing specialized coefficient Hom, rather than constructing a
  second internal Hom or assuming a closed structure.
- The first two conjuncts are (i) iff (ii) and (ii) iff (iii), which give all three
  equivalences. The third conjunct is conditional on (i), hence on any of the three.
- The canonical isomorphism over k is specified using a bounded flat representative P
  and `e : Q.obj P ≅ K.obj`. Such a representative is supplied in the conclusion,
  not assumed or restricted to constructible objects. The formula is then asserted
  for EVERY bounded flat representative and every such e, not an arbitrarily selected
  representative. Both the reduction model `Q(ext.mapHomologicalComplex.obj P)` and
  RHom are bounded, and the isomorphism i is in D(X_et,k). Since D^b is full, this is
  equally an isomorphism in D^b(X_et,k). Its inverse is the node's RHom-to-tensor
  orientation.
- Canonicity is retained: the natural transformation δ from ordinary residue extension
  to coextension is characterized by
  `extensionUnit ≫ restrict(δ.app M) ≫ coextensionCounit = (l ^ r) • 𝟙 M`.
  Under the two adjunctions this is the unique map M/ell M → M[ell] induced by
  multiplication by ell^r. The displayed equation for `i.hom` is Q of its termwise
  map, followed by the fixed right-derived unit and the image of e. A final comparison
  identifies the underlying Lambda object of the reduction model with the recorded
  derived tensor. The comparison i is consequently residue-linear and normalized;
  mere existence of an arbitrary isomorphism over Lambda is not the conclusion.
- There are no hypotheses of excellence, ell-invertibility on X, or constructibility.

Dependency declarations read and used:

- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  and its publicly imported `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; Mathlib's `DerivedCategory.Bounded`
  and `DerivedCategory.TStructure.t.bounded`. The recorded derived-category module
  was absent from the old source checkout; `scompile.py --source` supplied the live
  declaration and full docstring.
- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`, exposing the
  existing bounded-interval `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`
  in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. The lower-bounded variant
  is not substituted for this predicate.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`, specialized to ModuleCat in universe u+1.
- `def-pur-derived-internal-hom`: imported owning module
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, including its full generic
  construction and comparisons, and its public import of
  `WeilConjectures.SixFunctors.Etale.Derived.Hom`. This records the same internal Hom
  (the coefficient specialization is `AlgebraicGeometry.Etale.derivedHom`). For the
  required k-action the statement uses the existing
  `WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars`:
  `AlgebraicGeometry.Etale.coextendScalars` and its `Functor.rightDerivedFunctor`.
  Its objectwise Hom definition, restriction/coextension adjunction, and exactness of
  restriction were read in full. No replacement definition of internal Hom is made.

The extension helper is the existing `Functor.leftAdjoint` of exact sheaf restriction;
its adjunction universal property determines it, together with its unit, up to the
unique compatible isomorphism. This is an allowed universal construction, not data
chosen from a mere non-unique existence theorem. `IsBoundedFlatComplex` is the existing
predicate in `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`; its use
expresses the source's normalization on bounded flat representatives, without importing
that module's constructibility assumption into this theorem.

All recorded modules of stated proof dependencies are imported without `public`, unless
already publicly imported as statement dependencies. The metatheoretic
`def-weil-size-convention` has no defining module (its record is `convention: true`):
explicit u, u+1, the small etale topology, and the recorded HasDerivedCategory instances
implement it. No proof-import cycle was encountered.

Searches for an existing theorem or duplicate helper:

- `msearch.py ... leanfinder "For bounded etale complexes of Z mod prime power modules
  finite Tor amplitude is equivalent to bounded derived Hom from the residue field"`:
  eight hits, including derived-category t-structure and algebraic smoothness lemmas;
  none states this criterion or normalized comparison.
- `msearch.py ... leansearch "bounded derived Hom residue field prime power coefficients
  finite Tor amplitude"`: eight hits; bounded representative, Ext size and residue-field
  facts, no match.
- `msearch.py ... loogle "ZMod.castHom, derivedHom, derivedTensor"`: no hit; Loogle
  reports unknown identifier derivedHom (it searches Mathlib, not this project's names).
- `msearch.py ... grep "primePower.*[Hh]om|[Hh]om.*primePower|[Tt]or.*[Bb]ounded"`:
  general bounded-set matches, no criterion. Direct focused rg of Mathlib/Algebra/Homology
  for prime-power Hom / Hom-tensor boundedness found no theorem.
- Direct rg of upstream WeilConjectures and side `lean/Sheaf` for prime-power, Hom/tensor,
  and residue-Tor terms found `ResidueTorAmplitudeTest`, `ConstantTwoTermResolution`,
  `CoextendScalars`, and the existing derived tensor/Hom APIs. The residue-Tor theorem
  assumes bounded CONSTRUCTIBLE complexes and padic coefficient extensions and has no
  Hom test/comparison, so is not an exact match. ConstantTwoTermResolution resolves a
  quotient of padic integers, not k over Z/ell^n. Reused the existing coextension API.
- Direct rg of both source trees and `dag/lean_names_upstream.json` for
  `prime_power_hom_tensor_test|primePowerResidue(Map|Extension|Complex)` returned no
  existing declaration. The prescribed grep of the item id in upstream returned no hit.

Edge cases checked against the source and the twelve proof steps: X empty; K zero;
exponent n = 1 (r = 0, quotient is the identity, normalization is multiplication by 1);
X a point with n = 2 and K = k[0] (Tor/reduction/Hom all unbounded in the relevant test);
K = Lambda_X[0] (normalization identifies quotient with ell-torsion by ell^(n-1));
ell equal to the characteristic of X; nonconstructible sheaves and arbitrary finite
cohomology intervals. None is excluded. These are mathematical checks, not extra proved
Lean lemmas. No STATEMENT-DISPUTED flag or source correction is needed.

Validation: the sole delivered Lean file compiled through the prescribed scompile.py
wrapper as both sandbox and final library module, with no errors or warnings. No global
build was run and no shared repository source was modified.

## Second reading by Q17

This is the author's second reading; the dispatcher prohibits sub-agents, and independent
review belongs to the maintainer. I reopened the node, the final module, and the source
on printed pp. 294–295. Noetherian, primality, every positive exponent, the literal
prime-power/residue rings, bounded K, all three conditions, the residue-linear comparison,
and the absence of finiteness/invertibility/excellence assumptions match as described
above. I changed the normalization clause from existence of one flat representative
to an equation on every bounded flat representative, and added explicit boundedness of
the residue-linear tensor model. This ensures canonicity is readable in the signature.
The helper map has no sorry; the natural δ and flat models are conclusions of the named
statement, never arbitrary hypotheses. The comparison over k is the normalized composite
through the right-derived unit. The use of boundedness after exact scalar restriction
in condition (ii) is explained explicitly, while (iii) and i retain k coefficients.
