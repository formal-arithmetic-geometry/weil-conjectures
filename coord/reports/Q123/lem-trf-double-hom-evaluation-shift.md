## Worker report

This is a stage-2 statement delivery, not a reopening of the accepted Q68 stage-1 split.
The live node has a stage-1 reviewed record but no lean or reviewed_lean record.
Q68's accepted report explicitly says that no Lean was written or compiled.
The sandbox was empty at the start of this continuation.

The module Sheaf.Algebra.Homology.DoubleHomEvaluationShift states
CategoryTheory.DoubleHomEvaluationShift.signed_evaluation_shift, with sorry.
Its auxiliary definitions are real specializations, maps and component evaluations
of the existing product Hom and total tensor. There is one postponed theorem,
matching this item's DAG statement, with the complete six-step proof in its docstring.
No new node, dependency repair or statement correction is needed.

Hypothesis and clause correspondence:

- The commutative ring is {R : Type u} [CommRing R], with explicit universe u.
  Complex R is CochainComplex (RingSiteModules R) ℤ. RingSiteModules uses exactly
  the constant ring R on Discrete PUnit with bottom topology. Thus this is the
  one-object-site encoding expressly allowed by the node, for every ring universe.
- P, J and I are independently bound arbitrary Complex R, with no K-flatness,
  K-injectivity, boundedness, nontriviality or finiteness hypothesis. The source
  conventions of homComplex give product Hom with d(f)=d_target f-(-1)^n f d_source.
  The Mathlib cochain shift is X[m]^n=X^(n+m), with differential (-1)^m d_X.
- A=Hom(J,I) is hom J I. G(P)=Hom(Hom(P,J),I) is hom (hom P J) I.
  tensor is the recorded CochainComplex.mapBifunctor of curriedTensor, giving
  the direct-sum total with the usual sign on the second differential.
- The existential E has type tensor (hom J I) P ⟶ hom (hom P J) I, so it is a
  chain map. Its pure-tensor conjunct states E(h tensor x)(f)=(-1)^(bc)h(f(x)).
  Here a=degree h, b=degree x, c=degree f; value uses homComplexπ and evaluates
  at the identity object of the slice. The output index a+b+c is explicit.
  The equation quantifies over every product-Hom family f, without a finite-support
  restriction. pure uses the existing sheafification unit and total summand inclusion.
- The existential s U V m is hom (U⟦m⟧) V ≅ (hom U V)⟦-m⟧ for all U,V,m.
  Its first conjunct explicitly projects its degree-q component and requires
  the source-reindexing sign (m*q).negOnePow. Its second conjunct states naturality
  contravariantly in U and covariantly in V. No arbitrary normalization is allowed.
- tensorShift is exactly Mathlib CochainComplex.mapBifunctorShift₂Iso. Its
  homogeneous-component conjunct states h tensor x maps to (-1)^(ma) h tensor x,
  after the canonical shift degree identifications. Its naturality equation is
  asserted for every chain map p and every induced map homMap j i on A.
- χ is an existential chain isomorphism G(P[m]) ≅ G(P)[m]. Its defining equation
  is m.negOnePow times homMap (s P J m).inv (identity I), followed by
  s (hom P J) I (-m), followed by the canonical equality transport -(-m)=m.
  This is exactly (-1)^m s_outer composed with inverse Hom(s_inner,I).
- The following χ conjunct gives the explicit component formula: after shifting
  the target degree n to n+m and projecting at c, the map equals
  (m*(n+c)).negOnePow times projection at c+m followed by precomposition with
  reindex P J m c. reindex is the unsigned graded source reindexing defined from
  the recorded Hom product universal property; it adds no chain-map premise.
  χ naturality in all three complexes is the doubleMap equation.
- The final conjunct is E (P⟦m⟧) J I ≫ χ.hom = tensorShift.hom ≫ (E P J I)⟦m⟧'.
  Mathlib's composition order is left-to-right, so this is precisely the node's
  χ composed with E_shift = E[m] composed with τ, as equality of chain maps.

Dependency declarations used and read in full:

- def-pc-cochain-complex-modules: CochainComplex,
  Mathlib.Algebra.Homology.HomologicalComplex, with its chain-map category.
- def-weil-abstract-derived-category: DerivedCategory and HasDerivedCategory,
  Mathlib.Algebra.Homology.DerivedCategory.Basic; only the cochain-shift convention
  is needed here, so no HasDerivedCategory hypothesis is imposed.
- def-pur-hom-complex: CategoryTheory.homComplex and homComplexFunctor,
  WeilConjectures.Algebra.Homology.HomComplex, including its product and differential
  specification. These are used directly, never replaced by the differently
  normalized CochainComplex.internalHomObj.
- def-pc-tensor-complex-sheaves: CochainComplex.mapBifunctor and curriedTensor,
  Mathlib.Algebra.Homology.BifunctorShift; SheafOfModules.monoidalCategory is the
  existing sheaf-module structure.
- Added the already landed def-pc-ring-hom-extension-shared-definitions to stmt_deps:
  CategoryTheory.RingSiteModules and CochainComplex.onePointRingSheaf from the
  public imports of Sheaf.Algebra.Homology.RingHomExtensionDefs.
- Added the already landed lem-sc-hom-complex-projections to stmt_deps:
  CategoryTheory.homComplex_projections_exists in
  WeilConjectures.Algebra.Homology.HomComplexProjections and its component API
  homComplexπ and homComplexIsLimit in HomComplexComponents. This exposes the
  exact projections chosen with the recorded homComplexFunctor.
- Added the already landed def-sc-hom-tensor-degreewise-equation to stmt_deps:
  CategoryTheory.homTensorCurrySectionMap in
  WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation. This gives the
  prescribed map from presheaf pure tensors into the sheaf tensor.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree provides the
  existing additivity instances needed by Mathlib's tensor-shift isomorphism.
  No new instance or second monoidal structure is defined in this delivery.

Searches performed:

- msearch.py leanfinder, "For arbitrary cochain complexes signed double Hom
  evaluation commutes with every integer shift": eight hits on HomComplex cochain
  shifts, shift components, inverses and differential formulas; no full evaluation
  square. Results are retained in searches.jsonl, digest 415045c2594458ef.
- msearch.py loogle, '"HomComplex", "leftShift"': twelve hits on component
  leftShift and inverses/additive equivalences; no double-evaluation theorem.
  Digest 0cc552485b97450b.
- msearch.py grep, 'doubleHom|evaluation|leftShift_comp' in
  Algebra/Homology/HomotopyCategory/HomComplexShift.lean: three matching lines,
  395, 411, 414, about composition of cochain shifts. Digest 277e2e05bcba2352.
- rg of doubleHom/DoubleHom/double_hom/evaluation-shift across lean/WeilConjectures
  found unrelated double-homology and derived-section transport. Exact blueprint-id
  grep found no declaration. rg across lean/Sheaf found SignedDoubleHomCone,
  CoefficientBidualEvaluationShiftOne and DerivedEvaluationCanonicalMap. I opened
  those interfaces: the first two use one target and/or shift one, and the last is
  a derived-level statement. None states this arbitrary-complex chain-level square.
  Existing component and tensor APIs found by these searches are reused.

Source checked: literature/stacks-project/more-algebra.tex,
lemma-evaluate-and-more (0A60), remark-sign-explanation (0A61), and sign-rules.
The Stacks construction uses the Koszul swap sign, giving exactly |x||f|.
The all-integer source-shift normalization is explicitly the agent calculation
already accepted in the node, not an unmentioned Mathlib normalization.

Edge cases checked before writing: m=0 gives identity comparisons; m=1 and m=-1
use the same parity calculation. For a=1,b=c=0,m=1 both square signs are -1.
The parity difference 2m(b-m) works for positive and negative m. In characteristic
2 all signs become 1. Zero complexes and the zero ring give zero maps. Arbitrarily
unbounded complexes are retained: homogeneous tensors have finite support while
Hom elements may have infinitely many nonzero coordinates. J and I remain distinct.
No statement dispute or source correction was found.

Validation: compiled through scompile.py only, against the live server. Initial
elaboration fixes supplied the existing tensor additivity import, specified the
section ring in the pure tensor, and fixed the ring-sheaf argument in homObjMap.
These are interface annotations, not changes to hypotheses or conclusions.

## Second reading by Q123

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
