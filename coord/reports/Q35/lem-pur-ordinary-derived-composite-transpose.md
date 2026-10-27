## Worker report

The module Sheaf.SmoothPurity.OrdinaryDerivedCompositeTranspose states
WeilConjectures.PurityFiniteSetting.ordinaryDerivedCompositeTranspose, with proof
`sorry`. No definition or theorem proof is added. The current Q70 stage-1 split,
including its statement, statement dependencies, proof and proof dependencies,
is retained verbatim; this is a stage-2 delivery, not another stage-1 split.

Hypothesis and clause correspondence:

- The finite-field and finite coefficient datum is `P : PurityFiniteSetting.{u}`.
  Its field, coefficient prime different from the characteristic, finite
  coefficient extension, valuation-ring quotient and positive exponent are the
  published fields/constructions. `P.Ring` is O_E/(varpi_E^n), and `P.Coefficient`
  is exactly its ordinary size lift ULift into u+1, with the published ring instance.
- The separated finite-type k-schemes are `X Y B : Over (Spec
  (CommRingCat.of P.field.k))`, each with `IsSeparated`, `LocallyOfFiniteType`
  and `QuasiCompact` on its structural arrow. The last two classes mean finite
  type. The arrows `f : X ⟶ Y`, `g : Y ⟶ B` are k-morphisms by the definition
  of Over; their actual scheme maps are `f.left`, `g.left`.
- `D(T)` is rendered as `DerivedCategory (Sheaf (ProEt.topology T.left)
  (ModuleCat.{u+1} P.Coefficient))`. This is the published fixed-scalar
  presentation of the ordinary derived category of sheaves of A-modules on
  the small pro-etale site, with the standard size lift of A. It is the
  same category presentation used by the recorded finiteDirectImageComposition.
  It is not a bounded, constructible, complete or integral category.
- `P_u` is `(upperStar (ModuleCat.{u+1} P.Coefficient) u).leftDerivedFunctor`,
  the existing K-flat total derived inverse image. `R_u` is the matching
  lowerStar.rightDerivedFunctor, computed by K-injectives. The adjunction,
  including its normalization, is the existing derivedUpperStarLowerStarAdjunction.
  These are the original finite-coefficient operations publicly reexported by
  the recorded ordinary-operations dependency, not new copies of operations.
- `alpha` is the existing `ProEtale.leftDerivedUpperStarComp`, whose definition
  derives the ordinary canonical pullback comparison and then uses the derived
  composition comparison. Its full source docstring explicitly specifies
  composite-to-iterated direction. In the fixed-scalar presentation this is the
  same termwise K-flat comparison prescribed by the pullback-composition node;
  there is no arbitrary isomorphism parameter. Both sides act on the original
  small sites, with their actual object and morphism universes.
- `kappa` is exactly the dependency's `finiteDirectImageComposition P.Coefficient
  f.left g.left`. Its definition is the inverse of rightDerivedFunctorCompIso'
  applied to the fibre-product-pasting lowerStarComp, with preservation of
  K-injectives supplied by the exact inverse-image adjunction. Thus the theorem
  retains the required K-injective normalization, rather than defining kappa
  to be a mate or choosing a fresh adjunction on isomorphic functors.
- `M`, `Q`, `N` range over all three ordinary unbounded derived categories.
  `w` and `v` have exactly the node's types. They are arbitrary morphisms.
- The node's h is expanded each time as `w ≫ R_g.map v ≫ kappa.inv.app N`.
  Its transpose on the left is explicitly `P_gf.map h ≫ epsilon_gf.app N`.
- The first conjunct is the first displayed equality: the latter transpose
  equals `alpha.hom.app M ≫ (adj_g.comp adj_f).homEquiv.symm
  (h ≫ kappa.hom.app N)`. Lean's composition order is left to right.
- The second conjunct is the second displayed equality: that same intermediate
  expression equals `alpha.hom.app M ≫ P_f.map
  (P_g.map w ≫ epsilon_g.app Q) ≫ (P_f.map v ≫ epsilon_f.app N)`.
  Thus both w-hat and v-hat are the exact counit-defined transposes in the node.
- The third conjunct states the final 'in particular' clause before alpha:
  the composite-Hom-bijection transpose of `w ≫ R_g.map v` equals
  `P_f.map (P_g.map w ≫ epsilon_g.app Q) ≫
  (P_f.map v ≫ epsilon_f.app N)`.
- There is no properness, boundedness, constructibility, acyclicity, K-flatness
  of the objects, or assumption about comparison compatibility in the signature.
  The comparisons are fixed published constructions, not supplied hypotheses.

Dependency declarations and source signatures read:

- def-pur-conventions: Sheaf.Paper.PurityFiniteSetting,
  WeilConjectures.PurityFiniteSetting, Ring, Coefficient and their ring instances.
  The structure and quotient/lift definitions were read in full.
- def-weil-pbc-proetale-operations:
  Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations and its publicly imported
  intrinsic finite operations. The fixed-scalar originals used here are
  AlgebraicGeometry.ProEtale.upperStar, lowerStar and
  derivedUpperStarLowerStarAdjunction, from the published
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient modules. The derived
  adjunction has precisely upperStar.leftDerivedFunctor left adjoint to
  lowerStar.rightDerivedFunctor on ordinary unbounded categories.
- def-weil-scheme-morphism-properties is explicitly a convention node. Its
  collected Mathlib properties are used directly, namely IsSeparated,
  LocallyOfFiniteType and QuasiCompact; it has no declaration/module of its own.
- lem-pur-proetale-constant-ring-composition:
  Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition,
  Scheme.proEtaleCoefficientInverseImageMap_comp. Its full equation and finite
  coefficient hypotheses were read; it is imported for the normalization step.
- lem-weil-pbc-proetale-derived-pullback-composition:
  Sheaf.Paper.IntegralFinitePullbackComposition,
  WeilConjectures.integralTowerGeneralPullbackComposition and its reexported
  Scheme.proEtaleCanonicalPullbackComposition. Their arbitrary ring-sheaf
  signatures, composite coefficient transport and flat-term K-flat
  characterization were read. For the fixed-scalar presentation used in this
  theorem, the actual existing comparison is ProEtale.leftDerivedUpperStarComp
  in WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar;
  its signature, construction and docstring were read in full. The integral
  module is imported to retain the stated dependency; no integral operation is
  used in place of a finite one.
- lem-weil-derived-direct-image-composition:
  Sheaf.Paper.FiniteDirectImageComposition,
  ProEtale.finiteDirectImageComposition, read in full and used literally.
- lem-sfb-ringed-derived-monoidal-comparisons:
  Sheaf.SixFunctors.RingedDerivedMonoidalComparisons,
  CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons.
  Its system and normalized adjunction/comparison meaning supply the proof's
  comparison compatibility, not additional assumptions. This is a plain proof
  import. Its normalization proof and composite counit equation were read.
- def-weil-pbc-composite-adjunction is a Mathlib leaf:
  Mathlib.CategoryTheory.Adjunction.Basic, CategoryTheory.Adjunction.comp.
  The actual comp construction, comp_homEquiv and comp_counit_app were read;
  comp and its actual inverse Hom bijection occur in the statement.

Sources read locally: sites-cohomology.tex, lemma-adjoint and
lemma-derived-pushforward-composition (Tags 07A6, 0D6E), and categories.tex,
lemma-compose-counits (Tag 0DV0). The source proves direct-image composition
using pullback composition and uniqueness of adjoints; the retained DAG proof
specifies the additional normalization and explicit naturality calculation.
The declaration docstring carries all four retained proof steps.

Edge cases checked before writing: both identity maps reduce the equations to
v composed with w; one identity leaves the single-adjunction calculation.
Zero source, intermediate or target object, or either zero arrow, is permitted
and yields zero morphisms. Empty schemes are allowed as objects of Over, and
no nonemptiness is imposed on their sites. The least positive finite level
n=1 is included in P; level zero is excluded by the node's conventions.
Unbounded objects and nonproper maps remain permitted. Every final morphism
has source P_gf M and target N, except the explicitly stated final consequence
which has source P_f P_g M. No independent site-universe equality is imposed.

Searches made:

- msearch leanfinder: 'The transpose of a composite under derived pullback
  pushforward adjunction equals successive transposes through the canonical
  composition isomorphisms'. Eight hits, including underived
  Scheme.Modules.conjugateEquiv_pullbackComp_inv and ExponentiableMorphism
  pushforwardComp. None states the prescribed ordinary-derived K-injective
  compositor formula.
- msearch leansearch: 'The transpose of a composite through two right adjoints
  equals the composite of the successive transposes under the canonical derived
  composition isomorphism'. Eight hits, including Adjunction.comp_homEquiv,
  comp_rightAdjointMate and rightDerivedNatTrans_comp. These are general pieces,
  not the full fixed-compositor statement.
- msearch loogle: 'CategoryTheory.Adjunction.comp'. Twelve hits including comp,
  comp_homEquiv and comp_counit_app. They give the composite adjunction, already
  the dependency's Mathlib match, but not its identification with these fixed
  derived comparison maps. An earlier comma-separated query also naming
  Functor.rightDerivedFunctorCompIso returned zero hits with that upstream-only
  identifier unknown to Mathlib's search; it was replaced by the working query.
- msearch grep: 'comp_homEquiv|comp_counit_app|conjugateEquiv_pullbackComp'
  in CategoryTheory/Adjunction returned six relevant abstract adjunction hits.
- rg of Mathlib, lean/WeilConjectures and lean/Sheaf for the item id and proposed
  declaration name found no declaration of this node. Concept searches located
  the published canonical pullback, adjunction and direct-image comparison
  definitions used here, plus underived adjunct_comp_comparison helpers; the
  latter do not state the prescribed derived assertion.

No statement correction, disputed statement, new node or dependency repair was
needed. Only the item's lean field changes. The statement was compiled using
scompile.py in both sandbox and library module modes; both passed with no
unexpected warning (6.2 s and 7.0 s respectively).

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
