## Worker report

The module Sheaf.Paper.FiniteFieldHomEtaleWitness states
AlgebraicGeometry.ProEtale.finiteField_hom_etale_witness. It contains three real
presentation helpers and one theorem with `sorry`; it proves no new theorem.
The node's mathematical statement, proof, and proof dependencies are unchanged.
Its statement dependencies gain the already landed
lem-sf-finite-discrete-normalized-encoding, used by the coefficient transport.
There are no new nodes or dependency repairs.

Hypothesis and clause matching:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Arbitrary positive-characteristic ground field: `(k : Type u) [Field k]`,
  `[Fact (ringChar k).Prime]`; a field has positive characteristic precisely when
  its characteristic is prime. The exclusion is `[Fact (ringChar k ≠ l)]`.
  There is no finiteness, perfection, or separable-closedness assumption on k.
- Finite field A of characteristic ell: `(A : Type u) [Field A] [Finite A]
  [CharP A l]`. `finiteFieldCondensedRing A` is the recorded continuous-map
  condensed ring, with the discrete topology explicitly installed in its body.
- X over k: `[X.Over (Spec (.of k))]`. Separatedness is `IsSeparated` of that
  structure map; finite type is `LocallyOfFiniteType` and `QuasiCompact` of it.
  Quasi-compactness and quasi-separatedness of X itself are `[CompactSpace X]`
  and `[QuasiSeparatedSpace X]`, exactly as in the recorded dependency notes.
- `A_X` is `condensedRingObj (finiteFieldCondensedRing A) X`, the actual monoidal
  inverse image from the point. No separately supplied coefficient sheaf occurs.
- C_P,C_Q are in the ordinary unbounded derived category of fixed-scalar module
  sheaves on the original small etale site. These are the retained constant-ring
  module presentation of def-pe-etale-constructible-module. `ULift A` merely
  accommodates the existing additive sheaf universe u+1, retaining the same field.
- Their boundedness is `DerivedCategory.TStructure.t.bounded C_P` and the same
  for C_Q. For every q, `Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf`
  applied to their derived homology expresses the recorded finite locally closed
  stratifications and locally constant finitely generated module values. Over
  a field, finitely generated means finite-dimensional. For finite-type X over k,
  finite affine-cover refinement identifies this affine-local predicate with
  the finite global stratification in the item's wording. No stalk-only or
  site-perfect predicate is substituted.
- `finiteFieldEtalePullback` is the actual `comparisonUpperStar` localized by
  `mapDerivedCategory`, then transported to internal modules. Thus its images
  are exactly P and Q. `finiteFieldEtaleInternalHom` is the actual ambient
  `CondensedRing.derivedHom` applied contravariantly to P and covariantly to Q.
- The first three conjuncts use `constantModelBoundedConstructible` for P,Q,J,
  so boundedness and finite constant local-model constructibility are retained
  for all three objects.
- `∃ D : CochainComplex ... ℤ` followed by ordered m,n and
  `D.IsStrictlyGE m ∧ D.IsStrictlyLE n` requires an actually bounded complex,
  not merely a bounded object of the derived category.
- `∀ q, IsAffineLocallyConstructibleEtaleModuleSheaf (D.homology q)` supplies
  constructible finite-dimensional cohomology of this complex.
- `Nonempty (finiteFieldEtalePullback.obj (DerivedCategory.Q.obj D) ≅ J)` is the
  requested isomorphism in the ambient derived category, not a degreewise claim.
- The same D precedes `∀ a b, a ≤ b → ...`. The antecedent is vanishing of every
  cohomology object of J outside [a,b]. The conclusion quantifies over EVERY
  degree-zero etale module sheaf N and every q outside that interval, requiring
  `IsZero` of the cohomology of the genuine `Etale.derivedTensor` of Q(D) with
  `(DerivedCategory.singleFunctor _ 0).obj N`. Neither test modules nor bounds
  are restricted by constructibility, finite dimension, or a chosen resolution.
- The final existential ordered interval, with the same tensor tests and the
  same D, explicitly records the stated finite Tor amplitude consequence.

The three helpers belong to the object's own canonical coefficient presentation:
`finiteFieldFixedToInternal`, `finiteFieldEtalePullback`, and
`finiteFieldEtaleInternalHom`. Their definitions have real data. The first uses
`FiniteDiscreteOrdinary.encoding_exists`, which is already proved, and whose
Encoding specifies ringIso.normalization on every constant scalar,
ordinary_functor = sectionEncoding ringIso, and fixed_functor = fixedRestriction.
The normalization determines the ring map by the constant-sheaf adjunction;
these two forward functors are therefore fixed, and their adjoint inverses are
unique up to natural isomorphism. This is not a choice of an unconstrained
functor, arbitrary coefficient isomorphism, or arbitrary comparison map. All
uses here are invariant under those unique isomorphisms. The discrete topology
is installed explicitly inside the transport definition; no file-local instance
or notation is needed to read any statement. The server accepted the identity
of this continuous coefficient construction with `finiteFieldCondensedRing`.

Dependency declarations read and used:

- sk-def-sfb-dc-setting: the recorded
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
  interface says the setting is expressed by explicit field and scheme binders;
  no compactification is used or chosen in this theorem.
- sk-def-sfb-condensed-ring: Profinite.CondensedRing in
  Sheaf.Topology.ProfiniteCondensedRing is the general ring-object encoding;
  here its existing discrete-field specialization is finiteFieldCondensedRing
  in Sheaf.Paper.FiniteFieldInternalHomFiniteness, with its MonObj and
  IsCommMonObj instances.
- sk-def-sfb-pulled-back-coefficients: condensedRingObj and coefficientRing in
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic use upperStarFromPoint.
- sk-def-sfb-derived-tensor-hom: CondensedRing.derivedHom in
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom is the ambient
  relative closed internal Hom, not a Hom restricted to a perfect subcategory.
- def-weil-pbc-site-comparison-morphism: proEtaleSiteComparisonModules in
  Sheaf.AlgebraicGeometry.ProEtaleSiteComparison identifies the original-site
  comparisonUpperStar/comparisonLowerStar adjunction; we use comparisonUpperStar.
- def-weil-pbc-quasi-compact-scheme: Mathlib CompactSpace. Its definition is
  compactness of the whole space without a Hausdorff condition.
- def-weil-quasi-separated-morphism: Mathlib AlgebraicGeometry.QuasiSeparated
  says the diagonal is quasi-compact; the scheme form is QuasiSeparatedSpace.
- def-pe-etale-constructible-module: the recorded
  Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules publicly retains
  ConstructibleNoetherianEtaleModules and its original-site
  Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf. This exactly states the
  dependency's notion for our successor-universe coefficients, so no repair is
  needed and no copy of constructibility is defined.
- sk-def-sfb-constructible: constantModelBoundedConstructible and its finite
  scalar-model predicate in Sheaf.Paper.CondensedConstantConstructibility.
- Added landed interface lem-sf-finite-discrete-normalized-encoding:
  FiniteDiscreteOrdinary.Encoding, encoding_exists and Encoding.fixedDerived,
  in Sheaf.Paper.FiniteDiscreteOrdinaryEncoding, as explained above.
- Proof dependencies are imported: ConstructibleProEtaleComparison,
  ProEtaleClassicalSheavesModules, ConstantFieldTorBounds,
  ProEtaleFiniteTorComparisonNoetherian, FiniteFieldInternalHomFiniteness,
  Mathlib DerivedCategory.TStructure (exists_iso_Q_obj_of_isGE_of_isLE), and
  Mathlib ShortComplex.PreservesHomology (Functor.homologyFunctorIso).
  CondensedConstantConstructibility is public through the field finiteness module.

Edge cases checked: the empty scheme and zero input complexes are allowed.
In the zero case every ordered interval must work, as it does for the zero
model. There is no lower bound on an endpoint, so negative degrees and a=b are
included. Nontrivial finite fields exclude the zero ring by Field, as the
source requires. Characteristic zero for k and p=ell are excluded explicitly,
not inferred from site-perfectness. Nonfinite and nonperfect base fields remain
in scope. No equality between site object and morphism universes is imposed:
the original sites retain objects in u+1 and morphisms in u. The finite field
is in Type u and its module values in Type (u+1), through the fixed ULift.

Sources read: Stacks proetale.tex, lemma-compare-constructible and
lemma-compare-constructible-derived (09AL), and the current blueprint
sk-cor-pe-finite-tor-comparison-noetherian.proof.md, especially the Tor-amplitude-
detected paragraph. The original node supplies the Bhatt--Scholze extraction;
the proof docstring retains its five steps and all hypotheses.

Searches (fresh results in searches.jsonl):

- msearch leanfinder: "Derived internal Hom of bounded constructible finite
  field sheaves descends to a bounded etale complex with the same Tor interval".
  Eight hits: light condensed closed structures/projectivity, derived fractions,
  sheaf cohomology, and the condensed abelian instance; no witness theorem.
- msearch loogle: `"DerivedCategory", "constructible"`: zero hits.
- msearch grep: `(constructible|etale|proetale).*(internalHom|derivedHom)|
  (internalHom|derivedHom).*(constructible|etale|proetale)`: zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, finiteField Hom,
  EtaleWitness and FiniteFieldHom: no exact witness declaration. Existing field
  internal-Hom finiteness is reused, and IntegralGeneralLfpHomFiniteness has a
  different integral-coefficient residue witness, not this statement.
- Further source searches located the normalized Encoding and the original-site
  constructibility interface; both were read and reused rather than copied.

No STATEMENT-DISPUTED issue and no statement correction.
Validation: scompile.py Q68 lem-sfb-finite-field-hom-etale-witness compiled the
complete delivered file as sandbox and library module, without errors or
unexpected warnings (12.8 s and 8.0 s respectively). All variables and universes
are explicit and autoImplicit is false. The theorem alone is postponed.

## Second reading by Q68

Self-audit of the node and full file, pending the maintainer's independent review
(the dispatch forbids starting other agents). The separate P,Q,J conclusions,
strict bounds on actual terms of D, constructibility of D's cohomology, derived
isomorphism, universal interval for the same D, and explicit final finite-Tor
consequence are all present. Bounds occur after the existential D, and the
cohomology antecedent refers to J. The tensor is the ambient K-flat etale tensor,
with N placed in degree zero; it is not an underived substitute. The fixed-scalar
encoding is justified by the dependency's retained original-site declaration and
the added normalized coefficient-encoding dependency. No mismatch was found;
no original mathematical statement was changed.
