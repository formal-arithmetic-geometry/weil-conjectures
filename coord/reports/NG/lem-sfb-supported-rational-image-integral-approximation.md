## Worker report

The module `Sheaf.Paper.SupportedRationalImageIntegralApproximation` states
`AlgebraicGeometry.ProEtale.supported_rational_image_integral_approximation`, with
one `sorry` and its complete eight-step natural-language DAG proof in its docstring.
Four definitions in the same owning module spell out the notation introduced by
this statement: ordinary abelian localization, supported image sections, integral
image generators, and their isomorphism and extension closure. All four have real
construction bodies, use the existing library functors, and have source/blueprint
docstrings. No independent mathematical notion or new DAG node is introduced.

The released repair note `coord/repair-notes/lem-sfb-supported-rational-image-integral-approximation.json`
was read. Its resolved stage-1 correction is respected: the current assertion is
extension closure, not the withdrawn filtered presentation by direct sums. The
existing statement_change record, proof and all other inherited node fields are
preserved. The inherited source place's wording about a filtered presentation is
historical; the actual current statement and eight-step proof specify extensions.

Clause-by-clause statement correspondence:

- Affine original base: `(X : Scheme.{u}) [IsAffine X]`.
- Small sites and sizes: `X.ProEt` is Mathlib's scheme site, with object universe
  `u+1` and morphism universe `u`; sheaves have values `Ab.{u+1}`. Scheme sites are
  not replaced by a small category with equal object/morphism universes. The etale
  site is imported through its recorded Mathlib module. No etale test-object
  hypothesis, etale cohomological bound, or Noetherianity is imposed.
- Arbitrary support chain: `tree : QcqsOpenClosedTree X` and `p : tree.Path S`.
  The existing `p.extension R` is literally the composite of open `j_!` and closed
  `i_*` for the actual edge maps; root paths give the identity. The endpoint is
  any vertex, not just a leaf. Every allowed chain from an affine X has qcqs
  vertices: qc opens and closed subschemes preserve qcqs. Insert its complementary
  sibling at each edge, as a leaf, to obtain exactly such a finite binary tree.
  Conversely a closed path edge has its specified complementary qc open, and an
  open edge is qc. Thus this encoding neither loses chains nor adds edge types.
  Complementary closed subschemes can be taken reduced; this does not change the
  actual edge in the path. An empty chain uses a root path.
- Prime and finite extension: `(ell : Nat) [Fact ell.Prime]`, a normed field E,
  its normed Q_ell-algebra structure and `[FiniteDimensional Q_ell E]`.
  Using the unique compatible extension norm gives the stipulated norm topology;
  every finite extension has such a model, including E=Q_ell. Scalar carriers are
  small (`E : Type`) as in the recorded continuous coefficient interface; finite
  extensions are small up to their canonical field isomorphism over Q_ell.
- Integral and rational condensed rings: `CondensedRing.integralCoeff ell E`
  uses `continuousIntegers ell E`, and `Profinite.continuousMapRingObj E` is the
  all-continuous rational coefficient ring. These have precisely the norm and
  subspace topologies, rather than finite-subextension or discrete coefficients.
- Finite scalar local models on S: `hL`, `hM` use the recorded scheme predicate
  `HasFiniteConstantLocalModel R S`. Its cover and finitely presented point
  module are existential independently for each module and each covering member.
  The point finite presentation is a finite matrix with entries in R(*), and its
  point inverse image gives the scalar extension required by the node. This is
  not local finite presentation with arbitrary coefficient-function matrices.
- Actual map and actual image: `f : L ⟶ M` in `Mod ... (condensedRingObj R S)`;
  `supportedImageSections` applies `CategoryTheory.Limits.image f`. No closure
  of a topological image, finite presentation of the image, or completeness of
  the image is assumed.
- Affine pro-etale test object: `(U : X.ProEt) [IsAffine U.left]`, with actual
  morphism U.hom. `supportedImageSections` applies `(p.extension R).obj` then
  `(CondensedRing.upperStar R U.hom).obj`, places the result in degree zero with
  `DerivedCategory.singleFunctor _ 0`, and applies
  `(condensedModuleSections R U.left).rightDerivedFunctor.obj`. This is precisely
  ordinary uncompleted module-derived R Gamma with values in D(Ab).
- Integral generators over the same original X: `supportedIntegralImageGenerator`
  takes `(X : Scheme.{u}) (U : X.ProEt)` as fixed parameters and existentially
  quantifies S, tree rooted at X, path, integral L,M with separate local-model
  proofs and an arbitrary actual g. Their chains, modules and maps may vary;
  the test object U and its morphism to X stay fixed throughout the class.
- Ordinary scalar localization of the section complex:
  `abelianPrimeLocalization ell` is the total derived functor of tensoring
  abelian groups with `ULift (Localization.Away (ell : Int))`, i.e. Z[1/ell].
  Tensor with this flat group is exact; hence its right derived functor is the
  termwise localization on every complex and equals its left derived functor.
  For the stipulated constant B-action on C and E=B[1/ell], associativity of
  scalar tensor identifies the underlying abelian complex of C tensor_B^L E
  with C tensor_Z^L Z[1/ell]. This holds for unbounded complexes as well. Thus
  this construction states exactly the requested object in D(Ab), without an
  arbitrary chosen scalar-coordinate action or a replacement condensed tensor.
- Smallest class closed under isomorphisms and extensions:
  `supportedIntegralImageExtensionClosure` quantifies over all object properties
  P for the same fixed X and U with `P.IsClosedUnderIsomorphisms` and `P.IsTriangulatedClosed₂` containing
  the integral generators at that fixed U. Mathlib's latter class closes the middle object of
  a distinguished triangle up to isomorphism; the former closes that isomorphism.
  The resulting intersection is exactly the required smallest class. It does
  not require shifts, all cones, coproducts, filtered diagrams, or decompositions.
- Final conclusion applies `supportedIntegralImageExtensionClosure ell E X U`
  to the rational `supportedImageSections` evaluated at that same U.
  There are no additional mathematical hypotheses or auxiliary choices in the
  theorem's binders, and no theorem besides this item's statement is postponed.

Dependency declarations used (full signatures and construction docstrings read):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme` / `AlgebraicGeometry.Scheme`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale` / `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale` / `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: `None` / `None`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion` / `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` / `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-sfb-module-open-lower-shriek`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` / `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`.
- `def-sfb-module-lower-star`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs` / `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull` / `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.ProfiniteFiniteConstantLocalModel` / `AlgebraicGeometry.ProEtale.HasFiniteConstantProfiniteLocalModel`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` / `Padic.finite_coefficientExtensionRing`.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients` / `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `def-weil-pbc-continuous-integral-coefficients`: `Sheaf.Paper.ContinuousIntegralCoefficientData` / `AlgebraicGeometry.ProEtale.CondensedRing.continuousIntegers`.
- `def-sfb-qcqs-open-closed-tree`: `Sheaf.Paper.QcqsOpenClosedTree` / `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree`.
- `def-sfb-condensed-module-sections`: `Sheaf.Paper.CondensedQcqsPushforwardContinuity` / `AlgebraicGeometry.ProEtale.condensedModuleSections`.
- Proof-only continuity dependency: `lem-weil-pbc-condensed-qcqs-pushforward-continuity` / `AlgebraicGeometry.ProEtale.condensed_qcqs_pushforward_continuity`.

For sk-def-sfb-constructible the recorded module publicly imports the unchanged
scheme predicate in `Sheaf.Paper.CondensedConstantConstructibility`; its newer
profinite-slice companion is not substituted for the scheme predicate. For the
continuous coefficient dependency the actual `integralCoeff`, `continuousIntegers`
and `integralScalarMap` are read from ContinuousIntegralCoefficientData. The
localizing-admissibility predicate is not used to replace the explicitly specified
coefficient rings. Proof dependency modules with recorded declarations are all
imported with proof-only visibility unless already public statement imports.
The tree and section-evaluation nodes are added to stmt_deps because their already
landed declarations are now used explicitly in the statement's notation. The
section-evaluation definition is cited by its owning definition node, rather than
the continuity theorem node; the latter remains in the unchanged proof_deps.

Edge cases checked before writing and again against the final signature:
empty X and S (no Nonempty hypotheses); root path/empty support chain; zero rank,
zero modules and f=0; independent covers/ranks for L and M; E=Q_ell; arbitrary
ell including 2; non-Noetherian affine bases; unbounded derived section complexes.
The zero section complex is an integral generator via the zero map on the root
path. No characteristic restriction, finite torsion-cd or global lattice appears.

Searches (executed using the prescribed msearch.py wrapper):

- LeanFinder: “Supported rational image derived section complexes belong to
  extension closure of rationalized integral image section complexes”: eight
  generic supported-complex declarations, no match for this theorem.
- LeanSearch: “The smallest isomorphism closed extension closed class containing
  rationalizations of supported integral image section complexes”: eight generic
  isomorphism/triangulated closure declarations, no supported-image assertion.
- Loogle: `CategoryTheory.ObjectProperty.IsExtensionClosed,
  CategoryTheory.ObjectProperty.isoClosure`: no match (first name nonexistent).
  Follow-up `CategoryTheory.ObjectProperty.IsTriangulatedClosed₂`: found the
  exact existing triangle-middle closure class and its lemmas, now reused.
- Mathlib grep `extensionClosure|SupportChain` in CategoryTheory: no hits.
  `abelianPrimeLocalization|supportedIntegralImageGenerator|supportedImageSections`:
  no hits. Local rg in Mathlib's triangulated Subcategory found extensionProduct,
  extensionProductIter and IsTriangulatedClosed₂; no existing R_X definition.
- Project rg in WeilConjectures and Sheaf for SupportChain, supportChain,
  supported_rational_image_integral and this exact node id: no existing theorem.
  Concept searches found QcqsOpenClosedTree.Path.extension,
  HasFiniteConstantLocalModel and condensedModuleSections, all reused.
- `tools/blueprint_refs.py search 'support chain'`: zero blueprint nodes.
  The existing tree node, module and signatures were opened directly; no new
  support-chain definition was made. The upstream id search produced no match.

Sources opened: current DAG and resolved repair note; HRS PDF text for Lemma
5.3(1), its bounded-below continuity and proof; current blueprint
`sk-lem-stratified-lattice.proof.md` (lattice scheme and trace); all statement
interfaces above and the existing related supported-image modules. The proof in
this module is attributed to the node's assembly, not falsely claimed to be a
verbatim statement in HRS. No STATEMENT-DISPUTED finding or new statement correction.

## Second reading by NG

This is the worker's own second pass, not a claim of independent agent review:
the dispatcher explicitly forbids starting other agents; the maintainer supplies
independent review after delivery. I reopened the node and final module and checked
each binder and conclusion against the list above. In particular I checked that
paths may end at non-leaf vertices, the root and test object U are fixed for every
generator, and there is no shift closure hidden in the use of
IsTriangulatedClosed₂. I checked actual image rather than its closure, the two
separate finite-model hypotheses, and underlying abelian localization versus
condensed scalar extension. The initial compile had only a long docstring line;
it was split before final validation. The original fixed-U mismatch was subsequently identified by independent review
and is repaired below; the previous claim that varying U matched R_X was incorrect.

## Validation

The initial prescribed scompile.py run compiled sandbox and library modes, reporting
only one line-length warning in the proof docstring. It was corrected, and the final
file was submitted through scompile.py again. The revised file compiled cleanly in both sandbox and library modes. The first
dry run found a record-format mismatch: the signature record included the `:=`
delimiter, whereas preflight expects the signature immediately before it. The
record was corrected without changing the Lean statement. A subsequent dry run
and final delivery use the prescribed wrappers.

## Returned delivery repair: head 58b58cce656c

1. H2: replaced `lem-weil-pbc-condensed-qcqs-pushforward-continuity` in the
   added statement dependencies with the already landed definition node
   `def-sfb-condensed-module-sections` (existing:true, 2026-10-21). I read that
   node's full statement and Lean record and reopened the abbreviation's body
   and docstring at CondensedQcqsPushforwardContinuity.lean:127. The abbreviation
   forgets the internal module action and evaluates at the terminal object,
   exactly the notation this statement uses. The public import stays unchanged;
   the continuity theorem stays in proof_deps and is still used in proof step 6.

2. H3: the returned version incorrectly quantified over affine U inside the
   integral generator, enlarging the generated class. Both
   `supportedIntegralImageGenerator` and `supportedIntegralImageExtensionClosure`
   now take `(U : X.ProEt)` as a parameter after X. The generator's existential
   U and its affine conjunct were removed: affine U is supplied by the theorem's
   existing `[IsAffine U.left]`. Every generator uses this fixed U in
   `supportedImageSections ... p U g`. The closure uses the generator at that U,
   and the theorem's conclusion is the closure at its own U. Only integral
   support chains, modules and actual maps vary. The module and helper docstrings
   and every contrary claim in this report have been corrected accordingly.

The sandbox's retained module and node were compared with the returned content
and current main. The node was reconstructed from current main, then the repaired
Lean record and the two required landed definition dependencies were applied.
The natural-language statement, proof, proof_deps, and inherited correction record
are unchanged. No new nodes or dependency modules are required. Root paths, zero
maps, empty U, and E=Q_ell still occur with exactly the same fixed-U convention.
This section is the worker's repair audit; independent review is the maintainer's.

Repair validation: prescribed scompile.py compiled the repaired module cleanly in
both sandbox mode (17.6 s) and library mode (3.4 s), without errors or warnings.
The signature record is verbatim from the repaired theorem. Compared with current
main, only lean and stmt_deps differ; the latter adds exactly the two landed
definition nodes. The only sorry is this item's theorem proof.
