## Worker report

The module Sheaf.AlgebraicGeometry.ProjectiveTorusFixedWeightSchemes states
AlgebraicGeometry.ProjectiveTorusFixedWeights.projective_torus_fixed_weight_schemes.
It has one theorem, whose whole proof is `sorry`; all other declarations contain real
definitional data. No statement correction or dependency repair is made.

Sources read: Milne, Algebraic Groups (2017), printed pp.138--139 (Theorem 7.1 and
its definition of fixedness), pp.234--235 (Definition 12.11, Theorem 12.12 and
Remark 12.13), and pp.274--275 (Example 13.50, Lemma 13.51, and its following
paragraph). These were read from the local PDF with pdftotext. The extra chart and
arbitrary-closed-subscheme clauses are exactly the universal-algebra calculations
already present in this node's accepted proof; they do not require smoothness or
connectedness of X. The eight proof steps are included in the theorem docstring.

Hypotheses, with their Lean rendering:

* k is an arbitrary field: `{k : Type u} [Field k]`. E is an arbitrary vector space
  in the independent universe v, finite dimensional and nonzero:
  `{E : Type v} [AddCommGroup E] [Module k E] [FiniteDimensional k E] [Nontrivial E]`.
* The finite direct-sum decomposition is `V : Ω → Submodule k E`,
  `[Finite Ω]`, `hV : DirectSum.IsInternal V`, and `hne : ∀ ω, V ω ≠ ⊥`.
* The adapted basis requested in the node is `b : Module.Basis I k E`, with finite
  nonempty I. `c : I → Ω` assigns its block. The equation `hc` says that the span
  of the basis vectors assigned to ω is exactly V ω. Thus the restricted basis
  identifies V ω with the coordinate space on `{i : I // c i = ω}`. This states
  the node in its explicitly chosen adapted coordinates, without restricting E to
  a predetermined coordinate space. DecidableEq instances are only computational
  choices on finite indices, available classically for every such decomposition.
* Rank r is an arbitrary natural number. `MultiplicativeType.splitTorus k r` is
  the existing iterated product of the recorded G_m; rank zero is the tensor unit.
* `ρ : splitTorus k r ⟶ Grp.mk (GeneralLinearGroup I k)` is an actual morphism in
  the category of group schemes, not a representation of T(k). The existing
  GeneralLinearGroup.homMulEquiv evaluates it as an invertible matrix on every
  k-algebra A. The scalar-extended basis b.baseChange A interprets that matrix as
  an automorphism of A tensor_k E, canonically symmetric to E tensor_k A.
* The characters `χ ω` are group-scheme morphisms to the recorded G_m;
  `hχ : Function.Injective χ` says they are distinct. The scalar weight condition
  `hρ` tests the basis vectors after every algebra extension, so by A-linearity it
  gives scalar action on every vector of each scalar-extended block. It uses the definition-owned
  TrivialTorusCoherent.characterValue, followed by Scheme.ΓSpecIso, to pull back
  the actual Laurent coordinate and identify its value as an element of A.
* The Laurent exponents are `n : Ω → Fin r → ℤ`; `hn` equates the character with
  the product of the powers of the recorded torus coordinates on every test
  scheme W. torusCoordinate recursively uses the actual Cartesian projections.

Conclusions, clause by clause:

* `projective k I` is the existing ProjectiveSpace I (Spec k), over Spec k. In
  basis b these are homogeneous line coordinates on P(E). No new Proj model is
  substituted for the dependency's base-change projective space.
* The leading unique-existence assertion supplies its induced projective action.
  IsInducedAction fixes the action on every tuple generating the unit ideal over
  every test algebra: it is the actual matrix transform of homogeneous sections.
  Local triviality of an invertible sheaf makes this a characterization of the
  entire action morphism. This action is asserted to exist, rather than imposed
  as an additional existence hypothesis or chosen from unspecified data. The
  rest of the conclusion holds for every action with that characterization.
* Existence of a separating group-scheme cocharacter is the first existential
  conjunction, with `m : Ω → ℤ` injective and
  `lam.hom.hom ≫ (χ ω).hom.hom = (𝟙 G_m) ^ m ω`. Powers here are pointwise powers
  in the group of morphisms to G_m. The next universal quantifier takes every
  cocharacter and every exponent family satisfying exactly those conditions.
* The displayed disjoint union is the categorical coproduct in Over (Spec k) of
  the projective spaces on the restricted bases. Each jω is normalized by
  IsBlockInclusion, extending homogeneous tuples by zero outside its block.
  `Sigma.ι _ ω ≫ j = jω ω` fixes the total inclusion, and
  `IsClosedImmersion j.left` asserts that this coproduct is a closed subscheme.
* `RepresentsFixed a (𝟙 _) j` and `RepresentsFixed a lam.hom.hom j` identify this
  very same inclusion with both fixed functors. RepresentsFixed means unique
  factorization of every algebra-valued point. IsFixed quantifies over every
  A-to-B algebra map and every B-valued group point. In particular nilpotents,
  finite base fields and nontrivial line bundles on Spec A are included; the
  definition of fixedness is not limited to globally represented coordinate tuples.
* The equality of inverse-image opens under a.smul and the second projection
  states invariance of every entire standard chart D_+(z_i). The kernel of
  j.left.app on that chart equals chartIdeal c i. This ideal is literally the
  span of coordRatio i j for c j distinct from c i. This is an equality of ideals,
  not radicals, supports, or conditions only on geometric points.
* X is any object over Spec k, with any torus action aX and any closed immersion
  i into P(E). The displayed equation is equivariance of its action morphisms.
  `pullback.fst i j` is the actual fibre-product inclusion; it is asserted closed
  and to represent both universal fixed functors of X.
* `chart i q` is X intersect D_+(z_q), with its actual inverse-image open and
  structure map. It is asserted affine. The existential action aU is constrained
  by equivariance of chartInclusion, so it is the restriction of aX. The pullback
  of pullback.fst i j to this open is closed and represents both fixed functors
  on that open. This is precisely the final inverse-image clause of the node.

Dependency declarations read and used:

* def-weil-field: Mathlib.Algebra.Field.Defs, Field (line 180).
* def-weil-finite-dimensional-subspace: Mathlib.LinearAlgebra.FiniteDimensional.Defs,
  FiniteDimensional (line 75, abbrev Module.Finite).
* def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp, GrpObj and Grp;
  and WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, its documented
  specialization to Over (Spec k). Homomorphisms are bundled Grp morphisms.
* def-sc-gm-ga: Sheaf.AlgebraicGeometry.StandardGroupSchemes, multiplicative,
  multiplicativeGroup, affine and map. Their definitions use the canonical
  Laurent Hopf algebra and the algebraic Spec functor.
* def-sc-general-linear-group: its recorded Sheaf.AlgebraicGeometry.LinearGroupSchemes
  publicly imports WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.
  The latter's GeneralLinearGroup and homMulEquiv (lines 48 and 68) supply the GL
  scheme and all algebra-valued automorphisms, exactly as its lean.note directs.
* def-nagata-projective-space-base-change:
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace, ProjectiveSpace (line 129).
* def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  IsClosedImmersion (line 45).
* def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, Scheme (line 42) and its Hom.
* def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  pullback and pullback.fst (lines 95 and 111), used in Over (Spec k). Their
  underlying scheme square is the fibre product by the limit creation in Over.
* Two existing landed nodes were added to stmt_deps under brief-stage2 §5:
  def-sfb-tori-multiplicative-type supplies MultiplicativeType.splitTorus in
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType; and
  def-sfb-trivial-torus-coherent-data supplies Character and characterValue in
  Sheaf.AlgebraicGeometry.TrivialTorusCoherentData. The evaluator takes an arbitrary
  group scheme T and test scheme W; here W is Spec A. Its result is converted by
  (Scheme.ΓSpecIso (.of A)).hom to the scalar in A. No theorem node is used as
  a statement dependency for character evaluation.
* Projective coordinate helpers are existing homOfSections, standardOpen and
  coordRatio in ProjectiveSpace.OfSections and ProjectiveSpace.OfInvertible.
  Generic internal actions use Mathlib.CategoryTheory.Monoidal.Cartesian.Mod.
* Stated proof dependencies are imported privately: ProjectiveSpaceStandardCharts,
  ProjectiveSpace.LinearCombination (ratio extensionality), RelativeProj.Functoriality,
  FreeProjectiveBundleBaseChangeSpace, and ProjectiveSpectrum.Basic. The remaining
  unstated proof lemmas are not duplicated; this statement does not require them
  to elaborate. Mathlib quotient, gluing and localization primitives are present
  through those imports.

Edge cases checked before writing and again after elaboration:

* r=0: there are no projections and hn uses the empty product, which is 1.
  Injectivity forces at most one weight; E nonzero and the direct sum force one.
  Trivial lam is allowed and all chart ideals are zero.
* One character, including repeated basis weights within its nonzero block:
  separation is vacuous, all chart generators are absent, and the whole projective
  space is fixed. The quantification over cocharacters includes the trivial one.
* E=0 is excluded by the node, explicitly by Nontrivial E; I empty and Ω empty
  cannot occur for a nonzero direct sum. No positive-rank assumption is introduced.
* Empty X is allowed: there is no point hypothesis, and inverse-image opens and
  fibre products may be empty. All universal factorization conditions still type.
* Finite fields, positive characteristic, nonreduced test algebras, and the zero
  test algebra are allowed. The definition uses universal algebra extensions,
  not finding a rational torus element with distinct evaluated eigenvalues.
* E's universe is independent of k's. Test algebras have the same small universe
  as k and the existing Scheme/CommAlgCat interface, as in the source's convention
  of small k-algebras; there is no independent smaller test universe making a
  quantifier vacuous.

Searches actually run for this item:

* msearch.py leanfinder, “A split torus acts diagonally on a projective space and its
  fixed subscheme is the disjoint union of projective weight spaces”: 8 hits,
  including Projectivization.smul_def, LieModule.disjoint_genWeightSpace and
  Rep.diagonal_succ_projective. These concern projective points over fields,
  Lie weights, or projective objects, not this universal scheme statement.
* msearch.py loogle, “Projectivization, FixedPoints”: 0 hits, with unknown identifier
  FixedPoints reported by the service; no usable match was obtained.
* msearch.py grep, “fixedSubscheme|cocharacter|[Tt]orus.*[Pp]roject”: 0 hits.
* rg over WeilConjectures and Sheaf for torus, cocharacter, fixed schemes and
  projective actions found DiagonalProjectiveAction, FixedScheme,
  SchemeActionFixedIdeal, TorusFixedSchemeSmooth, CentralTorusFaithfulWeightBlocks,
  and ToriMultiplicativeType. Their full relevant interfaces were read. The first
  has a coordinate-action predicate for a different affine Proj model, FixedScheme
  is a correspondence equalizer, and SchemeActionFixedIdeal concerns an abstract
  subgroup of automorphisms. None states this theorem. The last two supply the
  existing product torus and the former evaluator. The repair uses instead the
  exact evaluator owned by def-sfb-trivial-torus-coherent-data, as detailed below.
* rg for the item id in WeilConjectures returned no match. Searches for the chosen
  theorem name and helper names found no existing declaration.
* tools/blueprint_refs.py search “projective weight fixed” and “fixed subfunctor”:
  both returned 0 blueprint nodes. DAG searches for fixed-subfunctor terminology
  found related fixed-scheme lemmas but no duplicate of this statement.

The prescribed scompile.py checks were run after each elaboration repair. Initial
syntax fixes parenthesized a dependent Hom return type, used image notation for the
span of adapted basis vectors, and renamed the cocharacter binder from the reserved
lambda glyph. DirectSum requires DecidableEq on Ω. The unused-Fintype warning was
repaired by using Finite Ω. The final module is checked again by deliver2.py.

## Second reading by Q83

This is the author's final check; independent mathematical review is performed by the
maintainer, as the dispatcher brief specifies. I reread the node, source and final
signature together. The action initially appeared as given data with its normalization;
I changed this to assert unique existence of the induced action, then state the result
for every such action. Thus the formal statement does not assume availability of an
otherwise unconstructed projective action. I checked that j is constrained by the
actual block coordinate inclusions, that the chart assertion gives the ideal itself,
and that the X clause uses a fibre product followed by another fibre product on its
open charts. Both fixedness predicates include all algebra extensions. There are no
hollow definitions, unbound variables, or additional postponed theorem declarations.


## Returned finding repaired

The single H2 finding at immutable head 0a2400e7d703 is repaired. The theorem node
lem-sfb-central-torus-faithful-weight-blocks has been removed from stmt_deps, and its
module CentralTorusFaithfulWeightBlocks is no longer publicly imported. No part of
that theorem's conclusion is used. Explicit imports of LinearGroupSchemes,
TensorProduct.Basis and DirectSum.Module supply the GL and linear-algebra definitions
formerly obtained through that public import.

The existing definition node def-sfb-trivial-torus-coherent-data owns the module
Sheaf.AlgebraicGeometry.TrivialTorusCoherentData and lists the plain definition
AlgebraicGeometry.TrivialTorusCoherent.characterValue in its lean.declarations. I read
that node's full statement and record, and the definition and docstring in its source
(lines 76--82). It takes an arbitrary group scheme T, its group-scheme character
written additively, an arbitrary test scheme W and its T-point, and pulls back the
Laurent coordinate along t followed by the character. The relevant source is Milne,
Definition 12.45; the evaluator is documented at that source in its owning module.
This is an existing definition-owned interface of the kind requested in the return.
The node is added to stmt_deps and its module is publicly imported.

In hρ the replacement scalar is now
`(Scheme.ΓSpecIso (.of A)).hom (TrivialTorusCoherent.characterValue
(MultiplicativeType.splitTorus k r) (Additive.ofMul (χ (c i)))
(StandardGroupSchemes.affine k A) t)`.
Unfolding characterValue gives exactly the former characterScalar expression:
ΓSpecIso sends to A the pullback of LaurentPolynomial.T 1 along t followed by χ.
Additive.ofMul only wraps the same character; it does not change its morphism.
The evaluator imposes no affineness, smoothness, characteristic or field-closure
assumptions on the torus and no reducedness assumption on the test algebra.
Consequently every hypothesis and conclusion of the previously reviewed statement
retains the same meaning, including the rank-zero and one-character cases.

I compared the retained sandbox node with current main using parsed JSON, without
Git commands in the read-only checkout: there were no changes outside the delivery's
lean and stmt_deps fields. The repaired record is based on the current main node,
with the revised verbatim Lean signature. deliver2.py will build its commit on current
main. No new node or dependency module is needed, and no other node is changed.
The final author rereading checked the replacement against both definitions and
confirmed the theorem node and its public import are absent. The prescribed compile,
dry run and delivery are rerun for this repaired module.
