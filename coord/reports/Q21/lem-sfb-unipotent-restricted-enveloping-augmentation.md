## Worker report

Item: lem-sfb-unipotent-restricted-enveloping-augmentation. The module is
Sheaf.AlgebraicGeometry.GroupScheme.UnipotentRestrictedEnvelopingAugmentation.
Its theorem AlgebraicGeometry.BorelDistributions.unipotent_restricted_enveloping_augmentation
states the complete item, with one sorry and its six-step proof plan. The helper
leftInvariantOperator is the explicit linear composite `(id tensor a) Delta`, followed
by the right tensor unitor. It has real data. No other theorem or definition is postponed.

The node statement is unchanged. Three already-landed definition nodes were added to
stmt_deps: def-sfb-restricted-enveloping-algebra,
def-sfb-affine-group-distribution-calculus, and def-sfb-semisimple-group-scheme.
No new node and no dependency repair was necessary. In particular this delivery does
not duplicate the restricted quotient, coaction predicate, or semisimplicity predicate.

Hypothesis and object correspondence:

- F algebraically closed of prime characteristic p>0 is `(F : Type u) [Field F]
  [IsAlgClosed F] (p : Nat) [Fact p.Prime] [CharP F p]`. Prime implies p>=2.
- S, T, B are bundled `Grp (Over (Spec (.of F)))`, using the recorded group-scheme
  interface. `hS : IsSemisimpleGroupScheme S.X` spells out smoothness, connectedness,
  affineness, finite type, and the absence of nontrivial smooth connected solvable
  normal subgroups. This existing definition uses scheme-theoretic derived series.
- Simply connected is `hsc`: every semisimple S' with a surjective group morphism
  to S and finite central kernel is an isomorphism. `IsFinite (GrpObj.ker f).hom`
  is finite-dimensional coordinate algebra over F. The kernel centrality equality
  is quantified over all F-algebras and all kernel and S' points, so includes
  nonreduced algebras and every further scalar extension. The test algebra universe
  is u, the base field universe, as in the existing group-scheme interface.
- `iT`, `iB`, `jT`, and `hTB` are the inclusions T in B in S and their compatibility.
  `hT` is the recorded maximal torus predicate. `hsplit` is an isomorphism to the
  existing split torus for some rank including zero. `hB` is the recorded Borel
  predicate, defined by maximal smooth connected solvable closed subgroups.
- U is a scheme over F with its actual group structure. The affine instance exposes
  its coordinates; it restricts no radical, since U is a closed subgroup of the
  affine B. `iU` is the inclusion into B. `hU` gives closedness, normality,
  smoothness, connectedness and the recorded geometric-matrix unipotence condition,
  and the universal factorization from every subgroup with those properties. It
  therefore says precisely that U is the largest such subgroup.
- The existing actions `ModObj T.X S.X` and `ModObj T.X B.X` are pinned by
  `hconjS` and `hconjB` to conjugation along iT and jT. They are not arbitrary
  representations. The commutative-object instances expose the additive Hom groups
  defining the character and cocharacter lattices.
- `Phi` in the file (Lean identifier `Φ`) is the finite root set inside the actual
  additive character group `Additive (T --> Grp.mk (StandardGroupSchemes.multiplicative F))`.
  `P` is its integral RootDatum on the actual character and cocharacter groups;
  `[P.IsReduced]`, `b : P.Base`, `hroot`, `hpair`, `hweights`, `hpos` identify its
  roots, pairing and positive system with those of the stated torus action and B.
  The pairing is pinned to composition with integer power maps. These are the
  data specified in the node by reference to reductive_borel_pair_structure.
- `πT`, `hπT`, `hker`, `hsd` specify the given projection B to T: identity on T,
  kernel U by its pullback square, and the product isomorphism U times T to B.
  This is exactly the semidirect-product interface of the recorded dependency.
- Q=S/B is contextual in this item: none of its conclusions depends on a choice
  of quotient representative. The imported reductive_borel_pair_structure already
  provides Q and its torsor; this theorem does not introduce an unrelated Q.

Conclusion correspondence:

- The Lie algebra is the existing `GrpObj.Lie (U.asOver (Spec (.of F)))`, with its
  existing commutator bracket and F-module structure. No replacement Lie algebra
  or bracket is supplied as a hypothesis.
- The conclusion produces a linear map d into the existing coordinate convolution
  dual, with `d x f` equal to the epsilon coefficient of the actual dual-number
  tangent point, expressed using `GrpObj.tangentPoint`, `appTop`, `ΓSpecIso`, and
  `.snd`. Thus d is fixed pointwise, not an arbitrary representation.
- The conclusion produces q and requires
  `leftInvariantOperator F U (d (q x)) = leftInvariantOperator F U (d x) ^ p`.
  Since multiplication of endomorphisms is composition, this is precisely the
  pth-iterate definition of x^[p] in the node. Evaluation of D_x at the identity
  recovers d x, and the affine dual-number tangent map is injective; thus this
  characterization fixes q uniquely. There is no choice of an uncharacterized
  structure and no extra hypothesis assuming the desired restricted operation.
  `LieAlgebra.IsRestrictedOperation F p q` records its three standard identities.
- A is literally the existing `RestrictedEnvelopingAlgebra F (GrpObj.Lie ...) p q`.
  Its definition is the tensor quotient by ALL bracket and p-relations, with the
  same signs as the node, and `RestrictedEnvelopingAlgebra.ι` is its generator map.
- `Module.finrank F A = p ^ Nat.card {α : Φ // b.IsPos α}` is dim A=p^N,
  with N the number of positive roots. Nat.card counts this finite subtype without
  demanding an extraneous decidability instance or excluding the empty case.
  The RHS is positive; finrank is zero on an infinite-dimensional space, so this
  equality does not permit a spurious infinite-dimensional interpretation.
- The augmentation ε is concluded as `A -->ₐ[F] F`, so is unital and fixes F;
  its value on every Lie generator is required to be zero. The tensor quotient is
  generated by these generators and scalars, so these conditions fix ε uniquely.
- J is `RingHom.ker ε.toRingHom`; this is Mathlib's left-ideal presentation of the
  two-sided kernel. Its inherited ideal power is the ordinary product ideal even
  for a noncommutative algebra. `exists h : Nat, 1 <= h and ker ε ^ h = bot`
  says precisely J^h=0 for some h>=1, not merely that each element is nilpotent.
- Rational W is universally quantified as `(W : Type v) [AddCommGroup W] [Module F W]`
  with `c : W -->ₗ[F] W tensor[F] Γ(U, top)` and the existing
  `IsCoordinateCoaction (.of F) U c`. The latter is exactly coassociativity and
  the counit identity. No finite-dimensionality assumption occurs.
- The conclusion gives `ρ : A -->ₐ[F] Module.End F W`, a unital action. Its value
  on each Lie generator is the existing `moduleAction (.of F) U c (d x)`, whose
  definition is `(id_W tensor d x) c`. Thus it is exactly differentiation of the
  specified coaction. The final generator identity explicitly says
  `ρ (ι (q x)) = ρ (ι x)^p`.
- For U isomorphic to the trivial group, the final implication gives an F-algebra
  isomorphism A with F and `RingHom.ker ε.toRingHom = bot`, rendering A=F and J=0.
  It does not impose U nontrivial or any nonempty root-family hypothesis.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic:
  IsAlgClosed (both underlying dependency matches read at their declarations).
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj and Grp;
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: group-scheme terminology,
  IsClosedSubgroupScheme and IsNormalSubgroupScheme.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure:
  AlgebraicGeometry.reductive_borel_pair_structure and
  semisimpleGroupScheme_isReductive; full signature and proof docstring read.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  ReductiveTorusCentralizer.IsMaximalTorus; Sheaf.AlgebraicGeometry.GroupScheme.Borel:
  IsBorelGroupScheme; Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights:
  TorusCharacterTangent.weightSpace, using genuine torus characters.
- Sheaf.AlgebraicGeometry.GroupScheme.Semisimple: IsSemisimpleGroupScheme,
  IsSolvableGroupScheme and its actual derived-series definition.
- Sheaf.Algebra.Lie.RestrictedEnvelopingAlgebra: RestrictedEnvelopingAlgebra,
  RestrictedEnvelopingAlgebra.ι, LieAlgebra.IsRestrictedOperation and tensor relations.
- Sheaf.AlgebraicGeometry.GroupScheme.AffineGroupDistributionCalculus:
  BorelDistributions.fullDual, IsCoordinateCoaction, moduleAction and the canonical
  affine-coordinate Hopf instances. The module was read in full.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic, Lie.Bracket, Lie.Ring,
  Lie.Differential: GrpObj.Lie and tangentPoint and their commutator interpretation.
- Proof-only imports: Sheaf.Algebra.Lie.RestrictedPBWBasis,
  RestrictedEnvelopingAlgebra.exists_restricted_pbw_basis; and
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections,
  AlgebraicGeometry.RankOneRoots.reductive_rankOne_reflections. Their full
  signatures and docstrings were read. The regular-cocharacter and rational-
  differentiation proof inputs have no Lean record at inspection, so there is no
  module to import for them. Their mathematical proof steps remain in the docstring.

Edge cases checked before finalization: U=1 and empty positive roots give N=0,
p^N=1, A isomorphic to F, J=0 with h=1. Prime p=2 is included. The operation q
is NOT asserted zero on all vectors: the nilpotence proof only uses zero p-operation
on root basis vectors, so it remains valid at bad primes and with nonzero p-map
on sums. W=0 and infinite-dimensional W are included. Semisimple products and
rank-zero tori are included; there is no simple-group or nonempty-base assumption.

Searches (2026-10-24):

- msearch.py leanfinder: "The restricted enveloping algebra of the Lie algebra of a
  Borel unipotent radical has dimension p to the number of positive roots and
  nilpotent augmentation ideal". Eight hits: ordinary UniversalEnvelopingAlgebra,
  root construction and Cartan/rank results; no restricted augmentation theorem.
- msearch.py loogle: "UniversalEnvelopingAlgebra, IsNilpotent". Zero hits.
- msearch.py grep: "restricted.envelop|nilpotent.*augmentation", Algebra. Zero hits.
- msearch.py leansearch: "The augmentation ideal of a restricted enveloping algebra
  of a Borel unipotent radical is nilpotent". Eight hits: ordinary enveloping and
  Lie-algebra nilpotence; none is the assertion about associative ideal powers.
- rg of lean/WeilConjectures and lean/Sheaf for restrictedEnvelop,
  RestrictedEnvelop, restricted_rational, unipotent_restricted, semisimple and
  simply-connected terminology: found and reused Q20's restricted quotient and
  Q27's distribution/coaction definitions and existing semisimple/Borel interfaces.
  The assigned theorem has no existing declaration. grep -rn of the assigned
  blueprint id in lean/WeilConjectures: no hit.
- rg of both project trees and Mathlib for leftInvariantOperator and
  unipotent_restricted_enveloping_augmentation: no existing names.
- tools/blueprint_refs.py search "restricted enveloping": zero blueprint matches;
  ancestor of this item is null. No new definition node is introduced.

Source reading: Milne's local PDF, Definition 10.39, Theorem 10.40 and the
paragraph before Proposition 11.36, including the invariant-derivation pth-power
construction. The node's six proof steps and their stated root-theoretic references
are carried in the theorem docstring. No mathematical statement fault found.

Validation: prescribed scompile.py, 60 seconds per file, server fallback: clean in
3.0 seconds. The first run found only a missing Fintype instance on the positive-root
subtype; Nat.card repairs that without a hypothesis. The local wrapper reported
no disk space, then successfully used its built-in server confirmation path. No
launcher file, live Lean file, or shared repository was modified directly.

## Second reading by Q21

I reopened the completed Lean file and the unchanged node for a separate reading
pass. The dispatcher requires one worker and explicitly prohibits starting agents;
this is a fresh pass by the author, not a claim of review by a second agent. The
maintainer's independent review remains the independent check.

Checked every binder and conclusion against the correspondence above. In particular,
hsc retains finite central kernels on every test algebra; hU is largest, not just
some unipotent subgroup; hconjS/hconjB and hweights/hpos fix actual roots and their
sign; hker is the kernel of the specified πT. The datum d is fixed by tangentPoint,
and q by powers of the actual invariant operator, so no arbitrary endomorphism
enters as an assumption. The same q is used in the tensor quotient, augmentation
and module identities. The dimension counts all positive roots, not only the
simple base support. Ideal nilpotence has one uniform positive exponent, not a
pointwise nilpotence condition. W has no dimension restriction, and the trivial-U
clause has no excluded zero case. No mismatch found. Corrected a source-section
label in the docstrings from 11e to 11h (the cited printed page 223 and proposition
were already correct). No statement correction was required.
