## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.AffineReflectionDominantDescent states
AlgebraicGeometry.affine_reflection_dominant_descent. Its sole theorem has proof `sorry`.
Eight same-notion helper definitions spell out the orders and shifted actions introduced
by this node; their data are real formulas, with no choices or postponed proof fields.
No natural-language statement, proof, or proof dependency was changed. The recorded,
landed def-sfb-rank-one-root-interfaces was added to statement dependencies because its
actual normalizer quotient is used directly.

Clause-by-clause reading:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  Positive prime characteristic is `(p : ℕ) [Fact p.Prime] [CharP F p]`.
  The primality witness includes positivity and excludes characteristic zero.
- The actual group schemes are `S T B : Grp (Over (Spec (.of F)))`.
  Semisimplicity is `hS : IsSemisimpleGroupScheme S.X`. The binder `hsc` is
  copied verbatim from exists_rho_section_modules: every surjective homomorphism
  from a semisimple group scheme with finite central kernel is an isomorphism.
  Centrality is tested on every commutative F-algebra and every pair of points.
- The inclusions are `iT`, `iB`, and `j`, with `hTB : IsRhoBorelPair iT iB j`.
  This is precisely maximal torus, splitness, Borel, and j followed by iB = iT.
- The character lattice X is the actual additive group of morphisms T to Gm;
  the cocharacter lattice is the actual additive group of morphisms Gm to T.
  The two IsCommMonObj witnesses are the structures already supplied by the
  recorded Borel-pair theorem, rather than new commutativity restrictions.
- `P : RootDatum Φ X X_*`, `b : P.Base`, `[P.IsReduced]` are the recorded
  finite reduced crystallographic root datum and its base. `hconjS`, `hconjB`
  pin the torus actions to conjugation. `hroot` identifies indexed roots with
  the actual character values. `hpair` pins the integer pairing to composition
  with powers of the identity of Gm, exactly as in the dependency theorem.
  `hweights` says roots are exactly nonzero character weights of Lie(S), and
  `hpos` says b.IsPos is exactly the roots in Lie(B). Thus neither the roots,
  pairing, nor choice of positive system can be replaced by an unrelated one.
- The integral half-sum is the character `ρ` with `hρ : 2 • ρ = sum of positive
  roots`. This equation is in the integer character lattice, not in F. In
  particular no inversion of 2 in characteristic 2 occurs.
- W is exactly `RankOneRoots.Weyl iT`, the quotient of the scalar-extension
  normalizer by the torus-point subgroup. Its finiteness is a conclusion.
  The existential `act` has its value on every normalizer representative pinned
  by the displayed conjugation identity after every F-algebra extension.
  `AffineWeight.characterAction` pulls characters back by the inverse of this
  automorphism, so it is the specified action chi(n^-1 t n).
- The dot action is `AffineWeight.dot a ρ w x = a w (x+ρ)-ρ`.
  `reflectionDot P ρ α x` uses Mathlib's actual root-datum reflection.
- `AffineWeight.Dominant P b ρ x` requires every shifted simple coroot pairing
  to be nonnegative, exactly the closed chamber D, including its walls.
- `AffineWeight.LE P b y x` says x-y belongs to the additive submonoid generated
  by the simple roots. This is exactly an integral nonnegative sum, including
  the empty sum. `LT` adds y != x; no total order on the weight lattice is used.
- `Edge P b ρ p y x` quantifies a positive root and an integer n >= 0, requires
  y = s_beta dot x + np beta, and requires y <= x. `Linked` is its reflexive
  transitive closure, oriented from lower to upper weight. It therefore states
  exactly the finite-chain definition of y up-arrow x, including a length-zero
  chain. Equality in an edge is allowed, as in the node.
- Existence of a Coxeter system is a conclusion, not an extra hypothesis:
  `∃ M : CoxeterMatrix b.support, ∃ cs : CoxeterSystem M W`. Its simple elements
  act on every character by P.reflection of the specified simple root. `cs.length`
  is Mathlib's minimum simple-word length. The existential w0 reverses the positive
  roots and its length is the positive-root finset's cardinal N. This realizes
  the node's Coxeter-length and longest-element clause without an arbitrary
  numerical length function or a reflection-group replacement for W.
- `WellFounded` is asserted for the strict root order on the subtype of weights
  in D, exactly the node's ancillary well-foundedness assertion.
- The function d is a conclusion. For each y, the first conjunct asserts d(y) in
  D, the second says it is in y's finite dot orbit, and the last says every
  element of that orbit in D equals d(y). Thus d is uniquely characterized and
  is not chosen from a bare existence proposition in a definition.
- The final clause quantifies x in D, a simple root alpha, and w in W with
  `cs.length (cs.simple α * w) = cs.length w + 1`. It first concludes r >= 0,
  where y is explicitly the dot action on x. It then quantifies every integer k
  with 0 < kp < r and every z equal to s_alpha dot y + kp alpha, and concludes
  both `LT P b (d z) x` and `Linked P b ρ p (d z) x`. Quantifying z together with
  its defining equality avoids a non-unfoldable statement `let` and is equivalent
  to the node's instruction to put z equal to that expression.
- Q = Z Phi, the opposite Borel, rational modules, one-dimensional modules,
  homogeneous bundles, cohomology and simple constituents are context conventions
  repeated in the node; no conclusion in this root-geometric lemma mentions them.
  They supply no additional hypothesis on x, alpha, w, k or the group scheme, so
  no artificial binders or constructions of unused representation objects appear.

Dependency declarations read and reused:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic:
  IsAlgClosed (the relevant algebraically-closed clause of the closure leaf).
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, Grp, IsMonHom;
  group schemes are their specializations in Over(Spec F), as the recorded node says.
- Sheaf.AlgebraicGeometry.RhoSectionModules: IsRhoBorelPair and the full signature
  and docstring of exists_rho_section_modules, including its simply-connected binder.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure:
  reductive_borel_pair_structure, semisimpleGroupScheme_isReductive; full signatures
  and docstrings read. The character, coroot, action and positive-root binders are
  exactly its interface for an already selected Borel pair.
- Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces: normalizer,
  torusInNormalizer, Weyl, and Character, using the recorded all-algebra normalizer.
- Mathlib.LinearAlgebra.RootSystem.Defs and Base: RootDatum, RootPairing.reflection,
  Base.support and Base.IsPos. Mathlib.GroupTheory.Coxeter.Length: CoxeterSystem.length;
  Basic: CoxeterSystem and simple. Mathlib.Logic.Relation: ReflTransGen.
- The stated proof dependency rho_regular_weyl_orbit is imported privately from
  Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit. The source declaration
  and full docstring were read. The other proof dependencies had no Lean record or
  Mathlib match in the read snapshot: semisimple-roots-span, weyl-reflection-realization,
  simple-root-reflection-generation, root-sign-word-deletion and
  simple-chamber-fold-affine-step. Their natural-language statements were read;
  their future imports belong to maintainer bookkeeping. They are not assumed as
  hypotheses of this theorem. The eight proof steps in this theorem's docstring
  retain every part of the node's proof plan, including length(w0)=N.

Edge cases checked before and after writing:

- Empty root system: no Nonempty assumption on the root index or simple-root
  subtype; the sum and N are zero. The rank-zero Weyl group has the empty Coxeter
  system. Semisimplicity makes X = 0; D is a singleton and strict order is empty.
  The error clause is vacuous because there is no simple root.
- Reducible systems: no irreducibility or connected Dynkin-diagram assumption.
  One base, closed chamber and dominance submonoid work component by component.
- Singular shifted weights: the chamber is closed. Orbit representatives are
  unique as weights, with no uniqueness assertion for the Weyl element. r=0
  permits no integer k satisfying the strict inequalities.
- Characteristic 2 is included. Integer multiplication and the integral half-sum
  equation are independent of field arithmetic. There is no p>h restriction.
- Empty linkage chain is included by ReflTransGen.refl. Level n=0 and zero
  simple-root difference are allowed for lowering edges.
- All schemes and test algebras use the dependency's universe u. No independent
  smaller test-algebra universe, connectedness assumption on Phi, or total
  lattice ordering is introduced. The generic helper universes are explicit.

Searches made:

- msearch.py leanfinder: “The dominant representative of an affine reflection error
  weight is strictly lower and strongly linked to the original dominant weight”.
  Eight hits: LieAlgebra.IsKilling.reflectRoot, RootPairing.coxeterWeightIn_le_four,
  LieAlgebra.IsKilling.le_chainBotCoeff_of_rootSpace_ne_top,
  RootPairing.chainTopCoeff_reflectionPerm_right/left,
  RootPairing.coxeterWeightIn_ne_four, RootPairing.Base.IsPos.reflectionPerm,
  RootPairing.chainBotCoeff_reflectionPerm_right. These are reflection, root-string
  or Coxeter-angle lemmas, not the chamber, linkage or descent assertion.
- msearch.py loogle: “RootPairing.Base, length”. No hits, unknown identifier length.
  Direct reading of Mathlib/GroupTheory/Coxeter/Length.lean then found the existing
  Coxeter length; this existing definition is used, never copied.
- msearch.py leansearch: “dominant Weyl dot orbit chamber representative strong
  linkage order”. Eight hits including span_orbit_eq_top, rootForm restriction,
  coxeterWeightIn_le_four and generic order-theory declarations. No match.
- msearch.py grep: strongLinkage|dotAction|dominant.*reflect|reflect.*dominant|affineWeyl.
  Zero hits in Mathlib. Direct rg in lean/Sheaf and lean/WeilConjectures for
  strongLink, StrongLink, dotAction, DotAction, dominantRepresentative,
  affineLower/AffineLower and rootDominance/RootDominance found no definitions.
  grep for this blueprint id in lean/WeilConjectures returned no occurrence.
  DAG searches for CoxeterSystem, root dominance, strong linkage order and dot
  action found this item and its consumers/geometry prerequisites, no definition
  node or usable recorded declaration for this same notion.
- Source correspondence: read the current blueprint direct-images proof (3).
  Andersen's PDF is absent locally, as the node itself records. Retrieved and read
  the original Goettingen OCR pages 54, 55, 57 and 58, from
  https://gdz.sub.uni-goettingen.de/fulltext/PPN243919689_0315/00000058?_format=xml
  (likewise pages 00000059, 00000061 and 00000062). Definition 1 gives the
  finite lowering chains; Proposition 1 and Lemma 1 give dominant chamber
  reduction; Lemma 5 gives strict descent and strong linkage. Andersen takes
  positive roots opposite the roots of his Borel, which is exactly the node's
  use of B-minus for cohomology. No source correction is necessary.

Validation: scompile.py checked both the temporary sandbox module and the final
library module separately, successfully, within the standard 60-second limit.
No error or unexpected warning remains. No statement dispute or dependency repair.

## Second reading by Q143

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
