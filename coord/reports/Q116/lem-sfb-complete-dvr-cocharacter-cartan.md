## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CompleteDvrCocharacterCartan`
states `AlgebraicGeometry.completeDvr_cocharacter_cartan`. Its single theorem has
proof `sorry`; it introduces no definitions, choices, instances or other theorems.
The accepted stage-1 split and its proof are preserved. Only `lean` and the
addition of the already landed terminology node to `stmt_deps` change.

The previous ending was a stage-1 unchanged-split refusal. The current node has no
Lean record, is a stage-2 queue item, and has no repair note. The explicit stage
handoff in brief-stage2 §0 permits this stage-2 statement; no reviewed split is reopened.

The source was read at https://sites.math.washington.edu/~jarod/papers/iwahori.pdf:
Theorem 1.3 (1) implies (3), Definition 3.4, Remark 1.2, Lemma 3.6 and its proof.
In particular Theorem 1.3 and Section 4 explicitly remove the algebraically closed
residue-field restriction in Theorem 1.1. The latest blueprint unit and its direct-image
proof (3) were also read; this remains a supporting input to the recorded route.

Hypotheses and clauses, in node order:

* A DVR: `(A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]`.
  The Mathlib class is a local principal ideal domain whose maximal ideal is nonzero.
* Uniformizer: `(pi : A) (hpi : Irreducible pi)`. The recorded dependency's
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies this precisely with
  `IsLocalRing.maximalIdeal A = Ideal.span {pi}`; in particular pi is nonzero.
* Fraction field: `(K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]`.
  The embedding used in evaluation is exactly `algebraMap A K`.
* Completeness: `[IsAdicComplete (Ideal.span ({pi} : Set A)) A]`, using the recorded
  adic-completion dependency. Its Hausdorff and precomplete conditions are equivalent
  to bijectivity of the natural map to the inverse limit. Including n=0 adds only
  A/(1)=0, so gives the same inverse limit as n≥1 in the node.
* The A-group scheme is `(H : Grp (Over (Spec (.of A))))`; `Grp` bundles an actual
  scheme over Spec A with `GrpObj` multiplication, identity and inverse. These are
  the recorded group-scheme dependency's diagrams, now over the specified base A.
* Affine, smooth and finite type: `[IsAffine H.X.left] [Smooth H.X.hom]`
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`. As Spec A is affine,
  affineness of the underlying scheme is equivalent to the structure morphism being
  affine. Locally finite type plus quasi-compact is precisely finite type.
* Reductive geometric fibres: `hred` quantifies over every algebraically closed field
  Ω and every ring homomorphism `f : A →+* Ω`, and applies
  `ReductiveTorusCentralizer.IsReductive` to
  `((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj H)`.
  This is the actual geometric base change with its transported group law, not an
  unrelated group over Ω. The existing predicate requires smooth affine finite type,
  connectedness after algebraic closure, and triviality of every connected normal
  smooth closed unipotent subgroup. Over Ω these are exactly the node's fibre clauses.
  Its `SolvableGroupStructure.IsUnipotent` uses a faithful closed matrix representation
  with all geometric matrices unipotent, as required. Smoothness is included in that
  predicate, so there is no unintended test on nonsmooth subgroup schemes.
* G_m over A is used directly as
  `(Spec (.of (LaurentPolynomial A))).asOver (Spec (.of A))`, equipped with the
  canonical Laurent Hopf algebra `GrpObj` supplied by Mathlib. It has the specified
  multiplication of units. The existing field-only `StandardGroupSchemes.multiplicative`
  is not applied to A and no second definition is introduced.
* H(B) is the hom-set `Spec B` over `Spec A` to `H.X`, with its existing `GrpObj`
  pointwise group operation (`open scoped MonObj`). In particular `g` ranges over
  every K-point. The existential `a b` range over maps from the terminal A-scheme,
  i.e. precisely H(A).
* A cocharacter is the existential `lambda` in `Grp (Over (Spec A))`, from the
  specified G_m to H; this is an actual A-group homomorphism.
* Evaluation at pi: `t` is a morphism from `Spec K` to this G_m whose underlying map
  is REQUIRED to equal `Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂
  (algebraMap A K) (Units.mk0 (algebraMap A K pi) ...)))`.
  The unit is exactly the image of pi; nonvanishing follows from hpi and the
  fraction-field injection. The coordinate map takes constants by A→K and T^n to
  pi^n. Forgetting from Over is faithful, so this equality uniquely fixes t.
  It is merely an explicit encoding of the canonical evaluation, not an arbitrary
  evaluation parameter or extra mathematical conclusion. The specified ring map is
  over A, since Laurent evaluation restricts on constants to `algebraMap A K`.
* The last equality is exactly `g = a_K * lambda_K(pi) * b_K`:
  precomposing `a` and `b` with `toUnit (Spec K over Spec A)` is extension A→K,
  while `t ≫ lambda.hom.hom` is evaluation followed by the cocharacter. Order of
  multiplication agrees with the source and node; no commutativity is assumed.
* There is no condition on the residue field, no chosen maximal torus, no splitness,
  no restriction on characteristic, and no assumption of semisimplicity.

Dependency declarations read and used:

* `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
* `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, `AdicCompletion`.
* `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`;
  the recorded `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documentation and
  `CategoryTheory.IsMonHom` give the same group-scheme and homomorphism conventions.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
* `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (through the existing
  reductivity predicate); it includes nonemptiness, as the dependency requires.
* Added the already landed `def-sfb-reductive-torus-centralizer-terminology` to
  stmt_deps and publicly imported its module
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`, using
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive` verbatim. Read its full
  signature and its implementations of geometric connectedness and unipotence in
  `SolvableGroupStructure` / `ToriMultiplicativeType`.
* `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra` and
  `Mathlib.AlgebraicGeometry.Group.Affine`: the actual Laurent Hopf group scheme and
  `instGrpObjSpecAsOverSpec`, valid for commutative base rings, not just fields.
* `Mathlib.RingTheory.Localization.FractionRing`: `IsFractionRing` and its `injective`.
* Proof-only imports of the stated proof dependencies:
  `Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle`
  (`AlgebraicGeometry.Scheme.exists_scheme_of_zariski_cocycle`) and
  `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`
  (`AlgebraicGeometry.RepresentedRightTorsor`). The other four proof-dependency
  nodes have no Lean record yet, so there is no module to import. The theorem's
  docstring retains their exact role and the complete four-step proof.

Edge cases checked before writing:

* The trivial group is allowed: a=b=1 and the unique trivial cocharacter work.
* For G_m, the assertion is the DVR unit-times-integer-power factorization;
  negative powers are allowed by Laurent polynomials and K-units.
* g=1 allows the trivial cocharacter and a=b=1. The cocharacter is never required
  to be injective or nontrivial; no torus rank is required to be positive.
* An anisotropic reductive torus over a complete DVR is not excluded. The theorem
  can use its trivial cocharacter, consistent with the integral-point case.
* Arbitrary positive or zero residue characteristic, imperfect residue fields and
  nonclosed residue fields are all retained. The zero ring and fields cannot
  satisfy the DVR assumptions; pi=0 and pi a unit cannot be uniformizers.
* Universes are explicitly bound, `autoImplicit false`. Schemes, their coordinates,
  K, Ω and algebraic closures use the same standard scheme universe u. All geometric
  points required for finite-type schemes can be tested in this universe; no smaller
  independent test universe or empty/vacuous field quantifier was imposed.

Searches made (2026-10-24):

* msearch.py leanfinder: “Cartan decomposition of points of a reductive group scheme
  over a complete discrete valuation ring using cocharacters”: eight hits on Lie
  algebra Cartan subalgebras/root spaces, no scheme Cartan decomposition.
* msearch.py loogle: “GrpObj, IsMonHom, Reductive”: zero hits, reports unknown
  unqualified identifier GrpObj. Direct source inspection supplied the actual API.
* msearch.py grep: “[Cc]ocharacter|[Rr]eductive|[Uu]nipotent”, AlgebraicGeometry:
  zero matches in Mathlib. The notion of field reductivity is in the project.
* msearch.py leansearch: “reductive group scheme complete discrete valuation ring
  Cartan decomposition”: eight valuation/uniformizer/DVR results, no decomposition.
* rg on Mathlib AlgebraicGeometry and project WeilConjectures/Sheaf for
  reductive/Reductive, cocharacter/Cocharacter, Unipotent/unipotent and Cartan/cartan:
  found the existing field predicate and standard field group schemes; no existing
  complete-DVR cocharacter Cartan theorem. A node-id search of WeilConjectures had
  no match. `dag/lean_names_upstream.json` supplies no such theorem.
* DAG search and `tools/blueprint_refs.py search 'multiplicative group'`:
  the existing `def-sc-gm-ga` is a field group-scheme definition; Mathlib's canonical
  Laurent Hopf construction already handles A without any replacement node.
  `tools/blueprint_refs.py ancestor` confirms the inherited ancestor is None; no
  new node or statement correction is necessary.

No STATEMENT-DISPUTED finding or statement correction. Compilation used only the
prescribed scompile.py server wrapper. The first probe diagnosed a missing
`open scoped MonObj`; adding that scope made the exact statement compile cleanly.

## Second reading by Q116

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
