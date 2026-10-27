## Worker report

The module `Sheaf.AlgebraicGeometry.RhoTensorSquareInvariantLine` states
`AlgebraicGeometry.RhoSection.tensorSquareInvariantLine` with a `sorry` proof.
The only helper, `tensorSquareEvaluation`, is a real linear construction: it composes
multiplication in the test algebra with the two recorded evaluations and the inclusions
of the actual section subspaces, then applies `TensorProduct.lift`.
It is a canonical map belonging to this node, listed in `lean.declarations`.
No new independent notion, dependency replacement or statement correction is needed.
Only the item's `lean` field changes.

Hypotheses and conclusion, clause by clause:

- An algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- An F-group scheme S: `S : Grp (Over (Spec (.of F)))`.
- Semisimplicity: `hS : IsSemisimpleGroupScheme S.X`, the same predicate as the
  rho-section dependency. It includes smoothness, affineness, connectedness, finite type,
  and absence of nontrivial smooth connected solvable normal closed subgroups.
- Simple connectedness: `hsc` is verbatim the dependency's condition on every semisimple
  S', every surjective homomorphism f with finite kernel and kernel central on every
  commutative F-algebra: `IsIso f`.
- Split maximal T and Borel B with T contained in B contained in S:
  `T B`, the maps `i j k`, and `hTB : IsRhoBorelPair i j k`.
  That predicate includes maximality, an isomorphism with a split torus of any finite
  rank, the Borel condition, and `k ≫ j = i`.
- The character rho and its extension from the dependency: the data `a`, `ha`, `Φ`,
  `ρ`, `ρB`, `hΦnodup`, `hΦ`, `hρ`, `hρB`, `hU` reproduce its specifications.
  `ha` fixes a to actual conjugation; `hΦ` gives exactly the nontrivial character
  weights in Lie(B); `Φ.Nodup` ensures the product counts each root once;
  `hρ` is rho squared = product of the positive roots, in the character lattice,
  without division by two in F; `hρB` states that rhoB restricts to rho, and `hU`
  states triviality on every closed connected normal unipotent subgroup.
  These binders unpack the instruction to use the rho data of the dependency;
  they do not postulate an arbitrary representation or an extra representation property.
- Each integer m >= 1 is rendered by `(m : ℕ) (hm : 0 < m)`. The positive integers
  are exactly the positive natural numbers; no positive integer is omitted.
- The two actual W_m factors are each `RhoSection.sectionModule S B j ρB m`, with
  its existing inclusion in `RhoSection.Coordinate S.X`, never an abstract copy.
- Diagonal rational invariance is rendered by the intersection over A, its commutative
  ring and F-algebra structures, and s,g,h in S(A), of the kernels of
  `tensorSquareEvaluation ... (s⁻¹ * g) (s⁻¹ * h) - tensorSquareEvaluation ... g h`.
  On a pure tensor this is exactly
  `f(s⁻¹g) f'(s⁻¹h) - f(g) f'(h)`.
  These are equations over EVERY commutative F-algebra, including nonreduced ones.
  They express the specified left translation on both factors, with no finite-group
  or Lie-algebra substitution. To see equivalence with the coaction equalizer, embed
  W tensor W in F[S] tensor F[S] (tensoring is injective over F) and test the equation
  at the universal triple of points over F[S] tensor F[S] tensor F[S]. This detects
  exactly the regular-function coaction equality. This algebra lies in Type u,
  so the tests do not restrict the invariance condition. Conversely a coaction equality
  pulls back to all these equations, and also to algebras in larger universes.
- The asserted dimension is `Module.finrank F ↥( ... : Submodule F (W_m ⊗[F] W_m)) = 1`.
  No nonzero, finiteness, simplicity, self-duality or characteristic assumption is
  added: the first two follow from the recorded rho-section theorem, and the latter
  three would incorrectly restrict the scope in positive characteristic.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs (def-weil-field).
- `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic (def-weil-algebraic-closure).
  The node's algebraic-closure record explicitly also identifies this predicate.
- `CategoryTheory.GrpObj` and bundled `CategoryTheory.Grp`,
  Mathlib.CategoryTheory.Monoidal.Grp (def-sc-group-scheme); the group-scheme
  specialization and kernels were read in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `AlgebraicGeometry.IsRhoBorelPair` and `AlgebraicGeometry.exists_rho_section_modules`,
  Sheaf.AlgebraicGeometry.RhoSectionModules (lem-sfb-rho-section-modules).
  The new theorem unpacks precisely the rho data in its conclusion.
- Transitive notions from that dependency: `RhoSection.sectionModule`, `Coordinate`,
  `evaluate`, `HasRationalLeftTranslation` in RhoSectionModuleData;
  `IsSemisimpleGroupScheme` in GroupScheme.Semisimple; `TorusCharacterTangent.weightSpace`
  in TorusCharacterTangentWeights. The full declarations and docstrings were read.
  No private copies are supplied.
- Mathlib's `LinearMap.mul`, `LinearMap.compl₁₂` and `TensorProduct.lift` construct
  the helper with actual data.

Proof dependencies: lem-sfb-rho-section-modules is imported publicly since it also
supplies statement data. The two proof-only nodes
lem-sfb-rational-induction-character-reciprocity and lem-sfb-induced-module-primitive-line
currently have neither Lean records nor mathlib matches, so there are no recorded modules
to import for them. They are named in the four-step proof docstring, following the DAG.
Their statements are not needed to type this item.

Edge cases checked:

- Trivial rank-zero semisimple group: T and B can be trivial, Φ is empty, rho is trivial,
  W_m = F, and its tensor-square invariant space has dimension one.
- Characteristic 2 is retained: rho is specified by a lattice identity, never by
  multiplying the root sum by the inverse of 2 in F.
- Positive characteristic with arbitrary m is retained, even when W_m is not simple
  or self-dual. The argument uses induction reciprocity and the primitive line, not
  Schur's lemma for simple representations.
- m=0 is outside the node's asserted range, and the positive-nat parameter includes
  every positive integer. Zero sections are not assumed away by a new hypothesis.
- Nonreduced test algebras and the zero algebra are included; the latter's equations
  are automatic and do not change the intersection. No points-only restriction.
- The same coefficient universe u is used for F, the coordinate rings and all tests;
  the universal test algebra exists in that universe. No site-universe restriction.

Searches for an existing statement:

- msearch leansearch: "For an algebraically closed field the rational invariants of the
  tensor square of the induced module of m times rho have dimension one".
  Eight hits, including FDRep.finrank_hom_simple_simple, Representation.invariants,
  LieModule triangularizability. None states the assertion for rational group-scheme
  rho sections; simple abstract-group modules do not cover arbitrary m here.
- msearch leanfinder: "The tensor square of rho section modules for a semisimple simply
  connected group has a one dimensional rational invariant subspace". Eight hits,
  mainly coinvariants of abstract regular representations and simple FDRep Hom spaces;
  no match.
- msearch loogle: `Representation.invariants, Module.finrank`. Two character-average
  hits for finite groups with invertible cardinality; no match.
- msearch grep: `rho.*tensor|tensor.*rho|RationalHom`, restricted to RepresentationTheory:
  five abstract tensor-dual representation hits; no match.
- rg of lean/WeilConjectures and lean/Sheaf for the item id, RhoSection, rho/tensor,
  tensorSquareInvariantLine, tensorSquareEvaluation and tensor/coaction/invariant names:
  found RhoSectionModuleData and RhoSectionModules, but no tensor-square calculation.
  RationalHighestWeightData defines invariants of an already supplied coaction;
  it neither supplies the actual W_m action nor this canonical tensor evaluation,
  and is not duplicated here. The statement writes the specified equations directly.
- dag/lean_names_upstream.json searched for RhoSection and rho/tensor; no match.

Source checked: https://arxiv.org/html/1005.2398v3#S9.SS7,
Lemma 9.7.2(1) and Remark 9.7.3, including the field invariant-line version.
No STATEMENT-DISPUTED issue found. The Lean proof docstring reproduces all four DAG
steps: rational dual, tensor-Hom identification, induction reciprocity, primitive line
and w_0 rho = -rho.

Validation: the module is compiled only using the prescribed scompile.py wrapper;
final compilation and deliver2.py dry run are recorded by the delivery tools.

## Second reading by Q69

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
