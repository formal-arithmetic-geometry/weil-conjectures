## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalSubgroupProducts`
states `AlgebraicGeometry.affineNormalSubgroup_products`, with its sole proof
`sorry`. It contains no definitions, auxiliary theorems, or instances. The node
is copied verbatim except for `lean`; no statement correction is needed.

The theorem has three conjuncts. The product statement quantifies over M and N
inside the first conjunct, so the two dimension statements do not depend on the
existence or choice of those subgroups.

Hypothesis and clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- A k-group scheme is a bundled `Grp (Over (Spec (.of k)))`. Its existing
  `GrpObj` instance supplies all operations and laws. Morphisms in this category
  are homomorphisms of group schemes; the two `.hom` projections give the
  morphism in `Over` used by the dependency's subgroup predicates.
- The ambient separated finite-type group scheme is `G` with
  `[IsSeparated G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
  Neither smoothness, connectedness, affineness nor commutativity of G is assumed.
- The first conjunct quantifies over M,N and their inclusions iM,iN. Their closed
  and normal hypotheses are exactly the recorded `IsClosedSubgroupScheme` and
  `IsNormalSubgroupScheme` classes, respectively. The structure morphisms have
  `Smooth`; the underlying spaces have `ConnectedSpace`; the schemes have
  `IsAffine`. No extra finite-type or separated hypotheses are imposed on M,N:
  those properties follow from closedness in G.
- The required P is existentially quantified as a group scheme, with inclusion
  iP and the same closed, normal, smooth, connected and affine properties.
- Containment of M and N is `(∃ a : M ⟶ P, a ≫ iP = iM)` and the analogous
  statement for N. This states factorization of the actual subgroup inclusions,
  with homomorphisms a,b, rather than a comparison of unrelated schemes.
- Every commutative k-algebra is quantified by
  `∀ (R : Type u) [CommRing R] [Algebra k R]`. Its G-points are exactly morphisms
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G.X`.
- Membership of g in P(R) is the left side of the biconditional,
  `∃ p, p ≫ iP.hom.hom = g`, with p a point of that same P over that same R.
- The right side quantifies over a commutative k-algebra R' and a k-algebra map
  `φ : R →ₐ[k] R'`, requiring `φ.toRingHom.FaithfullyFlat` and
  `φ.toRingHom.FinitePresentation`. The former is Mathlib's flatness plus
  faithfulness of tensoring; the latter is finite generators and finitely
  generated relations. Both properties refer to the specified φ, not an
  independently chosen algebra structure.
- The local factors m,n are R'-points of the specified M,N. The equality
  `Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g.left =
  ((m ≫ iM.hom.hom) * (n ≫ iN.hom.hom)).left`
  is restriction along the actual map φ followed by multiplication in G(R').
  Using equality of underlying scheme arrows avoids an unnecessary helper
  definition of the induced map in `Over`. Since φ is a k-algebra map, it is
  precisely the canonical restriction of the original point. The multiplication
  instance is the existing `CategoryTheory.Hom.group`, enabled by the standard
  `CategoryTheory.MonObj` scope. Its order is m then n, with no commutativity.
- The second conjunct quantifies over EVERY closed subgroup H of G, with no
  smoothness, connectedness, normality or affineness requirements. It states
  `∃ d : ℕ, topologicalKrullDim H.X.left = (d : WithBot ℕ∞) ∧
  (d : WithBot ℕ∞) ≤ topologicalKrullDim G.X.left`. Equality to the natural
  number proves both finiteness and nonnegativity, including the endpoint zero.
- The third conjunct quantifies over closed inclusions K → G and J → K and
  smooth connected J,K. Thus their composite is the inclusion J → G; there is
  no need for an extra independently specified inclusion with a factorization
  equation. Strictness is `¬ IsIso j.hom.hom.left`. For a closed inclusion,
  equality as a closed subscheme is precisely being an isomorphism, so this
  retains scheme-theoretic strictness. The conclusion is exactly
  `topologicalKrullDim J.X.left < topologicalKrullDim K.X.left`.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically
  closed clause of def-weil-algebraic-closure; no algebraic closure is selected).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`,
  `CategoryTheory.Grp` and its homomorphisms; the pointwise group is in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme`. Their full definitions quantify over algebra-valued
  points as the node requires.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, together with `QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its public separated import:
  `AlgebraicGeometry.IsSeparated`, defined by the closed diagonal. `IsProper`
  itself is not assumed.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`; existing
  `AlgebraicGeometry.IsAffine` is in `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, with the recorded
  `WithBot ℕ∞` chain convention.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`;
  `Mathlib.RingTheory.FinitePresentation`: `RingHom.FinitePresentation` and
  `Algebra.FinitePresentation`, whose definition explicitly gives a surjection
  from `MvPolynomial (Fin n) R` with finitely generated kernel.

All available proof-dependency modules are imported privately, including the
homomorphism factorization, affine finite-type algebra, dimension finiteness,
identity component, geometric reducedness, reduced induced closed subscheme,
affine pullbacks, flatness, faithful flatness and fpqc descent modules. The
unrecorded proof node `lem-sfb-exact-algebraic-group-property-permanence` has no
usable Lean declaration in the read DAG and consequently has no import yet.
It is needed only for the future proof, and is retained in the proof plan and
in `proof_deps`. No helper is needed to state this item. For reduced induced
closed subschemes, the dependency's recorded upstream module exists and is
used: its note mentions an obsolete Sheaf-side alternative whose object file
is absent, so that alternative was removed after the first compile diagnosed it.

Source reading: the local Milne PDF was read using pdftotext. Section 5(f),
printed pp.111--112, defines HN as the image of the semidirect-product
homomorphism and gives faithfully flat local factorization. Proposition 8.1,
printed p.149, gives exactly the affine/smooth/connected permanence used here.
Lemma 6.41 and Proposition 6.42, printed p.134, give the product and
largest-dimension argument. Corollary 1.35 and the dimension discussion,
printed p.17, identify connected components with irreducible components.
The eight numbered proof steps, including the finite-presentation refinement
and the chain argument, are included in the theorem's docstring.

Edge cases checked before writing:

- The trivial subgroup, M=N, M trivial or N trivial all satisfy the local product
  formulation and containment clauses. No distinctness assumption is present.
- The zero test algebra is admitted; it represents the empty test scheme. Its
  point sets are singletons, and its identity extension is faithfully flat and
  finitely presented. No `Nontrivial R` or `Nontrivial R'` assumption was added.
- Every actual group scheme over the nonzero field is nonempty by its identity
  section, so dimension ⊥ is correctly excluded in the closed-subgroup clause.
  Infinitesimal and disconnected closed subgroups remain covered by that clause.
- For zero-dimensional smooth connected groups there is no strict smooth
  connected subgroup inclusion, consistent with the strict inequality.
- Smoothness in the strict dimension clause excludes equal-support nilpotent
  thickenings as counterexamples. Strictness is not incorrectly tested merely
  by comparing sets of rational points.
- G can be non-affine, disconnected, nonreduced and noncommutative. J,K need
  not be affine or normal. The statement uses no characteristic restriction.
- All groups, schemes, and test algebras use the same arbitrary universe u as
  the recorded subgroup interface. Tests cannot become vacuous by falling in
  a universe below that of k. All variables/universes are explicitly bound;
  `autoImplicit false` is enabled.

Searches made (2026-10-24):

- `msearch.py ... leanfinder` query: "Products of smooth connected affine normal
  subgroup schemes and strict subgroup dimension inequalities". Eight results,
  headed by `Algebra.IsStandardSmooth.relativeDimension` and related relative
  dimension results, with Lie group product and real-codimension results. None
  gives the stated algebraic-group product or strict subgroup dimension result.
- `msearch.py ... loogle` query:
  `"IsNormalSubgroupScheme", "topologicalKrullDim"`: zero hits.
- `msearch.py ... grep`, AlgebraicGeometry, query:
  `affine.*[Nn]ormal.*[Ss]ubgroup|[Nn]ormal.*[Ss]ubgroup.*[Pp]roduct`: zero hits.
- `rg` with the same expression and `affineNormalSubgroup` in the upstream
  WeilConjectures and project Sheaf sources: only references to the separately
  unstated solvable-subgroup product lemma and unrelated occurrences. No match.
- The required `grep -rn` for this item's id in WeilConjectures: no match.
- `rg` for the proposed full declaration name in Mathlib, WeilConjectures,
  Sheaf and `dag/lean_names_upstream.json`: no match.
- Read the related DAG node `lem-sfb-solvable-normal-subgroup-products`: no Lean
  record and a different statement (affine ambient group and solvability/base
  extension conclusions). It is not a duplicate of this statement.

No node faults or disputed statements were found. No new nodes or dependency
repairs were necessary.

## Second reading by NQ

This is a separate reread by the dispatched worker; no second agent was started,
as required by the dispatch brief. The maintainer supplies the independent
review of the delivery. I reopened the node and checked its three clauses
against the final signature. The first is a biconditional with an existential
faithfully flat finitely presented extension, rather than the false global
identity P(R)=M(R)N(R). Its product is in the specified ambient group and keeps
factor order. The quantified closed-subgroup dimension clause does not inherit
smoothness or connectedness from the product subgroups. The strict clause
quantifies over closed J → K → G and assumes smoothness/connectedness of J,K
only; it uses scheme isomorphism for equality, not equality of supports.
The reread found no missing clause or extra mathematical hypothesis. Compiler
feedback required enabling the existing pointwise group scope and choosing
the available recorded upstream reduced-subscheme module; neither changes
the statement. The node signature is extracted verbatim from the delivered file.
