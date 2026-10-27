## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.QuotientBorelTorusImages` states
`AlgebraicGeometry.quotient_borel_torus_images`, with its sole proof `sorry`.
It states all four image/lifting assertions of Milne, Algebraic Groups (2017),
Proposition 17.20, printed pp.357--358, with faithfully flat restrictions as in
Theorem 5.39, printed p.108. The PDF's proposition and complete proof were read.
The node statement is unchanged. Its statement dependencies gain the two already
landed definition nodes `def-sfb-borel-subgroup-scheme` and
`def-sfb-reductive-torus-centralizer-terminology`, because the theorem uses their
existing predicates. No new notions, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Affine F-group schemes: `A D : Grp (Over (Spec (.of F)))`, with
  `[IsAffine A.X.left] [IsAffine D.X.left]`. Bundled group morphisms automatically
  carry `IsMonHom`; there is no additional homomorphism assumption to supply.
- Finite type: `LocallyOfFiniteType` and `QuasiCompact` on both structure maps.
  Every subgroup appearing as a Borel or maximal torus is a closed subgroup by
  its existing predicate. Closed subgroups of these affine finite-type groups
  are themselves affine finite type, so redundant hypotheses are not imposed.
- Smoothness: `[Smooth A.X.hom] [Smooth D.X.hom]`.
- Connectedness: `[ConnectedSpace A.X.left] [ConnectedSpace D.X.left]`.
  This includes nonemptiness; no empty-scheme exception is lost.
- Faithfully flat homomorphism: `f : A ⟶ D` and
  `hf : f.hom.hom.left.appTop.hom.FaithfullyFlat`. The coordinate map has direction
  F[D] → F[A]. Mathlib's `RingHom.FaithfullyFlat` is precisely the faithfully flat
  module structure induced by that ring homomorphism, hence exactness and
  detection of zero for scalar extension.
- Borel convention: `IsBorelGroupScheme` requires a closed subgroup, smoothness,
  connectedness, `IsSolvableGroupScheme`, and maximality by factorization.
  The reused solvability is termination of the smallest-closed-commutator-derived
  series (`IsDerivedGroupScheme`, `GroupSchemeDerivedLength`), exactly the node's
  convention, not solvability merely on rational points.
- Torus convention: `ReductiveTorusCentralizer.IsMaximalTorus` requires a closed
  torus subgroup and maximality among containing tori. Its existing
  `MultiplicativeType.IsTorus` means a finite split product after algebraic closure;
  because F is already algebraically closed this is equivalent to being split
  over F itself. `splitTorus` is the actual iterated product of the recorded G_m,
  with the terminal group for rank zero. No alternate torus predicate is defined.
- First conjunct: for every Borel inclusion `iB : B ⟶ A`, there are `C`, its Borel
  inclusion `iC : C ⟶ D`, and `r : B ⟶ C`, with `iB ≫ f = r ≫ iC` and faithfully
  flat coordinate map for `r`.
- Second conjunct: for every Borel inclusion `iC : C ⟶ D`, the same factorization
  exists with `B` a Borel of A, including faithful flatness of the restriction.
- Third conjunct: every maximal-torus inclusion `iT : T ⟶ A` factors through a
  maximal-torus inclusion `iS : S ⟶ D`, with faithfully flat `r : T ⟶ S`.
- Fourth conjunct: every maximal-torus inclusion of D occurs in that way.
- Scheme-theoretic image in each clause: the codomain inclusion is closed by
  the Borel/maximal-torus predicate and `r` is faithfully flat. Since all groups
  involved are affine, the ring map of `r` is injective, while the ring map of
  the closed inclusion is surjective. Consequently the ideal defining the closed
  codomain is exactly the kernel of the composite coordinate map. Thus these
  existential representatives specify exactly the scheme-theoretic image,
  uniquely up to its unique isomorphism over D; no set-theoretic/rational-points
  image or additional arbitrary-map hypothesis replaces it.
- No kernel restriction: no kernel, smooth-kernel, reduced-kernel, centrality,
  finiteness, or separability hypothesis is present.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (via imports).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the recorded
  `AlgebraicClosure` construction was also read in its recorded module.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, group morphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` (the complete declarations
  and docstrings were read; closedness is used through the two predicates).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.multiplicative`, `multiplicativeGroup` (through split tori).
- `Sheaf.AlgebraicGeometry.GroupScheme.Borel`: `IsBorelGroupScheme`, using
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple.IsSolvableGroupScheme`
  (declaration namespace is `AlgebraicGeometry`, not the module prefix).
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsMaximalTorus`, using the already recorded
  `MultiplicativeType.IsTorus` and `splitTorus` in
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.

Every currently recorded proof-dependency module is imported privately, including
Mathlib proof leaves. Proof dependencies without a recorded declaration or
Mathlib match are not invented here. The declaration docstring reproduces all
seven DAG proof steps: affine flat-image factorization; properness descending
from A/B to D/f(B); fixed-point Borel criterion; conjugation and lifting of
Borels; solvable unipotent/torus quotient reduction; maximality of torus images;
and conjugation and lifting of arbitrary maximal tori. No proof import cycle
was encountered. The proof plan intentionally remains a plan for stage 3.

Searches for existing declarations:

- msearch.py LeanFinder: “A faithfully flat quotient homomorphism of connected
  smooth algebraic groups maps Borel subgroups and maximal tori onto Borel
  subgroups and maximal tori, and all such subgroups lift”: eight unrelated
  hits (Galois categories, number-field units, root systems, abstract groups,
  Lie extensions); no group-scheme theorem.
- msearch.py Loogle: `"BorelSubgroup", "MaximalTorus"`: zero hits.
- msearch.py grep: `IsBorel|IsMaximalTorus|IsTorus`: zero Mathlib hits.
- msearch.py LeanSearch: “Images and lifts of Borel subgroups and maximal tori
  for faithfully flat homomorphisms of smooth connected algebraic group schemes”:
  eight unrelated abstract-group/open-immersion/formal-smoothness hits; no match.
- rg over `lean/WeilConjectures` and `lean/Sheaf`: the existing definitions in
  Borel, Semisimple, ToriMultiplicativeType, and
  ReductiveTorusCentralizerTerminology were found and reused. Searches for the
  item id in upstream returned none; downstream mentions in BorelQuotientLifting,
  BorelSchemeNormalizer and CentralIsogenyBorelRootCompatibility cite this item
  rather than state it. The old Borel-lifting theorem states only one of the
  four clauses (and finite presentation), so is not an existing match.
- rg for the proposed full declaration name over Mathlib and both project
  roots returned none.

Edge cases checked mathematically: the identity quotient; a quotient onto the
trivial group; both groups trivial; rank-zero maximal tori in unipotent groups;
G_m × G_a → G_m; SL_2 → PGL_2; Frobenius on G_m in positive characteristic,
with nonreduced kernel μ_p; and Frobenius on G_a, with kernel α_p. The formula
places no constraint on these kernels and uses the full scheme structures.
Universes are explicit and match the existing group-scheme interfaces: F and
all schemes/test algebras are at u. No free or automatically bound variables,
file-local notation/instances, or new definition choices occur.

Validation: scompile.py Q30 lem-sfb-quotient-borel-torus-images compiled the
module in sandbox and library modes on the server, each in 1.8 seconds, with
exit code zero and no diagnostic. Dry-run and delivery results follow below.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q30

I reread the node and the completed signature clause by clause. The first and
third conjuncts quantify over source subgroups and prove image maximality; the
second and fourth quantify over target subgroups and prove lifting. All four
include a commuting factorization and faithfully flat restriction in the right
coordinate-map direction. Maximality uses the existing predicates, and the
closed-plus-faithfully-flat factorization recovers the entire scheme-theoretic
image, so no smoothness or reducedness of the kernel was introduced. I also
checked nonempty connectedness, finite type as its two recorded conditions,
and the rank-zero product. No mismatch or correction was found. This is a
worker self-audit; independent review is performed by the maintainer's delivery
review, as specified in the dispatcher brief, with no additional agents started.
