## Worker report

The module `Sheaf.AlgebraicGeometry.SemiabelianClosedSubgroupTrivialTorsionFinite`
states `AlgebraicGeometry.isFinite_closedSubgroup_of_semiabelian_trivial_prime_torsion`,
with `sorry` as its entire proof. No definition or auxiliary theorem is introduced.
The node is unchanged except for `lean`.

Source checked: Brian Conrad, *Semistable reduction for abelian varieties*,
[Corollary 3.3, printed p. 8](https://math.stanford.edu/~conrad/DarmonCM/2011Notes/SemistableReduction.pdf).
The author PDF states the result for a closed subgroup scheme, and its proof reduces
first to the reduced identity component. Thus neither reducedness nor connectedness
is a hypothesis on H. The delivered docstring follows the six steps of the accepted
DAG proof, including the component argument needed to restore the full H.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The group scheme over k is `G : Grp (Over (Spec (.of k)))`.
  `[IsCommMonObj G.X]` is its commutativity.
- Smoothness and separatedness are `[Smooth G.X.hom]` and
  `[IsSeparated G.X.hom]`. Finite type is the pair
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- Semiabelian geometric fibres are exactly
  `hG : HasSemiabelianGeometricFibres G`, using the dependency's existing predicate,
  including its actual split torus, abelian quotient, kernel square and fppf epimorphism.
- The subgroup is `(H : Over (Spec (.of k))) [GrpObj H]` with
  `(i : H ⟶ G.X) [IsClosedSubgroupScheme i]`. This recorded predicate includes
  preservation of the group operations, injectivity on every algebra's points,
  and closed immersion of the underlying scheme map. No smoothness, reducedness,
  connectedness or properness of H is added. Commutativity of H is forced by its
  subgroup inclusion in G; no extra typeclass assumption for it is needed here.
- The prime integer is represented by its positive natural value `(ℓ : ℕ)` with
  `(hℓ : ℓ.Prime)`. Its nonzero image in k is `(hℓk : (ℓ : k) ≠ 0)`.
- Multiplication by ℓ is `𝟙 H ^ ℓ`. The scoped `MonObj` instance equips morphisms
  into H with the pointwise group law; this is not composition power.
- The fibre product H[ℓ] is `GrpObj.ker (𝟙 H ^ ℓ)`, definitionally the pullback of
  that multiplication morphism and `MonObj.one`, the identity section of H,
  in the category of schemes over Spec k. The over-category pullback gives exactly
  the stated scheme fibre product.
- The hypothesis that its identity section is an isomorphism is encoded as
  `hH : IsIso (GrpObj.ker (𝟙 H ^ ℓ)).hom`, where `.hom` is its structure map to
  Spec k. This is equivalent for precisely this scheme, not an alternative
  triviality condition on rational points: its canonical identity section e
  satisfies e followed by the structure map p equals the identity of Spec k.
  If p is an isomorphism, that equality identifies e with its inverse; if e is
  an isomorphism, it identifies p with its inverse. This uses only the existing
  kernel and structure map, and changes no hypothesis or object.
- The conclusion `IsFinite H.hom` is finiteness of H's structure morphism.
- Rank-zero tori and zero-dimensional abelian quotients are permitted by the
  unchanged semiabelian predicate, with no positivity condition in the theorem.

Recorded statement-dependency declarations used, with their sources read:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic (the appropriate part of
  def-weil-algebraic-closure's Mathlib match).
- `AlgebraicGeometry.Scheme`, Mathlib.AlgebraicGeometry.Scheme.
- `CategoryTheory.Grp`, `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp, and `CategoryTheory.IsCommMonObj`.
  These are used in the specified specialization to `Over (Spec (.of k))`.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `AlgebraicGeometry.HasSemiabelianGeometricFibres`,
  Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres.
- `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `CategoryTheory.Limits.pullback`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, through the existing
  `CategoryTheory.GrpObj.ker`,
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp.
- `AlgebraicGeometry.IsFinite`, Mathlib.AlgebraicGeometry.Morphisms.Finite.
- `AlgebraicGeometry.IsSeparated`, Mathlib.AlgebraicGeometry.Morphisms.Separated,
  for the explicitly stated separatedness assumption.

Statement dependencies use public imports, with foundational declarations also
available through those imports. The stated proof dependencies are imported plainly:
`Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite`,
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny`,
`Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates`,
`Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent`,
`Sheaf.AlgebraicGeometry.ClosedImmersionProducts`, and
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
The torus, algebraic-closure, finite-type and closed-immersion proof notions are
already available through public statement imports. The proof-only node
lem-sfb-smooth-connected-semiabelian-subgroup has no recorded declaration, so it has
no import yet; its use is retained in the proof docstring. It is not required to
state the delivered theorem. No proof dependency is dropped from the DAG.

Edge cases checked before writing:

- The trivial group scheme and rank zero satisfy the statement with no dimension
  positivity assumption. Abelian varieties with zero torus rank are included.
- For G_m and any invertible prime ℓ, a nonidentity ℓth root of unity prevents
  the torsion-triviality hypothesis, as required.
- A finite constant subgroup of order prime to ℓ has trivial ℓ-torsion and is
  finite; the statement does not force such a disconnected subgroup to be trivial.
- In characteristic p, H = μ_p inside G_m is allowed for ℓ different from p:
  multiplication by ℓ is an automorphism of μ_p, so its kernel is trivial and
  H is finite despite being nonreduced. No reducedness was inadvertently added.
- The hypothesis excludes ℓ equal to the positive characteristic, and primality
  excludes zero and one. In characteristic zero every prime is allowed.
- An empty group scheme over the nonempty Spec k has no identity section and is
  not an omitted group-scheme case. All types and schemes use the explicit
  ambient universe u, as in the recorded semiabelian predicate; no additional
  independent universe restriction on test fields is introduced.

Searches for an existing statement (2026-10-24):

- msearch.py leanfinder: "A closed subgroup scheme of a semiabelian group with
  trivial invertible prime torsion is finite". Eight hits, including
  `CommGroup.finite_of_fg_torsion`, `AddCommGroup.finite_of_fg_torsion`,
  `FiniteAddGrp`, and additive-circle torsion; none is about group schemes.
- msearch.py leansearch: "A closed subgroup of a semiabelian variety whose prime
  torsion is trivial is finite". Eight hits on topological closed subgroups and
  finitely generated torsion groups; no match.
- msearch.py loogle: `"semiabelian", "torsion"`. Zero hits.
- msearch.py grep: `semi.?abelian|torsion.*finite|finite.*torsion` in
  Mathlib/AlgebraicGeometry. Zero hits.
- rg: `semiabelian.*finite|finite.*semiabelian|trivial.torsion|trivialTorsion`
  in WeilConjectures/, Sheaf/ and dag/lean_names_upstream.json. Matches were
  unrelated trait, ample-reflection and power-integrality discussions, not an
  existing statement of this result. A recursive search for this node id in
  WeilConjectures/ returned no match.
- Read the existing group-scheme definitions and kernel implementation in full
  at the used interfaces. Their genuine pullback and pointwise multiplication
  supply the objects needed here, so no helper or new node is necessary.

There is no statement correction, disputed statement or unusable dependency record.
The first server compile diagnosed a missing scoped pointwise-power instance;
opening `MonObj` fixed it. scompile.py then compiled the module cleanly on the server
in 2.3 seconds (60-second limit, two threads, nice 19). Its local attempt reported
no free disk space; the prescribed wrapper's server fallback succeeded.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
