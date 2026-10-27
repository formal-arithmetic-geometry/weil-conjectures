## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.PseudoabelianProper` states
`AlgebraicGeometry.isProper_of_pseudoabelian`, with its single proof left as `sorry`.
No new definitions, auxiliary theorems, dependency repairs or statement changes are needed.
The node copy changes only `lean`. The declaration docstring gives all six steps of the
accepted proof, including the induction base, centrality, fpqc descent of normality,
and the vanishing of the scheme-theoretic image ideal.

Source read: Milne, Algebraic Groups (2017), Definition 8.3 on printed p.149 and
Theorem 8.26 and its proof on printed p.154. The theorem says that pseudo-abelian
varieties over perfect fields are complete, and its proof explicitly reduces to the
algebraically closed case. The assigned node is precisely that case. No commutativity
hypothesis is imposed in the source or in the Lean statement.

Clause-by-clause correspondence:

- The algebraically closed base field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The k-scheme Q and its multiplication, inverse and unit diagrams are
  `(Q : Over (Spec (.of k))) [GrpObj Q]`, using the recorded group-scheme encoding.
- Smoothness is `[Smooth Q.hom]`; connectedness of the underlying scheme is
  `[ConnectedSpace Q.left]`; separatedness is `[IsSeparated Q.hom]`, whose definition
  requires the diagonal to be a closed immersion.
- Finite type is exactly `[LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]`, the two
  component predicates in the dependency's recorded interface.
- The hypothesis quantifies over every `S : Over (Spec (.of k))` with `[GrpObj S]`
  and every `i : S ⟶ Q`. `IsClosedSubgroupScheme i` includes the homomorphism,
  injectivity on all k-algebra points and closed immersion. `IsNormalSubgroupScheme i`
  requires the image on all k-algebra points to be normal. These are the upstream
  recorded predicates, not conditions merely on k-rational points.
- The remaining conditions on S are `Smooth S.hom`, `ConnectedSpace S.left` and
  `IsAffine S.left`. The last is Mathlib's predicate that the canonical map to
  Spec of global sections is an isomorphism, equivalent to being isomorphic to
  Spec of some commutative ring. No extra finite-type condition on S is imposed.
- The conclusion for each S is `IsIso (MonObj.one (X := S)).left`. `MonObj.one`
  is the identity section from the tensor unit in Over, whose underlying scheme
  is Spec k, so this says exactly that the identity morphism Spec k → S is an
  isomorphism of schemes. It does not identify an arbitrary rational point with the unit.
- The final conclusion `IsProper Q.hom` says Q is proper over k. Mathlib's properness
  extends separatedness, universal closedness and local finite type; universal
  closedness implies quasi-compactness, as noted in the recorded dependency.
- There is no `IsCommMonObj Q` or other commutativity binder.

Dependency declarations read and reused:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (available transitively).
- `def-weil-algebraic-closure`: its `mathlib_match` explicitly identifies the relevant
  algebraically closed predicate as `IsAlgClosed` in `Mathlib.FieldTheory.IsAlgClosed.Basic`.
  Its full class signature and root characterization were read; an extension field or
  chosen algebraic closure is not required by this node.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`, specialized to Over (Spec k), as the record
  directs and as documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
  `CategoryTheory.MonObj.one` is the unit section inherited by this structure.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme` and
  `AlgebraicGeometry.IsNormalSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`; their full signatures,
  docstrings and inherited `IsSubgroupScheme`/`IsMonHom` were read.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-connected-scheme`: `ConnectedSpace`,
  `Mathlib.Topology.Connected.Basic`, including its nonemptiness field.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` and
  `AlgebraicGeometry.IsSeparated`, `Mathlib.AlgebraicGeometry.Morphisms.Proper` and
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; affineness is `AlgebraicGeometry.IsAffine` in
  `Mathlib.AlgebraicGeometry.AffineScheme`. These are transitively available through
  the public imports of the recorded group-scheme interface.

The stated proof dependencies are imported without `public`: identity components
(`Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent`), abelian varieties
(`WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`), fpqc coverings, their axioms
and representable descent (`Mathlib.AlgebraicGeometry.Sites.Fpqc`), proper images
(`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`) and geometric reducedness
(`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`). Finite properness,
proper base change and composition already come from the public Proper import.
The four proof nodes `lem-sfb-affine-normal-subgroup-products`,
`lem-sfb-general-group-centre-zero-dimension-affine`,
`lem-sfb-rosenlicht-nonproper-affine-subgroup` and
`lem-sfb-rosenlicht-connected-almost-complement` have no recorded Lean declaration
in the inspected base, so they have no module to import yet. They remain in proof_deps;
none is needed to elaborate this statement. There is no omitted import due to a cycle.

Edge cases checked before writing:

- The trivial group Spec k satisfies the hypothesis and is proper; its identity
  section is an isomorphism. The dimension-zero case of the source proof is retained.
- An affine Q must be tested against its own identity inclusion. The hypothesis then
  forces Q to be trivial, excluding Ga, Gm and nontrivial connected affine groups.
- Empty schemes are excluded by ConnectedSpace, consistently with the dependency's
  nonempty convention and with the presence of a group unit over a nonempty field.
- Infinitesimal nonsmooth subgroups such as alpha_p are outside the quantified smooth
  subgroups. The hypothesis is not silently strengthened to exclude every finite
  connected subgroup of an abelian variety in positive characteristic.
- Both characteristic zero and positive characteristic are included; no characteristic
  binder, perfectness restriction beyond the algebraically closed assumption, or
  commutativity restriction has been added.
- The field, Q and S use the same explicit universe u, as in the recorded subgroup
  definitions. The quantification includes Q itself and all its closed subgroup schemes
  up to isomorphism; closed immersions into a Scheme.{u} do not require a larger scheme
  universe. The algebra-point normality in the reused interface uses Type u, the
  universe of k itself, so there is no smaller independent test universe or vacuous test.

Searches for an existing statement:

- `msearch.py`, LeanFinder: “A smooth connected separated finite type group scheme over
  an algebraically closed field with no nontrivial smooth connected affine closed normal
  subgroup is proper”. Eight hits: finite-morphism properness, properness of Proj,
  finite iff proper and affine, Galois-category connectedness, integral schemes,
  compactness from universal closedness and affine compactness. None states this theorem.
- `msearch.py`, Loogle: `"GrpObj", "IsProper"`. Zero hits.
- `msearch.py`, grep in Mathlib/AlgebraicGeometry:
  `pseudo.?abelian|Rosenlicht|Barsotti`. Zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `pseudo.?abelian|Rosenlicht|Barsotti|isProper.*[Gg]roup|[Gg]roup.*isProper`.
  Only unrelated Rosenlicht mentions in line-bundle linearization and the Borel
  Picard sequence; no properness theorem for pseudo-abelian groups.
- Exact node-id search in `lean/WeilConjectures`: no hit.
- Candidate declaration names `pseudoabelian_isProper|isProper_of_pseudoabelian`
  searched in Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json`:
  no existing declaration.

No statement dispute or node fault was found. Validation uses the required server
single-file compiler and delivery preflight; only the expected sorry warning is permitted.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
