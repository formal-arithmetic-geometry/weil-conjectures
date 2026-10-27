## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.LangFiniteFieldSurjectivity` states
`AlgebraicGeometry.lang_finite_field_surjective`, with its sole proof `sorry`.
No definition, helper theorem, node correction, or extra node is needed.

Hypotheses and clauses, checked against the unchanged DAG statement:

- A finite field k is `{k : Type u} [Field k] [Fintype k]`. Its cardinality q is
  `Fintype.card k`, already built into the recorded Frobenius declaration; no
  separate arbitrary q or prime-power hypothesis is introduced.
- An algebraic closure is `{K : Type u} [Field K] [Algebra k K]
  [IsAlgClosure k K]`. The chosen field and chosen inclusion are arbitrary.
- The k-group scheme is `(G : Over (Spec (.of k))) [GrpObj G]`.
  Affineness is `[IsAffine G.left]`; finite type is the recorded pair
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`; smoothness is
  `[Smooth G.hom]`; connectedness is `[ConnectedSpace G.left]`.
- A K-point is `(Spec (.of K)).asOver (Spec (.of k)) ⟶ G`. This is the canonical
  functor-of-points presentation, not an arbitrary group or map. For affine G,
  the Spec/global-sections equivalence identifies it with the k-algebra maps
  from C = Γ(G, O_G) to K. Thus writing morphisms instead of choosing the
  coordinate presentation changes neither points nor their group law.
- The arithmetic Frobenius is exactly the dependency declaration
  `FiniteField.frobeniusAlgEquivOfAlgebraic k K`. Its `.toAlgHom.toRingHom`
  retains the algebra-homomorphism syntactic interface required by the existing
  `Scheme.Hom.IsOver` instance. Its value at z is z^(Fintype.card k).
  Precomposition `Spec.map σ ≫ g` corresponds by contravariance to `σ ∘ x`
  on coordinate-algebra maps, hence precisely `c ↦ x(c)^q`.
- `g⁻¹ * (Spec.map σ ≫ g) = h` is the required ordered product in the
  existing `CategoryTheory.Hom.group` instance, enabled with the established
  `MonObj` scope. The quantifiers `∀ h, ∃ g` state surjectivity.
- There is no `IsCommMonObj`, reductivity, splitness, matrix realization,
  finite-dimensional representation, or finite-type assumption on K itself.

Dependency declarations read and reused:

- `Field`, Mathlib.Algebra.Field.Defs: commutative field structure.
- `GaloisField`, Mathlib.FieldTheory.Finite.GaloisField, and the node's arbitrary
  finite-field interpretation: `Fintype k` represents a field of arbitrary finite
  cardinality; it does not restrict k to a named model.
- `IsAlgClosure`, Mathlib.FieldTheory.IsAlgClosed.Basic: an algebraic, algebraically
  closed extension with its algebra structure. Using this recorded predicate
  covers any chosen closure, rather than fixing `AlgebraicClosure k`.
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp, on the over
  category; and `CategoryTheory.Hom.group`,
  Mathlib.CategoryTheory.Monoidal.Cartesian.Grp. These are publicly imported
  through Mathlib.AlgebraicGeometry.Group.Affine. The interpretation agrees with
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, whose documentation was read.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `ConnectedSpace`, Mathlib.Topology.Connected.Basic: includes nonemptiness.
- `FiniteField.frobeniusAlgEquivOfAlgebraic` and its coefficient-power formula,
  Mathlib.FieldTheory.Finite.Basic.
- Mathlib.AlgebraicGeometry.Group.Affine supplies the canonical algebra-map
  `IsOver` instance for Spec, and the Spec/coordinate-algebra machinery.

The available proof-dependency modules are imported plainly (not publicly):
WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected,
Sheaf.AlgebraicGeometry.LfpSmoothFlatBaseChange,
Mathlib.AlgebraicGeometry.Morphisms.Separated,
WeilConjectures.AlgebraicGeometry.Regular,
Sheaf.AlgebraicGeometry.FiniteTypeLocalDimension,
Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension,
Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry,
and Mathlib.AlgebraicGeometry.AlgClosed.Basic.
Finite-type composition/base change and the Jacobson-space result are already
in the public finite-type import. The two proof nodes
`lem-sfb-inner-frobenius-fixed-points-finite` and
`lem-sfb-zero-dimensional-stabilizer-finite-orbit` have no recorded Lean
interface or Mathlib match, so they have no import yet. They are proof inputs,
not notions needed to state this theorem. The docstring records all five proof
steps with their node names; no proof is performed in this delivery.

Edge cases checked before drafting: the trivial group is included and gives the
singleton surjection; q=2 and every other finite-field characteristic are included;
q=0 or q=1 are impossible for a field. ConnectedSpace excludes the empty scheme,
as does the group unit over a field. No dimension lower bound is added, so
zero-dimensional connected smooth groups are included. Noncommutative groups are
included, with the inverse and Frobenius in precisely the stated order. The
statement works in arbitrary explicitly bound scheme universe u; k, K, and G
are taken in the common scheme universe as in the recorded group-scheme API.

Searches made before writing:

- msearch.py leanfinder: “Lang theorem: g inverse times arithmetic Frobenius g is
  surjective on algebraic closure points of a smooth connected affine group
  scheme over a finite field”. Eight results, including field Frobenius,
  fixed-point automorphism maps and field norm surjectivity; none is this theorem.
- msearch.py loogle: `"Frobenius", "surjective"`. Only `surjective_frobenius`,
  a field/perfect-ring theorem, not a theorem about arbitrary group schemes.
- msearch.py grep:
  `LangSteinberg|langMap|lang_map|[Ll]ang.*[Ss]urjective|[Ss]urjective.*[Ll]ang`.
  Only formal-language reversal, unrelated.
- msearch.py leansearch: “Lang theorem for connected smooth affine algebraic
  groups over finite fields”. Eight results about field Galois groups, field
  Frobenius and formal smoothness, no group-scheme Lang theorem.
- rg in lean/WeilConjectures and lean/Sheaf for LangSteinberg, langMap,
  lang_map, and Lang/surjectivity combinations; grep for this item id in
  lean/WeilConjectures; rg in dag/lean_names_upstream.json and both source
  trees for the proposed declaration name. No existing matching declaration.
  The Artin–Schreier files mention a different semilinear vector-space theorem.
- Read the existing affine-group and categorical group APIs; used their
  canonical points and operations instead of defining a second notion.

Source checked directly with pdftotext: Milne, Algebraic Groups, Section 17.k,
paragraph before Definition 17.95 (printed p.382), Theorem 17.96 and Corollary
17.97 (p.383), and Proposition 17.99's proof (p.384). The source's displayed
map x F(x⁻¹) becomes g⁻¹ F(g) upon substituting x=g⁻¹; its Frobenius action is
explicitly the q-power action on coordinates. No statement fault or dispute found.

Validation: scompile.py compiled the sandbox probe and the delivered module
separately against the live build, each in about 1.8 seconds, with no errors or
unexpected warnings. All binders/universes are explicit and autoImplicit and
relaxedAutoImplicit are disabled. The first compile identified a missing scoped
group instance and the need to retain the AlgHom projection in Spec's IsOver
instance; both interface issues were repaired using existing APIs.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
