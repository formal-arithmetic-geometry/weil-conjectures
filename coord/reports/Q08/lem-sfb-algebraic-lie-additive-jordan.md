## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicLieAdditiveJordan` states all clauses of
`lem-sfb-algebraic-lie-additive-jordan`, in four named theorems. All proofs are `sorry`.
Its two transparent Prop-valued helpers package conditions within this node; they introduce
neither new mathematical objects nor another construction of a dependency notion.
The node statement, statement dependencies and proof plan are unchanged.

Hypotheses and clauses, matched to Lean:

- A field k: `{k : Type u} [Field k]`. A fixed algebraic closure:
  `(Ω : Type v) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]`. Its universe is independent
  of that of k. No algebraic closedness or characteristic assumption is placed on k.
- An affine finite-type k-group scheme: `H : Over (Spec (.of k))`, `[GrpObj H]`,
  `[IsAffine H.left]`, `[LocallyOfFiniteType H.hom]`, `[QuasiCompact H.hom]`.
  There is no smoothness, reducedness, connectedness or positive-dimensional hypothesis.
- Its tangent Lie algebra: `GrpObj.Lie H`, with the upstream canonical Lie bracket.
  This is linearly identified with the dependency's actual `schemeTangentSpace` at the
  identity by imported `GrpObj.lieIdentityTangentEquiv`. The bracket is the canonical
  mixed commutator, not an arbitrary Lie structure supplied by the consumer.
- Rational representation of positive integer dimension n: `n : ℕ`, `0 < n`,
  `r : GeneralLinearGroup.RationalHom H (LinearGroupSchemes.Index.{u} n)`,
  `[IsMonHom r]`. `Index n = ULift (Fin n)` gives exactly n coordinates in the
  field's universe. `RationalHom` is a scheme morphism H -> GL_n over k;
  `IsMonHom` imposes the algebraic group homomorphism equations.
- Its differential is the existing `r.differential`, obtained by composing the canonical
  group differential with the canonical `Lie(GL_n)` matrix equivalence.
- Geometric semisimplicity of a matrix A:
  `Module.End.IsSemisimple (Matrix.toLin' (A.map (algebraMap k Ω)))`.
  On the algebraically closed field Ω the finite-dimensional endomorphism is semisimple
  exactly when diagonalizable (Mathlib.LinearAlgebra.Eigenspace.Semisimple,
  `Module.End.IsSemisimple.iSup_eigenspace_eq_top`). Nilpotence is `IsNilpotent A`,
  equivalent here to vanishing of a positive power; for A=0 use exponent 1.
- The perfect-field premise is `[PerfectField k]` on precisely the first three theorems.
  Mathlib's irreducible-polynomial separability definition is equivalent to every
  algebraic extension being separable.
- Existence and uniqueness of an ordered pair: `∃! p : GrpObj.Lie H × GrpObj.Lie H,
  IsAlgebraicLieJordanPair Ω H Y p.1 p.2`. The helper expands to `Y = Ys + Yn`,
  `⁅Ys, Yn⁆ = 0`, and the above semisimplicity/nilpotence conditions for EVERY r.
  Since `r.differential` is a Lie homomorphism, its images sum to dr(Y) and commute;
  hence they are exactly the commuting matrix Jordan parts, by matrix uniqueness.
  These identities need no extra assumptions and are not replaced by separate arbitrary
  matrix witnesses. The helper includes both universal representation clauses.
- Preservation under homomorphisms: `algebraicLieJordanPair_differential` takes affine
  finite-type H,H', a genuine homomorphism `f` with `[IsMonHom f]`, and a Jordan pair;
  its conclusion is the same pair predicate for `df(Y),df(Ys),df(Yn)` in H'.
  Combined with existence/uniqueness, this is equality with the unique parts there.
- Preservation under perfect field extensions: `algebraicLieJordanPair_scalarExtension`
  has fields k,K with `[Algebra k K]` and BOTH perfect, using the actual group pullback
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj (Grp.mk H)`.
  The inputs YK,YsK,YnK are required by `IsLieScalarExtension` to be the canonical
  extensions: their dual-number points project to the old points precomposed with the
  explicit `Spec.map (DualNumber.mapRingHom (algebraMap k K))`.
  This condition uniquely specifies each image of 1 tensor Y by the pullback universal
  property and the upstream Lie/tangent equivalence. It is not a free map or a
  representability hypothesis. The conclusion asserts the Jordan predicate for ALL
  rational representations of the pulled-back K-group, not merely those descending
  from k. An independently chosen closure ΩK is allowed.
- Arbitrary-field faithful detection: `algebraicLie_faithful_differential_detection`
  DOES NOT require perfectness. It takes positive m and a genuine rational representation
  i with `[IsClosedImmersion i.left]`. The conclusion gives `Function.Injective i.differential`
  and, for each Y and every positive-dimensional algebraic r, both implications:
  geometric semisimplicity of di(Y) implies that of dr(Y), and nilpotence of di(Y)
  implies that of dr(Y). Both conclusions use the prescribed closure Ω.
- No declaration quantifies over an abstract Lie representation; every matrix-valued
  differential comes from `GeneralLinearGroup.RationalHom` plus `IsMonHom`.

Dependencies read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosure` and `AlgebraicClosure`,
  Mathlib.FieldTheory.IsAlgClosed.Basic/AlgebraicClosure.
- `CategoryTheory.GrpObj` / `IsMonHom`, Mathlib.CategoryTheory.Monoidal.Grp,
  with the k-group convention in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact;
  `IsClosedImmersion`, Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- `schemeTangentSpace`, WeilConjectures.AlgebraicGeometry.SchemeTangentSpace,
  read in full including its residue-field scalar convention;
  `GrpObj.lieIdentityTangentEquiv`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv, realizes its
  identity-point specialization. No dependency-interface repair is needed.
- `LieRing`, `LieAlgebra`, Mathlib.Algebra.Lie.Basic; realized by the canonical
  `GrpObj.Lie`, `GrpObj.lieEquivTangent` and bracket instances from
  WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic/Bracket.
- The general-linear dependency's module Sheaf.AlgebraicGeometry.LinearGroupSchemes
  is imported, using its `LinearGroupSchemes.Index` and the upstream GL construction
  that its record explicitly says to reuse. `GeneralLinearGroup`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear;
  `GeneralLinearGroup.RationalHom`, `RationalHom.differential`,
  `GeneralLinearGroup.lieAlgebraEquivMatrix`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie;
  `GrpObj.differential`, GroupScheme.Lie.Differential. Their full signatures and
  dual-number formula docstrings were read.
- The already recorded proof dependency is imported without `public`:
  Sheaf.AlgebraicGeometry.AffineGroupTensorReconstruction,
  `RationalRepresentation.affineGroup_tensor_reconstruction`.
  The faithful-representation, tangent-calculus and linear-compatibility proof nodes
  have no recorded Lean declaration in the inspected live read clone, so no fictitious
  imports for them were added. Their steps remain in the theorem docstrings.

Source and edge cases:

Read the local Milne PDF, Proposition 17.74(a),(b), printed p.377, and the preceding
p.376 preliminaries. The node explicitly confines the representations to algebraic
rational ones; it does not transfer the source's loose wording to arbitrary Lie modules.
The source is an exercise and the node supplies its full reconstruction proof plan,
which is carried into the four theorem docstrings. No source correction was needed.

Checked Y=0, the trivial group, nonreduced groups (including infinitesimal groups in
positive characteristic), imperfect k in the detection theorem, finite perfect fields,
and n=m=1. The first three results apply in every characteristic. The theorem does not
assert existence of k-rational Jordan parts over imperfect k. The node defines rational
representations with n>=1, and the delivered universal quantifiers have precisely this
range; the proof plan may use the zero representation internally. `ULift (Fin n)`
retains exactly n coordinates. Identity extensions K=k and identity group homomorphisms
are included. Scalar extension admits independently chosen algebraic closures and does
not assume K-representations descend. Empty schemes are not group schemes over a field,
since their identity section cannot exist; no excluded group case is hidden there.

Searches (the exact wrapper outputs are in the sandbox searches.jsonl):

- msearch.py leanfinder: "Additive Jordan decomposition in the tangent Lie algebra of
  an affine algebraic group, functorial for rational representations". Eight hits concern
  manifold Lie algebras or abstract weight spaces; none is the algebraic theorem.
- msearch.py loogle: "Module.End.IsSemisimple, IsNilpotent". Six hits, including
  `Module.End.exists_isNilpotent_isSemisimple` and its uniqueness theorem, are linear
  Jordan decomposition; none asserts membership in the algebraic group's tangent Lie
  algebra or faithful differential detection.
- msearch.py grep: "JordanChevalley|groupLieAlgebra|GroupScheme.*Lie". Nine Mathlib hits;
  these are abstract associative-adjoint Jordan results and manifold Lie constructions.
- msearch.py leansearch: "The Jordan Chevalley decomposition of an algebraic group Lie
  algebra element is respected by rational representation differentials". Eight hits,
  with the linear endomorphism theorem but no group-scheme theorem.
- rg of lean/WeilConjectures and lean/Sheaf for GroupLie/groupLie, tangent Lie,
  RationalRepresentation, generalLinearGroup, scalar/base-change Lie and Jordan names.
  Found the canonical upstream differential/matrix/Lie construction and reused it;
  no statement of this node and no existing pair/scalar-extension helper were found.
  The exact node-id grep in WeilConjectures has no match. The same helper-name grep
  in dag/lean_names_upstream.json has no match.
- `tools/blueprint_refs.py search 'Jordan decomposition'` reports 0 blueprint nodes.
  The existing DAG tangent-calculus and linear-compatibility proof nodes were read;
  no duplicate new node is introduced for either.

Validation: scompile.py compiled the delivery module in both sandbox and library modes,
2.4 and 2.3 seconds respectively, with no errors or unexpected warnings. The initial
namespace elaboration error for dot-notation `.IsSemisimple` was repaired by writing
`Module.End.IsSemisimple` explicitly. All variables/universes are explicit, enforced by
`set_option autoImplicit false`. No definitions contain sorry data. No theorem is proved.

## Second reading by Q08

This is the dispatcher's single-worker packet; no independent sub-agent was started,
as the assignment explicitly prohibits it. This section records a separate self-audit
of the node beside the final module; the maintainer's independent mathematical reading
remains the delivery review.

Checked all eight statement-dependency records, the unchanged statement and proof plan,
and the final declarations. The ordered-pair `∃!` includes equality of both parts;
`IsAlgebraicLieJordanPair` includes sum, zero bracket, and BOTH representation properties.
The commuting matrix identities follow from the existing Lie-hom differential, so no
representation clause was lost. The arbitrary-field detection result contains injectivity
and both implications, with no perfectness binder. The scalar-extension result uses
actual pullback group structure and actual projection equality of tangent points, and
its conclusion tests arbitrary K-representations. No arbitrary isomorphism, field
embedding between chosen closures, or arbitrary Lie-module hypothesis has been inserted.
The source-tangent equivalence is imported explicitly, so the canonical `GrpObj.Lie`
carrier is the recorded tangent space at identity, with its canonical operations.
No statement discrepancy or disputed assertion was found. The only elaboration repair
was the explicit semisimplicity namespace mentioned above.
