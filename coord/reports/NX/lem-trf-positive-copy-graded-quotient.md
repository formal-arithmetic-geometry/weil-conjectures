## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.PositiveCopyGradedQuotient`.
Main statement: `AlgebraicGeometry.exists_positiveCopyGradedQuotient`.
The sole postponed proof is that theorem's `sorry`. The two helper definitions contain
actual data: the piecewise family and the canonical direct-sum linear map. No new
independent notion, node, or dependency repair is needed, and no node statement changes.

Source read: Stacks `morphisms.tex`, Tag 0B3I, `lemma-finite-projective`, especially the
canonical map to the projective bundle and its affine generator 1. The target node's
six proof steps give the explicit positive-copy construction. This delivery follows
those steps, including their categorical-sheaf-coproduct correction, rather than claiming
that a sheaf coproduct is computed on sections over arbitrary opens. The source's finite
morphism is the motivating application; the construction itself needs no finiteness.

Hypotheses and clauses:

- `X : Scheme.{u}` is an arbitrary scheme, with its full universe explicitly bound.
  `E : X.CommAlgebraSheaf` supplies a commutative unital structure-sheaf algebra.
  `[E.toModule.IsQuasicoherent]` is the sole additional assumption.
- `positiveCopyPiece E 0` is literally `SheafOfModules.unit X.ringCatSheaf`;
  `positiveCopyPiece E (n+1)` is literally `E.toModule`. Thus the family is the stated
  family, including degree zero even when E is zero.
- The conclusion supplies an algebra sheaf B, sheaf-module arrows `i n` from those
  pieces, and `G : GradedSheafAlgebra (positiveCopyPiece E)`.
  `Nonempty (IsColimit (Cofan.mk B.toModule i))` says precisely that the underlying
  module is the categorical sheaf coproduct. It is an existence assertion for a proof
  of the coproduct property, not a definition choosing undetermined data from a sorry.
- `B.toModule.IsQuasicoherent` is quasi-coherence of the total underlying module.
- `G.unit = 𝟙 ...` fixes the homogeneous unit in degree zero. Four homogeneous product
  clauses specify degree zero times degree zero, zero times positive, positive times
  zero, and positive times positive. The mixed formulas use `E.hom.hom.app` and the
  positive formula uses multiplication of E. HEq only handles definitionally different
  natural-number expressions for the same component. The algebra laws and restriction
  compatibility are the fields of the existing `GradedSheafAlgebra` structure.
- The `i (m+n)` product equation says the algebra multiplication on B is the extension
  of G's homogeneous multiplication. The `i 0` equation identifies the scalar inclusion
  with B's actual algebra structure homomorphism, hence also fixes its unit.
- `positiveCopySectionSum E B i U` is `DirectSum.toModule` of the section maps `i n`.
  Its bijectivity is required for every `U : X.affineOpens`. It is already linear over
  `Γ(X,U)`, and its component maps are exactly the homogeneous inclusions. Together
  with the preceding multiplication and scalar equations this is precisely the
  canonical graded R-algebra identification of B(U) with R plus the positive A copies:
  the source multiplication on finite sums is the bilinear extension of those equations.
  This avoids an arbitrary ring structure on the direct-sum model. Inclusions of
  arbitrary affine opens commute with this comparison because every `i n` is a sheaf
  morphism; naturality on summands extends to all finite sums. No principal-open or
  affine-intersection hypothesis is imposed.
- The source of `q` is the existing constructed `SymmetricAlgebraSheaf.algebra E.toModule`.
  Its degree-one map is the existing `SymmetricAlgebraSheaf.inclusion`. `∃! q` and the
  first clause assert the unique extension of the degree-one inclusion into B.
- The second q-clause sends the nth power of the range of `SymmetricAlgebra.ι` into
  the nth target piece on every open. This is the dependency's symmetric-degree
  submodule (tensor images equal these powers). Applying the canonical `sectionMap`
  and sheafifying gives precisely the symmetric homogeneous subsheaf. Therefore this
  clause encodes degree preservation as a sheaf map, not just on a single affine chart.
  Locally every section of that homogeneous sheaf is represented this way, and the
  inclusion `i n` identifies a subsheaf: coproduct injections are split monomorphisms
  in sheaves of modules. Thus local membership gives membership in the target piece.
- The third q-clause is its scalar/degree-zero identity, using the identification
  `B_0 = O_X` and `i 0`. It does not assume an injective structure map into E.
- The last clause is degreewise surjectivity, expressed by homogeneous lifts on every
  open. Positive lifts are the stated `j(a) j(1_E)^(n-1)`; degree zero lifts are scalars.
  These lifts already exist in the sectionwise symmetric algebra, so the clause implies
  the required surjectivity for the homogeneous sheaf maps, including on their sections.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
  Affine opens use `X.affineOpens`, whose ring is canonically `Γ(X,U)`; no separate
  presentation by an arbitrarily chosen isomorphic spectrum is needed.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `Scheme.IsQuasiCoherentAlgebra`, `QuasiCoherentAlgebra`; its underlying encoding is
  `Scheme.CommAlgebraSheaf` and `Scheme.CommAlgebraSheaf.toModule` from
  `WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf`. We use exactly this underlying
  module and Mathlib's `SheafOfModules.IsQuasicoherent` predicate.
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`: `GradedSheafAlgebra`,
  with its full bilinear-map, naturality, associativity, commutativity and unit fields.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`:
  `exists_quasiCoherentSymmetricAlgebra`, universal property and canonical affine
  section comparison. The actual algebra, inclusion and section map are read from
  `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`.
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`:
  `SymmetricAlgebra.graded_by_tensor_images`, including its spanning, zero/one-degree,
  internal-direct-sum and multiplication clauses. The range-power form is the same
  grading, by mapping tensor-power ranges along the quotient algebra map.
- Proof imports retain `Mathlib.AlgebraicGeometry.Modules.Tilde` for `tilde.adjunction`,
  `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`, `tildeSelf`, `tildeFinsupp`,
  `isoTop`, and the module-restriction interface from Mathlib's Modules.Sheaf.
  `Sheaf.AlgebraicGeometry.CoherentFiniteType` is retained as the recorded module of
  proof dependency `pqf-def-coherent`; its extra finite-type predicate is not imposed
  on this theorem. The quasi-coherence component is Mathlib's existing predicate.

Searches actually run:

- `msearch.py leanfinder`: “A quasi coherent commutative algebra sheaf gives a graded
  algebra with degree zero the structure sheaf and a copy of the algebra in each
  positive degree and a degreewise surjective symmetric algebra map”. Eight results
  concerned Proj structure sheaves; none states this construction or quotient.
- `msearch.py loogle`: `SymmetricAlgebra.lift`. Six hits gave the ring-level lift and
  its generator equations, not the graded sheaf result. The declaration and its
  relevant type were read in Mathlib's SymmetricAlgebra/Basic.lean.
- `msearch.py grep`: `positiveCopy|PositiveCopy|positive.copy|graded.*sheaf.*quotient`,
  restricted to Mathlib/AlgebraicGeometry: zero hits.
- `rg` on both project roots for `positive.copy|PositiveCopy|positiveCopy` and for the
  item id: zero matches. Further `rg` searches for `SymmetricAlgebraSheaf` and
  `GradedSheafAlgebra` located the reused declarations and the canonical affine-basis
  symmetric grading; none was an existing positive-copy quotient theorem.
- `rg` on `dag/lean_names_upstream.json` and both project roots for the three proposed
  full declaration suffixes found no conflicts before writing the delivery record.

Edge cases checked mathematically before writing: empty scheme and empty open;
zero algebra (positive pieces vanish while degree zero remains the structure sheaf);
E equal to the structure algebra; noninjective maps such as Z to Z/2; degree zero;
degree one (exponent zero in its lift); arbitrary non-finite-type algebras. None adds
a finiteness, local-freeness, nonzero, injectivity, or characteristic assumption.
The index set is all natural numbers, with no truncation.

Validation: `scompile.py NX lem-trf-positive-copy-graded-quotient` compiled the delivered
module in sandbox mode and at its actual module name with no warnings or errors.
No proof was supplied. No statement dispute or source correction is required.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
