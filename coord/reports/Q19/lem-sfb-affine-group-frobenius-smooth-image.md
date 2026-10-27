## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupFrobeniusSmoothImage` states
`AlgebraicGeometry.affine_group_frobenius_smooth_image`, with its sole proof `sorry`.
No definition, new node, dependency repair or statement correction is needed.
Read the source PDF, printed pp.71--73 (PDF pp.83--85): Cartier Theorem 3.23,
Proposition 3.29 and Remark 3.30 agree with the node. Proposition 3.29 explicitly
identifies the coordinate map with b tensor c to c b^(p^r), and Remark 3.30
identifies the image factorization. No faithful-flatness clause has been added.

Hypotheses and clauses, against the node:

- The arbitrary algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The k-scheme is `(G : Scheme.{u}) (s : G ⟶ Spec (.of k))`; the explicit structure
  map is appropriate because the conclusion uses its base change. The given group
  structure is `[GrpObj (Over.mk s)]`, and affineness is `[IsAffine G]`.
- Finite type is exactly `[LocallyOfFiniteType s] [QuasiCompact s]`, as recorded
  by def-weil-finite-type-morphism; no connectedness, reducedness or commutativity
  of the group is assumed.
- The characteristic-zero clause is `(CharZero k → Smooth s)`.
- Positive characteristic is quantified by `(p : ℕ) (hp : p.Prime) (hk : (p : k) = 0)`;
  over a field this is exactly characteristic p, and p is positive by primality.
- The required integer r >= 1 is `∃ r : ℕ, 1 ≤ r ∧ ...`.
- The twist is `pullback s (Spec.map (CommRingCat.ofHom
  (iterateFrobeniusOfPrime k hp hk r)))`, with second projection as structure map.
  The recorded ring Frobenius has actual underlying function a to a^(p^r).
- The existential map `F` has first projection `G.iterateFrobenius hp hG r` and
  second projection `s`. The auxiliary proof `hG : (p : Γ(G, ⊤)) = 0` is a
  conclusion, not an extra hypothesis; it follows by the structure ring map from hk.
  The pullback universal property makes F unique. This is exactly relative
  Frobenius, not an arbitrary map. In the affine tensor-product identification,
  the two projections force the coordinate map b tensor c to c b^(p^r).
- The target group structure `hT` is required to equal
  `Over.grpObjMkPullbackSnd`, the canonical base change of the original group.
  The subsequent existential `GrpObj` is the group structure on the image I.
- I is `F.image`, Mathlib's scheme-theoretic image `F.ker.subscheme`. The definitions
  in Mathlib.AlgebraicGeometry.IdealSheaf.Basic and .Subscheme construct the kernel
  ideal sheaf and cover its subscheme by Spec of the quotient rings. On the affine
  target, this is exactly Spec(k[G^(p^r)] / ker F^*), as in the node, up to its
  canonical affine isomorphism. No reduced or topological image is substituted.
- The image's k-structure is `F.imageι ≫ pullback.snd s ...`. Its required
  properties are `IsAffine F.image`, `LocallyOfFiniteType` and `QuasiCompact` of
  this structure map, and `Smooth` of the same map.
- `u` and `j` are morphisms in Over(Spec k), with `u.left = F.toImage` and
  `j.left = F.imageι`. Thus they are the canonical scheme-theoretic image factor
  maps. `IsMonHom u` and `IsMonHom j` make them group homomorphisms for the
  supplied image group and the canonical base-changed target group.
- `IsClosedImmersion j.left` renders the specified closed immersion, and
  `u.left ≫ j.left = F` renders j composed with u equal to relative Frobenius.

Dependency declarations read and used (including their defining signatures/docstrings):

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field`.
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, `IsAlgClosed`
  (the algebraically closed field component of its mathlib_match).
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp, `GrpObj`, together
  with Mathlib.CategoryTheory.Monoidal.Mon, `IsMonHom`; the recorded upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents precisely this use.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `LocallyOfFiniteType`, and .QuasiCompact, `QuasiCompact`.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth, `Smooth`.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `pullback`, `pullback.fst`, `pullback.snd`, and its universal property.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, `Spec`, `Spec.map`.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `IsClosedImmersion` (closed embedding and surjective stalk maps).
- Added already-landed def-weil-absolute-frobenius-scheme and
  def-weil-ring-frobenius to stmt_deps because the projection specification uses
  their recorded declarations: WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius,
  `Scheme.iterateFrobenius`, and WeilConjectures.Mathlib.Algebra.CharP.Lemmas,
  `iterateFrobeniusOfPrime`. Both have real constructions, including zero rings.
- Mathlib.CategoryTheory.Monoidal.Cartesian.Over, `Over.grpObjMkPullbackSnd`,
  gives the prescribed base-changed group structure.
- Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme, `Scheme.Hom.image`,
  `Scheme.Hom.toImage`, `Scheme.Hom.imageι`, gives the canonical image.

All twelve proof dependencies were inspected. Their available modules are imported
in the proof's scope: Mathlib.AlgebraicGeometry.Group.Affine (coordinate Hopf algebra
and `hopfSpec`), Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra,
Sheaf.RingTheory.HopfAlgebra.ReducedCoreNilpotentFibre,
Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField,
Mathlib.AlgebraicGeometry.Group.Smooth (`smooth_of_grpObj`), and
Mathlib.RingTheory.TensorProduct.Maps. The affine reducedness, affine pullback,
tensor algebra and closed-immersion modules are also supplied by these imports
and the public dependency imports. The theorem docstring carries all six proof
steps with the exact node identifiers.

Edge cases checked before writing: the trivial group is included; finite infinitesimal
groups such as alpha_p and mu_p are permitted and their Frobenius image is trivial
and smooth. For alpha_(p^n), r must be large enough, so no fixed r or r=1 conclusion
is asserted. Disconnected and noncommutative groups are included. A group scheme
over a field cannot be empty because it has a unit section; no extraneous nonempty
hypothesis was added. Characteristic zero and every prime, including 2, are covered.
The single universe u is arbitrary, as for the recorded Scheme/Spec interfaces;
there is no test-object quantifier whose universe can make a hypothesis vacuous.
The exponent is explicitly positive. The auxiliary section-characteristic proof
adds no restriction to the initial hypotheses.

Searches actually run:

- msearch.py leanfinder: "Finite type affine group scheme over algebraically closed
  field smooth characteristic zero and smooth image of iterated relative Frobenius
  in positive characteristic" returned eight hits, including
  Algebra.Smooth.exists_finiteType, Algebra.FormallySmooth.of_perfectField,
  IsAlgClosed.perfectRing and FiniteField.frobeniusAlgEquiv; none states this theorem.
- msearch.py loogle: `AlgebraicGeometry.smooth_of_grpObj` returned the exact
  geometrically reduced group smoothness theorem; it requires geometric reducedness
  and therefore does not supply the item, as already recorded by its proof dependency.
- msearch.py grep: `Frobenius|frobenius|Cartier` in AlgebraicGeometry returned no hits.
- msearch.py leansearch: "Cartier smoothness and reduced images of powers of Frobenius
  on affine algebraic groups" returned LinearMap.frobenius, smoothLocus_eq_univ_iff,
  LinearMap.iterateFrobenius and five other ring/smoothness hits; no exact match.
- rg in the prescribed WeilConjectures and Sheaf trees for relativeFrobenius,
  frobeniusTwist, Frobenius image and Cartier found absolute Frobenius, finite-field
  relative Frobenius, and curve statements that specify relative Frobenius by its
  projections. No general theorem gives this item. The finite-field relative map
  is too specialized, so it is not used or duplicated.
- grep -rn for this node id in WeilConjectures returned no match. Searches of the
  upstream name index and both project trees for the proposed declaration name
  returned no match.

Validation: scompile.py compiled the delivered module in sandbox and library mode
against the published server build without errors or warnings (1.9 s / 2.3 s).
The first elaboration exposed that a general Over object is not definitionally
Over.mk of its structure map for group-instance search. The final interface uses
an explicit scheme and structure map with exactly `GrpObj (Over.mk s)`; this is
the same mathematical hypothesis and requires no dependency repair.

## Second reading by Q19

I re-read the complete node statement, source pp.71--73, and final compiled signature
clause by clause. This is a worker self-check; the dispatcher brief assigns the
independent review to the maintainer, and forbids starting another agent.
The conclusion keeps both characteristic clauses, the positive exponent, the
actual Frobenius twist, its canonical base-change group structure, the
scheme-theoretic quotient image, all four geometric image properties, both group
homomorphisms, the closed immersion, and the composition equality. In particular,
F is pinned down by its two projections, and u and j by their equalities with the
canonical factor maps; no arbitrary substitute can satisfy those specifications.
There are no changed mathematical hypotheses or clauses. The compiler repair
replaced a bundled Over variable by its explicit structure morphism to make the
same group instance available to Mathlib's base-change operation. All postponed
proof content is confined to the one matching theorem.
