## Worker report

The module `Sheaf.RepresentationTheory.Sl2LatticeIntegration` states
`RepresentationTheory.existsUnique_sl2_lattice_integration`, with its sole theorem proof
`sorry`. It defines the actual integral weight submodules as kernels. No statement correction,
dependency repair, or disputed mathematical assertion is needed. The original statement and
proof are preserved; the item only gains its Lean record and one definition dependency.

Source read: Milne, Algebraic Groups (2017), printed pp.507--511 (PDF pages 519--523),
Theorem 23.70, equations (152)--(153), and the integral-group paragraph following 23.73.
The node explicitly supplies the integral two-chart argument that Milne omits. The current
blueprint unit `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` was read;
this supporting node is not that unit's statement. Its nearest recorded blueprint ancestor
is null, as confirmed by `tools/blueprint_refs.py ancestor`.

Hypothesis and clause correspondence:

- Free finite-rank abelian L: `(L : Type u) [AddCommGroup L] [Module ℤ L]
  [Module.Free ℤ L] [Module.Finite ℤ L]`. The recorded free-module notion is used directly.
- Rationalization W: the actual `ℚ ⊗[ℤ] L`. This reverses the displayed factor order
  L tensor Q by the canonical tensor symmetry and gives the standard scalar-extension
  API; the canonical lattice map is `l ↦ 1 ⊗ₜ l`. No unrelated rational space is introduced.
- Rational endomorphisms E,F,H: `Module.End ℚ (ℚ ⊗[ℤ] L)`.
- All three commutator equations: exactly `hHE`, `hHF`, `hEF`, in the stated order,
  with rational scalar multiples 2 and -2.
- Nilpotence: `hE : IsNilpotent E`, `hF : IsNilpotent F`.
- Diagonalizability with integral eigenvalues: `hH` is a finite rational basis with an
  integer-valued weight function and the eigenvector equation for every basis vector.
  This is the same encoding used by the recorded rational-polynomial-model theorem.
- Integral weight decomposition: `hL : DirectSum.IsInternal (sl2LatticeWeight L H)`.
  The helper is the kernel of H minus j on the canonical integral inclusion, hence
  precisely L intersect W_j. Mathlib's `IsInternal` means the canonical direct-sum map
  is bijective, including independence and spanning.
- Every divided power preserves L: `hdivE`, `hdivF`, for every natural m, assert that
  its rational endomorphism is the base change of an integral endomorphism D.
  Since L is free, the map L to Q tensor L is injective, so preservation of L is
  equivalent to the existence of this unique integral lift. These are not arbitrary
  extra operators: their rationalizations fix them uniquely.
- The finite X-plus and X-minus formulas: the first conjunct specifies the underlying
  linear maps of the upper and lower root images as
  `∑ m ∈ Finset.range N, a ^ m • (dE m).baseChange A`, respectively dF.
  It quantifies over every common nilpotence bound N and all families of the uniquely
  specified integral divided powers. Such families exist by hdivE/hdivF and choice;
  a common bound exists by nilpotence. Thus the implication has a nonempty intended
  domain. The finite sum is exactly the infinite displayed sum, whose omitted terms
  vanish. There is no denominator in the test ring A.
- The formulas give automorphisms: `ρ.app A` takes values in actual A-linear
  equivalences, and the root images equal the displayed linear maps.
- D(s) acts by s^j on each weight summand after tensoring: the second conjunct acts
  on `a ⊗ₜ l` for every l in `sl2LatticeWeight L H j`, every a, and every integer j.
  These pure tensors generate the summand; `hL` makes their sum the whole module.
  Units power `s ^ j` allows all negative weights. `integralSl2Diagonal` is exactly
  diag(s,s inverse): multiplication of its explicit root words gives that matrix.
- Unique homomorphism of affine group schemes: `∃! ρ : IntegralSl2LatticeHom B L`.
  Its `app` field is a group homomorphism on all determinant-one matrices, not just
  elementary matrices. `naturality` tests every algebra map and every vector.
  Its `regular` field states that all matrix entries in some finite integral basis
  are polynomial functions on the determinant-one matrices. The source coordinate
  ring is therefore exactly B[a,b,c,d]/(ad-bc-1). Applying the group law to g and
  its adjugate supplies polynomial inverse entries, so this determines a map from
  the existing GL localization coordinate ring. Conversely every affine group-scheme
  map has such polynomial representatives. Representatives and bases occur only
  existentially in a Prop field, not as redundant data that would spoil uniqueness.
- Arbitrary base change, including nonreduced rings: B is any `Type v` with only
  `[CommRing B]`. Both existence and uniqueness are asserted over B, on every
  `CommAlgCat.{max u v} B`. For B = integers this gives the requested integral action;
  its scalar extension satisfies the same restrictions and regularity, and uniqueness
  over B identifies it with the action asserted there. Thus the full base-change
  uniqueness assertion is retained. Test-algebra universes include both the lattice
  and base universes, so neither universal coordinate rings nor small rings are lost.
- Rank zero/trivial action: no Nontrivial or positive-rank hypothesis is imposed.

Dependencies read and used:

- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`,
  full class and docstring at lines 43--44; finite-basis instances in
  `Mathlib.LinearAlgebra.FreeModule.Finite.Basic`.
- Proof dependency `lem-sfb-sl2-rational-polynomial-model`:
  `Sheaf.RepresentationTheory.Sl2RationalPolynomialModel`,
  `RepresentationTheory.exists_sl2_rational_polynomial_model`; full signature and
  proof docstring read, imported without public visibility.
- Proof dependency `lem-weil-pbc-scheme-morphism-gluing`: its Mathlib match is
  `Mathlib.AlgebraicGeometry.Gluing`, `AlgebraicGeometry.Scheme.Cover.glueMorphisms`,
  together with `hom_ext` and `ι_glueMorphisms`; declarations and docstrings read.
  This proof module is imported without public visibility.
- Added statement dependency `def-sfb-integral-sl2-lattice-hom` supplies the regular
  natural action type and the diagonal point. Existing Mathlib tensor products,
  baseChange, linear equivalences, internal direct sums, polynomial evaluation,
  determinant-one matrices and transvections are used without private replacements.

Edge cases checked mathematically before writing: zero lattice admits an empty basis,
all rational endomorphisms are zero, even N = 0 gives the zero linear map, which is the
identity on the zero module. For positive-rank trivial representations, all positive
powers vanish, m = 0 is identity, and only weight zero occurs. Negative weights use
unit zpow. Finite characteristic and nonreduced rings never divide by m factorial.
The zero test ring is allowed. Bases and regularity allow n = 0. Any two sufficiently
large nilpotence bounds give the same sum because all further integral coefficients
have zero rationalization and L is torsion-free. Root-word multiplication was checked
with arbitrary unit s: w(s) has entries [0,s;-s inverse,0], and w(s)w(1) inverse is
[s,0;0,s inverse]. The two charts cover because ad-bc = 1, even after arbitrary base change.

Searches actually performed (exact service responses are in the new node's search records):

- msearch LeanFinder: "A finite free integral weight decomposed sl2 module stable under
  divided powers integrates uniquely to an SL2 group scheme representation" returned
  Lie-module primitive-vector lemmas and abstract modular-group facts; no integration.
- msearch Loogle: "Matrix.SpecialLinearGroup, IsSl2Triple" returned zero hits.
- msearch grep: `divided.power|integrat.*SL|admissible.lattice`, Algebra, returned only
  the vertex-operator Hasse derivative.
- msearch LeanSearch: "Natural representations of the affine group scheme SL2 over
  arbitrary commutative base rings on a finite free integral lattice" returned matrix
  SL and linear SL definitions and matrix actions; none defines the regular natural family.
- msearch LeanFinder: "Natural families of group homomorphisms from SL2 matrices over
  all algebras to automorphisms of a scalar extended integral module" returned mapGL,
  baseChange, modular-group and standard matrix actions; no general family interface.
- msearch grep: `SL2Hom|LatticeHom|SpecialLinearGroup.*TensorProduct|SL2.*Representation`
  returned unrelated order-lattice homomorphisms. Direct project searches for SL2Hom,
  sl2, integral lattice and group schemes found `RankOneRoots.SL2Hom`, whose full
  signature was read: it requires a field base and a target group scheme, so it cannot
  describe this ring-general integral action. `LinearGroupSchemes.specialLinear` is
  likewise field-specific; its coordinate and point interfaces were read.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib, `dag/nodes`, and
  `dag/lean_names_upstream.json`, plus grep for the exact item id in WeilConjectures:
  no existing integration theorem or integral action type. The upstream GL coordinate
  ring and scheme declarations were read to check the coordinate-ring interpretation.
- `tools/blueprint_refs.py search` on "integral SL2" and "natural family" returned
  zero matches; definition-node searches found the field-only general linear and
  rank-one interfaces, not this integral action notion.

Validation: both delivered modules compile separately via scompile.py, with no errors
or warnings. The theorem remains sorry as required for stage 2. No proof is supplied.

## New nodes

`def-sfb-integral-sl2-lattice-hom` defines regular natural SL2 actions on the scalar
extension of an integral finite free lattice over an arbitrary commutative base B.
Its own module is `Sheaf.RepresentationTheory.IntegralSl2LatticeHom`. The only data
field is the actual family of group homomorphisms; naturality and regularity are proofs
required of the family, with no sorry or arbitrary choices in the definition. The helper
`integralSl2Diagonal` is the explicit root-word construction of the diagonal matrix.
Its source is Milne equations (152)--(153) and the item's affine functor-of-points
convention. The LeanSearch, LeanFinder and Mathlib/project/DAG grep searches above
found no existing ring-general interface. The field-only `RankOneRoots.SL2Hom` cannot
be instantiated with integers or a nonreduced base. This is an independent definition
of the missing integral interface, not another copy of matrix SL, GL or tensor product.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
