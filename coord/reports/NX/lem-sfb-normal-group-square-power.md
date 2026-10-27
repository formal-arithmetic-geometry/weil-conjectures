## Worker report

The module `Sheaf.AlgebraicGeometry.NormalGroupSquarePower` states
`AlgebraicGeometry.exists_tensorPow_square_of_normal_base`, with its sole proof
`sorry`. There are no definitions or additional postponed lemmas. Only `lean`
is added to the item node; its accepted statement, split, and dependencies remain
unchanged. The previous worker's stage-1 refusal is superseded for this assignment
by brief-stage2 §0: the live node is split/reviewed but has no Lean record.

Source read: Guo, *Divisors on coherent schemes and homogeneous spaces*, online
PDF https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf,
Proposition 5.9, final assertion (1), printed pp. 13–14, and its proof. The source
proves the normal integral-base assertion. The accepted DAG extends this over
finitely many disjoint normal integral components; the module docstring retains
all six steps of that argument. The latest blueprint target preservation
statement/proof was also inspected; this auxiliary is not that unit's statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme S is `(S : Scheme.{u})`; affine is `[IsAffine S]`, and locally
  Noetherian is `[IsLocallyNoetherian S]`.
- Normality is exactly `hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
  IsIntegrallyClosed (S.presheaf.stalk s)`. This uses the node's local rings,
  rather than imposing integrality or connectedness of S.
- The S-scheme H and its structure morphism are `(H : Over S)` and `H.hom`.
  `[GrpObj H]` supplies multiplication, identity, inverse and their axioms in
  the cartesian monoidal category `Over S`. Its product is the scheme fibre
  product, and its tensor unit is S. There is no commutativity hypothesis.
- Smoothness and separatedness are `[Smooth H.hom]` and
  `[IsSeparated H.hom]`; the latter means the diagonal is a closed immersion.
- Finite presentation is `[LocallyOfFinitePresentation H.hom]`,
  `[QuasiCompact H.hom]`, and `[QuasiSeparated H.hom]`, exactly the comparison
  convention of def-sbc-locally-finite-presentation. The final conjunct is
  redundant under separatedness but included to spell out finite presentation.
- Connected fibres are `hH : ∀ s : S, ConnectedSpace (H.hom.fiber s)`.
  The definition of `.fiber s` is the pullback along `S.fromSpecResidueField s`,
  so the fibres are precisely H times_S Spec kappa(s). `ConnectedSpace`
  includes nonemptiness, as required by def-weil-connected-scheme.
- The invertible module is `(L : H.left.Modules) [L.IsInvertible]`, using the
  recorded scheme-module notion, not a separate sheaf predicate.
- The positive integer exponent is `∃ r : ℕ, 1 ≤ r ∧ ...`; positive naturals
  identify with the integers r >= 1 of the node. The module power is the
  existing `L.tensorPow r`.
- `∀ (B : Over S) (g h : B ⟶ H)` ranges over every S-scheme and every pair of
  its H-valued points, with one r fixed before B, g, h are introduced.
- In `Over S`, `H ⊗ B` has underlying scheme
  `pullback H.hom B.hom`. Its first and second projections are respectively
  `(fst H B).left` and `(snd H B).left`; the latter is q_B.
- Write p = fst H B and q = snd H B in this explanation only. The categorical
  Hom-group multiplication satisfies `a * b = lift a b ≫ μ`, so
  `((q ≫ g) * p).left : (H ⊗ B).left ⟶ H.left` sends (x,b) to g(b)x.
  It is exactly the first projection after translation by g. The first factor
  uses `g * h`, in that order, so evaluates to (gh)x without commuting g, h.
- Each displayed translated term is the tensor pullback of `L.tensorPow r`
  along that composite. By pullback composition this is canonically
  tau_g^*(M_B), where M = L^(tensor r) and M_B = p^*M. The unshifted term
  is `(tensorPullback p.left).obj (L.tensorPow r) = M_B`.
  Writing the composite directly avoids a second definition of translations
  or of the square condition. No arbitrary translation maps are quantified.
- `∃ N : B.left.Modules, N.IsInvertible ∧ Nonempty (...)` gives an invertible
  base line and existence of exactly the isomorphism
  tau_(gh)^*M_B tensor M_B ≅
  (tau_g^*M_B tensor tau_h^*M_B) tensor q_B^*N.
  The last term is `(tensorPullback (snd H B).left).obj N`.
  All three tensor signs are sheaf-module tensors in the same scheme's module
  category. `Nonempty` requests no chosen isomorphism or coherence.

Dependency interfaces read and used (full signatures/docstrings inspected):

| Node | Module and declaration |
| --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation: AlgebraicGeometry.LocallyOfFinitePresentation |
| def-weil-connected-scheme | Mathlib.Topology.Connected.Basic: ConnectedSpace (mathlib_match) |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: CategoryTheory.Limits.pullback, pullback.fst, pullback.snd |
| def-weil-residue-field | Mathlib.AlgebraicGeometry.ResidueField: AlgebraicGeometry.Scheme.residueField; the standard .fiber uses it |
| def-sc-invertible-module | WeilConjectures.AlgebraicGeometry.Modules.Invertible: AlgebraicGeometry.Scheme.Modules.IsInvertible and tensorPow |
| def-pc-module-pullback | Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: tensorPullbackSectionAdjunction and the publicly imported Scheme.Modules.tensorPullback |
| def-pur-sheaf-tensor-product | Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: SheafOfModules.cochainModulesMonoidal; the standard Scheme.Modules tensor instance from Invertible specializes this same localization construction |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian |
| def-weil-pbc-normal-ring | Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: IsIntegrallyClosed and IsDomain, applied to each stalk |

Additional existing Mathlib APIs: CategoryTheory.GrpObj in
Mathlib.CategoryTheory.Monoidal.Grp, the cartesian Hom group and multiplication
in Mathlib.CategoryTheory.Monoidal.Cartesian.Grp/Mon, the cartesian product
on `Over` (Mathlib.CategoryTheory.Monoidal.Cartesian.Over), and
AlgebraicGeometry.Scheme.Hom.fiber in Mathlib.AlgebraicGeometry.Fiber.
Their bodies were read to check the order of multiplication and projections.

Every available proof-dependency module is imported privately: Slicing for
Smooth.exists_geometricallyIrreducible_of_section; Geometrically.Reduced for
Smooth.geometricallyReduced; Mathlib Geometrically.Integral (also the standard
IsIntegral imported through Properties); RegularNormalDecomposition for
regular_normal_and_normal_decomposition; Proper and Smooth for the two
base-change clauses; QuasiSeparated and its imports for qcqs permanence;
Separated for separated base change. Statement imports remain public when the
same module is also needed by the proof. The supporting nodes
lem-sfb-field-product-square-power and lem-sfb-normal-product-square-descent
have no recorded Lean declarations yet, so have no import to add. Both are
named explicitly in the six-step proof docstring; they are proof inputs only,
not unstated notions needed to type the present statement.

Edge cases checked before writing:

- Empty S is allowed: hS and hH quantify over no points, H and every B over S
  are empty, and r = 1 gives the unique module identity. No Nonempty S binder.
- Disconnected normal S is allowed: hS is pointwise and no IsIntegral S or
  ConnectedSpace S hypothesis appears. The finite clopen argument supplies a
  common positive exponent, rather than an exponent depending on B.
- H is allowed nonproper and noncommutative. Hom multiplication gives ghx
  in the stated order; no IsCommMonObj or IsProper binder occurs.
- B may be empty, nonaffine, nonreduced, or disconnected. No condition on B
  other than its S-structure is added, and g and h may be equal or the identity.
- r = 0 is excluded by 1 <= r, r = 1 is retained. The trivial line is allowed.
- A nonempty fibre cannot be dropped: ConnectedSpace is the exact nonempty
  connected-space class. S need not itself have any points.
- Universe u is explicit, and all scheme objects and module constructions use
  the existing Scheme.{u} conventions, with no extra universe equations.

Searches for existing statements:

1. msearch.py leanfinder, query: "Every invertible sheaf on a smooth group
   scheme with connected fibres over a normal Noetherian affine scheme has a
   positive tensor power satisfying the theorem of the square". Eight hits,
   consisting of quasi-compact denominator lemmas, pullback carrier tensors,
   and purely inseparable powers; none states a group-scheme square theorem.
2. msearch.py loogle, query: `"GrpObj", "tensorPow"`. Zero hits.
3. msearch.py grep, query: `theorem.of.the.square|squareCondition|SquareCondition`,
   Mathlib/AlgebraicGeometry. Zero hits.
4. msearch.py leansearch, query: "A positive tensor power of a line bundle on
   a smooth group scheme over a normal affine Noetherian base satisfies the
   theorem of the square". Eight hits, TensorPower.mulEquiv and tensor-power
   linear algebra/Proj identities; none is the claimed geometric statement.
5. rg in lean/WeilConjectures and lean/Sheaf for the node id and
   `theorem.of.the.square|squareCondition|SquareCondition`: only unrelated
   supported coefficient tensor comparison squares in Sheaf; no match upstream.
   Exact proposed declaration name also absent from Mathlib, both project roots,
   and dag/lean_names_upstream.json. No existing definition is duplicated.

No statement correction, dependency repair, new node, or mathematical dispute
was needed. The example CompactObject Sheaf file has been withdrawn; its node
now records the upstream definition, so that upstream example and the current
module-mode conventions were used.

Validation: scompile.py compiled both the sandbox probe and the actual library
module cleanly (first pass 1.9/2.1 s); explicit statement-dependency imports were
then added and the final module was compiled again. No proof was attempted.
Final explicit-import compile: sandbox 2.2 s, library module 2.0 s, no errors or
warnings. `deliver2.py --no-push` returned
`OK (dry run): commit 567e565625b passes the preflight and compiles; nothing pushed`.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
