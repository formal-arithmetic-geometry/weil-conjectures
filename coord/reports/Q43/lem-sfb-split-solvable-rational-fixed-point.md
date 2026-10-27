## Worker report

The module `Sheaf.AlgebraicGeometry.SplitSolvableRationalFixedPoint` states
`AlgebraicGeometry.exists_rational_fixed_point_of_isSplitSolvable`, with a single
`sorry` proof and no new definitions. The node is unchanged except for `lean`.

Source read: Milne, Algebraic Groups (2017), Theorem 16.51 and its proof, printed
p.343, in `literature/milne-algebraic-groups_iAG2017.pdf`. The theorem explicitly
assumes a split solvable algebraic group acting on a complete algebraic scheme
with a rational point. The preceding paragraph defines the split series and
notes smoothness and connectedness. The delivered docstring gives all eight
steps of the DAG proof, including the reciprocal-coordinate additive limit,
its universal fixedness, the multiplicative case, and induction through the
normal fixed subscheme and the represented quotient action.

Hypothesis and conclusion correspondence:

- The arbitrary field is `{k : Type u} [Field k]`. No perfection, infinitude,
  algebraic closedness, or characteristic binder is present.
- The k-group scheme is `H : Grp (Over (Spec (.of k)))`. Its bundled `GrpObj`
  includes multiplication, inverse, and unit with their morphism identities.
- Smooth and connected are `[Smooth H.X.hom]` and
  `[ConnectedSpace H.X.left]`. ConnectedSpace includes nonemptiness, exactly as
  def-weil-connected-scheme requires.
- Affineness is `[IsAffine H.X.left]`. Finite type is the recorded pair
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`.
- The split solvable assumption is the existing `hsplit : IsSplitSolvable H`.
  Reading its definition shows `∃ n, SplitSolvableLength H n`. At zero it
  requires an isomorphism to the trivial group. At a successor it gives the
  smooth connected current group, a closed normal subgroup, the represented
  fppf quotient, its group-scheme isomorphism to G_a or G_m, and the shorter
  series. The quotient uses the actual scheme-theoretic kernel. This is the
  node's subnormal series; no normality in all of H is required.
- The target k-scheme is `X : Over (Spec (.of k))`. Its properness is `[IsProper X.hom]`.
  IsProper includes separatedness, universal closedness, and local finite type;
  universal closedness implies quasi-compactness, so finite type of X is
  included without a redundant additional binder.
- The scheme action and both laws are `[ModObj H.X X]`: its `smul` is the
  k-morphism from the fibre product, and its `one_smul` and `mul_smul` fields
  are precisely the unit and associativity morphism identities. This uses
  Mathlib's existing notion, rather than introducing an abstract action on
  H(k) or an unverified family of actions on algebra points.
- The nonempty set X(k) is
  `hX : Nonempty (𝟙_ (Over (Spec (.of k))) ⟶ X)`.
  The tensor unit in this over-category is Spec k with its identity map.
- The conclusion chooses `x : 𝟙_ (Over (Spec (.of k))) ⟶ X`, a k-rational
  point, and universally quantifies over `(A : Type u) [CommRing A]
  [Algebra k A]` and `h : StandardGroupSchemes.affine k A ⟶ H.X`.
  Here `affine k A` is the existing Spec A with its specified k-structure.
- Scalar extension x_A is `toUnit (StandardGroupSchemes.affine k A) ≫ x`.
  Mathlib's `CategoryTheory.Hom.smul` defines the displayed `h • x_A` as
  `CartesianMonoidalCategory.lift h x_A ≫ ModObj.smul`. Thus the concluding
  equality is literally a_A(h,x_A) = x_A, as a morphism of schemes over k.
  All test algebras in the ambient scheme universe are quantified over, with
  no independent smaller universe or finiteness restriction on A. As H is
  affine, testing its coordinate algebra's universal point also gives the
  orbit-map equality; this expresses scheme-theoretic fixedness and therefore
  remains true on evaluation in any larger universe as well.
- There are no reducedness or connectedness assumptions on X and no positive
  length restriction on the split series.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and
  `CategoryTheory.Grp` (def-sc-group-scheme); the full signatures and fields
  were read. The source's `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`
  documents this precise over-category specialization.
- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms), with its affine-pair smoothness condition.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`
  (def-weil-connected-scheme), extending PreconnectedSpace and Nonempty.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`
  (def-weil-finite-type-morphism), whose signatures/docstrings were read.
- `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`:
  `AlgebraicGeometry.IsSplitSolvable` and `SplitSolvableLength`
  (def-sfb-split-solvable-right-torsors). The entire module and its
  `SolvableGroupStructure.IsFppfQuotient` dependency were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `AlgebraicGeometry.IsProper` (def-weil-proper-morphism), whose full
  class signature and parent classes were read.
- Existing auxiliary interfaces used directly, without new definitions:
  `Mathlib.CategoryTheory.Monoidal.Mod` supplies `ModObj`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod` supplies the induced action
  on hom types; `Sheaf.AlgebraicGeometry.StandardGroupSchemes` supplies
  `StandardGroupSchemes.affine`; `CartesianMonoidalCategory.toUnit` gives
  the structural map to Spec k.

The ordinary imports cover the recorded proof interfaces: the polynomial
IsDomain instance; spectrum stalk and function-field identifications;
Noetherian finite-type permanence; the full signature and docstring of
`exists_extension_at_valuation_stalk`; Spec; principal opens and ideal-sheaf
subschemes; IsIntegral; closed immersions; relative separated dominant
extensionality; and the upstream closed-immersion properness lemmas.
Proof-only nodes without a recorded Lean declaration are not silently
assumed: lem-sfb-split-torus-rational-fixed-point,
lem-sfb-universal-fixed-subscheme, and
lem-sfb-normal-fixed-subscheme-quotient-action have no module to import yet.
Their roles are included in the proof docstring for stage 3.

Edge cases checked before writing:

- H = 1: IsSplitSolvable allows length zero, and the unit action identity
  fixes any chosen rational point. No nontriviality condition excludes it.
- Empty X: hX fails, exactly as the natural-language hypothesis does. A
  nonempty X with no k-rational point also fails hX, as required.
- X = Spec k: its unique rational point is universally fixed for every action.
- Nonreduced or disconnected proper X: no assumption removes them; equalities
  on Spec A include nilpotent test algebras and capture infinitesimal fixedness.
- Finite fields and imperfect fields in positive characteristic: no field
  property beyond Field appears; the conclusion tests all algebras, not only
  the possibly too small finite abstract group H(k).
- The zero k-algebra is allowed by CommRing A; its empty spectrum yields the
  expected unique morphism identity.

Searches actually run through
`/home/ubuntu/weil-launcher-all/batch2/msearch.py Q43
lem-sfb-split-solvable-rational-fixed-point`:

1. `leanfinder`: "A split solvable algebraic group acting on a proper scheme
   with a rational point has a rational fixed point". Eight hits, all about
   fixed subfields, Galois categories, and related abstract algebra; no match.
2. `loogle`: `"IsSplitSolvable"`. Zero hits.
3. `grep`: `Borel.*fixed|fixed.*Borel|split.*solvable|solvable.*fixed`.
   Four hits, all in Mathlib/FieldTheory/AbelRuffini.lean, no match.
4. `leansearch`: "A split solvable group scheme acting on a proper scheme with
   a rational point has a universally fixed rational point". Eight hits on
   abstract group-action fixed points and Abel--Ruffini, no scheme theorem.
5. `rg` of `lean/WeilConjectures` and `lean/Sheaf` for split/solvable fixed-point
   names, and for the exact node id: no declaration stating this theorem.
   The broader action/group searches found the existing ModObj usage in
   GeneralBorelFlagVariety and the split-solvable definition, which are reused.
6. `rg` of `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`
   for `split.*solvable.*fixed|splitSolvable.*fixed|fixed.*splitSolvable|` plus
   the exact node id: no hit.

No statement correction, disputed statement, new node, or dependency repair.

## Second reading by Q43

Independent second reading (maintainer cc review service, 2026-10-25), replacing the
dispatcher's single-worker rereading. The node, its seven stmt_deps, the item module,
`IsSplitSolvable`/`SplitSolvableLength` (Sheaf/AlgebraicGeometry/SplitSolvableTorsorDefinitions.lean),
Mathlib `ModObj`, `Hom.smul` (Mathlib/CategoryTheory/Monoidal/Cartesian/Mod.lean:56,
`m • x = lift m x ≫ ModObj.smul`) and `algSpec` (Mathlib/AlgebraicGeometry/Group/Affine.lean:73)
were read.

Node clause → Lean → verdict:

- field k → `{k : Type u} [Field k]` → exact, no extra field hypothesis.
- k-group scheme H (def-sc-group-scheme) → `H : Grp (Over (Spec (.of k)))` → exact.
- smooth, connected (def-sbc-smooth-morphisms, def-weil-connected-scheme) →
  `[Smooth H.X.hom] [ConnectedSpace H.X.left]` → exact (also implied by every
  `SplitSolvableLength`; harmless repetition of the node's hypotheses).
- affine, finite type (def-weil-finite-type-morphism) → `[IsAffine H.X.left]`
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]` → exact.
- split solvable (def-sfb-split-solvable-right-torsors) → `hsplit : IsSplitSolvable H` →
  exact: length 0 is `H ≅ trivial`, successor gives closed normal N ⟶ H, represented fppf
  quotient q, Q ≅ G_a or G_m, and `SplitSolvableLength N n` (normal in predecessor only).
- proper finite-type X (def-weil-proper-morphism) → `X : Over (Spec (.of k))`, `[IsProper X.hom]`
  → exact (IsProper ⊇ LocallyOfFiniteType; UniversallyClosed ⇒ QuasiCompact).
- action a with a(1,x)=x, a(h,a(h',x))=a(hh',x) as morphism identities → `[ModObj H.X X]`
  (`one_smul'`, `mul_smul'` are those identities, left action, fibre product over Spec k)
  → exact.
- X(k) ≠ ∅ → `hX : Nonempty (𝟙_ _ ⟶ X)` → exact.
- conclusion: ∃ x ∈ X(k), ∀ k-algebra A, ∀ h ∈ H(A), a_A(h,x_A)=x_A →
  `∃ x, ∀ (A : Type u) [CommRing A] [Algebra k A] (h : Spec_k A ⟶ H.X),
  h • (toUnit Spec_k A ≫ x) = toUnit Spec_k A ≫ x` → exact, quantifiers in order; A in
  the scheme universe u (project convention; testing the coordinate algebra of the affine
  H already gives the orbit-map identity).

Edge cases: H = 1 (length 0 allowed); X = ∅ and X with no rational point (hX false);
nonreduced/disconnected X (no assumption); finite or imperfect k; A = 0 (empty Spec,
trivially true). All covered as in the node.

Searches: rg in lean/Sheaf and lean/WeilConjectures for `fixed_point`, `IsSplitSolvable`,
`ModObj` uses; DAG nodes lem-sfb-split-torus-rational-fixed-point,
lem-sfb-universal-fixed-subscheme, lem-sfb-normal-fixed-subscheme-quotient-action and
def-sfb-scheme-action-torsor-groupoids read: none states this theorem (proof deps
only; the last is the action-groupoid construction, not a predicate the item needs).

Mismatch found and changed: the statement used `StandardGroupSchemes.affine k A`, owned by
def-sc-gm-ga, which is only a proof_dep/tool_use, not a stmt_dep. The wrapper's body
`(algSpec (.of k)).obj (.op (CommAlgCat.of k A))` (Mathlib) was inlined in the statement
and docstring, with `public import Mathlib.AlgebraicGeometry.Group.Affine`; the lean
record's statement was updated verbatim. Definitionally the same object; no mathematical
change. Compiled with nt_compile.py: clean (only the `sorry`), 1.7 s.

## Validation

The worker's prescribed `scompile.py` compilation and delivery dry run passed (see the
delivered report). The reviewer's corrected file compiled clean through
`tools/nt_compile.py` (exit 0, 1.7 s); a control with a deliberate type error in the
conclusion failed as expected, confirming the file elaborates.
