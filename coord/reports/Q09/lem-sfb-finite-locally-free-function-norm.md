## Worker report

Stage 2, Q09: `Sheaf.AlgebraicGeometry.FiniteLocallyFreeFunctionNorm` states
`AlgebraicGeometry.exists_finiteLocallyFree_functionNorm`. Its only postponed proof is
that theorem (`by sorry`). The accompanying helper
`AlgebraicGeometry.Scheme.Hom.sectionMultiplicationMatrix` is fully defined, with entries
`e.repr (b * e j) i`; it installs exactly `(f.app U).hom.toModule` in its body. This is
the multiplication matrix in Stacks Tag 0BD2, not a new independent notion or norm.

Read the full node and its proof, all three statement dependencies and their recorded
signatures/docstrings, the available proof interfaces, Stacks divisors.tex Section 0BCX
and Lemma 0BD2, and the current blueprint direct-image proof in
literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/.
The inherited stage-1 BLOCKED message is obsolete for this assignment: the current
queue lists stage 2 and brief-stage2.md explicitly authorizes this handoff.

Hypothesis and clause correspondence:

- Schemes and the given morphism are `{X Y : Scheme.{u}} (f : Y ⟶ X)`, with arbitrary
  explicit universe u. The orientation is Y to X, exactly as in the node.
- Constant finite locally free degree is `[f.IsFiniteLocallyFreeOfDegree d]` with
  `(d : ℕ) (hd : 1 ≤ d)`. The recorded class extends finite locally free and specifies
  the fibre degree at every point, including the empty-base case vacuously.
- One simultaneous norm family over every open is
  `∃ ν : ∀ V : X.Opens, Γ(Y, f ⁻¹ᵁ V) →* Γ(X, V)`. The monoid homomorphism type
  supplies preservation of multiplication and 1, without imposing additivity.
- The first conjunct quantifies all `V W`, inclusions `hWV : W ≤ V`, and sections b;
  it equates the restriction of `ν V b` with `ν W` of the restricted b. Both restriction
  maps are the structure-presheaf maps on `homOfLE`, upstairs using `f.preimage_mono`.
- The second conjunct is precisely `ν V (f.app V a) = a ^ d` for every V and a.
- The third conjunct quantifies every `y : Y` and `hy : y ∈ f ⁻¹ᵁ V`. It reads
  `Y.evaluation ... b = 0 → X.evaluation V (f y) hy (ν V b) = 0`.
  These evaluations land in the recorded residue fields; hy also expresses f(y) in V.
- The final conjunct quantifies every affine `U ≤ V` and every basis e indexed by
  `Fin d` for sections upstairs over `Γ(X,U)`. Its module structure is explicitly
  `(f.app U).hom.toModule`, never an arbitrary action. On affine U, the finite
  pushforward is quasi-coherent, so such a basis is exactly a rank-d trivialization
  of its restriction, and every basis is included. The equality identifies the
  restriction of the norm with `Matrix.det` of the helper applied to b restricted
  upstairs. The helper's column j is the coordinate vector of multiplication by b
  on e(j). Thus this is the requested multiplication matrix, not just an unspecified
  determinant or isomorphism. Matrix.det is Mathlib's Leibniz determinant. Its
  convention `prod i, M (σ i) i` equals `prod i, M i (σ i)` after inverting σ, whose
  sign is unchanged; hence it is the exact determinant specified by the node.
- There are no reducedness, separability or Noetherian assumptions, no arbitrary
  base-change conclusion, and no extra uniqueness claim.

Dependencies used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- def-pc-finite-locally-free:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, classes
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` and
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` (read lines 895--909).
- def-weil-residue-field: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.Hom.residueFieldMap`, and the
  canonical `Scheme.evaluation` into that residue field.
- The matrix and basis use Mathlib's `Module.Basis`, `RingHom.toModule`, and
  `Matrix.det` directly. No definitions of the dependency notions are copied.

The plain proof imports preserve every currently recorded module: the
FiniteLocallyFreeStructureSheaf theorem for lem-pc-flf-properties; LocallyFree for
SheafOfModules.IsFiniteLocallyFreeOfRank; Mathlib finite/integral morphisms;
LinearAlgebra.Determinant for LinearMap.det; Matrix.Adjugate and determinant Basic
for the three Cramer identities and Matrix.det; and the upstream
Localization.NormTrace module for Algebra.norm_notMem_iff. Scheme and ResidueField
are already public statement imports. The node
lem-a1-principal-free-algebra-determinant-norm has no Lean record or Mathlib match,
so has no import to add yet; it is cited in the theorem's full natural-language
proof. It is a proof dependency, not a missing notion needed to state this item.

Edge cases checked before writing: empty base and empty open, with their unique
section rings and vacuous point conditions; d=1 (the identity norm); the split
algebra R^d (product of components); nonreduced dual numbers, where the scalar
norm is a^2 and vanishing follows from the prime criterion; arbitrary characteristic;
and the zero ring/empty affine chart, whose finite indexed basis and determinant
still make sense. The theorem excludes only d=0, exactly as the node does.
On a general nonaffine open the section module need not be globally free; therefore
the norm family is existential and is not defined as `f.normAt V` on all opens.

Searches made (all for this item via the prescribed msearch.py):

- LeanFinder: "A finite locally free morphism of schemes has a multiplicative norm
  on regular functions compatible with restriction, equal to the determinant of
  multiplication and carrying scalars to their degree power". Eight hits included
  Algebra.norm_localization, Algebra.norm_apply and Algebra.norm_eq_matrix_det;
  none supplies this entire scheme-level norm family.
- Loogle: `Algebra.norm, AlgebraicGeometry.Scheme`: zero hits.
- Mathlib grep: `normAt|norm_charts|norm.*[Ss]heaf|[Ss]heaf.*norm` in AlgebraicGeometry:
  five Normalization.lean hits, unrelated to the determinant function norm.
- LeanSearch: "Finite locally free morphisms of schemes have a multiplicative
  determinant norm on structure sheaves taking scalar sections to their degree power":
  eight hits (LinearMap.det, finite morphisms and determinant variants), no exact match.
- rg in both lean/WeilConjectures and lean/Sheaf for normAt, norm_charts,
  functionNorm/function_norm, finiteLocallyFree.*[Nn]orm and norm.*finiteLocallyFree.
  Read BaseChangeNorm.lean: `Scheme.Hom.normAt` is an algebra norm on arbitrary section
  rings, with its useful restriction/nonvanishing theorems restricted to a finite
  field-extension base-change situation. It is not a global locally free sheaf norm.
  Read FiniteLocallyFreeNormCharts.lean: exists_finiteLocallyFree_norm_charts gives
  a section with local determinants on some charts; it does not state the coherent
  family and the scalar/vanishing/every-basis clauses here. The nearby Sheaf affine
  groupoid norm uses these charts but does not state this theorem either.
- rg for the exact node id in lean/WeilConjectures: no match. Exact declaration-name
  searches for sectionMultiplicationMatrix and exists_finiteLocallyFree_functionNorm
  in Mathlib, WeilConjectures, Sheaf and the upstream name index: no collision.

No new nodes, dependency repairs, disputed statements, or statement corrections.
The inherited blueprint.from.node is null; it is maintainer-owned and unchanged.
The example CompactObject module is now withdrawn (no declarations); the current
module-mode header conventions in the brief were followed.

Validation: scompile.py compiled the final module both as Sheaf.Stage2.Sandbox0
(15.3 seconds) and under its library name (6.7 seconds), exit 0, with no warnings.
The initial direct coordinate expression lacked a synthesizable module instance
when coercing a basis to its vector family. The fully defined matrix helper repairs
that elaboration issue while retaining the explicit canonical module structure.

## Second reading by Q09

Author's final clause-by-clause recheck only: the dispatcher explicitly forbids
starting other agents and specifies the maintainer's independent review of the
delivery. No independent worker review is claimed here. Reading the actual node
against the final signature confirms one common family (not separate pointwise
choices), all open restrictions, multiplication and 1, every scalar, every point
and residue field, and every rank-d basis on every affine subopen. The helper has
real data, and no theorem beyond the item's matching node was introduced. Independent
mathematical second reading is left to the maintainer as requested in this brief.
