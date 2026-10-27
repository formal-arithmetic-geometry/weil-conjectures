## Worker report

The module `Sheaf.AlgebraicGeometry.CurveNonzeroLineMapDegree` states
`AlgebraicGeometry.Scheme.Modules.curve_nonzero_line_map_degree`. Its only theorem has
proof `sorry`; it introduces no definitions or instances. Only the item's `lean` record
changes. There is no statement correction, disputed statement, new node, or dependency repair.

Source read: `literature/stacks-project/varieties.tex`, Tag 0B40,
`lemma-check-invertible-sheaf-trivial`, especially the displayed sheaf-Hom identity in the
proof of (5), and Tag 0AYX, `lemma-degree-tensor-product`, in rank one. The former applies
nonnegative section degree to the tensor quotient; the latter gives its degree difference.
The stronger equality/implies-isomorphism assertion of 0B40(5) is not part of this node
and is not appended to the Lean conclusion.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`.
- A scheme C proper over k: `(C : Scheme.{u}) [C.Over (Spec (.of k))]` and
  `[IsProper (C ↘ Spec (.of k))]`. No algebraic closure, perfection, smoothness,
  regularity, or geometric integrality is assumed.
- C integral: `[IsIntegral C]`, including nonemptiness, reducedness and irreducibility.
- Topological dimension one: `(hC : topologicalKrullDim C = 1)`.
- Invertible modules A and B: `(A B : C.Modules) [A.IsInvertible] [B.IsInvertible]`.
- A-dual means precisely sheaf Hom(A,O): the existing `Scheme.Modules.dual A`, defined
  as `SheafOfModules.homObj A (SheafOfModules.unit _)`, is used throughout.
- L is precisely `B ⊗ dual A`, the existing sheafified tensor over the structure sheaf.
  It is expanded in the signature instead of introducing an opaque object or a let binder.
- A-dual and L invertible: `(dual A).IsInvertible ∧ (B ⊗ dual A).IsInvertible`.
- The evaluation is an isomorphism: `IsIso (dualEvaluation A)`. This is the existing
  canonical evaluation with source `A ⊗ dual A` and target the tensor unit O_C;
  it asserts that evaluation itself is invertible, not an unspecified isomorphism.
- The canonical Gamma(C,O_C)-linear isomorphism: an additive equivalence
  `E : (A ⟶ B) ≃+ Γ(B ⊗ dual A, ⊤)` together with
  `∀ (r : Γ(C, ⊤)) (φ : A ⟶ B), E (φ ≫ B.smulHom r) = r • E φ`.
  Postcomposition with `B.smulHom r` is exactly multiplication of a sheaf map by r.
  Thus the additive equivalence and this equation say exactly that E is linear over
  Gamma(C,O_C), without introducing a second module structure on Hom.
- The map is canonical and has the node's local formula: for every φ,
  `homOfGlobalSection (B ⊗ dual A) (E φ) = Hom.adjointSection φ`.
  I opened the full definition and docstring of `Hom.adjointSection` in upstream
  `Modules/ZeroLocusDual.lean`: it is `inv (dualEvaluation A) ≫ φ ▷ dual A`.
  On any open with frames e_A,e_B, inverse evaluation sends 1 to e_A tensor e_A-dual,
  and the second map sends it to h e_B tensor e_A-dual when φ(e_A)=h e_B.
  The defining equation therefore fixes exactly the local formula in the node,
  simultaneously on every trivializing open. It excludes arbitrary linear equivalences.
  `homOfGlobalSection` is the existing bijection between sections and maps from O_C:
  its source definition sends r to r times the restriction of the section. Hence the
  equation is an exact characterization of the section, not an added hypothesis.
- Degree convention: `Scheme.Modules.degree` from `Cohomology/EulerChar.lean` is
  literally `M.eulerChar k - (SheafOfModules.unit C.ringCatSheaf).eulerChar k`.
  The recorded Euler characteristic in `Cohomology/Defs.lean` is the alternating finsum
  of `Module.finrank k (M.H q)` in Z. On a proper dimension-one scheme with invertible
  sheaves, coherence and cohomological vanishing make this the node's finite sum.
- Degree of the dual: `(dual A).degree k = -A.degree k`.
- Degree of L: `(B ⊗ dual A).degree k = B.degree k - A.degree k`.
- Nonzero φ implies nonzero corresponding section and nonnegative degree:
  `∀ φ : A ⟶ B, φ ≠ 0 → E φ ≠ 0 ∧ 0 ≤ (B ⊗ dual A).degree k`.
  The equivalence is supplied also when φ=0; nonzeroness is imposed only in this
  implication, as in the node.

Dependency declarations inspected and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (the field dependency is a Mathlib leaf and
  correctly has no lean record).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, extending
  separated, universally closed and locally finite type; universally closed also
  supplies quasi-compactness, so this is the node's properness.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, locally trivial of rank one.
- `WeilConjectures.AlgebraicGeometry.Modules.Dual`: `dual`, `dualEvaluation`,
  `IsInvertible.dual`, `nonempty_iso_dual_dual`, and its tensor-inverse API.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded tensor dependency, imported
  publicly; the scheme's tensor is the same existing sheafification construction.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.Modules.degree`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar` and `smulHom`.
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocusDual`: existing canonical helper
  `AlgebraicGeometry.Scheme.Modules.Hom.adjointSection`; its imported
  `Modules.PullbackFreeGenerator` supplies `homOfGlobalSection`.
- Proof imports: `Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive` and
  `Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity`, with declarations
  `degree_tensorObj_of_topologicalKrullDim_le_one` and
  `curve_section_degree_nonneg_and_pos`. The remaining proof dependency,
  `lem-pc-tensor-dual-invertible`, is recorded in the publicly imported upstream Dual
  module. No proof dependency module is omitted.

The module and all variables/universes are explicit (`autoImplicit false` and
`relaxedAutoImplicit false`). There are no local instances or private definitions.
The public-import convention and the current replacement for the withdrawn
CompactObject example were checked in the source.

Edge cases checked mathematically before writing:

- A=B and φ the identity: the canonical section is the inverse evaluation section;
  both degree differences are zero.
- The zero map: E sends it to zero; no nonzero or positivity assertion is made for it.
- On P1, A=O(a), B=O(b), Hom can be nonzero precisely when b-a is nonnegative;
  the tensor-dual is O(b-a), matching both degree statements.
- If b<a on P1, the nonzero-map implication has no nonzero input, while the
  equivalence and degree identities remain valid.
- Singular integral proper curves and non-algebraically-closed fields are included;
  local rank-one frames, evaluation and section positivity still apply. Smoothness
  and the assumption Gamma(C,O_C)=k would wrongly exclude these cases and are absent.
- Empty C and dimension-zero schemes are excluded by the original integral/dimension
  hypotheses; the statement introduces no additional nonemptiness assumption.
- Frame changes e_A'=u e_A and e_B'=v e_B give h'=u v^{-1} h and
  (e_A')-dual=u^{-1} e_A-dual; the section is invariant. This also checks the order
  B tensor A-dual, rather than A tensor B-dual.

Searches actually run through the prescribed msearch wrapper on 2026-10-24:

- leanfinder: `A nonzero morphism between invertible sheaves on a proper integral curve
  is a section of target tensor source dual and has nonnegative degree difference`.
  Eight hits on affine/projective global-section restriction and local equations;
  none states this theorem.
- loogle: `"IsInvertible", "degree"`: zero hits.
- grep, Mathlib AlgebraicGeometry: `degree.*dual|dual.*degree|Hom.*sections`:
  seven hits, concerning Proj global-section maps, an integral morphism comment and
  module morphisms; no theorem with the required clauses.
- Direct rg over upstream WeilConjectures and project Sheaf for degree/dual,
  nonzero/degree, Hom/sections and `Hom.adjointSection`: upstream Dual and
  ZeroLocusDual supply the constructions; RiemannRoch has specialized degree facts
  under curve hypotheses, not the full statement here. Project section positivity
  and tensor additivity are the existing proof dependencies.
- `grep -rn 'lem-sfb-curve-nonzero-line-map-degree' lean/WeilConjectures`:
  no hits. Direct rg for the proposed declaration across Mathlib, WeilConjectures,
  Sheaf and `dag/lean_names_upstream.json`: no hit before writing the sandbox file.

Validation: the required `scompile.py Q109 lem-sfb-curve-nonzero-line-map-degree`
compiled the sandbox and library forms cleanly (1.7 s each). The 100-column check passed.
Dry-run/delivery results are recorded below after the prescribed checks.

## Second reading by Q109

Dispatcher policy forbids starting other agents and assigns independent review to the
maintainer. No independent worker reading is claimed here. In my final self-check with
the node and the module open, I matched every hypothesis and clause as listed above;
checked that the scalar equation uses all global functions, not just k-scalars;
checked that the canonicality equation fixes the map rather than merely giving a
Nonempty choice; and checked that the nonzero-section and nonnegative-degree clauses
use the same E. No mismatch was found. The maintainer's independent review remains
part of the delivery process.
