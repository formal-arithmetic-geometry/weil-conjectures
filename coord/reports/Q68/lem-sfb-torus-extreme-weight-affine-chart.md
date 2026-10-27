## Worker report

The delivery states `AlgebraicGeometry.torus_extreme_weight_affine_chart` in
`Sheaf.AlgebraicGeometry.TorusExtremeWeightAffineChart`, with its entire proof `sorry`.
The theorem docstring reproduces all five steps of the accepted proof plan. The supporting
module `Sheaf.AlgebraicGeometry.TorusProjectiveWeightData` contains seven explicit definitions;
none has postponed data or proof fields. There is no statement correction or dispute.

The source was read directly from Milne's PDF: printed pp.274--276 (PDF pp.286--288),
including Lemma 13.51 and Propositions 13.52 and 13.53, and printed p.374 (PDF p.386).
The statement follows Proposition 13.53(a), whose conclusion has dimension one; the
printed dimension-two sentence in its proof is the known typo already noted by stage 1.
The current blueprint is latest/main-20261024 at ef6f9619; `blueprint_refs.py ancestor`
returns null for this auxiliary node, and the new node preserves that ancestry and via chain.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k, any characteristic | `(k : Type u) [Field k] [IsAlgClosed k]`; no characteristic restriction |
| Nonzero finite-dimensional E | `E : Type v`, `AddCommGroup`, `Module k E`, `FiniteDimensional k E`, `Nontrivial E` |
| Coordinates of P(E) | Arbitrary finite coordinate type `I : Type u` and arbitrary `b : Module.Basis I k E`; the representation is expressed in this basis. Any finite-dimensional E, in any universe v, admits such a finite small index type. No adapted basis is assumed. |
| Split rank-r torus | `T : Grp (Over (Spec (.of k)))`, `r : ℕ`, `_hT : Nonempty (T ≅ MultiplicativeType.splitTorus k r)` |
| Rational group-scheme representation | `ρ : T.X ⟶ GeneralLinearGroup I k` with `[IsMonHom ρ]` |
| Action on P(E) induced by ρ | `[pact : ModObj ...]`, `_hinduced : IsInduced T ρ`; the latter checks actual matrix images of generating vectors over every algebra, including nonreduced ones. Trivializations cover every line subbundle locally, so this fixes the entire action, not merely k-points. |
| Nonempty smooth connected projective k-scheme X | `X : Over ...`, `[Smooth X.hom] [ConnectedSpace X.left] [IsProjective X.hom]`; ConnectedSpace includes nonemptiness |
| Equivariant closed immersion i | `i : X ⟶ Over.mk ...`, `[IsClosedImmersion i.left]`, `_hequiv` is equality of the two action/embedding composites as morphisms |
| Lines i(y), y in X(k), span E | `_hspan` is the submodule span of every vector whose b-coordinates `Represents` some `y ≫ i`; all nonzero scalar multiples are included, so this is exactly the span of the lines |
| Fixed subscheme is finite nonempty disjoint union of reduced k-points | `F : Over ...`, `[IsFinite F.hom] [IsReduced F.left] [Nonempty F.left]`, closed inclusion `j`; over algebraically closed k a finite reduced k-algebra is a nonempty finite product of k exactly under these hypotheses |
| F represents points fixed after every algebra extension | `_hfixed` says factorization through j iff, for every B and algebra map A to B and every t in T(B), the base-changed point is fixed; the base-change map is the recorded `StandardGroupSchemes.map k f.hom` |
| Decomposition into nonzero character eigenspaces | Finite `Ω`, distinct group-scheme characters `χ` via `_hχ`, subspaces `W`, `_hnonzero`, `_hdirect : DirectSum.IsInternal W`, and `_hweights` identifies membership with `IsWeightVector b T ρ (χ c)` over every algebra |
| Existence of separating cocharacter | First conjunct `∃ ell m, Separates T χ ell m`; Separates includes injectivity of m and equality χ_c ell = t^(m_c) over every algebra |
| Every such cocharacter | Second conjunct `∀ ell m, Separates ... → ...`; it is not restricted to a chosen witness of the first conjunct |
| Unique least character | `∃ c₀, (∀ c, c ≠ c₀ → m c₀ < m c) ∧ ...`; the strict inequalities determine c₀ uniquely |
| Least space is one-dimensional | `Module.finrank k (W c₀) = 1` |
| Its line is i(x₀) for unique fixed k-point x₀ | `∃! x₀ : affine k k ⟶ F`, with every nonzero vector of `W c₀` representing `x₀ ≫ j ≫ i` |
| Any nonzero e₀ | `∀ e₀ : E, e₀ ∈ W c₀ → e₀ ≠ 0 → ...` |
| Define normalized dual f₀, zero on other weights | Existence of `f₀ : Module.Dual k E` with `f₀ e₀ = 1` and `∀ c ≠ c₀, ∀ e ∈ W c, f₀ e = 0`; the direct sum and dimension-one assertion determine this form uniquely. The following universal quantifier proves the chart assertion for every form with these defining equations, so no unconstrained choice is used. |
| U is inverse image of D(f₀) | `i.left ⁻¹ᵁ dualOpen b f`; dualOpen is the generating locus of the actual section sum f(b_i) z_i of O(1) |
| U affine | `IsAffineOpen (i.left ⁻¹ᵁ dualOpen b f)`, equivalently its canonical open subscheme is affine |
| Exact equality of k-point sets | Equality of the two sets indexed by `y : affine k k ⟶ X`; membership in U is tested on the unique point `IsLocalRing.closedPoint k` of Spec k |
| Zariski closure of T(k) orbit in X | `closure (Set.range fun t : affine k k ⟶ T.X ↦ (t • y).left (IsLocalRing.closedPoint k))`; the closure is taken in X.left, not in the projective ambient space or a discrete rational-point type |
| Rank zero and trivial cocharacter included | r is unrestricted; Separates contains no nontriviality condition; with one character injectivity of m is automatic |

Dependency declarations read and reused:

- `Field` (Mathlib.Algebra.Field.Defs), `FiniteDimensional = Module.Finite`
  (Mathlib.LinearAlgebra.FiniteDimensional.Defs), and `Module.Basis`
  (Mathlib.LinearAlgebra.Basis.Defs; the free-module dependency's underlying basis notion).
- `CategoryTheory.GrpObj`, `Grp`, `IsMonHom`, `ModObj` and the action on test-point Hom
  types (Mathlib.CategoryTheory.Monoidal.Grp, Mon, and Monoidal.Cartesian.Mod).
- `StandardGroupSchemes.affine`, `.map`, `.multiplicative` and its canonical GrpObj
  (Sheaf.AlgebraicGeometry.StandardGroupSchemes), read with their full docstrings.
- `MultiplicativeType.splitTorus` (Sheaf.AlgebraicGeometry.ToriMultiplicativeType),
  including its rank-zero branch, and `RankOneRoots.Character`, `Cocharacter`,
  `multiplicativeValue` (Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces).
- `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`
  (WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear). The attached linear-group
  node records SL constructions and explicitly reuses this upstream GL implementation;
  no duplicate GL, SL or determinant construction is introduced here.
- `Scheme`, `Spec` and `Scheme.ΓSpecIso` (Mathlib.AlgebraicGeometry.Scheme),
  `ProjectiveSpace` (WeilConjectures.AlgebraicGeometry.ProjectiveSpace),
  `ProjectiveSpace.homOfSections` (its OfSections module), `twistOneSection` and `twist`
  (its Twist module), and `Scheme.Modules.generatingLocus`
  (WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus).
- `Smooth` (Mathlib.AlgebraicGeometry.Morphisms.Smooth), `ConnectedSpace`
  (Mathlib.Topology.Connected.Basic), `IsProjective` and its H-projective convention
  (WeilConjectures.AlgebraicGeometry.Morphisms.Projective), `IsClosedImmersion`
  (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion), `IsOpenImmersion`
  (Mathlib.AlgebraicGeometry.OpenImmersion), and `IsAffine`
  (Mathlib.AlgebraicGeometry.AffineScheme). Opens use the canonical open subscheme;
  there is no replacement definition of open immersion or affine scheme.
- Proof-only imports are WeilConjectures.AlgebraicGeometry.Regular (`IsRegular.of_smooth`,
  `IsRegular.isIntegral`) and Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
  (`ProjectiveSpace.projectiveSpace_standardCharts`). The two other proof dependencies,
  split-torus-representation-weight-decomposition and projective-torus-fixed-weight-schemes,
  have no Lean records in the read snapshot, so there are no modules to import for them.

Edge cases checked mathematically: Spec k with E one-dimensional and r=0; a single character
with a trivial cocharacter; two distinct weights on P¹, for either ordering; the Veronese
conic with weights 0,1,2; arbitrary positive characteristic; negative cocharacter pairings;
zero and nonreduced test algebras. Empty X is excluded by ConnectedSpace as in the source;
zero E is excluded by Nontrivial. An empty Ω cannot satisfy the internal direct sum for
nonzero E, so no spurious least-weight witness is required. No independent smaller universe
is used for test algebras: their universe is exactly the base field/scheme universe u.

Searches: msearch leanfinder query on a projective torus least-weight chart returned eight
LieModule weight-chain hits, none geometric. msearch loogle `Projectivization, IsAffine`
reported unknown IsAffine and no hits. msearch grep `extrem.*weight|least.*weight|minimum.*weight`
in Mathlib/AlgebraicGeometry returned zero. msearch leansearch query on rational character
weights and dual linear charts returned Module.End.eigenspace, Representation.dual,
FDRep characters and CharacterModule duals; these do not provide group-scheme projective
coordinates. msearch loogle `LinearMap.eqLocus` returned the general equalizer API, not the
missing interface. The wrapper's original JSON search outputs are included verbatim in the
new node's mathlib_searches, plus the direct source/DAG search summary. Direct rg in
WeilConjectures and Sheaf found no statement of the item (including its blueprint id);
related existing torus-weight definitions concern G_m coactions, monoid-algebra coactions,
tangent spaces or coherent sheaves, not this projective interface. Blueprint search
`projective torus` returned zero, and the relevant DAG definition-node hits were read to
avoid duplicating their underlying primitives.

Validation uses scompile.py only, with both files separately in dependency order. The
wrapper reported local disk exhaustion and fell back to server confirmation. The server
compiled the explicit data module in 2.4 seconds and the theorem module in 2.7 seconds;
an unused-Fintype warning on Ω was repaired by using Finite Ω and recompiled. Expected
sorry is confined to the main theorem. No live files or direct Git commands were used.

## New nodes

`def-sfb-torus-projective-weight-data` defines the actual coordinate sections of an algebra
vector, its line-representation predicate, the matrix action of a scheme representation,
the induced projective-action predicate, the all-algebra weight-vector equation, separating
cocharacter pairings, and the open D(f) of a dual linear form. Its own module builds all data
from existing constructors. Source: Milne pp.234--235, 274--276 and 374, as in its source field.
LeanSearch, Loogle, Mathlib grep, both project source roots, DAG definitions and blueprint
searches found the primitives above but no combined interface. This is a new definition node,
not a replacement for an existing theorem or a duplicate of G_m/tangent/coherent weight spaces.
The item cites it and the already-landed split-torus definition node in stmt_deps. All other
fields of the existing item are retained verbatim. No dependency modules are repaired.

## Second reading by Q68

The dispatcher forbids additional agents. This section is an explicit fresh self-reading of
the node and final two files; it does not claim an independent reviewer was started. The
maintainer's independent review remains the delivery review required by the brief.

I compared every hypothesis and conclusion with the correspondence table above. I checked
that the projective coordinate action is imposed after every algebra extension, that weights
are actual group-scheme characters and cocharacters, that fixedness is universal after
extensions, and that the finite fixed scheme is genuinely reduced and nonempty. I checked
that the arbitrary coordinate basis makes no weight-basis assumption, the minimum space is
one-dimensional, and uniqueness is stated for the fixed k-point. The dual functional's
existence and all of its defining equations are present, and the chart property holds for
every such normalized form. The set equality uses the full torus orbit and the topology of X.
I repaired the binder name `λ` (a Lean reserved token), changed fixed-point base change to the
recorded `StandardGroupSchemes.map` so the test-point action elaborates without a transport,
and changed Fintype Ω to Finite Ω to remove the linter warning. None changes the mathematics.
All definitions have actual data, every declaration has its owning blueprint docstring, and
only the main theorem is postponed. No further mismatch or missing clause was found.
