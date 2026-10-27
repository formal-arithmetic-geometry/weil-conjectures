## Worker report

The module `Sheaf.AlgebraicGeometry.RhoTensorSquareEventualDetection` states
`AlgebraicGeometry.rho_tensor_square_eventual_detection`, with proof `sorry`.
It also defines the real-data evaluation helper `AlgebraicGeometry.RhoSection.scalarAction`:
apply the canonical matrix action to the scalar-extended basis obtained from the supplied
linear equivalence. No action, section module, or map is chosen from an existence axiom.
The item node changes only in `lean`; there are no new nodes or dependency repairs.

Source read: Alper, *Adequate moduli spaces*, Section 9.7 immediately before and at
Lemma 9.7.2(2), https://arxiv.org/html/1005.2398v3#S9.SS7. Its eventual quantifier is
retained. Its printed omission of nonvanishing is already repaired in the assigned node;
this delivery retains the node's `v ≠ 0`. The six-step double-flag proof supplied by the
node is reproduced in the theorem docstring, including the common denominator argument
which gives every sufficiently large integer, with no congruence restriction.

Hypothesis and clause correspondence:

- Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- The F-group scheme: `S : Grp (Over (Spec (.of F)))`, whose bundled group object
  supplies the given multiplication, inverse and identity over F.
- Semisimple: `hS : IsSemisimpleGroupScheme S.X`. This recorded predicate means
  smooth, connected, affine, finite type (locally finite type plus quasi-compact),
  with every smooth connected solvable normal closed subgroup trivial.
- Simply connected: `hsc` is copied exactly from the rho-section dependency's interface:
  every semisimple `S'`, surjective group homomorphism `f`, finite kernel, and kernel
  central on all A-valued points implies `IsIso f`. No geometric-point replacement.
- Split maximal torus and containing Borel: `T B`, inclusions `i j k`, and
  `hTB : IsRhoBorelPair i j k`. This is the dependency's definition: maximal torus,
  isomorphism to a split torus, Borel, and `k ≫ j = i`.
- The canonical character data are unpacked in the identical form returned by
  `exists_rho_section_modules`: `aB` and `hconj` pin the T-action on B to conjugation;
  `Φ`, `hΦ`, and `hpos` say the positive roots occur exactly once and are exactly the
  nontrivial characters with nonzero tangent weight space in Lie(B); `ρ` and `hρ`
  say its square is the product of those characters. This is the integral-character
  half-sum identity, without division in F. `ρB` and `hext` extend it along k;
  `hrad` says it kills the unipotent radical, expressed as all closed normal connected
  unipotent subgroups. `SolvableGroupStructure.IsUnipotent` includes smoothness.
  These binders identify the character already fixed by the node; they are the same
  canonical data, rather than an arbitrary replacement character or an added restriction.
- An arbitrary finite-dimensional rational module: `{V : Type v} [AddCommGroup V]
  [Module F V]`, a finite type `I` with `Fintype`/`DecidableEq`, and
  `eV : (I → F) ≃ₗ[F] V`, together with `rV : GeneralLinearGroup.RationalHom S.X I`
  and `[IsMonHom rV]`. Choosing a finite basis is an equivalent presentation of
  every finite-dimensional V, including V in an independent larger universe v;
  it does not fix a dimension or restrict V to a coordinate-space carrier.
  RationalHom is an actual scheme morphism to GL, so its matrix coefficients are
  regular and its homomorphism law gives the coassociativity and counit identities.
- Nonzero invariant vector: `(v : V) (hv : v ≠ 0)` and `hinv` fixes `1 tensor v`
  under the canonical scalar-extended action for every commutative F-algebra A and
  every s in S(A). This is precisely the node's expressly permitted alternative to
  the coaction identity `c(v)=v tensor 1`; it is not just invariance under S(F).
- Positive threshold: `∃ M : ℕ, 1 ≤ M`. Positive integers are represented by naturals
  with that lower bound; no negative integer could occur under the source's bound.
- Eventual quantifier: `∀ m : ℕ, M ≤ m → ...`, after V and v are fixed. Thus M may
  depend on both, and no subsequence replaces the eventual conclusion.
- Actual target spaces: both tensor factors are exactly
  `RhoSection.sectionModule S B j ρB m`, the dependency's intersection of kernels
  inside its actual coordinate algebra, imposing positive-exponent right
  semi-invariance over every algebra. There is no abstract induced-module substitute.
- Their canonical rational action is encoded by the existential finite basis `eW`
  and rational GL map `rW` satisfying the exact coefficient formula of the recorded
  `HasRationalLeftTranslation`. This unpacks that existing predicate's witnesses
  because the conclusion must refer to the operators. It introduces no new notion.
  The formula is checked for every A, s, g and basis column q; therefore it pins the
  action to `(s f)(g)=f(s inverse g)` on all functions and all scalar extensions.
  Existence of these witnesses is already the rho-section theorem's conclusion.
- `a : V →ₗ[F] W_m ⊗[F] W_m` is F-linear and `a v ≠ 0` is the requested detection.
- Equivariance: the final equality, for every A, s and x in A tensor V, intertwines
  `a.baseChange A` with the domain action and the tensor of the two canonical W_m
  actions. `TensorProduct.AlgebraTensorModule.distribBaseChange` is the canonical
  comparison sending b tensor (w tensor z) to (b tensor w) tensor_A (1 tensor z).
  Hence the displayed tensor of operators is exactly the diagonal S-action. Testing
  every A includes the universal point and is equivalent to the coaction identity.

Dependencies inspected and reused:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: its match explicitly supplies `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`; no closure of F is substituted for F.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` / `Grp`, with the Over(Spec F)
  specialization explained in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `lem-sfb-rho-section-modules`: public import
  `Sheaf.AlgebraicGeometry.RhoSectionModules`, reusing `IsRhoBorelPair`, the complete
  signature of `exists_rho_section_modules`, and its public dependencies
  `RhoSection.sectionModule`, `RhoSection.evaluate`, `HasRationalLeftTranslation`,
  `IsSemisimpleGroupScheme`, and `TorusCharacterTangent.weightSpace`.
- Existing `GeneralLinearGroup.RationalHom` and `homMulEquiv` from upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie` and
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear` are reused through
  the dependency. Scalar extension uses Mathlib `Module.Basis.baseChange`,
  `Matrix.GeneralLinearGroup.toLin'`, and the actual tensor/baseChange maps.

The already stated proof dependencies are imported privately:
`WeilConjectures.AlgebraicGeometry.InvertSCOhomology`
(`Scheme.Modules.invertS_cohomology`),
`Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`
(`exists_homogeneousLineBundle_sections`),
`WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorBijective`
(`Scheme.Modules.externalGlobalSectionsTensor_bijective`), and
`Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`
(`reductive_borel_pair_structure`). The proof dependency
`lem-sfb-double-flag-invariant-boundary` has no recorded declaration yet, so its
future proof import is omitted; its proof step remains in the docstring.

Edge cases checked: V=0 has no v satisfying hv, as required. An empty finite basis
is permitted by the type, not excluded by a positive-dimension assumption. For the
trivial S and rank-zero torus the root list is empty, rho and its extension are
trivial, W_m=F and a functional nonzero on v gives the conclusion for every m>=1.
No characteristic assumption occurs, including characteristic two: rho is an
integral character with a squared-character identity, not division by two in F.
All test algebras include nonreduced and zero algebras. M>=1 excludes m=0 exactly
as in the node. The actual vector space V is universe-polymorphic; finite basis
indices can always be lifted to Type u, and test algebras use the same universe
as F and S, so include the coordinate algebra and universal points.

Searches (all searches were read before selecting the interface):

- `msearch.py ... leansearch`: "eventual nonzero invariant vector detection by tensor
  squares of highest weight rho section modules". Eight hits about Lie weights and
  abstract-group invariants; no match to this group-scheme theorem.
- `msearch.py ... leanfinder`: "A nonzero invariant vector of a finite dimensional
  rational algebraic group module is detected by an equivariant linear map to all
  sufficiently large rho section module tensor squares". Eight unrelated Hilbert 90,
  sl2, finite-group norm/averaging/Tannaka and Lie-rank hits; no match.
- `msearch.py ... loogle`: "RhoSection.sectionModule, Representation.tensor,
  Coalgebra.Comodule". No hits; RhoSection is project-owned, not a Mathlib name.
- `msearch.py ... grep`: "rho.*tensor|tensor.*rho|eventual.*detect" in
  `RepresentationTheory`. Five tensor/character/resolution hits, no eventual theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `rho_tensor|tensor_square_eventual|eventual.*detection|RhoSection`, and exact-name
  searches also in `dag/lean_names_upstream.json`: no existing theorem or proposed
  declaration name. RhoSectionModuleData/Modules are the existing spaces and reused.
  Exact item-id grep in `lean/WeilConjectures` returned no attachment.
- Searches for rational actions/coactions found and read the existing
  `RationalRepresentationComoduleDictionary`: its finite_dictionary,
  intertwines_iff and tensor_coaction confirm the finite-basis/all-algebra encoding.
  Also inspected `CentralTorusWeightBlocks.pointAction`: it acts only on its fixed
  coordinate space, whereas the helper here transports to arbitrary V (and the
  actual W_m subtype) through the supplied basis. The underlying GL operator is
  Mathlib's existing `toLin'`, not a second representation definition.

Validation: scompile.py compiled the final complete module in sandbox and library
mode, separately, in 5.0 and 5.4 seconds. No error or non-sorry warning.
No statement correction or STATEMENT-DISPUTED issue was found.

## Second reading by Q61

Self-rereading, not an independent agent review: the dispatcher prohibits spawning
other workers and the maintainer supplies the independent review. Reopened the
node and the final module and checked the above correspondence clause by clause.
In particular the tensor factors are actual semi-invariants, the left-translation
column convention has s inverse g and positive right exponent, centrality and
invariance quantify over all algebras, the half-sum is an integral character, the
threshold is positive and every larger m is covered, and the equivariance square
uses two copies of the same pinned section action. The real helper transports the
standard basis and introduces no proof. No mismatch found or source statement
changed. The earlier scratch attempt to identify two coefficient presentations by
definitional equality was discarded before this formulation; no unused probe or
additional module remains in the delivery.
