## Worker report

States `AlgebraicGeometry.SplitWeylCharacter.split_charzero_weyl_character_identity`
in `Sheaf.AlgebraicGeometry.GroupScheme.SplitCharzeroWeylCharacterIdentity`.
The only postponed proof is this named theorem. Its docstring follows all eight
steps of the DAG proof. Two real helper definitions belong to this statement:
`weightSpace`, an intersection of kernels of the character eigenvalue equations,
and `alternant`, the finite sum in the actual additive group algebra.

Hypothesis-by-hypothesis and clause-by-clause reading:

- The base is literally `ℚ`; `G T : Grp (Over (Spec (.of ℚ)))` are group schemes,
  using the recorded `CategoryTheory.GrpObj` interface through bundled `Grp`.
- Affineness is `[IsAffine G.X.left]`, smoothness is `hsm`, and connectedness is
  `hconn`. `hss` applies the existing `IsSemisimpleGroupScheme` to the actual
  algebraic-closure base change. Its quantified smooth connected solvable normal
  subgroup condition is exactly the geometric semisimplicity specified in the node.
  The algebraic-closure predicate also records finite type, implicit in the source's
  term algebraic group; this does not restrict an algebraic group over Q.
- `hsc` quantifies over smooth connected affine geometrically semisimple groups H.
  Surjectivity of f and finiteness of its scheme kernel are explicit. Centrality
  tests kernel points commuting with all H-points over every Q-algebra, including
  nonreduced algebras. The conclusion is `IsIso f`. Thus this is precisely the
  stated central-isogeny definition of simple connectedness over Q.
- `i : T ⟶ G` is the inclusion; `hsplit` is an actual isomorphism with a finite
  product of G_m. `hmax` tests the existing maximal-torus predicate on the
  algebraic-closure base change; its closed inclusion descends, so no extra
  abstract torus unrelated to the given inclusion is supplied.
- X and Y are the actual additive character/cocharacter Hom groups from
  `RankOneRoots.Character` and `RankOneRoots.Cocharacter`. Their integer modules
  are finite; the perfect pairing in `P : RootDatum ...` makes them torsion free,
  hence free over Z. `hpair` identifies that pairing with actual character/cocharacter
  composition and integer powers of the identity on G_m.
- `a` is pinned by `ha` to the conjugation morphism. `hweights` says exactly that
  Φ is the set of nonzero character weights of that tangent action. `hroot` fixes
  each root to its actual character, so there is no arbitrary root embedding.
- RootDatum includes normalization `<α,α∨> = 2`, a perfect pairing, and simultaneous
  root/coroot reflection permutations. `P.IsReduced` excludes nontrivial proportional
  roots. `hspan` is rational spanning; `Fintype P.weylGroup` expresses the specified
  finite reflection group. The coroots are thereby determined by the finite root
  reflection action and its normalization, agreeing with the opposite-root-subgroup
  normalization; no arbitrary differential or coroot scaling is allowed.
- `b : P.Base` gives independent simple roots, integer positive/negative simple
  coordinates, and its positive predicate `b.IsPos`. `hρ` defines precisely half
  the sum of positive roots in `ℚ ⊗[ℤ] X`.
- `n : ℕ` and `r : GeneralLinearGroup.RationalHom G.X (Fin n)` with `IsMonHom r`
  write any finite-dimensional algebraic-group representation in a basis. This
  uses the recorded representation notion, rather than replacing it by an abstract
  Lie representation. `hnonzero` and `hsimple` assert nonzero and that every subspace
  invariant after all algebra extensions is zero or top; the latter uses the
  existing `IsInvariantRationalSubspace` verbatim.
- `lam : X` and `hdom` give the nonnegative simple-coroot pairings. `hv` supplies
  a nonzero weight-lam vector annihilated by every positive-root tangent subspace
  in `r.differential`, the actual dual-number differential into matrices. Matrix
  multiplication on the chosen coordinate space is `Matrix.toLin'`.
- The helper weight spaces are simultaneous eigenspaces under T(Q). For a split
  torus over the infinite field Q these coincide with the all-algebra character
  weight spaces: in split coordinates a Laurent polynomial vanishing on every
  tuple of nonzero rational numbers is zero. Thus this is not a pointwise substitute
  over an inadequate finite field.
- `DirectSum.IsInternal` gives the internal sum of ALL weight spaces, and the
  following `.Finite` clause gives precisely finite nonzero support.
- `∃ ρ₀, 1 ⊗ ρ₀ = ρ` expresses `ρ ∈ X`, without assuming integrality in advance.
- `∃ q : AddMonoidAlgebra ℚ X` with EVERY `q.coeff χ = finrank ℚ V_χ` determines
  exactly the finite formal character. This existential is uniquely characterized
  coefficientwise, not an arbitrary object chosen from a mere existence claim.
- `alternant P ν` sums over the canonical RootDatum Weyl group, with exponent
  `w • ν` and determinant of the canonical weight map after `baseChange ℚ`.
  Finally `q * alternant P ρ₀ = alternant P (lam + ρ₀)` is the required polynomial
  identity. `AddMonoidAlgebra.single_mul_single` gives `e^ξ e^η = e^(ξ+η)`;
  there is no localization, quotient, or denominator cancellation.

Dependency declarations used in the statement:

- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.Grp`, `GrpObj` (recorded
  def-sc-group-scheme).
- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation:
  `GeneralLinearGroup.RationalHom.representation`; its public Lie import provides
  `RationalHom`, `RationalHom.points`, and `RationalHom.differential`. Read the
  recorded ClosedSubgroup.Lie standardRepresentation and these full definitions.
  The general RationalHom interface is the applicable declaration in the same
  recorded algebraic-representation notion; standardRepresentation specializes
  to closed matrix subgroups and is not incorrectly imposed here.
- Mathlib.Algebra.Lie.Basic and the upstream group-scheme Lie API: `LieRing`,
  `LieAlgebra`, `LieHom`/`LieModule` and the actual `GrpObj.Lie` tangent algebra,
  used through the differential and tangent weight spaces.
- Sheaf.AlgebraicGeometry.GroupScheme.Semisimple: `IsSemisimpleGroupScheme` and its
  commutator-derived-series solvability predicate.
- Sheaf.AlgebraicGeometry.ToriMultiplicativeType: `MultiplicativeType.baseChange`,
  `splitTorus`; Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  `ReductiveTorusCentralizer.IsMaximalTorus`.
- Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces: `Character`, `Cocharacter`.
- Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights: `TorusCharacterTangent.weightSpace`.
- Sheaf.AlgebraicGeometry.RhoSectionModuleData: `RhoSection.characterValue`.
- Sheaf.AlgebraicGeometry.LinearlyReductiveGroupScheme: `IsInvariantRationalSubspace`.
- Mathlib root-system Base, Reduced, WeylGroup: `RootDatum`, `RootPairing.Base`,
  `IsReduced`, `weylGroup`, `Equiv.weightEquiv`; determinant and tensor APIs give
  `LinearMap.det` and `LinearMap.baseChange`. All variables/universes are explicit.

Added the seven already landed definition nodes corresponding to the Sheaf
terminology just listed to stmt_deps, as expressly allowed by brief §5. No new
nodes, dependency repairs, or statement correction. The two helper definitions are
listed in lean.declarations, carry their source/blueprint docstrings, and have real data.

Proof-plan imports include every currently recorded module for the proof dependencies:
ReductiveBorelPairStructure, RhoSectionModules, RhoRegularWeylOrbit,
CharZeroDifferentiationHom, SimpleModuleDualHighestWeight,
HomogeneousLineBundleSections, CharacteristicZeroCompleteReducibility, and upstream
Descent. AlgebraicClosure is exposed through the statement imports. Other proof
dependencies currently have no Lean record or usable declared module to import;
they remain named in the proof docstring for stage 3. No proof dependency is changed.

Sources read: Milne PDF printed pp.480--481 and appended Chapter 22 erratum for
p.480 (explicitly restricts simple V in 22.52 to characteristic zero). Read the
current latest blueprint direct-images proof (3), whose inherited supporting chain
this node serves; this delivery changes no unit statement.

Edge cases checked before/following writing:

- Empty roots and rank-zero torus: no Nonempty index assumption. P.Base and the
  full Weyl sum accept the empty root system. Spanning gives X rationally zero;
  its torsion-free lattice is zero. The trivial-group simple module has n=1,
  q=1 and rho=lam=0, so the identity is 1=1; determinant in rank zero is one.
- Reducible systems: no irreducibility of the root system is imposed; all positive
  roots and the full product Weyl group are used.
- Zero representation is correctly excluded by hnonzero/hv, as in the node.
- For SL2 and highest weight m, rho is the fundamental weight and
  (e^m+e^(m-2)+...+e^(-m))(e-e^(-1)) = e^(m+1)-e^(-m-1).
  For m=0 this gives the trivial representation, with no strict-dominance assumption.
- Scheme kernels and invariance include nonreduced scalar extensions. Characteristic
  zero is literal Q, not an omitted assumption. DecidableEq is computational data
  available classically and not a mathematical restriction.

Searches for duplicate statements/helpers:

- msearch leanfinder: "Weyl character formula for simple representation of split
  semisimple simply connected algebraic group in characteristic zero" returned 8
  hits, chiefly FDRep finite-group character identities and Lie weight/trace lemmas;
  none states this group-scheme Weyl character identity.
- msearch loogle: "RootPairing.weylGroup, RootPairing.Base, AddMonoidAlgebra": 0 hits.
- msearch grep: "weyl.*character|Weyl.*character|alternant": 0 Mathlib hits.
- msearch leansearch: "weight space of algebraic group representation for a character
  of a split torus": 8 hits, all LieModule weight-space/generalized-weight APIs;
  none is the actual algebraic-group character eigenspace.
- rg on lean/WeilConjectures and lean/Sheaf for Weyl character/formula/alternant and
  the proposed names: no existing identity/alternant declaration. Existing G_m and
  relative split-coordinate coaction weightSpace definitions have different input
  types; the helper here names the character eigenspaces of the supplied RationalHom.
- rg on the upstream tree for the item id: no occurrence. DAG definition-node search
  found and reused the seven existing terminology nodes rather than private copies.
- tools/blueprint_refs.py search Weyl character: 0 blueprint nodes.

No STATEMENT-DISPUTED issue or node fault found. The original natural-language
statement and proof remain unchanged.

## Second reading by Q157

Written by the maintainer's independent second reader (cc review service,
2026-10-24) in place of the worker's own self-check, which stated that it was
not an independent reading (delivery-errors H11). The Lean module and the node
record are unchanged.

Node statement, item by item, against the delivered Lean
(`AlgebraicGeometry.SplitWeylCharacter.split_charzero_weyl_character_identity`):

| Node | Lean | Verdict |
|---|---|---|
| G a group scheme over Q, smooth, connected, affine | `G : Grp (Over (Spec (.of ℚ)))`, `[IsAffine G.X.left]`, `hsm`, `hconn` | exact |
| semisimple: after algebraic closure no nontrivial smooth connected solvable normal subgroup | `hss : IsSemisimpleGroupScheme (baseChange (K := AlgebraicClosure ℚ)).obj G).X` (def-sfb-semisimple-group-scheme: smooth, connected, affine, finite type, every smooth connected solvable normal closed subgroup terminal) | exact |
| simply connected: every surjective hom from a connected semisimple group with finite central kernel is an iso | `hsc`: all H smooth, connected, affine, geometrically semisimple; f : H ⟶ G in Grp, `Surjective f.hom.hom.left`, `IsFinite (ker f).hom`, kernel A-points commute with all H A-points for every Q-algebra A; conclusion `IsIso f` | exact (same encoding as landed lem-sfb-rho-section-modules) |
| T ⊆ G split, ≅ product of G_m, maximal after closure | `i : T ⟶ G`, `hsplit : ∃ r, Nonempty (T ≅ splitTorus ℚ r)`, `hmax : IsMaximalTorus (baseChange.map i)` (closed subgroup + torus + maximal); the closed immersion descends from the closure | exact |
| X = Hom(T,G_m), Y = Hom(G_m,T), pairing χ∘η = t^⟨χ,η⟩ | `Additive (RankOneRoots.Character T)`, `Additive (RankOneRoots.Cocharacter T)` (morphisms in Grp); `hpair : ν ≫ χ = 𝟙 ^ P.toLinearMap χ ν`; finiteness instances are true Props for a split torus | exact |
| roots = nonzero T-weights of the adjoint action on Lie G | `a` pinned by `ha` to `(i ⊗ 𝟙) ≫ GrpObj.conj` (Mathlib conj = x y x⁻¹, a left action); `hweights : χ ∈ Φ ↔ χ ≠ 0 ∧ TorusCharacterTangent.weightSpace a χ ≠ ⊥`; `hroot : P.root α = α` | exact |
| coroots, ⟨α,α∨⟩ = 2, reflections permute pairs, reduced, W finite, spanning | `P : RootDatum Φ X Y`, `[P.IsReduced]`, `[Fintype P.weylGroup]`, `hspan` over ℚ. Coroots are not separately pinned, but with roots fixed, the pairing fixed by `hpair`, and Φ spanning X⊗Q, the coroot of each root is unique (Bourbaki VI.1.1 Lemma 1), hence equals the opposite-root-subgroup coroot | exact |
| base Δ, positive roots | `b : P.Base`, `b.support`, `b.IsPos`. Mathlib's Base also requires the coroot conditions; for a reduced root datum Δ∨ is automatically a base of Φ∨, so no extra assumption | exact |
| ρ = ½ Σ_{Φ+} α in X⊗Q | `ρ`, `hρ` in `ℚ ⊗[ℤ] X` | exact |
| V nonzero finite-dimensional simple algebraic representation (invariance after every scalar extension) | `r : RationalHom G.X (Fin n)`, `[IsMonHom r]`, `hnonzero`, `hsimple` via `IsInvariantRationalSubspace` (all Q-algebras) | exact |
| λ dominant | `hdom : ∀ α ∈ b.support, 0 ≤ ⟨lam, α∨⟩` | exact |
| v ≠ 0 of weight λ killed by positive root Lie spaces | `hv`: `v ∈ weightSpace i r lam`, `Matrix.toLin' (r.differential x) v = 0` for x in each positive root space | exact |
| V_χ weight spaces | helper `weightSpace`: common eigenspace of r on T(Q). Since T is split over the infinite field Q, T(Q) is schematically dense in the reduced torus, so this equals the scheme-theoretic weight space | exact |
| V = ⊕ V_χ, finitely many nonzero | `DirectSum.IsInternal`, `.Finite` | exact |
| ρ ∈ X | `∃ ρ₀, 1 ⊗ ρ₀ = ρ` (X free, so ρ₀ is unique) | exact |
| q A(ρ) = A(λ+ρ) in Q[X], q = Σ dim V_χ e^χ, A(ν) = Σ det(w) e^{wν} | `q` pinned by all coefficients; helper `alternant`: Σ over `P.weylGroup` of `single (w • ν) (det (weightEquiv w).baseChange ℚ)`; Mathlib `w • ν` on M is `weightHom`, the same map whose determinant is taken | exact |

Edge cases: empty root system (empty index type, Base with empty support, Weyl
group trivial, hspan forces X⊗Q = 0, n = 1, identity 1 = 1); reducible systems
(full Weyl group, no irreducibility); rank-zero torus (splitTorus ℚ 0 = unit);
characteristic is literally 0 (base ℚ); universes all 0, no unbound variables.

Records: node statement and proof unchanged; only `lean` and seven landed
definition stmt_deps were added (rank-one-root-interfaces, torus-character-tangent-weights,
tori, semisimple, reductive-torus-centralizer, rho-section-module-data,
linearly-reductive), each used in the statement. `lean.statement` is verbatim
the file signature. Docstrings carry Milne 22.52/22.53 and the blueprint id;
the theorem docstring follows all eight proof steps; the only proof is `sorry`.
Searches: no Mathlib or project Weyl character/alternant declaration; the
representation-weight-space lemma has no Lean record yet, so the local
`weightSpace` helper is not a duplicate.
