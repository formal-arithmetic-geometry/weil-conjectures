## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SteinbergInfinitesimalInducedSimple`
states `AlgebraicGeometry.steinberg_infinitesimal_induced_simple`, with exactly one
postponed theorem and no definitions or proofs. The node's mathematical statement,
proof, proof dependencies and sources are unchanged. Its statement dependencies gain
six already landed definition nodes, whose interfaces supply the inline terminology:
`def-sfb-semisimple-group-scheme`, `def-sfb-borel-subgroup-scheme`,
`def-sfb-reductive-torus-centralizer-terminology`,
`def-sfb-torus-character-tangent-weights`, `def-sfb-rho-section-module-data`, and
`def-sfb-rational-highest-weight-data`. No new nodes or dependency repairs are needed.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]`. |
| Prime characteristic p > 0 | `(p : ℕ) [Fact p.Prime] [CharP F p]`; primality includes positivity. |
| r ≥ 1 and q = p^r | `(r : ℕ) (hr : 1 ≤ r)`; every q is written explicitly as `p ^ r`. |
| F-group scheme S | `S : Grp (Over (Spec (.of F)))`, using the recorded `GrpObj` interface. |
| Semisimple: smooth, affine, connected, finite type, no nontrivial smooth connected solvable normal subgroup | `hS : IsSemisimpleGroupScheme S.X`. Its definition includes precisely these conditions and the scheme-theoretic derived series. Finite type is locally finite type plus quasi-compact. |
| Simply connected, including finite scheme-theoretic central kernels | `hsc`, universally over semisimple `S'`, group homomorphisms `f`, `Surjective f.left`, `IsFinite (GrpObj.ker f).hom`, and the displayed commutation identity over every F-algebra; concludes `IsIso f`. Over a field the finite kernel condition is the finite-dimensional-coordinate-algebra condition. |
| Split maximal torus and containing Borel | `T B`, `iT iB j`, `hT : IsMaximalTorus iT`, `hsplit : ∃ n, Nonempty (T ≅ splitTorus F n)`, `hB : IsBorelGroupScheme iB.hom.hom`, and `hj : j ≫ iB = iT`. Rank zero is allowed. |
| U is the unipotent radical | `U iU` and `hUclosed`, `hUnormal`, `hUsmooth`, `hUconnected`, `hUunipotent`, `hUmax`. The last is the largest-subgroup property, not a choice of some smaller unipotent subgroup. `SolvableGroupStructure.IsUnipotent` uses a faithful closed matrix representation and geometric matrix unipotence. |
| Positive roots are the nonzero character weights in Lie(B) | `[ModObj T.X B.X]` with `hconj` fixing its morphism to conjugation, and finite set `Φplus` with `hΦplus` characterizing membership as `χ ≠ 1 ∧ weightSpace T B χ ≠ ⊥`. The existing weightSpace uses actual dual-number tangent vectors and characters, not their differentials. The commutative group-object instance for G_m makes characters an abelian group; it is intrinsic to G_m, not an additional mathematical restriction. |
| Character rho and twice-rho identity | `ρ : T ⟶ Grp.mk (multiplicative F)` and `hρ : ρ ^ 2 = ∏ α ∈ Φplus, α`. Multiplication is addition in the character lattice. |
| B-character extending rho, trivial on the radical | `ρB`, `hρB : j ≫ ρB = ρ`, `hρU : iU ≫ ρB = 1`. |
| S^(q) = Spec(F[S] tensor_{F,Frob^r} F), with the same construction for T | `Sq Tq`, projections `πS πT`, and `hSq hTq : IsPullback` over `Spec.map (CommRingCat.ofHom (iterateFrobenius F p r))`. For affine S and T these squares are exactly the stated tensor-product spectra, with the right tensor factor carrying the F-algebra structure. |
| Base-changed torus inclusion T^(q) -> S^(q) | `iTq : Tq ⟶ Sq` with `hiTq : iTq.left ≫ πS = πT ≫ iT.hom.hom.left`. The cartesian square for Sq and the fact iTq is over F uniquely determine this map. |
| Relative Frobenius with coordinate formula c tensor a -> a c^q | `Fr : S.X ⟶ Sq` and `hFr : ∀ c, Fr.left.appTop (πS.appTop c) = c ^ (p ^ r)`. Because Fr is over F, its map fixes the right scalar factor a. Thus hFr gives exactly the formula on all tensor generators, and determines the entire map. This is not an unconstrained map or an additional Frobenius hypothesis. |
| S_r is its kernel, L = S_r T is its inverse image of T^(q) | `L iL tL` with `hL : IsPullback tL iL.hom.hom iTq Fr`. The kernel S_r is explanatory notation; the module only uses the inverse image L. This is a scheme-theoretic pullback, not an inverse image of sets of geometric points. |
| P = B intersection L = B_r T | `P iP pB` and `hP : IsPullback pB.hom.hom iP.hom.hom iB.hom.hom iL.hom.hom`. |
| Actual functions f with f(xb) = rhoB(b)^(q-1) f(x), for every commutative test algebra | `Z : Submodule F (RhoSection.Coordinate L.X)` and `hZ : Z = RhoSection.sectionModule L P iP (pB ≫ ρB) (p ^ r - 1)`. The existing sectionModule is the intersection of exactly these linear equations, quantified over all test algebras, including nonreduced ones. Restriction of the B-character to P is explicitly `pB ≫ ρB`. Thus lambda = (q-1)rho is the exact character used, without an independent lambda parameter. The notation widehat Z'_r(lambda) introduces no further object. |
| Finite dimensionality | `FiniteDimensional F Z`, a conclusion. The `IsAffine L.X.left` binder only exposes the affineness already implied by its defining closed pullback inside affine S. It restricts no possible case. |
| Rational module structure | The existential linear map `c : Z →ₗ[F] Z ⊗[F] coordinateAlgebra L`, with `HopfAction.Coassociative` and `HopfAction.Counital`, using the canonical coordinate Hopf algebra. |
| The action is left translation (h f)(x) = f(h^(-1)x) | The displayed identity for every A, h, x, f and every finite presentation `c f = ∑ i, fi i ⊗ₜ[F] ai i`: `∑ i, ev_x(fi i) * ev_h(ai i) = ev_(h⁻¹*x)(f)`. Pullback on the coefficient factor is explicitly `h.left.appTop`, followed by the canonical `Γ(Spec A)=A`. Every tensor has such a presentation, so this pins c itself. It is equivalent to the action formula after scalar extension, by A-linearity. |
| Z nonzero and the only coaction-stable F-subspaces are 0 and Z | `RationalHighestWeight.IsSimple c`, whose definition is `Nontrivial Z ∧ ∀ N, IsStable c N → N = ⊥ ∨ N = ⊤`; `IsStable` means the image lies in the range of the actual tensor inclusion. |

The twist, relative map, L, P and Z are quantified through their defining universal
properties or equalities, as with a specified pullback square. The statements are
invariant under the unique isomorphisms between representatives. All these data
exist for the objects of the node. In particular no arbitrary Frobenius lift,
arbitrary representation, or choice of a subspace replaces a canonical construction.
The group operations on L and P are fixed by their group inclusions into S and L.
The operations on the twists are their unique base changes; the proof does not use
them, so their underlying over-schemes suffice in the signature.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the algebraic-closure dependency's recorded algebraically-closed predicate).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, `IsMonHom` and their group
  structures; `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` and
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme`, `GrpObj.ker`, `GrpObj.kerι`, `IsFinite` terminology.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`;
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`: `TensorProduct`,
  its pure tensors and linear-map tensor operations (used inside the reused coaction predicates).
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: `IsSemisimpleGroupScheme`, with
  its `IsSolvableGroupScheme` / `GroupSchemeDerivedLength` / `IsDerivedGroupScheme` definitions.
- `Sheaf.AlgebraicGeometry.GroupScheme.Borel`: `IsBorelGroupScheme`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsMaximalTorus`; its imported
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `MultiplicativeType.splitTorus`,
  `IsTorus`; `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsUnipotent`.
- `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`: `TorusCharacterTangent.weightSpace`.
- `Sheaf.AlgebraicGeometry.RhoSectionModuleData`: `RhoSection.Coordinate`, `evaluate`,
  `characterValue`, `sectionModule`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`: `coordinateAlgebra`,
  `coordinateHopf`, `IsStable`, `IsSimple`; via its imported
  `Sheaf.AlgebraicGeometry.HopfCoactionLinearization` and
  `Sheaf.RingTheory.HopfActionModuleData`: `HopfAction.Coassociative`, `Counital`.
- Proof-only imports, already stated: `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`
  (`reductive_borel_pair_structure`, `semisimpleGroupScheme_isReductive`) and
  `.ReductiveRootSubgroupParametrizations` (`TorusCharacterTangent.reductive_root_subgroup_parametrizations`).
  The other three proof dependencies have no Lean records in the read DAG, so there
  are no imports to add for them; the full four-step node proof is preserved in the docstring.

Edge cases checked before writing and again against the signature: trivial S and
rank-zero torus (empty Φplus, rho=1, L=P=1, Z=F); p=2 with any r≥1; r=1; no case
r=0 is asserted; empty finite tensor presentations (the coaction formula reads 0=0
for f=0); zero subspace allowed as a candidate stable N; nonreduced test algebras;
all roots are tested as characters rather than differential weights. No root-system
nonemptiness, characteristic restriction, dimension formula, or nonzero-vector
hypothesis is added. The theorem itself concludes nontriviality.

Searches made for the item:

- `msearch.py ... leanfinder "The infinitesimal induced Steinberg module of a semisimple simply connected algebraic group is simple"`:
  eight hits: Geck/Weyl root representations, Lie irreducibility and FDRep lemmas.
  They concern Lie algebras or abstract groups; none states the group-scheme result.
- `msearch.py ... loogle '"Representation", "IsIrreducible"'`:
  ten hits centered on `Representation.IsIrreducible`, an abstract-monoid representation
  predicate. Its type does not encode rational Frobenius-kernel comodules.
- `msearch.py ... grep 'Steinberg|baby.?Verma|Frobenius.*kernel|Coaction'`: zero hits.
- `msearch.py ... leansearch "The infinitesimal induced Steinberg module for a Frobenius kernel times a torus is simple"`:
  eight hits on Weyl-group root representations, `IsSimpleModule`, and simple module objects;
  no matching infinitesimal induction theorem.
- `rg` in `lean/WeilConjectures` for `Steinberg|steinberg|baby.?Verma|InfinitesimalInduced`
  and the exact node id: only unrelated Lang--Steinberg material, no exact id or theorem.
  `dag/lean_names_upstream.json` likewise only has the unrelated Lang--Steinberg id.
- `rg` in `lean/Sheaf/AlgebraicGeometry/GroupScheme` and the representation/group-scheme
  source directories: located the six existing definition interfaces used here, and
  the highest-weight and homogeneous-line-bundle results, but no infinitesimal
  Steinberg simplicity declaration. Read their actual signatures and definitions,
  not only the search names. No existing notion has been redefined.

Source checked: the latest blueprint direct-images proof (3), and
[Kaneda's primary PDF](https://msp.org/pjm/1994/163-2/pjm-v163-n2-p07-s.pdf),
Section 2.5, printed pp.322--323. Equation (9) corroborates Steinberg simplicity.
Its Borel/sign conventions differ from this node's positive-in-Lie(B) convention,
so it is corroboration, not a verbatim identification of the restriction module.
Jantzen's local book is WANTED in the node; the module does not claim to have read it.
The natural-language proof is the four-step agent assembly already accepted in the DAG.
No statement fault or STATEMENT-DISPUTED flag was found.

Validation: scompile.py checked both sandbox and destination module cleanly (9.1s
and 5.7s respectively) before the final direct Mathlib import additions. No theorem
other than the named node statement is postponed. The final module, including direct Mathlib imports, passed `deliver2.py --no-push`:
`OK (dry run): commit af9c17fb2c2 passes the preflight and compiles; nothing pushed`.
The dry run staged exactly the one module, the item node, and this report.

## Second reading by N0

Author's separate second pass, not an independent-agent review (the task explicitly
forbids starting agents; the maintainer supplies independent review). Reopened the
node and final Lean file. Matched every clause using the table above; verified the
orientations of all four pullback squares, the right scalar factor of the Frobenius
twist, and the left-translation inverse sign. Checked that `hFr` together with the
over-morphism condition specifies c tensor a -> a c^q on all generators; it does not
allow a different lift. Checked that `hZ` uses the restricted B-character with exponent
q-1, and that `IsSimple c` includes nonzero and every stable linear subspace. The
first compile exposed differing implementation choices for the two canonical
coordinate-algebra scalar instances. The final formula uses arbitrary finite tensor
presentations and actual ring pullbacks, so it expresses the same evaluation identity
without requiring these algebra instances to be definitionally equal. The revised
statement compiled cleanly. No change to the mathematical node statement was needed.
