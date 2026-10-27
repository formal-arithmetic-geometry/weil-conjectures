## Worker report

The module `Sheaf.RepresentationTheory.JointContinuousCoordinateEquivalence` states
`ContinuousCohomology.exists_jointContinuousCoordinateEquivalence`. Its only theorem
has `sorry` as its proof. It states exactly the graded equivalence, with no differential,
complex, function-space topology, or derived-category assumptions. Only the node's
`lean` field changes. There are no new nodes, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| E is a field | `(E : Type u) [Field E]`, the Mathlib declaration recorded by `def-weil-field` |
| Continuous addition, multiplication and inversion away from zero on E | `[TopologicalSpace E] [IsTopologicalDivisionRing E]`; its `ContinuousInv₀` imposes continuity only at nonzero points |
| J is a group with continuous multiplication and inversion | `(J : Type v) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]` |
| V is an E-vector space with continuous addition and scalar multiplication | `(V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul E V]` |
| E-linear J-action | `ρ : J →* V ≃ₗ[E] V`, encoding the identity/composition laws and linear automorphisms |
| Joint continuity of the action | `hρ : Continuous (fun p : J × V ↦ ρ p.1 p.2)` |
| Every n ≥ 0 | `(n : ℕ)` |
| Finite powers with the product topology | `Fin (n + 1) → J` and `Fin n → J`, with Mathlib's standard Pi topology |
| Homogeneous space consists exactly of the jointly continuous equivariant functions | `∃ B : Submodule E ((Fin (n + 1) → J) → V)` followed by the exact membership equivalence `F ∈ B ↔ Continuous F ∧ ∀ a x, F (fun i ↦ a * x i) = ρ a (F x)` |
| Inhomogeneous space consists exactly of continuous functions | `continuousSubmodule (Fin n → J) E V`, whose carrier is `{f | Continuous f}` |
| Both are vector subspaces with pointwise operations | `Submodule E` of the respective all-function modules; neither changes the ambient operations |
| P sends g to (1,g₁,g₁g₂,...) | Existing `Fin.partialProd g`, whose ordered list-product definition has precisely these coordinates |
| r sends x to its successive ratios | `fun i ↦ (x i.castSucc)⁻¹ * x i.succ` |
| Phi is F composed with P | `(e F).val g = F.val (Fin.partialProd g)` |
| Psi is x₀ acting on f(r(x)) | `(e.symm f).val x = ρ (x 0) (f.val (fun i ↦ (x i.castSucc)⁻¹ * x i.succ))` |
| Phi and Psi are mutually inverse E-linear maps | `e : B ≃ₗ[E] continuousSubmodule (Fin n → J) E V`; `e` and `e.symm` carry linearity and both inverse identities |
| Phi F is continuous; Psi f is jointly continuous and equivariant | The image types, together with the exact carrier of B and the definition of continuousSubmodule |
| Degree zero C⁰ = V | `Fin 0 → J` is a singleton. Evaluating at its unique empty tuple identifies its continuous-function submodule with V, with inverse the constant function. Thus this is the empty-tuple convention explicitly permitted by the statement |
| Degree zero forward formula | `Fin.partialProd` on the empty tuple is the singleton tuple 1, giving F(1) |
| Degree zero inverse formula | There are no ratios; the displayed inverse is x₀ acting on v |
| No compactness, Hausdorffness or discreteness | No such instance or hypothesis is present |
| Graded vector spaces only | A degree parameter and linear equivalence; no complexes or derived objects |

The standard topological additive-group classes introduce no extra mathematical condition:
on E negation is multiplication by -1, and on V it is scalar multiplication by -1.
Those maps are continuous under the node's stated assumptions. Conversely the chosen
classes include continuous addition. Thus their use expresses the same hypotheses.
The three carrier universes `u v w` are independent and all binders are explicit;
`set_option autoImplicit false` enforces that requirement.

The homogeneous subspace is an object whose existence this theorem asserts, uniquely
specified by its carrier. It is not a separate unstated helper notion or a definition
chosen from an existence theorem. No definition is introduced, hollow or otherwise.
The inhomogeneous space and cumulative products reuse existing Mathlib definitions.
The module docstring and theorem docstring cite the node's source and all eight proof
steps, including both noncommutative cancellation computations and the empty tuple.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, class at line 180,
  imported through the public field/topological algebra imports.
- Proof dependency `lem-weil-pbc-initial-topology-continuity`:
  `continuous_iInf_rng` and `continuous_induced_rng`, `Mathlib.Topology.Order`;
  imported as a plain proof import. The former's full type is the equivalence
  between continuity into an infimum topology and continuity into each topology;
  the latter rewrites continuity into an induced topology as continuity of composition.
- `continuousSubmodule`, `Mathlib.Topology.ContinuousMap.Algebra`, line 513:
  the existing submodule of continuous functions with pointwise operations.
- `Fin.partialProd`, `Mathlib.Algebra.BigOperators.Fin`, line 483:
  ordered products of prefixes, suitable for nonabelian groups.

Edge cases checked before writing:

- n=0: the input inhomogeneous tuple is empty, its prefix-product tuple is (1),
  and the inverse is the orbit function. There is no positive-degree restriction.
- n=1: P(g)=(1,g) and r(x₀,x₁)=x₀⁻¹x₁.
- n=2 for nonabelian J: (x₀⁻¹x₁)(x₁⁻¹x₂)=x₀⁻¹x₂ in the written order.
- Trivial group and zero coefficient space: both formulas remain defined and inverse.
- Indiscrete/non-Hausdorff topologies: the continuity arguments require no separation.
- Positive characteristic and arbitrary carrier sizes: neither characteristic nor a
  universe equality is assumed. No local compactness or function-space exponential law.

Searches, all made with the prescribed `msearch.py NY <item>` wrapper:

- LeanFinder: "Jointly continuous equivariant homogeneous group cochains are linearly
  equivalent to continuous inhomogeneous cochains via cumulative products and successive
  ratios". Eight hits: continuous-cohomology complexes and ordinary `cochainsIso` maps;
  no exact graded jointly continuous statement.
- Loogle: `ContinuousMap, LinearEquiv`. Ten hits concern measures, bounded continuous
  functions or unitizations, with additional structures unrelated to this statement.
- Mathlib grep: `partialProd|inhomogeneousCochainsIso|cochainsIso`, subdirectory
  `RepresentationTheory/Homological`. Twenty-five hits include ordinary all-function
  cochain isomorphisms and ordered prefix-product ingredients. Reused `Fin.partialProd`.
- LeanSearch: "Continuous equivariant functions on finite powers of a topological group
  form a vector space linearly equivalent to continuous inhomogeneous cochains".
  Eight hits on continuous representations, unrelated invariant spaces and ordinary
  all-function low-degree cochains, with no exact statement.
- Local `rg` over `lean/WeilConjectures` and `lean/Sheaf` for joint continuity,
  homogeneous/inhomogeneous cochains and prefix products; item-id grep upstream;
  declaration-name grep in Mathlib, both project trees and `dag/lean_names_upstream.json`.
  No item declaration or name collision. Found and read the entire broader module
  `Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates`: it specifies
  complexes, differentials, naturality and derived isomorphisms and requires an ambient
  `HasDerivedCategory` instance, so it is not this graded-only statement. It introduces
  no separate concrete homogeneous submodule that should be reused here.
- Read Mathlib `TopRep.homogeneousCochains` in ContCohomology/Basic and its resolution
  definitions: these use iterated continuous-map spaces. Read
  `groupCohomology.inhomogeneousCochains` and `inhomogeneousCochainsIso`:
  these use unrestricted functions and cannot replace the jointly continuous terms.

Read the current local Stacks source, `etale-cohomology.tex` lines 9007–9040:
it permits arbitrary topological abelian coefficients and defines continuous maps on
finite products, with coefficient space in degree zero. The homogeneous equivalence
is agent-formulated, exactly as the node's provenance says. No source correction or
STATEMENT-DISPUTED issue was found. The designated CompactObject example was also read;
its current module is a withdrawn empty module, so the active module-mode conventions
in the stage brief supply the header used here.

Validation: server single-file compilation through `scompile.py`; dry-run preflight
and final delivery through `deliver2.py` as required. The maintainer supplies the
independent second reading; no other agents were started.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
