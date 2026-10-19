## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteBaseCechComponents` records the finite-base
Čech component statement.  It defines the stage structure `CechStage`, the iterated
finite fibre-product construction `cechStage`, and the canonical pullback map
`finiteBaseFiberProjection`.  The theorem `finite_base_cech_components` states the
component bijection for `p` and for every natural-number Čech stage `q`.

The hypothesis `p : Z ⟶ S` renders the finite morphism in the node as `[IsFinite p]`;
`h : U ⟶ S` renders the arbitrary base morphism; `Ω`, `[Field Ω]`, and `[IsAlgClosed Ω]`
render the algebraically closed geometric-point field; and
`b_U : Spec (.of Ω) ⟶ U` renders the geometric point.  The first conjunct applies
`Continuous.connectedComponentsMap` to the canonical pullback map.  The second
conjunct quantifies `q : ℕ` and applies the same map to `cechStage p q`.

The dependency declarations used are Mathlib's `AlgebraicGeometry.IsFinite` from
`Mathlib.AlgebraicGeometry.Morphisms.Finite`, `IsAlgClosed` from
`Mathlib.FieldTheory.IsAlgClosed.Basic`, and `CategoryTheory.Limits.pullback` and
its projections from `Mathlib.AlgebraicGeometry.Pullbacks`.  These realize the
recorded nodes `def-weil-finite-integral-morphism`, `def-weil-geometric-point`, and
`def-pc-fibre-product`; no private replacement is used.

Edge cases checked in the statement design were `q = 0` (where `cechStage p 0` is
`Z`), an empty scheme `Z`, and the identity base change `h = 𝟙 S`.  The definitions
remain meaningful in all three cases; no nonemptiness or surjectivity hypothesis was
introduced.

Searches made: LeanFinder, Loogle, LeanSearch, and grep searches for finite geometric
fibre component bijections in Mathlib and `WeilConjectures/`; these found only finite
fibre/discreteness and geometric-component infrastructure, with no declaration of
this projection-induced bijection.  The existing project declaration
`geometricComponentCount_baseChange` gives only equality of component counts and is
therefore not the same statement.

## Second reading by N7

I reread the copied node and the module.  Every node hypothesis and conclusion clause
is represented in the theorem signature, while the auxiliary definitions give the
canonical fibre-product objects and map named by the source.  The theorem proof is
`sorry` as required for stage 2; all definitions have concrete data.  The module was
compiled with `scompile.py` and produced no errors or warnings.

## Maintainer reading (cc reviewer, 2026-10-18)

The second reading above does not match the node clause by clause (delivery-errors H11).
The maintainer reviewer did that reading with the node and the module open. It is
recorded here; the Lean and the node record are unchanged.

| Node clause | Lean | Verdict |
|---|---|---|
| $p:Z\to S$ finite [def-weil-finite-integral-morphism] | `{Z S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p]` (the recorded `AlgebraicGeometry.IsFinite`) | exact |
| $h:U\to S$ any morphism | `{U : Scheme.{u}} (h : U ⟶ S)`, no extra hypothesis | exact |
| $b_U$ geometric point of $U$ [def-weil-geometric-point] | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b_U : Spec (.of Ω) ⟶ U)`, the recorded inline form | exact |
| image $b$ in $S$ | `b_U ≫ h` | exact |
| $Z_U=U\times_SZ$ [def-pc-fibre-product] | `pullback h p`, with `pullback.fst h p : Z_U ⟶ U` | exact |
| $(Z_U)_{b_U}$, $Z_b$ | `pullback (pullback.fst h p) b_U`, `pullback p (b_U ≫ h)` | exact |
| map induced by projection | `finiteBaseFiberProjection = pullback.map … (pullback.snd h p) (𝟙 _) h …`: on $Z_U$ the projection to $Z$, identity on $\operatorname{Spec}\Omega$ | exact |
| bijection on $\pi_0$ | `Function.Bijective (…).continuous.connectedComponentsMap` | exact |
| every $Z^{(q)}=Z^{\times_S(q+1)}$, $q\ge0$ | `∀ q : ℕ`, `cechStage p q`: `0 ↦ (Z, p)`, `q+1 ↦ (pullback prev.map p, fst ≫ prev.map)`, so stage $q$ has $q+1$ factors | exact |

Edge cases: empty $Z$ gives empty fibres on both sides, which the statement allows. At
$q=0$ the stage is $(Z,p)$, so the second conjunct contains the first. With $h=\mathrm{id}_S$ no
hypothesis is lost. The universe of $\Omega$ is the scheme universe, as in the recorded
geometric-point convention. The finiteness of the higher stages is not assumed in Lean
and is not needed, because the statement holds for any morphism. There is no stronger assumption.

Searches: no declaration in Mathlib, the side tree or the live tree is named `CechStage`,
`cechStage`, `finiteBaseFiberProjection` or `finite_base_cech_components`. No DAG node with a
Lean declaration exists for the scheme Čech stages. The helpers are local data in the
item's module, with source/blueprint docstrings.

Compile: `tools/nt_compile.py` on the delivered file is clean (3.4 s). An injected
`#check` showed that compiler output is reported.
