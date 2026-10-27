## Worker report

The delivery states `AlgebraicGeometry.IsAbelianVariety.trace_adjoint_product_eq_intersection`
in `Sheaf.AlgebraicGeometry.AbelianVariety.TraceIntersection`. Its only theorem has proof
`sorry`. The item statement and its accepted proof plan are unchanged. The additional
module constructs composition extensions and the Tate action on the landed rational Hom;
it contains no postponed data or theorem. All work is in the prescribed sandbox.

I read the entire item, every statement-dependency node and its recorded declarations,
the available proof-dependency interfaces, Milne AV I Theorem 14.3 (printed p.62),
Proposition 10.20 (pp.50–52), and the Hom/Tate discussion on pp.45–46 and p.61.
Milne's displayed trace uses the cyclic order `f f†`; ordinary trace cyclicity gives
`f† f`, the order in this node. The four-step calculation accepted in stage 1 is carried
in the theorem docstring, naming every non-elementary prerequisite. Proof dependencies
without any Lean record are not restated or imported. The existing ample/Hilbert-degree
module is imported privately for the proof plan; Tate rank is already public through
the required Tate module definitions.

Hypotheses and clauses, matched to the Lean:

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| Abelian variety A/k | `A : Over (Spec (.of k))`, `[GrpObj A] [IsAbelianVariety A]` |
| Positive dimension | `g : ℕ` and `hd : topologicalKrullDim A.left = ↑↑(g+1)`; the node's dimension is `g+1`, covering every positive natural dimension |
| Ample invertible L | `L : A.left.Modules`, `[L.IsInvertible]`, `hL : IsAmple A.hom L` |
| The dual Aᵛ with its Poincare family | `D : AbelianDualPoincareDatum A`, using the already landed representing datum, not an arbitrary second abelian variety |
| lambda = phi_L | `lambda : A ⟶ D.dual`, `[IsMonHom lambda]`, and `hlambda : ClassifiesAbelianDifference D L lambda` |
| Rational inverse mu | `mu : abelianRationalHom D.dual A`, the actual tensor product `ℚ ⊗[ℤ] Hom(D.dual,A)` |
| mu lambda = 1_A | `hmulambda : rationalHomPrecomp lambda mu = abelianHomToRational (abelianHomId A)` |
| lambda mu = 1_Aᵛ | `hlambdamu : rationalHomPostcomp lambda mu = abelianHomToRational (abelianHomId D.dual)` |
| Every group-scheme endomorphism f | `f : A ⟶ A` and `[IsMonHom f]`; no nonzero, finite, surjective or isogeny hypothesis |
| fᵛ is pullback on the dual | `fDual` with `[IsMonHom fDual]`; `hfDual` identifies `(f × 1)* P` with `(1 × fDual)* P`, exactly the classifying-family characterization in `exists_dual_polarization_calculus` |
| Prime ell distinct from the characteristic | `ℓ : ℕ`, `[Fact ℓ.Prime]`, `hℓ : (ℓ : k) ≠ 0` |
| Endomorphism mu fᵛ lambda f | `rationalHomPrecomp (f ≫ lambda ≫ fDual) mu`, using categorical composition from left to right |
| Its action on V_ell A | `rationalHomTateMap ℓ`, defined by extension of the upstream componentwise action |
| Ordinary trace | `LinearMap.trace ℚ_[ℓ] (IsAbelianVariety.rationalTateModule ℓ A)` |
| Nonzero denominator | The first conjunct is `selfIntersectionNumber ... L ≠ 0` |
| Mixed numerator | `intersectionNumber` on the identity immersion of A, with `Fin.cons (pullback f.left L) (fun _ : Fin g ↦ L)`; there is one pullback entry and exactly g copies of L |
| Top self-intersection | `selfIntersectionNumber` with `g+1` entries, identity immersion, and dimension proof `hd` |
| Factor 2 dim A | `2 * (g + 1 : ℚ)` |
| Equality in Q_ell using the canonical embedding | Second conjunct equates the trace to `algebraMap ℚ ℚ_[ℓ]` of the entire rational ratio |

The dimension reindexing changes no mathematical hypothesis. In both intersection terms,
I supply `⟨A.hom⟩` explicitly as the scheme-over-field structure and
`IsAbelianVariety.toIsProper` as its properness proof. Thus the coefficient function uses
the specified k-scheme, with no extra independently selected structure map or properness
assumption. The invertibility proof for each mixed entry is supplied by `Fin.cases`,
the existing invertibility instance for pullback, and `[L.IsInvertible]`. This is actual
proof data for an existing construction, with no extra condition on f.

Dependency interfaces used (definitions and full signatures/docstrings read):

- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety`, its properness projection, `dim`, and
  `topologicalKrullDim_eq`.
- `Mathlib.CategoryTheory.Monoidal.Grp` and its Cartesian companion:
  `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, `Grp.ofHom`, `IsMonHom`,
  `IsMonHom.monoidHom`, and `yonedaGrpObj`. `abelianHom` is only an additive alias for
  the existing group of morphisms of group objects, not a new group-scheme definition.
  Abelian commutativity is the upstream instance in `AbelianVariety.Basic`.
- `Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus`:
  `IsAbelianVariety.exists_dual_polarization_calculus`; its lambda classification and
  dual-pullback family conditions are used verbatim through
  `AbelianDualPoincareDatum` and `ClassifiesAbelianDifference` from its public dependency
  `Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum`.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`:
  `tateModule`, `rationalTateModule`, `tateModuleMap`, `rationalTateModuleMap`,
  the rank statements, and their componentwise/base-change descriptions. The dependency
  `sk-def-av-tate` is already closed upstream in its audit record; no dependency repair
  or duplicate Tate module is needed.
- Mathlib `Field`, `IsAlgClosed`, `TensorProduct`, `TensorProduct.lift`,
  `LinearMap.baseChange`, `Padic`, `PadicInt`, `topologicalKrullDim`, and `LinearMap.trace`
  supply the corresponding Mathlib leaves.
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`: `AlgebraicGeometry.IsAmple`;
  `...Modules.Invertible`: `Scheme.Modules.IsInvertible` and its pullback instance.
- `Sheaf.AlgebraicGeometry.IntersectionNumber`: `Scheme.Modules.intersectionNumber`
  and `selfIntersectionNumber`, with their actual rational coefficient definition.
- The recorded `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` is public-imported.
  The module pullback in the displayed formula uses the already shared
  `Scheme.Modules.pullback`, as do the recorded polarization and invertibility interfaces.
  No private module-pullback construction or arbitrary map is introduced.
- `WeilConjectures.AlgebraicGeometry.Modules.Ample`: `Scheme.Hom.degree` and
  `degree_pos_of_isAmple_of_nonempty`, privately imported for the stated proof plan.

Edge cases checked before writing and on rereading:

- Dimension one is `g=0` in this signature: the numerator has only the f*L entry;
  there is no malformed `Fin 0` slot, truncated exponent, or exclusion of elliptic curves.
- For f = 0 the adjoint product is zero, f*L is a constant/trivial line, and the positive
  dimensional mixed intersection and trace both vanish. No non-isogeny case is excluded.
- For f = identity the formula gives trace `2 dim A`; for multiplication by n on an
  elliptic curve it gives `2 n²`. Both agree with the Tate action and intersection degrees.
- The prime condition works in characteristic zero and positive characteristic and
  includes ell = 2 when allowed. No characteristic assumption is added.
- The Hom action extension includes zero abelian varieties and zero homomorphisms.
  It uses arbitrary finite sums and rational coefficients in the tensor quotient,
  not an integral representative or a denominator chosen by a sorry theorem.
- The empty scheme is excluded by the existing abelian-variety connectedness convention;
  dimension zero is excluded only in the item, as required by its positive-dimension clause.
- All universes and variables are explicit; the construction uses `Scheme.{u}` consistently.

Searches actually run:

1. `msearch.py leanfinder`: “The trace of the Rosati adjoint product on a Tate module equals
   the mixed intersection number of an ample line bundle and its pullback”. Eight results
   about field trace dual bases, contraction, and class groups; no geometric identity.
2. `msearch.py loogle`: `LinearMap.trace, TensorProduct`. Eight generic trace/contraction
   and tensor-product trace facts; no abelian-variety trace/intersection formula.
3. `msearch.py grep`: `Rosati|rosati|trace.*intersection`. Zero Mathlib results.
4. For the new notion, `msearch.py leansearch` and `leanfinder` with “Rational homomorphisms
   of abelian varieties Hom tensor Q and their induced rational Tate module action”.
   Each returned eight generic tensor/rational linear algebra results, including
   `AddMonoidHom.toRatLinearMap`; none supplies the geometric Hom or Tate action extension.
5. `msearch.py grep`: `rationalHom|RationalHom|rationalTateModuleMap`. Zero Mathlib results.
   The new node records these three logged searches with their actual result records.
6. `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the rational-Hom names found
   unrelated adic-sheaf Hom and general-linear-group rational representations, and the
   integral `IsAbelianVariety.rationalTateModuleMap`, which is reused. No rational
   group-scheme Hom/Tate extension exists there. Grep by the item id found no declaration.
7. `python3 tools/blueprint_refs.py search 'rational homomorphisms'` returned zero blueprint
   nodes. DAG grep found consumers of rational Hom but no definition of this notion.
   `blueprint_refs.py ancestor` reports the same null nearest ancestor already recorded
   by the item; the new node retains it and extends the item's full provenance via-chain.

No STATEMENT-DISPUTED issue or source correction remains. Compiles use scompile.py only.

## New nodes

`def-sfb-abelian-rational-tate-action` extends the existing rational Hom interface
with precomposition and postcomposition by integral maps and the rational Tate action
`q ⊗ f ↦ q V_ell(f)`, following Milne AV I §10 pp.45–46 and §14 p.61. Its module is
`Sheaf.AlgebraicGeometry.AbelianVariety.RationalHomTateAction`. Every helper is recorded
in `lean.declarations` and has its own source/blueprint docstring. All definitions have
real bodies using Yoneda, scalar extension and the tensor universal map. It imports the
landed `Sheaf.AlgebraicGeometry.AbelianVariety.RationalHom` and uses its `abelianHom`
and `abelianRationalHom` directly. The integral inclusion and identities are also the
landed `abelianHomToRational` and `abelianHomId`, with no duplicate alias.

The first dry run passed, but its refresh found N9 had just landed
`def-sfb-abelian-rational-hom`. I read that full node and module and removed my
competing file and node before delivery. That landed interface supplies the tensor
Hom and integral composition/identity, but no composition extension or Tate action.
The actual searches above found no other definition of those missing extensions.
The item gains the landed rational-Hom node, the new action node, and the already landed
`def-sfb-abelian-dual-poincare-datum` as direct dependencies. No dependency node or
landed module is changed.

## Second reading by Q155

This is the dispatcher's sole worker's second reading; the independent maintainer review
is separate, as specified in the brief, and no other agent was started. I reopened both
modules and the original node and checked every row in the correspondence table.
I found and fixed an unwanted independently selected scheme-over-k structure: both
intersection terms now explicitly use `A.hom`, with its existing properness projection.
I also removed an unnecessary mixed-intersection helper: the signature now applies the
existing `intersectionNumber` directly, rather than introducing another notion.

I checked composition order directly: precomposition of mu by `f ≫ lambda ≫ fDual`
is mu after fDual after lambda after f. The two inverse equations use precomposition
and postcomposition respectively. I checked the new action on a pure tensor directly in
its body: the tensor lift applies the rational coefficient, via its Padic cast, to the
base change of the upstream componentwise `tateModuleMap`. All additivity/balancing
fields are actual proofs and no data depend on `sorry`. The only remaining sorry is the
item theorem, whose docstring contains its full accepted four-step proof plan.
The positive dimension reindexing includes dimension one; the first mixed entry is f*L
and all other entries are L. The field embedding applies to the entire rational ratio.
The original TeX statement is unchanged. The final wrapper compile and delivery preflight
results are recorded by the delivery tool.


On the final second reading after the parallel landing adjustment, I checked
N9's `abelianHom` and `abelianRationalHom` against every use in both modules. The
additive group structure and rational tensor factor order agree definitionally.
Both inverse identities now use N9's actual `abelianHomToRational (abelianHomId ...)`.
There is no replacement of the landed rational Hom module in this packet.

Final validation: dry run OK at 61906cf74e6; both delivered modules compile cleanly,
with the item theorem as the only postponed proof and no other warnings.
