## Worker report

Repaired the returned packet for `lem-pur-etale-sheaf-projection-map` (F1--F3). The item module is `lean/Sheaf/EtaleCohomology/Purity/Smooth/EtaleSheafProjectionMap.lean`, with main declaration `AlgebraicGeometry.Etale.etaleLowerShriekProjectionMap`.

The three constant-coefficient tensor helpers `etaleSheafTensor`, `etaleSheafTensorMap`, and `etaleSheafTensorSection` are declarations in this item module. The general dependency record for `def-pur-sheaf-tensor-product` was restored unchanged from the shared repository; its `SiteTensorFunctoriality` interface is retained. The returned ModuleCat inverse-image repair file was removed. The item imports `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk` for the existing canonical `upperStarCompSheafFiberIso`, and the inverse-image dependency record was restored unchanged.

The item node additionally cites `det-def-sfb-sheaf-tensor-structure`, `sk-def-sfb-sheaf-tensor`, `lemma-openclosed-stalk-upperstar`, and `def-weil-pbc-inverse-image`.

The item statement binds `A : Type (u + 1)` with `[CommRing A]`, schemes `V T : Scheme.{u}`, and `e : V ⟶ T` with exactly `[Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]`. The variables `M` and `N` are sheaves on the small etale sites with values in `ModuleCat.{u + 1} A`; no flatness, nonemptiness, torsion, or extra finiteness condition is added.

The helper definitions render the construction clause by clause:

- `etaleSheafTensor` is the tensor object of `Etale.sheafMonoidalCategory (ModuleCat A)`, using the canonical sheafified monoidal structure supplied by the landed sfb tensor structure and its tensor node.
- `etaleSheafTensorMap` is the corresponding `tensorHom f g`, and `etaleSheafTensorSection` is the canonical lax-monoidal sheafification tensorator applied to `m tensor n`.
- `etaleSumSection` inserts `m` through the recorded lift-indexed `lanUnit` and `toSheafify`; `etaleLiftSection` applies the `upperStarLowerStarAdjunction` unit and restricts along the graph `MorphismProperty.Over.mapPullbackAdj` unit.
- `etaleProjectionSumStalkIso` uses the germ-normalized witness from `Etale.exists_etaleSumStalksIso`. The tensor stalk comparison uses `sheafFiberTensorIso` and canonical universe-lift transports. `etaleProjectionLiftStalkIso` uses the existing `Etale.upperStarCompSheafFiberIso` and the lift triangle equality.
- `etaleProjectionSourceStalkIso` has codomain `(direct sum M_v) tensor N_t`, while `etaleProjectionTargetStalkIso` has codomain `direct sum (M_v tensor N_t)`. The lower comparison is the actual `TensorProduct.directSumLeft` module isomorphism, with generator formula `iota_v(m) tensor n` maps to `iota_v(m tensor n)`.

The theorem's existential supplies an isomorphism `p` from `e_Σ! M tensor N` to `e_Σ! (M tensor e^*N)`. Its first conjunct is joint naturality in `f : M ⟶ M'` and `g : N ⟶ N'`, with the displayed composites rendered by `etaleSheafTensorMap` and the map of `etaleLowerShriek`. Its second conjunct is the exact section equation `p (iota_s m tensor n) = iota_s (m tensor s^* n)`, where `s^* n` is rendered by `etaleLiftSection` (inverse-image unit followed by graph restriction), and inclusions are rendered by `etaleSumSection`. Its third conjunct quantifies every algebraically closed geometric point `t : Spec Ω ⟶ T` and states the commuting stalk square using `sheafFiber.map p.hom`, the fixed source and target comparison isomorphisms, and the actual direct-sum tensor map. The source retains the `N_t` tensor factor.

Edge cases checked: `M = 0`, `N = 0`, identity `e`, an empty lift fibre (zero direct sums), arbitrary infinite lift fibres (finite-support direct sums), empty schemes, and non-flat coefficient modules. The direct-sum tensor map remains an isomorphism in all these cases.

Dependency declarations used are the recorded `Etale.etaleLowerShriek` (EtaleMap), `Etale.exists_etaleSumStalksIso` (EtaleSumStalks), `Etale.sheafFiberTensorIso` and `Scheme.etale_stalk_tensor_unique` (EtaleStalkTensorScalar), upstream `Etale.upperStarCompSheafFiberIso` (UpperLowerStar.Stalk), and `Etale.upperStar` / `upperStarLowerStarAdjunction` (UpperLowerStar.Defs). The restored tensor dependency record is the `SheafOfModules.siteSheafTensorRightMap` interface. The landed `CategoryTheory.sfbSheafTensorStructure` and `CategoryTheory.sfbSheafTensor_properties` records are cited as the canonical tensor structure dependencies.

Searches run during the repair:

- `msearch.py ... leanfinder "canonical projection isomorphism extension by zero tensor sheaf etale"`: eight hits, all unrelated Kähler/presentation declarations.
- `msearch.py ... loogle "etaleLowerShriek tensor projectionMap"`: zero hits; `etaleLowerShriek` was unknown to Loogle.
- `msearch.py ... grep "etaleLowerShriekProjectionMap|projectionMap.*LowerShriek" WeilConjectures`: zero hits.
- `rg` over the source and shared `lean/Sheaf` tree located the upstream `Etale.upperStarCompSheafFiberIso`, the EtaleMap lower-shriek construction, and the tensor structure modules; no exact existing projection theorem was found.

No statement correction or statement dispute was needed. All variables and universes are explicit. The repaired item module compiles with `scompile.py`; only the theorem proof is the stage-2 `sorry`.

## Second reading by Q52

Independent maintainer second reading of immutable delivery
5acdcff6a6d860dab938f84cd669bf94b2558e76, performed on 2026-10-18.
This is the maintainer's reading, not a claim that the delivering worker performed one.

I read the item node, all 18 statement-dependency records, the complete delivered
module and its docstrings, and the source constructions and declarations. Clause checks:

| Node object or clause | Lean rendering | Verdict |
| --- | --- | --- |
| Commutative coefficient ring A | `A : Type (u + 1)` and `[CommRing A]` | Correct, including the zero ring |
| Schemes V,T and separated etale finite-type e | `Scheme.{u}`, `e : V ⟶ T`, `[Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]` | Exactly the node hypotheses |
| Module sheaves on the small etale sites | `Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)` and the analogous T category | The accepted constant-coefficient encoding in def-weil-pbc-etale-sheaves |
| Exact inverse image e* = e^-1 | Recorded `Etale.upperStar` and its module-valued unit | Correct; no arbitrary functor or exactness assumption added |
| Sheaf tensor | `etaleSheafTensor`, the existing `Etale.sheafMonoidalCategory` tensor object | Canonical localized objectwise tensor; not a new tensor construction |
| Sheafified lift-indexed sum | Recorded `etaleLowerShriek`; `etaleSumSection` uses its `lanUnit` and `toSheafify` | Correct summand inclusion |
| Every test object and lift | `W : V.Etale`, composed with e using `Over.map` | Equivalent encoding: every lift of a T-etale test scheme is etale over V by etale cancellation |
| Unit followed by graph restriction | `etaleLiftSection` uses `upperStarLowerStarAdjunction.unit` and `mapPullbackAdj.unit.app W` | Exactly the specified s* n |
| Canonical natural isomorphism in the stated direction | Existential family `p M N` of isomorphisms, first conjunct joint naturality | Correct; section generators uniquely fix the family |
| Displayed component formula | Second conjunct, with `etaleSheafTensorSection` and `etaleSumSection` | Exact formula |
| Restrictions and A-balancing | Sheaf morphisms in ModuleCat; local tensor section factors through ordinary module tensor | Built into the types and canonical constructions |
| All geometric points and sum-stalk identification | Third conjunct; `etaleProjectionSumStalkIso` from the germ-normalized `exists_etaleSumStalksIso` | Correct; its witness is fixed by generators, not hollow data |
| Tensor-stalk and inverse-image identifications | `etaleProjectionTensorStalkIso`, `etaleProjectionLiftStalkIso` | Canonical tensorator inverse and canonical pullback-stalk comparison, with explicit universe and triangle transports |
| Direct-sum component formula | `etaleProjectionDirectSumTensorIso` from `TensorProduct.directSumLeft` | Its `directSumLeft_tmul_lof` is precisely the requested generator rule |
| Actual map on stalks | Third conjunct contains `sheafFiber.map (p M N).hom` | Correct commuting square; source is `(direct sum M_v) tensor N_t` |

Source passages read: Stacks `more-etale.tex`, lemma-f-shriek-projection
(Tag 0GKF), lines 1808-1886; `etale-cohomology.tex`,
proposition-describe-jshriek (03S5), lines 11425-11472, and
lemma-stalk-pullback (03Q1), lines 4649-4723; `sites-modules.tex`,
lemma-j-shriek-and-tensor (0E8I), lines 4051-4092. The source's locally
quasi-finite statement specializes to the node's etale case. The lift-indexed
construction is the recorded sum model, so no finite-support-model comparison is
being assumed as a Lean definition.

Exact dependencies inspected include `Etale.etaleLowerShriek` in EtaleMap,
`Etale.upperStar` and its adjunction in UpperLowerStar.Defs,
`exists_etaleSumStalksIso` in EtaleSumStalks, the tensor uniqueness theorem in
EtaleStalkTensorScalar, `sheafFiberTensorIso` in StalkMonoidal,
`upperStarCompSheafFiberIso` in Stalk, the sfb tensor structure and comparison,
and the independent-universe SiteTensorFunctoriality interface. The two missing
local upstream source files were read through `scompile.py --source`: the exact
`etaleInverseImageModulesExact` package and `inverseImage_stalk_germ`.
The latter is abelian-valued; the comparison actually used here is the existing
general coefficient-category construction in Stalk. Its general-site unit-germ
calculation applies to ModuleCat, so no new map or missing data is needed.

Universes: `Scheme.{u}` has its usual etale site with objects at u+1 and morphisms
at u. The coefficient modules live at u+1, as the recorded sum-stalk and tensor
APIs require; there is no equation identifying the site's object and morphism
universes. `Omega : Type u` is the recorded geometric-point convention.
The point-universe lifts are transported by `uliftSheafFiberIso`, rather than
silently treating two fibre functors as equal. All variables are bound and
`autoImplicit` is false. Any larger coefficient size is covered by increasing the
ambient scheme universe; no algebraic or finiteness restriction on A or modules is added.

Edge cases checked mathematically: empty V or T, empty lift fibre, M=0, N=0,
A=0, e the identity or an open immersion, and non-flat modules over arbitrary
commutative rings. The distribution equivalence works for arbitrary index sets
and finite-support elements; under the node hypotheses geometric fibres are
finite, but the construction does not rely on that finiteness. Restricting lifts
may merge their indices, which adds summand entries and preserves the formula.

Independent duplicate search used lowerShriek/tensor/projection terminology in
both source trees and the project's Sheaf tree, and checked Mathlib's site and
direct-sum tensor APIs. A related upstream construction does exist:
`Etale.etaleLowerShriekTensorIso` and its naturality in
LowerShriek.EtaleMapProjection. I read that declaration: it supplies the abstract
projection isomorphism in the reverse orientation, but does not state this node's
section equation or its normalized stalk square. It is not an exact existing
binding for the complete node. The three local tensor helpers are transparent
specializations of existing operations, not replacements for the general
SheafOfModules tensor dependency. No exact complete duplicate was found.

Findings and fixes: H1/H11, the delivered second-reading section only disclaimed
having done a reading; replace it with this actual independent reading. H2/H8,
`etaleSheafTensor`, `etaleSheafTensorMap`, and `etaleSheafTensorSection` were missing
from the owning item's `lean.declarations` and their docstrings carried the
general dependency's blueprint id; list them and assign the owning item's id.
The obsolete documentation name `inverseImage_module_stalk_germ` was also
corrected to the actual general comparison and existing abelian germ theorem.
No mathematical signature or node statement was changed. The item's
`lean.statement` was checked byte-for-byte against the theorem signature and matches.

Compiler evidence: the immutable module was checked through the prescribed
`scompile.py Q52 lem-pur-etale-sheaf-projection-map <snapshot module>` wrapper;
exit 0, no diagnostics, sandbox 8.4 s and library-path 4.2 s. The installed
wrapper currently performs server-side confirmation with a private overlay,
although the brief describes its earlier local-overlay implementation. No direct
ssh, repository edits, live Lean writes, lake build or global build were used.
The corrected module changes docstrings only; its separate reproduction is
recorded in the maintainer review.

Pilot gates: all helper definitions contain actual constructed data; the only
new theorem has exactly `by sorry`; every declaration has source and blueprint
documentation after the repair; the six proof steps are in the theorem docstring.
No new independent notion, dependency repair, source-based statement correction,
or pro-etale replacement is needed. Verdict: FIX for complete mechanical repairs.

Corrected-module compiler reproduction: the prescribed `scompile.py` invocation
against the complete replacement file finished with exit 0 and no diagnostics;
sandbox 33.8 seconds and library-path 9.2 seconds, within the 60-second limits.
The theorem signature remains verbatim equal to the stored `lean.statement`,
and the corrected `lean.declarations` lists all twelve declarations.
