## Worker report

Stage 2 statement delivery, Q10, 2026-10-22. The prior Q23 merge recorded at
coord/ledger.md:24941 is the reviewed stage-1 split. It supplies no Lean attachment.
This delivery preserves that split, its statement, and its supporting nodes. No
repair note exists for this item. There is no new split and no statement correction.

The main module is Sheaf.AlgebraicGeometry.StableAbelianLevelNormalization;
its theorem is AlgebraicGeometry.exists_stable_abelian_level_normalization.
The only postponed proof in this delivery is that theorem. Its docstring carries
all five steps of the current node proof and the supporting node ids. Auxiliary
definitions contain actual functors, projections, and predicates, with their
structural identity/composition proofs; none contains sorry or a choice of data
from a mere existence statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Any field k | `(k : Type u) [Field k]`; no perfection, characteristic-zero, or algebraic-closure assumption |
| g >= 2 | `(g : ℕ) (hg : 2 ≤ g)` |
| Prime ell >= 3, distinct from char(k) | `ℓ : AbelianLevelPrime (Spec (.of k))`, the dependency's prime/at-least-three/stalkwise-unit subtype; over a field the last condition is exactly invertibility of ell |
| Unpointed stable moduli | `stableModuliBased (Spec (.of k)) g`, exactly `StablePointedModuli.forget ... g 0` as a based category |
| Smooth substack | `smoothModuliBased ... g`, the recorded full subcategory with `Smooth X.projection`; inclusion is `smoothModuliInclusion` |
| Full smooth level scheme L with the recorded meaning | `L : Over (Spec (.of k))`, `eL` into `abelianLevelBased ... g ℓ`, and `hL : eL.toFunctor.IsEquivalence`; this specifies the representative named in the node, rather than assuming an unrelated covering property |
| All frames, no symplectic condition | `AbelianLevelModuli` and `AbelianLevelModuli.HomCondition` are reused exactly; `abelianLevelToSmooth` forgets the frame by its actual arrow |
| Q is a coarse moduli scheme | `Q`, `π`, and `hQ : IsCoarseModuliScheme ... Q π`, retaining both the algebraic-space universal property and the geometric-point clause |
| Result represented by a k-scheme Z | existential `Z : Over (Spec (.of k))`; its represented fibred groupoid is `discreteModuli (yoneda.obj Z)` |
| Morphism a to stable moduli | existential `a : BasedFunctor ... (stableModuliBased ... g)` |
| Induced Z -> Q is finite | `c : Z ⟶ Q`, `IsFinite c.left`, and `ModuliTwoIso (a.comp π) (discreteModuliMap (yoneda.map c))`; c is tied to the actual composite |
| Normalize in the full level cover, not an arbitrary finite cover | `IsModuliChartNormalization (abelianLevelSchemeMap eL) a (discreteModuliMap (yoneda.map i)) e` |
| Normal finite-type etale chart | the new predicate universally quantifies T,t, assumes every stalk is a domain and integrally closed, `LocallyOfFiniteType T.hom`, `QuasiCompact T.hom`, and `IsEtaleModuliMap t` |
| Integral closure on that chart | it presents the actual two-base change of the full level scheme by E,p and uses `Scheme.Hom.normalization p.left`, `fromNormalization`, and `toNormalization` from Mathlib |
| Product of all generic fields | E is equivalent to the entire two-base change; no connected component is selected. On a normal Noetherian chart its smooth finite-etale cover is normal. Its functions are the normal subring of the product of all generic fields. Integral closure of the chart ring in that subring equals its integral closure in the full product: an element integral over the chart is integral over the finite-etale open cover and therefore lies in its normal functions. This also holds affine-locally for non-affine E. |
| Glue normalization with its descent arrows | comparisons are equivalences over h_T and commute with the canonical dominant map from E, via the final `ModuliTwoIso` in the predicate. Integral closure's uniqueness over the cover makes these comparisons compatible on overlaps; the specified global `a` supplies effective descent. |
| Upper arrow of the square | existential `i : L ⟶ Z` |
| Two-commutativity | `e : (discreteModuliMap (yoneda.map i)).comp a ≅ abelianLevelSchemeMap eL` in the category of based functors; its components are over identities |
| Two-cartesian square and exact smooth inverse image | the actual `moduliTwoFiberLift` of i, the underlying smooth-level map, and e has `toFunctor.IsEquivalence`. Its target is the dependency's `moduliTwoFiberProduct a (smoothModuliInclusion ...)`; objects include the family isomorphism, arrows obey its comma equation. |

The helper definitions of based moduli categories only package recorded projections
and forgetful functors. They neither define new families nor replace the dependency's
moduli categories by sets of isomorphism classes. A representing equivalence eL is
part of specifying L's meaning, and does not add a mathematical hypothesis. The
existence of that smooth representative is the separate rigidification theorem.
Similarly π,hQ specify the coarse scheme named in the original statement.

Dependency declarations actually used:

- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids:
  AlgebraicGeometry.StablePointedModuli, its forget and Smooth;
  AlgebraicGeometry.AbelianLevelPrime, AbelianLevelModuli, its forget and HomCondition;
  CategoryTheory.moduliTwoFiberProduct, moduliTwoFiberFst, discreteModuli,
  discreteModuliMap, ModuliTwoIso, IsCoarseModuliScheme, HasSpaceBaseChange,
  SpaceMapIsEtale. The full signatures and docstrings were read in the current source.
- Mathlib.Algebra.Field.Defs: Field; Mathlib.AlgebraicGeometry.Scheme: Scheme.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: IsFinite.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: Etale, through SpaceMapIsEtale.
- Mathlib.AlgebraicGeometry.Normalization: Scheme.Hom.normalization,
  normalizationDiagram, normalizationDiagramMap, fromNormalization, toNormalization,
  and toNormalization_fromNormalization. Their implementation takes integral closure,
  not a chosen finite scheme. The Over wrappers just compose its structure maps.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated: QuasiSeparated.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: IsIntegrallyClosed; IsDomain,
  in the existing def-weil-pbc-normal-ring inline normal-domain convention.
- Mathlib.CategoryTheory.FiberedCategory.BasedCategory: BasedCategory, BasedFunctor,
  and based natural isomorphisms. The new helper's universe binders for categories
  and morphisms are independent; no universe equality was imposed to repair an API.

None of the six theorem proof dependencies presently has a Lean record or Mathlib
match: coarse projectivity, stable finite isomorphisms, smooth level rigidification,
DM finite normalization charts, versal branch freeness, and inertia-free coarse
finiteness. Their imports cannot yet be added. Their mathematical statements remain
unaltered, and the theorem docstring explicitly names them. They are proof inputs,
not required definitions for typing this statement.

Edge cases checked before stating:

- g=2 and ell=3 are admitted; the hyperelliptic involution is retained in stable
  moduli, but cannot preserve a full frame of odd prime level.
- Characteristic ell is excluded by precisely the recorded unit condition;
  positive characteristic different from ell, including wild stabilizers, is admitted.
- The field need not be perfect; the perfect prime-field reduction is in the proof
  plan only. The result claims no smoothness of the boundary normalization.
- No marking, connectedness choice, symplectic frame, rational frame, or single
  generic component is introduced.
- Empty test schemes and empty chart pullbacks are allowed. The normalization of
  the empty cover is Mathlib's integral-closure construction in its zero ring.
- Smooth stable curves have no boundary nodes: the proof's empty parameter product
  is 1, and the same two-fibre product states the whole smooth restriction.
- A different coarse representative or a different representative of the full
  level scheme is allowed with its specified equivalence; no canonical model is
  silently fixed. All schemes and fields use the existing size convention u.

Searches for the item: msearch leanfinder, query "Normalization of the stable curve
moduli stack in the full abelian level cover is represented by a scheme finite over
coarse moduli", returned eight ordinary scheme-normalization results, no moduli
statement. msearch loogle `AlgebraicGeometry.Scheme.Hom.normalization,
CategoryTheory.BasedFunctor` returned no hits. msearch grep
`Moduli.*Normali|Normali.*Moduli|[Ss]table.*[Aa]belian|[Aa]belian.*[Ll]evel`
in Mathlib AlgebraicGeometry returned no hits. Direct rg of the item id and
StableAbelianLevelNormalization/stableAbelianLevelNormalization/IsModuliNormalization/
ModuliNormalization in both WeilConjectures and Sheaf returned only the parent
ProjectiveStablePointedLevelParameter's proof-plan mentions. Names for each added
helper were also checked in both roots and Mathlib.

The source is Pikaart--de Jong, arXiv alg-geom/9501003, §§1.1 and 2.3.3--2.3.7,
read through the primary PDF https://arxiv.org/pdf/alg-geom/9501003. Section 2.3.5
specifies normalization; Remark 2.3.7 gives scheme representability. Proposition
2.3.6 does not claim that every abelian-level compactification is smooth. The
current blueprint direct-images proof was read for the item's ancestor context.
No STATEMENT-DISPUTED issue or correction is proposed.

## New nodes

`def-sfb-moduli-chart-normalization`, in the item's chapter and unit, defines the
missing chart-normalization predicate and its typed comparisons. Its own module is
Sheaf.AlgebraicGeometry.ModuliChartNormalization. It also supplies real comparison
functors for two-fibre products and three Over wrappers for Mathlib normalization;
all public declarations are listed in lean.declarations with source docstrings.
No theorem or existence assumption is hidden inside these definitions.

Searches were made before writing: `tools/blueprint_refs.py search 'normalization
stack'` returned 0 nodes, and rg on definition-node files found no such interface.
The existing def-sc-normalization and def-fin-normalization-extension apply to an
integral scheme in one field; neither is the multiple-component stack construction.
The genuine lem-sfb-dm-finite-normalization-charts is an existence theorem, not a
previous definition of this predicate; the new node does not state that theorem.
The already recorded moduli-groupoid definition supplies all groupoid vocabulary.

The new node records verbatim results of msearch LeanSearch on "Normalization of a
moduli stack in a finite cover is characterized on etale scheme charts by integral
closure and the canonical dominant map" (only Mathlib scheme-normalization hits),
Loogle `"normalization", "BasedFunctor"` (0), and grep on
`ModuliChartNormalization|IsModuliChartNormalization|moduliTwoFiberLift|moduliTwoFiberMapRight|IsEtaleModuliMap`
(0). Direct rg in WeilConjectures and Sheaf likewise found no helper with those
names. Relative normalization already exists and is used directly, not duplicated.
The source is Pikaart--de Jong §2.3.5 and Mathlib's Stacks 035H implementation.

Its blueprint.from uses the parent item's current inherited ancestor (null), as
reported by `tools/blueprint_refs.py ancestor`; its via prepends the item id to the
item's existing via. No parent provenance was modified.

Validation: both delivered modules compiled separately in dependency order using
scompile.py, including their actual library module names, with no errors or warnings.
The chart module took 14.7 s and the main module 9.8 s in the successful run.
The main theorem is the sole intentional sorry. Preflight and delivery follow.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
