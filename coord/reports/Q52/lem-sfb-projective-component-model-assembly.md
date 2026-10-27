## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveComponentModelAssembly` states
`AlgebraicGeometry.exists_projective_component_model_assembly`. Its only theorem has
proof `sorry`; it introduces no definitions, helper axioms, new nodes or dependency repairs.
The existing statement, dependencies and proof are unchanged.

I read the entire item and all its statement dependencies, including their Lean records or
Mathlib matches and the source declarations. I read ILO, Travaux de Gabber, Expose X,
2.3 Step 1, printed p.150 (PDF page 156), which reduces by the disjoint sum of components.
The coordinate-block and ideal assembly are the node's explicitly agent-written expansion.

Hypothesis matching:

| Node hypothesis | Lean rendering |
| --- | --- |
| Field e | `(e : Type u) [Field e]` |
| Nonempty reduced e-scheme T | `T : Scheme.{u}`, `T.Over (Spec (.of e))`, `Nonempty T`, `IsReduced T` |
| Proper and finite type over e | `IsProper (T ↘ Spec (.of e))`, `hfiniteType : LocallyOfFiniteType ... ∧ QuasiCompact ...` of that same structure map |
| Finite nonempty enumeration T_1,...,T_s | `s : ℕ`, `hs : 0 < s`, `Ti : Fin s → Scheme.{u}` |
| Reduced irreducible component subschemes | `IsReduced (Ti i)`, closed immersions `j i`, `hcomponent` asserting that each range is an irreducible component |
| Distinct components, exhausting all components | `henumeration : Function.Bijective (fun i ↦ ⟨Set.range (j i), hcomponent i⟩)` |
| Component structures induced from T | `(Ti i).Over` and `(j i).IsOver` for the same `Spec e` |
| C closed and nowhere dense | `hC : IsClosed C`, `hCnd : interior C = ∅`; for closed C this is exactly nowhere density |
| Nonempty integral N_i over e | `(N i).Over` and `IsIntegral (N i)`; integrality includes nonemptiness |
| Normal means all local rings are integrally closed domains | `hnormal : ∀ i x, IsDomain ((N i).presheaf.stalk x) ∧ IsIntegrallyClosed ((N i).presheaf.stalk x)` |
| Geometrically reduced N_i | `GeometricallyReduced (N i ↘ Spec (.of e))` |
| Given closed embedding in P^{m_i}_e | `m : Fin s → ℕ`, `a i : N i ⟶ ℙ(ULift (Fin (m i + 1)); Spec (.of e))`, `IsClosedImmersion (a i)` and `(a i).IsOver` |
| Proper surjective e-morphisms q_i | `qi i : N i ⟶ Ti i`, `IsProper (qi i)`, `Surjective (qi i)`, `(qi i).IsOver` |
| Birational, as an isomorphism between dense opens | `hbirational`: opens U and V with `Dense` underlying subsets and `φ : U.toScheme ≅ V.toScheme`, satisfying `U.ι ≫ qi i = φ.hom ≫ V.ι` |
| Effective Cartier ideals J_i | `Ji i : (N i).IdealSheafData` and `hJi : ∀ i, (Ji i).IsInvertible` |
| Support q_i^{-1}(C intersect T_i) | `hsupport`: support equals `(qi i ≫ j i) ⁻¹' C`, the identical subset on N_i |

Using arbitrary reduced closed component schemes with the specified images is equivalent to
using the reduced induced component subschemes: a reduced closed subscheme with given
closed support is the unique reduced induced structure. There is no additional choice of
component structure and no new definition. The retained scheme-reduction import supplies
the recorded nilradical/subscheme interface should stage 3 need this identification.

Conclusion matching:

| Node clause | Lean rendering |
| --- | --- |
| Disjoint union B exists as a scheme | Existential `B`, coprojections `ι`, and `Nonempty (IsColimit (Cofan.mk B ι))` |
| Each N_i is an open-and-closed subscheme | `∀ i, IsOpenImmersion (ι i) ∧ IsClosed (Set.range (ι i))`; openness follows from the open immersion |
| Induced e-structure and morphism q | Existential b and q; `ι i ≫ b = N i ↘ Spec e`, `ι i ≫ q = qi i ≫ j i`, and `q ≫ (T ↘ Spec e) = b` |
| B proper and finite type over e | `IsProper b ∧ LocallyOfFiniteType b ∧ QuasiCompact b` |
| B geometrically reduced | `GeometricallyReduced b` |
| Closed embedding B into P^M_e | Existential M and A, `IsClosedImmersion A`, and its composition with the projective-space projection equals b |
| M+1=sum_i(m_i+1) | `M + 1 = ∑ i, (m i + 1)` |
| Effective Cartier ideal J restricts to every J_i | Existential J, `J.IsInvertible`, and `∀ i, J.comap (ι i) = Ji i` |
| Its support is q^{-1}C | `(J.support : Set B) = q ⁻¹' C` |
| q is surjective | `Surjective q` |
| Generic point of N_i maps to generic point of T_i | For every η with `IsGenericPoint η Set.univ`, `IsGenericPoint (qi i η) Set.univ` |
| q maps that point to the component generic point in T | `IsGenericPoint (q (ι i η)) (Set.range (j i))` |
| Corresponding residue fields are isomorphic through q | `IsIso (q.residueFieldMap (ι i η))`; this specifies the actual induced map |
| Bijection on component generic points | `Set.BijOn q (genericPoints B) (genericPoints T)` |

A scheme coproduct is expressed by its universal property rather than a second construction.
That property also forces the coprojections to be disjoint and jointly cover B and makes the
map with the displayed restrictions unique. The normality and base hypotheses are retained
although several conclusions need fewer hypotheses. No statement correction is needed.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field` (available through the geometric imports).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`,
  `AlgebraicGeometry.IsIntegral`; the latter includes nonemptiness.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and its Basic dependency:
  `Scheme.IdealSheafData.subscheme`, `subschemeι`, `Scheme.nilradical`, used for the
  recorded interpretation of a reduced component structure.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, used
  together with `IsDomain` of the stalk, exactly the normal-domain conjunction.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` imports the recorded
  `GeometricallyReduced` class, defined in `Geometrically.Reduced`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`, its
  standard notation and canonical structure morphism; homogeneous coordinates are
  indexed by `ULift.{u} (Fin (m+1))`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible`, exactly local generation by a non-zero-divisor.
  `IdealSheafData.support` is the quotient support, not support of J as a module;
  `IdealSheafData.comap` from Mathlib's Functorial module gives restriction.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective` is the
  recorded convention, expressed here by the required finite-space embedding and equation.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoints`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`.

All recorded non-Mathlib proof dependency modules are imported privately:
`ProjectiveSpaceStandardCharts`, `ProjectiveSpaceFunctorOfPoints`,
`ProjectiveSpaceHomOfGeneratingSections`, `ProjectiveMorphismChartPreimage`,
`Morphisms.ProjectiveImpliesProper`, `ClosedImmersionResidueFieldIso`, all under
`Sheaf.AlgebraicGeometry`. The Mathlib proof leaves are provided by the imports of
Limits (coproducts and extensive base change), Properties/Sober (sobriety),
ClosedImmersion and its Basic dependency (target locality), and ResidueField
(point naturality and the open-immersion case). No import cycle was introduced.

Edge cases checked before writing:

- s=1: one component, with M=m_1, and q is its composite with the component inclusion.
- s=0 is excluded exactly by the given 1≤s and nonempty T, not silently by a universe choice.
- Every m_i=0: the dimension equation is M+1=s; the summands embed at the disjoint
  coordinate points in P^{s-1}. No positivity of m_i was added.
- Empty C: Cartier ideals can be the unit ideals, and the assembled ideal is the unit ideal
  with empty quotient support. No nonempty boundary or positive-dimensional component is assumed.
- Intersecting components of T: only their reduced component models become disjoint upstairs;
  j is never required to have pairwise disjoint ranges. Generic points remain distinct.
- The statement uses neither geometric irreducibility nor a perfect-field assumption.
  Geometric reducedness uses the existing arbitrary-field-base-change class.
- Normality is checked on every stalk, not just on the global section ring.
- No universe equality is added. The field and schemes live in u; Fin s is small for all u,
  and ULift lifts finite homogeneous-coordinate types to the required scheme universe.

Searches for an existing combined theorem:

- `msearch.py ... leanfinder`: "Finite disjoint union of projective birational component
  models with Cartier ideals is projective geometrically reduced and has a bijection on
  generic points". Eight hits: Proj basics, the affine-chart comparison, proper Proj
  structure maps, and `instIsIsoSchemeSigmaSpecOfFinite`. None states the assembly theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.ProjectiveSpace,
  AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`. No hits; Loogle does not index the
  upstream ProjectiveSpace name. Read the upstream source directly instead.
- `msearch.py ... grep`: `projective.*(coprod|sigma)|component.*model.*assembly`, under
  Mathlib AlgebraicGeometry. No hits.
- `rg` of the same expression in both project source roots found unrelated categorical
  projective objects, no scheme assembly theorem. Searches for the proposed declaration
  and module name in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found no existing declaration. `grep -rn` of the exact node id in WeilConjectures found none.
- Broader `rg` for birational/component-model language located the consumer
  `ProperPairRadicialPreparation` and constituent birational lemmas, not this combined theorem.

No STATEMENT-DISPUTED issue, new node, unusable dependency, or source fault was found.

## Second reading by Q52

I reopened the node and reread the delivered signature clause by clause after drafting.
This is a self-check; the maintainer supplies the independent review as specified in the
worker brief. I checked that component enumeration is both injective and surjective,
that each reduced component structure and all morphisms are over e, and that birationality
uses the given qi rather than an unrelated isomorphism. I checked that Cartier restriction
is equality of actual pulled-back ideals, and that residue-field isomorphisms concern the
actual map induced by q at the summand's generic point. The full M+1 equation is retained,
and `genericPoints` denotes component generic points, not all scheme points. The tables
above account for every hypothesis and conclusion. The compiler flagged overlapping proper/locally-finite-type instance binders. I changed the explicit finite-type hypothesis to the ordinary conjunction `hfiniteType`, preserving exactly its mathematical content while avoiding duplicate typeclass assumptions. No mathematical mismatch or statement change was found.
