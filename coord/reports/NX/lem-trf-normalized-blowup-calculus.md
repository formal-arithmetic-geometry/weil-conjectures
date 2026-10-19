## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizedBlowupCalculus` supplies two actual constructions,
`Scheme.IdealSheafData.normalizedBlowup` and `normalizedBlowupMap`, and the single statement
`Scheme.IdealSheafData.normalizedBlowup_calculus`, with proof `sorry`. These helpers belong to
this node's explicit introduction of B_J(S); they introduce no independent auxiliary notion.
There are no data placeholders, chosen unspecified maps, new nodes, dependency repairs, or
statement corrections. The original statement and dependency fields are unchanged.

Source reading: the local ILO PDF was converted to text inside this item's scratchpad. Read
Expose VIII, 2.2.1--2.2.4 and 2.2.7--2.2.9, printed pp.90--91. In particular 2.2.4(i) says
universal maximally dominating normal map with Cartier extended centre; 2.2.4(ii) gives the
comparison over the normalization. Lemma 2.2.9 identifies normalization after regular base
change by an integral generically isomorphic map to a normal target. Read Stacks
`morphisms.tex`, `lemma-normalization-normal` (035Q), including its arbitrary normal-source
factorization clause, and `lemma-nagata-normalization` (035S), supplying finiteness in the
finite-type rational case. No false assertion about integral closure commuting with adjoining
chart fractions is used.

Clause-by-clause rendering:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| S is a scheme | `(S : Scheme.{u})`, with explicit universe u. |
| S is over Q | `q : S ⟶ Spec (.of (ULift.{u} ℚ))`. ULift keeps the rational field in the scheme's universe without restricting schemes to universe zero. |
| S reduced | `[IsReduced S]`, the recorded Mathlib predicate. |
| S finite type over Q | `[LocallyOfFiniteType q] [QuasiCompact q]`, precisely the recorded finite-type conjunction. |
| J coherent ideal in O_S | `J : S.IdealSheafData` supplies quasi-coherence and inclusion as an ideal; `hJ : ∀ U : S.affineOpens, (J.ideal U).FG` supplies affine finite generation. A finite-type Q-scheme is Noetherian, so this is exactly coherence of the ideal, with no added hypothesis. |
| V(J) nowhere dense | `hcentre : Dense (J.support.compl : Set S)`; support is the closed zero locus of the ideal data, so density of the complement is precisely nowhere density. |
| nu is the componentwise normalization | The recorded `S.reducedNormalization` and `S.fromReducedNormalization`. No different normalization is introduced. |
| B_J(S) is Bl_J(S)^nu | `normalizedBlowup J := J.blowup.reducedNormalization`. |
| Map B_J(S) to S | `normalizedBlowupMap J := J.blowup.fromReducedNormalization ≫ J.blowupMap`. |
| B normal | First conjunct quantifies over every x of B and states `IsDomain (B.presheaf.stalk x) ∧ IsIntegrallyClosed (B.presheaf.stalk x)`, matching the explicit local-ring normality convention. |
| B reduced | `IsReduced J.normalizedBlowup`. |
| B finite type over Q | `LocallyOfFiniteType (J.normalizedBlowupMap ≫ q) ∧ QuasiCompact (J.normalizedBlowupMap ≫ q)`. |
| B to S surjective | `Surjective J.normalizedBlowupMap`. |
| B to S birational on each component | The map preserves generic points (`Set.MapsTo` between `genericPoints`), and there is an open U dense in S, with dense preimage in B, for which `IsIso (J.normalizedBlowupMap ∣_ U)`. For these reduced Noetherian schemes this is exactly componentwise birationality of this morphism: each component meets the dense open, the isomorphism identifies their generic points and function fields, and dense preimage excludes extra components. Conversely finitely many componentwise birational isomorphism opens can be shrunk away from component intersections and combined to this U. |
| B is an object of the stated final category | Its normality, generic-point condition, and `(J.comap J.normalizedBlowupMap).IsInvertible` appear explicitly. |
| Finality among normal S-schemes with generic-point preservation and invertible extended J | For every scheme Y and map f to S, the three antecedents are respectively stalkwise normality, `Set.MapsTo f (genericPoints Y) (genericPoints S)`, and `(J.comap f).IsInvertible`; conclusion is `∃! l : Y ⟶ J.normalizedBlowup, l ≫ J.normalizedBlowupMap = f`. No finite-type, nonempty, or integrality condition is imposed on Y. |
| Only S-automorphism is identity | For each `e : B ≅ B`, the over-S equation implies `e = Iso.refl _`. |
| Canonical map B to S^nu | Unique `n : B ⟶ S.reducedNormalization` with `n ≫ S.fromReducedNormalization = J.normalizedBlowupMap`. |
| Canonical identification B_J(S) with B_(J O_Snu)(Snu) over Snu | For that uniquely characterized n, a unique isomorphism e has `e.hom ≫ (J.comap S.fromReducedNormalization).normalizedBlowupMap = n`. This is an isomorphism over Snu, rather than merely an isomorphism of schemes. |
| Every smooth h:T to S with T finite type over Q | Quantifiers T and h with `[Smooth h]`, `[LocallyOfFiniteType (h ≫ q)]`, `[QuasiCompact (h ≫ q)]`; no reducedness or normality assumption on T. |
| T reduced | `IsReduced T` is the first conclusion in that smooth clause. |
| Extended centre remains nowhere dense | `Dense ((J.comap h).support.compl : Set T)`. |
| Canonical normalization comparison is an isomorphism | A unique n has the normalization square equation, and every such n satisfies `IsPullback n T.fromReducedNormalization S.fromReducedNormalization h`. Equivalently the unique arrow into `pullback S.fromReducedNormalization h` induced by n and nu_T is an isomorphism, with both projections prescribed. |
| Canonical normalized-blowup comparison is an isomorphism | A unique b has `b ≫ J.normalizedBlowupMap = (J.comap h).normalizedBlowupMap ≫ h`; every such b makes the analogous blowup square `IsPullback`. This is exactly the canonical isomorphism B_(J O_T)(T) to B_J(S) times_S T, with both projections fixed. |
| Induced normalized-blowup map smooth | `Smooth b` in the same clause, for the uniquely determined comparison's first projection b. |
| Normalization isomorphism on regular S | `IsRegularScheme S → IsIso S.fromReducedNormalization`, using the recorded locally Noetherian regular-scheme definition. |
| B_(O_S)(S) = S^nu | Unique isomorphism from `(⊤ : S.IdealSheafData).normalizedBlowup` to Snu whose composite to S is its structural map. |
| This equals S if S normal | Stalkwise normality implies both `IsIso S.fromReducedNormalization` and `IsIso (⊤ : S.IdealSheafData).normalizedBlowupMap`. |
| Normalization identity compatibility | Any normalization endomap whose composite with nu_S is nu_S is `𝟙 _`. This is the identity comparison under the usual identity fibre-product identification. |
| Normalized-blowup identity compatibility | For `hK : J.comap (𝟙 S) = K`, any comparison b over S equals the canonical `eqToHom` of the equality K = J. This includes the literal extended centre and its equality transport, using `J.comap_id`. |
| Normalization composition compatibility | For composable smooth g and h and their three uniquely characterized normalization maps, `n₂ ≫ n₁ = n₃`. All three commuting equations are explicit. |
| Normalized-blowup composition compatibility | For the three comparison maps, `b₂ ≫ b₁` equals the direct map b₃ after `eqToHom (congrArg normalizedBlowup (hK.symm.trans (J.comap_comp g h).symm))`. Thus no equality of iterated and direct ideal extension is assumed definitionally. K and hK allow any transport of the iterated extended centre, including K equal to the iterated or direct centre. |

The pullback-square presentation uses the standard categorical equivalence between an
`IsPullback` square and invertibility of its induced arrow to the chosen fibre product.
It gives the actual canonical comparison, with the map to T equal to the structural map;
it is stronger than merely asserting that the underlying schemes have some isomorphism.
Here it is exactly the canonical comparison-isomorphism clause in the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization` and
  `Scheme.fromReducedNormalization`; read the full component construction and its docstrings.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup` and `blowupMap`;
  read the gluing-data construction and the structural-map definition.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`; the normal
  domain convention also uses `IsDomain`. Read `Localization.AtPrime` in its Basic module;
  no localization predicate is needed here since local rings themselves are normal domains.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, defined as
  `IsLocallyNoetherian S ∧ IsRegular S` using the upstream stalkwise class.
- Ideal extension and identity/composition use Mathlib `IdealSheafData.comap`, `comap_id`,
  `comap_comp` in `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`.
- Invertibility is the existing `IdealSheafData.IsInvertible` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`: locally generated by a
  nonzerodivisor. It is invertibility of the extended ideal, not of an arbitrary module.
- `genericPoints` is Mathlib's set of generic points of irreducible components from
  `Mathlib.Topology.Sober`.

The recorded proof modules are imported without `public`: blowup `InvertibleCenter`,
`Principalization`, `BlowupUniversal`; `NormalizationDominantLift`,
`RegularNormalDecomposition`; upstream `Geometrically.Reduced` and `Morphisms.SmoothFiber`;
and Mathlib `Morphisms.UniversallyOpen`. The normalization-existence proof dependency is
already publicly imported by `ReducedNormalization`. Smooth-flat and local finite
presentation are in the already imported Mathlib smooth module. Each proof step of the
node is written in the main theorem's docstring, including finiteness, density,
normalization lifting, the two-sided comparison, smooth pullback, functoriality, and
unit/regular cases.

Edge cases checked:

- Empty S and empty smooth T: no `Nonempty`, integral-scheme or nonzero-ideal assumption
  was added; normality is pointwise and the component coproduct can be empty. Density of
  the complement and the dense-open-isomorphism clause make sense on the empty scheme.
- J = O_S: the empty centre is allowed and its normalized blowup is identified with Snu,
  rather than with a nonnormal S. The additional normality implication identifies S only
  in the normal case. J = 0 on a nonempty reduced scheme fails the required dense-complement
  hypothesis, as it should.
- Reducible S and a normal source Y with many components: `genericPoints` refers to all
  irreducible components; no integral replacement of S or Y is made.
- Normal singular S: the unit case uses normality, whereas the separate regular clause
  uses `IsRegularScheme`. It never asserts that a normal scheme is regular.
- The centre (x^2,y^3) on Spec Q[x,y]: no affine integral-closure/fraction adjunction
  identity is asserted; the comparison over Snu is characterized by universal properties.
- Smooth maps need not be surjective. The nowhere-dense conclusion concerns their own
  extended centre and includes empty fibres and an empty source.
- Identity and two-step smooth maps: centre equality is transported explicitly; no
  definitional identification of `comap (g ≫ h)` with iterated comap is used.
- Arbitrary scheme universe: the rational base is lifted into u, and the normal test
  scheme Y has the same universe as S. There is no smaller independent test universe.

Searches (all through the authorized NX/item wrapper or direct read-only rg):

- LeanFinder: `Normalized blowups commute with smooth base change and are final among normal
  schemes with invertible extended ideal`. Eight hits: relative `Scheme.Hom.normalization`,
  `normalizationDesc`, `fromNormalization`, `toNormalization`, normalizationDiagramMap and
  related identities. None gives the normalized-blowup statement.
- Loogle: `"normalization", "blowup"`. Zero hits.
- LeanSearch: `Normalized blowup of a reduced finite type scheme universal property smooth
  base change`. Eight hits: stability of smoothness under base change, relative
  normalization and its factorization identities, and universally closed base change.
  None gives the normalized-blowup calculus.
- Mathlib grep wrapper: `normalized.*blow|blow.*normalization|normalization.*blow`.
  One unrelated ITauto tactic comment, no mathematical declaration.
- Direct rg in upstream `WeilConjectures/` and the project's `lean/Sheaf/` for
  `normalizedBlow`, `normalized_blow`, `reducedNormalization`,
  `fromReducedNormalization`, and `normalizedBlowup_calculus`: componentwise
  normalization and field-change theorems exist; no normalized-blowup construction or
  calculus declaration. Direct search for the item id upstream also had no match.
- Direct rg in upstream ideal and blowup modules found the reusable `blowup`, `blowupMap`,
  `IsInvertible`, `comap`, `comap_id` and `comap_comp` interfaces used here.

No statement dispute or node fault was found. The only postponed proof is the named
`normalizedBlowup_calculus`, matching this DAG node.

Validation: the module compiled through `scompile.py NX lem-trf-normalized-blowup-calculus`
in both its sandbox and library-module form with no errors or warnings. Only the prescribed
wrapper is used; no global build, direct git command, or shared-source edit was made.

## Second reading by NX

A separate clause-by-clause reread was performed by the delivering worker with the node,
the Lean file and the ILO source open. No additional agent was started, as the dispatcher
brief explicitly forbids that; the maintainer's independent review remains the independent
reader. The table above records the result of this reread rather than claiming a second
agent's review.

The reread checked every hypothesis: reduced S, finite type over Q in an arbitrary universe,
coherent J and nowhere dense zero scheme; and every conclusion: normal/reduced/finite-type B,
surjectivity and componentwise birationality, finality including its object conditions,
automorphism rigidity, the comparison over Snu, reducedness of smooth T, both canonical
pullback comparisons, smoothness of the induced map, preservation of density, both identity
and composition equations, and regular/normal/unit-ideal cases. The unique n over Snu is
explicit, so the comparison over the normalization has the correct base. Both pullback
squares fix both projections, and centre transports in the last clauses use the actual
`comap_id` and `comap_comp` equalities. No mismatch requiring a node correction or dependency
repair was found. Explicit direct imports for the reduced-scheme and integrally-closed
predicates were added during this pass; no signature changed.
