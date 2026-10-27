## Worker report

This repaired stage-2 packet states `lem-sfb-stable-pointed-isom-finite` as
`AlgebraicGeometry.MultipointedPair.exists_finite_unramified_unorderedIsom` in
`Sheaf.AlgebraicGeometry.StablePointedIsomFinite`. Its proof is `sorry`, with the complete
DAG proof plan in its docstring. The only new definition node is
`def-sfb-unordered-pointed-isom`, whose four declarations have real data. The live
`def-sfb-stable-pointed-curve` record and module are preserved: neither file is delivered.
The item's natural-language statement and proof are unchanged; only `lean` and the three
added `stmt_deps` differ from the live node.

Source read: de Jong, *Families of curves and alterations* (1997), §3.8, last paragraph,
printed pp.608–609, publisher PDF https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf
(PDF pages 10–11). The paragraph uses the finite unramified unordered Isom scheme and
normality to extend the prescribed generic action. The source explicitly allows the
sections to be nonordered. The present statement includes every generic isomorphism,
without an identity condition.

Clause-by-clause rendering, using the supplied live stable-curve definition:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Field k | `{k : Type u} [Field k]` |
| Finite-type k-scheme S | `{S : Scheme.{u}} [S.Over (Spec (.of k))]`, with `LocallyOfFiniteType` and `QuasiCompact` on its structural map |
| Two families W and W' over S | `{W W' : Scheme.{u}} (f : W ⟶ S) (f' : W' ⟶ S)` |
| A finite number n of sections, including zero | `(n : ℕ)`, `s : Fin n → (S ⟶ W)` and `s' : Fin n → (S ⟶ W')` |
| Sections of each family | `hs : ∀ i, s i ≫ f = 𝟙 S` and `hs' : ∀ i, s' i ≫ f' = 𝟙 S` |
| Stable pointed curves | `hP : IsStablePointedCurve f s hs` and `hQ : IsStablePointedCurve f' s' hs'`, exactly the landed dependency predicate |
| Projectivity | The `IsProjectiveBundle f` conjunct of the live predicate, using a closed immersion into the projective bundle of a finite-type quasi-coherent module; the rejected H-projective replacement is removed |
| Flatness and finite presentation | `Flat f` and the predicate's `∃ hfp : LocallyOfFinitePresentation f, ...`; projectivity supplies quasi-compactness and separatedness for finite presentation |
| Connected nonempty nodal geometric fibres | `HasNodalGeometricFibres f`, tested over every `Ω : Type u` with `Field Ω`, `IsAlgClosed Ω`, and every `Spec Ω ⟶ S`; its `ConnectedSpace` conjunct includes nonemptiness |
| Completed local ring at each nonsmooth point | The live nodal predicate uses `Nonempty (AdicCompletion ... ≃+* (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}))` |
| Reduced, pure dimension one geometric fibres | `IsReduced (pullback f a)` and `(pullback f a).IsPureDimension 1` for every algebraically closed Ω and every geometric point a |
| Disjoint sections in the relative smooth locus | `Pairwise (fun i j ↦ Disjoint (Set.range (s i)) (Set.range (s j)))` and `∀ i, Set.range (s i) ⊆ f.smoothLocus` in the live predicate |
| Canonical normalization of each component | `Scheme.normalizedComponentMap` from the live dependency, through the reduced irreducible component and its existing normalization |
| Genus on the normalization over Ω | `Scheme.normalizedComponentGenus (pullback.snd f a) Z`, defined using the composite structural morphism to `Spec Ω` and `Scheme.arithmeticGenus` |
| Special points are nodes or markings, counted on the normalization | The inverse image under `normalizedComponentMap` of the nonsmooth locus union `⋃ i, Set.range (f.baseChangeSection (s i) (hs i) a)` |
| Three special points for genus zero; one for genus one | The two implications with lower bounds `3 ≤ ...encard` and `1 ≤ ...encard` in the live predicate; no added condition in higher genus |
| Underlying pair with the actual marked union | `ofSections f s hs`: curve `Over.mk f`, marking `Over.mk (Sigma.desc (fun _ : Fin n ↦ 𝟙 S))`, inclusion `Over.homMk (Sigma.desc s)`; its commutativity proof is constructed from `hs` by the coproduct universal property |
| Unordered marking isomorphisms | `UnorderedIsom (ofSections f s hs) (ofSections f' s' hs')`, an isomorphism of the inclusion arrows in `Arrow (Over S)`; no equation is imposed on any individual label |
| Preservation as closed subschemes | The arrow isomorphism includes a marking-scheme isomorphism commuting with the curve isomorphism, hence preserves its full scheme structure; for the disjoint sections of a projective family the inclusion is a closed immersion |
| Representing S-scheme I | `∃ I : Over S, ... ∃ e, IsUniversalUnorderedIsom ... I e` |
| Every S-test scheme, with canonical pullback | The universal-property predicate quantifies over every `T : Over S` and every test isomorphism and gives `∃! a : T ⟶ I`; its two equations use `parameterMap`, literally `pullback.map` induced by the identity and `a.left` |
| Finite and unramified over S | `IsFinite I.hom ∧ IsUnramified I.hom`; the latter is the recorded locally-finite-type/open-diagonal conjunction |
| S integral and normal for extension | `∀ [IsIntegral S]`, followed by `∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)` |
| Each generic isomorphism extends uniquely | `Function.Bijective` of the canonical `((Over.pullback (S.fromSpecResidueField (genericPoint S))).mapArrow).mapIso` on global unordered isomorphisms |
| The generic isomorphism need not be identity | The restriction map has all global isomorphisms as domain and all generic isomorphisms as codomain; no identity condition occurs |

In the universal-property predicate the two equations are equality of the curve and
marking morphisms after projecting to the original target pair. Both morphisms already
have fixed maps to T. The fibre-product uniqueness property therefore makes these
equations precisely equality with the pullback of the universal isomorphism. This gives
the representing bijection for the canonical pullback functor, rather than an arbitrary
bijection with parameter maps.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedCurve`:
  `AlgebraicGeometry.IsStablePointedCurve`, `Scheme.normalizedComponentMap`, and
  `Scheme.normalizedComponentGenus`. These retain their live signatures and definitions.
- Its defining modules `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`:
  `IsProjectiveBundle`; `Sheaf.AlgebraicGeometry.NodalGeometricFibres`:
  `HasNodalGeometricFibres`; `Sheaf.AlgebraicGeometry.PureDimension`:
  `Scheme.IsPureDimension`; `Sheaf.AlgebraicGeometry.ReducedNormalization`:
  `Scheme.reducedNormalizationComponent` and the existing normalization map;
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: `Scheme.arithmeticGenus`;
  `WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection`:
  `Scheme.Hom.baseChangeSection`.
- `Sheaf.AlgebraicGeometry.SemistableMultipointedPair`: `MultipointedPair` and
  `MultipointedPair.baseChange`. No geometric predicate from this module is substituted
  for the stable-curve predicate.
- `Mathlib.CategoryTheory.Comma.Arrow`: `Arrow`, `Arrow.mk` and `Functor.mapArrow`;
  `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`;
  `Mathlib.CategoryTheory.Limits.Shapes.Products`: `Sigma.desc`, `Sigma.hom_ext`,
  `Sigma.ι_desc`; the existing `Over.homMk` packages the constructed marking arrow.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.AlgebraicGeometry.Properties`:
  `IsIntegral`, `IsReduced`; `Morphisms.Proper`, `.Separated`, `.UniversallyClosed`:
  `IsProper`, `IsSeparated`, `UniversallyClosed`; `.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `.Irreducible`, `.Reduced`:
  `GeometricallyIntegral`, `GeometricallyIrreducible`, `GeometricallyReduced`, as the
  node's contextual notions, without imposing integrality on reducible fibres;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`;
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective` remains
  contextual vocabulary, rather than replacing projective-bundle stability.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `.Integral`, `.UnderlyingMap`:
  `IsFinite`, `IsIntegralHom`, `Surjective`; `.Flat`, `.FinitePresentation`, `.Smooth`,
  `.Etale`, `.ClosedImmersion`: `Flat`, `LocallyOfFinitePresentation`, `Smooth`,
  `Etale`, `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: `Scheme.functionFieldOfComponents`;
  the integral-base generic fibre is equivalently the existing `Scheme.functionField`,
  its generic stalk, using `Scheme.fromSpecResidueField` at `genericPoint S`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`; `Sheaf.FieldTheory.FieldTower`:
  `FieldExtension.degree`, contextual field-extension vocabulary.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.map`; `Mathlib.RingTheory.AdicCompletion.Basic`
  and `.Algebra`: `AdicCompletion`; `Mathlib.RingTheory.MvPowerSeries.Basic`:
  `MvPowerSeries`; `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `IsUnramified`.

The plain proof imports and proof docstring are retained from the returned packet, which
the return explicitly found faithful. They include the recorded finite-birational-normal
isomorphism, relative-ampleness base change, semistable marked base change, reduced induced
closed subscheme, unramified quasi-finiteness, proper locally-quasi-finite finiteness and
immersion permanence. The six proof prerequisites with no recorded declaration remain
named in the natural-language proof; they are not added as hypotheses.

Edge cases checked:

- n = 0: `Fin 0` gives the empty marking coproduct; the unique empty marking
  isomorphism is included. Unmarked stable curves of higher genus are allowed.
- Empty S: every fibre condition is vacuous, the marking and curve over S are empty,
  and the representing parameter scheme is empty. The integral-base clause does not
  impose any extension demand on the empty base.
- Empty geometric fibres over a nonempty base fail `ConnectedSpace`, even though the
  pure-dimension predicate by itself is vacuous on an empty scheme.
- A rational smooth component needs three markings and a genus-one smooth component
  needs one; self-nodes contribute both branches on the canonical normalization.
  Reducible fibres and every characteristic remain allowed.
- On a disconnected test scheme, an isomorphism of the finite coproduct marking schemes
  may use different permutations on different clopen pieces. No global permutation is
  chosen or required in the signature.
- On a nonreduced test scheme the arrow isomorphism preserves the scheme marking,
  not just its underlying set. Monomorphy of the inclusion determines its marking map.
- The extension clause includes nonidentity generic automorphisms and isomorphisms
  between different families. All test schemes and algebraically closed fields use
  the explicitly bound scheme universe u, with no smaller independent test universe.

Searches retained from the original packet (before adopting NO's landed stable-curve
interface). The old absence-of-stability conclusion below is superseded by the live
`def-sfb-stable-pointed-curve` record, which this repair uses directly:

- `msearch.py leanfinder`: “The isomorphism functor of stable pointed curves with
  unordered markings is finite unramified and generic isomorphisms extend over a normal
  integral base”. Eight general unramified/etale scheme-property hits, none the theorem.
- `msearch.py loogle`: `"AlgebraicGeometry", "Isom"`. Twelve scheme/sheafed-space
  isomorphism constructors and properties, none this relative pointed Isom functor.
- `msearch.py grep`: `stable.*curve|pointed.*curve|marked.*curve` in Mathlib's
  AlgebraicGeometry. No hits.
- For the stable-curve notion: LeanSearch on projective flat nodal pointed curves with
  positive logarithmic degree, and LeanFinder on the genus-zero and genus-one special
  point inequalities. The former returned generic smoothness/flatness and unrelated smooth
  sections; the latter returned Weierstrass predicates. Neither defines this notion.
- For unordered isomorphisms: LeanSearch on universal unordered marked isomorphisms and
  LeanFinder on their universal parameter. Returned generic categorical isomorphism and
  scheme-property results; none define the pointed Isom functor.
- Mathlib grep `StablePointed|Unordered.*Isom|stable.*pointed|unordered.*marked` in
  AlgebraicGeometry: zero hits. The same search in both project roots finds relative
  stable-modification material and theorem proof references. Those definitions only rule
  out certain contracted rational components; they neither impose genus-one stability nor
  count branches on normalization, and are not the stable-curve predicate here.
- `rg` for the exact proposed declaration names across Mathlib and both project roots
  found no collisions. An unrelated `parameterMap` lives in a different namespace.
- `rg` for the item id in WeilConjectures found none; in Sheaf it finds only the proof
  docstring of EquivariantSingleCurveNodalReduction, not a declaration of this item.
- DAG grep and `tools/blueprint_refs.py search 'stable pointed'` / `search 'unordered'`
  find theorem nodes and relative-modification definitions, but no definition node of
  stable n-pointed curves or the unordered marked Isom universal property. The ancestor
  query returns None, preserved in the new definition nodes' blueprint records.

The retained raw search results are stored in the new node's `mathlib_searches`.
The repair additionally searched Mathlib with `msearch.py grep` for
`ofSections|UnorderedIsom|StablePointed` in AlgebraicGeometry: its five hits are
unrelated Zariski presieve-of-sections declarations. A project search for `ofSections`,
`Sigma.desc s` and coproducts indexed by `Fin n` found coordinate-cover constructions,
splitting lemmas and unrelated finite coproducts, but no canonical conversion of labelled
curve sections to `MultipointedPair`. The existing raw pair and base change are reused.
The live `StablePointedCurve` source was also read using `scompile.py --source`; it agrees
with the read clone and is usable as supplied.

## Repair of return L at 0708d470d200

H13: Removed both sandbox files for `def-sfb-stable-pointed-curve`. The delivery therefore
cannot replace NO's dependency record or module, or delete `IsStablePointedCurve`,
`Scheme.normalizedComponentMap`, or `Scheme.normalizedComponentGenus`. The supplied live
`StablePointedGenericExtension` consumer still uses exactly that preserved interface.
The removed file in the saved packet contained `IsStableNPointed`; it is no longer part
of the delivery and is not imported or declared anywhere in this packet.

H4: Replaced the theorem's pair-stability hypotheses with the two exact landed
`IsStablePointedCurve f s hs` / `IsStablePointedCurve f' s' hs'` hypotheses, including
projective-bundle projectivity and geometric tests over every algebraically closed Ω.
The owned `def-sfb-unordered-pointed-isom` now constructs `ofSections`, the pair
`(Over.mk f, ∐_{Fin n} S, Sigma.desc s)` requested in the return. This construction forgets
labels only for the isomorphism type; it introduces no second stability predicate and
needs no equivalence theorem. `UnorderedIsom`, `parameterMap`, the universal-property
predicate, finite/unramified conclusion and bijective generic restriction remain as in
the accepted part of the returned packet, with the canonical constructed pairs supplied.

Both repaired files compiled through `scompile.py` separately in dependency order against
the published live library, without errors or unexpected warnings. The only postponed
theorem is `exists_finite_unramified_unorderedIsom`. No source statement is corrected and
no STATEMENT-DISPUTED issue remains.

## New nodes

`def-sfb-unordered-pointed-isom`, module `Sheaf.AlgebraicGeometry.UnorderedPointedIsom`,
defines the canonical underlying pair of labelled sections (`ofSections`), isomorphisms
of the two marking arrows (`UnorderedIsom`), the canonical `parameterMap` and the
`IsUniversalUnorderedIsom` predicate. All four declarations belong to this one notion
and definition node. Source: de Jong §3.8, pp.608–609. The retained LeanSearch,
LeanFinder, Mathlib, project, DAG and blueprint search results find the general category
infrastructure and relative stable-modification material but no definition of this
unordered pointed Isom functor. `MultipointedPair` and its base-change construction are
reused directly. The stable-curve definition belongs to NO's already landed node and
is not a new node of this delivery.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
