## Worker report

Stage 2, Q13, `lem-trf-marked-controlled-blowup-charts`. The delivery contains three
modules and two new definition nodes. The item module is
`Sheaf.AlgebraicGeometry.MarkedControlledBlowupCharts` and its four theorems all have
exactly `by sorry` as their proofs. The two definitions have actual data and no sorry.
There is no correction to the item's mathematical statement and no disputed statement.

I read the item, its complete proof, every recorded statement dependency, the stage-2
brief, the delivery error list H, the worker contract, and the source declarations and
docstrings. I read Stacks `divisors.tex`, `lemma-blowing-up-affine` (0804), and
`more-morphisms.tex`, `lemma-etale-local-structure` (0FUE),
`remark-relative-blowup`, and `lemma-blowup` (0FUT). The polynomial chart calculation
in those sources is pulled back along an actual étale map; an étale coordinate ring
is never assumed to be a polynomial ring.

The geometric and controlled-ideal assertions are in
`AlgebraicGeometry.smooth_marked_controlled_blowup`; geometric base change is in
`AlgebraicGeometry.smooth_marked_controlled_blowup_baseChange`; coordinate charts and
monomial exponents are in `AlgebraicGeometry.etale_coordinate_marked_blowup_charts`;
and compatibility of the actual fraction maps and division with smooth coefficient
change is in `AlgebraicGeometry.marked_blowup_chart_smooth_baseChange`.

The center is represented by `I : N.IdealSheafData`. Thus its scheme is
`I.subscheme` and its closed immersion in `N` is `I.subschemeι`. Its ambient ideal is
`I.map j`, the ideal of the composite closed immersion into `Z`. This is the same
center, rather than a second center chosen independently. The ambient modification
is `(I.map j).blowup` with its actual `blowupMap`. The support is the existing
scheme-theoretic `(I.map j).strictTransform j`. Controlled ideals are written on
`I.blowup`; the theorem gives its unique isomorphism over `N` with that exact support.
The direction is `I.blowup ≅ (I.map j).strictTransform j`, which is the inverse of
writing the support as `Bl_C N`. No set-theoretic substitute for the support is used.

Hypothesis-by-hypothesis correspondence:

| Node hypothesis | Lean representation |
| --- | --- |
| finite-type Q-schemes | `p : Z ⟶ Spec (.of (ULift.{u} ℚ))`, `[LocallyOfFiniteType p]`, `[QuasiCompact p]`; the closed subscheme `N` is automatically of finite type |
| smooth ambient and smooth embedded scheme | `[Smooth p]`, `[Smooth (j ≫ p)]` |
| closed pair | `j : N ⟶ Z`, `[IsClosedImmersion j]` |
| coherent ideal on N | `J : N.IdealSheafData`, `hJ : Scheme.Modules.IsQuasiCoherentFiniteType J.toModules`; on a smooth Q-scheme, locally Noetherian, the recorded coherence theorem identifies this with coherence |
| positive marking | `c : ℕ`, `hc : 1 ≤ c` |
| smooth closed center in N | `I : N.IdealSheafData`, `[Smooth (I.subschemeι ≫ j ≫ p)]`; the subscheme inclusion is already a closed immersion |
| order at every center point | `horder : ∀ x : N, x ∈ I.support → HilbertSamuel.stalkIdeal J x ≤ IsLocalRing.maximalIdeal (N.presheaf.stalk x) ^ c` |
| finite ordered SNC boundary | `E : List Z.IdealSheafData`, `hE : IsStrictNormalCrossingsBoundary E.prod` |
| transverse to N and adapted to C | `hflag : HasEtaleCoordinateFlag p j.ker (I.map j) E`: affine étale neighbourhoods with an actual étale map to affine space, normal coordinate set `B`, center coordinate set `A` with `B ⊆ A`, and distinct boundary coordinate labels outside `B` |
| centers inside old boundary components permitted | the definition imposes no disjointness between `A` and boundary coordinates; only the normal set `B` is disjoint |
| Z' is the blowup and N' is the scheme-theoretic strict transform | the canonical existing terms `(I.map j).blowup` and `(I.map j).strictTransform j` occur in the conclusion; no arbitrary replacement or additional universal-property hypothesis is supplied |
| F is the exceptional divisor | `(I.map j).comap (I.map j).blowupMap`, and intrinsically `I.comap I.blowupMap` |

The transformed list is named by an arbitrary binder `E'` and its exact defining
equality `hE'`. This is universally quantified notation for the stated ordered list,
not an additional mathematical assumption: its right hand side is an explicit list.
Each old entry is the kernel of the actual strict-transform inclusion, in its original
order, and the final entry is the extended center ideal. An empty strict transform is
represented by the unit ideal, that is, an empty divisor at that label. Deleting
unit entries gives the usual list with empty transforms omitted. Retaining these empty
labels makes arbitrary non-surjective base change literal list equality. The node's
proof explicitly permits disjoint exceptional components to share the new final label.
The existing SNC predicate is always applied to the product, so empty labels do not
create divisor components.

Clause-by-clause correspondence:

| Node conclusion | Lean representation |
| --- | --- |
| `J ⊆ I(C,N)^c` | first conjunct `J ≤ I ^ c` |
| Z' smooth and finite type | `Smooth`, `LocallyOfFiniteType`, and `QuasiCompact` of `(I.map j).blowupMap ≫ p` |
| N' smooth and finite type | the same three properties of `strictTransformToSource j ... ≫ j ≫ p` |
| canonical support identification with `Bl_C N` | `∃! e : I.blowup ≅ (I.map j).strictTransform j, e.hom ≫ strictTransformToSource ... = I.blowupMap`; agreement over N fixes the identification uniquely |
| new boundary SNC | `IsStrictNormalCrossingsBoundary E'.prod` |
| new boundary transverse to N' | `HasEtaleCoordinateFlag ((I.map j).blowupMap ≫ p) (strictTransformMap j ...).ker ⊤ E'`; the center argument `⊤` is the empty center, and the first ideal is the actual ideal of N' in Z' |
| affine charts on surviving support | the third theorem uses the actual `AffineBlowup.chartRing I (u i)` and the degree-one `Proj.basicOpen` chart cover; the canonical support isomorphism gives precisely the charts of N' |
| exceptional coordinate `e = u_i` | `v i = algebraMap R _ (u i)` |
| ratios for other center coordinates | `(v j : Localization.Away (u i)) = AffineBlowup.chartFraction (u i) 1 (u j)` for `j ∈ A`, `j ≠ i` |
| unchanged coordinates | `v j = algebraMap R _ (u j)` for `j ∉ A` |
| these are étale coordinates | the polynomial evaluation map on `v` is `.Etale`; the input evaluation on `u` is also `.Etale` |
| the original coordinates pull back by the advertised substitution | the identity `algebraMap ... (u j) = if j ∈ A ∧ j ≠ i then v i * v j else v j` |
| components of N contained in C disappear | `∀ D ∈ irreducibleComponents N, D ⊆ I.support → I.blowupMap ⁻¹' D = ∅`, transferred to N' by the specified isomorphism |
| ambient components contained in C disappear | the identical assertion for `Z`, `I.map j`, and its blowup map |
| controlled transform is a regular ideal | `controlledTransformIdeal` is constructed as a quasi-coherent ideal sheaf, not a meromorphic object; `∀ K, K * (I.comap I.blowupMap)^c = J.comap I.blowupMap ↔ K = controlledTransformIdeal ...` gives the unique division by the exceptional power |
| controlled transform is coherent | `Scheme.Modules.IsQuasiCoherentFiniteType (controlledTransformIdeal ...).toModules`, equivalent to coherence here |
| affine division is `e^(-c)` | for every affine open and every generator `e` of the exceptional ideal, its ideal of sections is `Submodule.colon (total ideal) {e ^ c}` |
| the exceptional equation is a nonzerodivisor locally | `(I.comap I.blowupMap).IsInvertible`, using the recorded effective-Cartier-ideal notion |
| nonzero on each surviving component | nonzero stalk ideal at every generic point of every irreducible component of N implies the same assertion on `I.blowup`; smoothness makes this equivalent to not being the zero ideal on a component |
| controlled ideal commutes with smooth base change | second theorem's first equality, along the named `I.blowupFlatBaseChangeIso (pullback.fst j g)` and the actual pullback projection |
| scheme-theoretic support comparison commutes with smooth base change | second theorem gives `q` with a cartesian `IsPullback` square over the canonical ambient blowup comparison, plus equality of its map to the old N with the base-changed source projection |
| ordered boundary commutes with smooth base change | literal list equality in the second theorem, strict-transform kernels at each old label and the final exceptional ideal |
| coordinate formulas commute with smooth base change | fourth theorem uses the existing canonical `strictChartMap` on `S ⊗[R] R[I/a]`, proves it bijective, and states its exact formula on every fraction; this covers denominator, ratios, unchanged coordinates and all ring expressions in them |
| ideal division commutes with smooth coefficient change | fourth theorem states that the old colon mapped along the canonical chart coefficient map is the new colon |
| monomial ideal and coordinate center | third theorem quantifies `T`, `a`, `c` with `A ⊆ T`, `1 ≤ c`, `c ≤ ∑ j ∈ A, a j`; the original ideal is `Ideal.span {∏ j ∈ T, u j ^ a j}` |
| new exceptional exponent | the controlled ideal is generated by `v i ^ ((∑ j ∈ A, a j) - c) * ∏ j ∈ T.erase i, v j ^ a j` |
| all other strict exponents unchanged | the product over `T.erase i` has exactly exponent `a j`; `v j` is a ratio on center coordinates and unchanged elsewhere |
| strict transform of `V(u_i)` absent | the scheme-theoretic saturation in the third theorem is `⊤` if `j = i` |
| other strict transforms | the same saturation is `Ideal.span {v j}` for `j ≠ i`; the saturation is the contraction of the extended ideal in localization away from `v i`, hence scheme-theoretic |
| outside the center the marked pair is unchanged | `IsIso (I.blowupMap ∣_ I.support.compl)`, equality of controlled and total ideals on that open, and equality of ordered old boundary pullbacks with the transformed list restricted to the ambient complement, with final empty label `[⊤]` |

Dependency declarations used, after reading their actual signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `WeilConjectures.Blowup.Gluing`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup`, `.blowupMap`.
- `WeilConjectures.Compactification.StrictTransform`:
  `AlgebraicGeometry.strictTransform`, `strictTransformMap`, `strictTransformToSource`,
  and `Scheme.IdealSheafData.strictTransform`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`:
  `AlgebraicGeometry.Scheme.Hom.ker`, `Scheme.IdealSheafData`, its complete lattice,
  products and powers; the actual closed-immersion kernel and actual ideal data are used.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `IdealSheafData.toModules`.
- `Sheaf.AlgebraicGeometry.MarkedIdealOrder`: `AlgebraicGeometry.HilbertSamuel.stalkIdeal`;
  its existing DAG node is added to the item's statement dependencies.
- `WeilConjectures.Blowup.Affine.ChartAlgebra`: `AlgebraicGeometry.AffineBlowup.chartRing`,
  `.chartFraction`, with the existing chart-ring definition node added to statement dependencies.
- `WeilConjectures.Blowup.FlatBaseChange`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowupFlatBaseChangeIso`.
- `WeilConjectures.Blowup.Affine.StrictTransformChart`:
  `AlgebraicGeometry.AffineBlowup.BaseChangeChart`, `.strictChartMap`.
  The latter's definition node is closed upstream in its `lean_audit.slopmaster2.decls`
  and needs no replacement construction. Its explicit current-server binding is supplied
  below under dependency modules.
  Both existing definition nodes are added to statement dependencies.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`,
  `.homOfVector`, using coordinate type `ULift.{u} (Fin n)`.
- `Mathlib.RingTheory.Ideal.Colon`: the existing `Submodule.colon`.

Published proof dependencies are imported privately, including the smooth normality and
component lemmas, smooth-pair regular equations, associated graded polynomial theorem,
strict-transform/blowup comparison, finite chart cover, chart regular-sequence presentation,
principalization, smooth descent, blowup properness, regular-intersection descent,
coherence on locally Noetherian schemes, smooth regularity, and étale local normal form.
Statements have public imports and module mode throughout. The source's withdrawn compact
object example was read together with its current node record and actual upstream example.

Edge cases checked before and during drafting:

1. `N`, `Z`, or the center empty: no `Nonempty`, `IsIntegral`, connectedness or dimension
   restriction is imposed. The affine chart cover permits an empty index set.
2. Center equal to a component of N or Z: `I = ⊥` on that component, the blowup has
   no positive-degree Rees points, and the explicit component-deletion assertions apply.
3. Empty center: `I = ⊤`, exceptional ideal is the unit ideal and division is ordinary
   pullback; the complement is the entire scheme.
4. Zero ideal J: the controlled ideal on every nonempty surviving smooth component is
   zero, and the generic-nonzero implication is simply not applicable. On a deleted
   component the order condition forces zero without a special extra assumption.
5. Positive marking at `c = 1`, and monomial equality `sum a_j = c`: the exceptional
   exponent is zero. Empty `A` produces an empty blowup and no chart assertion; for
   positive `c` the monomial sum condition is impossible. `T.erase i` includes no
   denominator factor and may be empty.
6. `n = 0`, the zero ring, empty boundary, absent labels and disconnected smooth
   schemes: all definitions and assertions retain these cases.
7. A center contained in one or several boundary components: their coordinates may
   belong to `A`; the denominator label disappears only from its own chart.
8. Smooth base change need not be surjective, connected or quasi-compact; the second
   theorem has only `[Smooth g]`, and retains the identity and empty-source cases.
9. Non-separated schemes are allowed. No separation hypothesis or global polynomial
   presentation is introduced.
10. All scheme/ring universes are explicitly `u`, with `ULift.{u} ℚ` providing the
    rational base and `ULift.{u} (Fin n)` the finite coordinate index. No universe is
    auto-bound, and no small index type suppresses a geometric case.

Searches actually run through `msearch.py` (full exact wrapper answers, dates and digests
are retained in both new nodes):

- LeanFinder: "Controlled transforms of coherent marked ideals under a smooth blowup
  with a normal crossings boundary, affine coordinate charts and monomial exceptional
  exponents". Eight general smooth/chart hits; no controlled-transform statement.
- Loogle: "AlgebraicGeometry.strictTransform, AlgebraicGeometry.Scheme.IdealSheafData.blowup".
  Zero hits; the public service does not know the project's strictTransform name.
- Mathlib grep: "controlledTransform|markedIdeal|blowup" in `AlgebraicGeometry`.
  Zero hits.
- LeanSearch: "A smooth closed flag and a labelled simple normal crossings divisor admit
  simultaneous etale coordinates". Eight generic smooth/étale presentation hits; no
  simultaneous flag with a boundary.
- LeanFinder: "Etale coordinate flag with a smooth closed subscheme, a smooth center
  inside it and labelled coordinate hyperplane boundary". Eight standard étale algebra
  hits; no matching predicate.
- Mathlib grep: "EtaleCoordinateFlag|controlledTransform|markedIdeal|HasAdaptedNormalCrossingsCenter".
  Zero hits.
- LeanSearch: "Controlled transform as the ideal quotient of the total transform of an
  ideal by a power of the exceptional ideal". Eight ideal quotient/cotangent/ramification
  hits; no quasi-coherent ideal quotient construction.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the new notion names and
  controlled/marked ideals, and `grep -rn` for this blueprint id in `WeilConjectures`:
  no exact declarations. Existing `HasAdaptedNormalCrossingsCenter` gives local regular
  parameters for one center only, not an embedded coordinate flag. Existing
  `HilbertSamuel.Step.Transforms` characterizes a controlled ideal by multiplication
  but does not construct the quotient.
- DAG searches and `tools/blueprint_refs.py search` for "etale coordinate flag",
  "smooth marked blowup", and "controlled transform ideal": zero matching blueprint
  nodes. The existing marked-ideal order node was found, read and reused.

Validation: every delivered file has compiled separately through `scompile.py`, including
preliminary compilation of sibling modules and compilation under its final module name.
No errors or warnings were reported. The final delivery dry run is recorded below.

## New nodes

`def-trf-etale-coordinate-flag` owns `Sheaf.AlgebraicGeometry.EtaleCoordinateFlag` and
`AlgebraicGeometry.HasEtaleCoordinateFlag`. It defines the simultaneous étale-coordinate
hypothesis appearing in the item's statement: nested coordinate ideals, distinct labelled
coordinate hyperplanes, and disjointness from the normal coordinates. Its sources are
Stacks 0FUE and the item's explicit simultaneous-coordinate hypothesis. It is a predicate
on the actual schemes and ideal sheaves, with actual étale maps, not an assumption that
an arbitrary ring is polynomial. The existing adapted-center predicate lacks the embedded
subspace and actual étale map. Searches above found no other node or declaration.

`def-trf-controlled-transform-ideal` owns `Sheaf.AlgebraicGeometry.ControlledTransformIdeal`
and `AlgebraicGeometry.controlledTransformIdeal`. Its actual construction is the supremum
of quasi-coherent ideals `K` with `K * (I.comap σ)^c ≤ J.comap σ`, in Mathlib's complete
lattice. On the blowup the theorem identifies it with unique division by the invertible
exceptional power, and its affine ideals with the existing colon operation. This directly
implements the item's proof step 7 and the controlled-transform formula in BMT 5.1--5.2.
It makes no choice from a mere existence theorem. The searches found ring quotient notions
and a relation characterizing transforms, but no existing quasi-coherent quotient
construction or definition node for it.

Both new nodes cite the existing definition nodes of every geometric notion they use,
carry the ancestor returned by `blueprint_refs.py ancestor`, preserve the item's chapter
and unit, and are directly cited by the item. The item additionally cites the existing
stalk-order, affine chart-ring and base-change chart-map nodes used by its signatures.
No existing dependency is redefined.

## Second reading by Q13

This is a separate reread by the same worker; the dispatcher explicitly forbids starting
other agents, and the maintainer performs the independent delivery review. I reopened the
node and all three module texts and checked the preceding two correspondence tables.

The second pass checked the direction of the support isomorphism, that its map lands over
the original N, and that smoothness and finite type are also asserted directly for the
scheme-theoretic strict transform. It checked that the ambient center is `I.map j`, not
an independent ambient ideal, and that arbitrary center-contained components disappear
rather than being excluded by a nowhere-dense hypothesis. It checked that the stalk
order hypothesis is on every point of the center, including generic points, with precisely
power `c` of the maximal ideal. Coherence uses the published finite-type predicate on a
locally Noetherian smooth scheme, not a new meaning of coherence.

For the new coordinate flag I made its global nesting explicit as `N ≤ C` (ideal
inclusion, hence the geometric inclusion is C inside N); no changes to the item's
statement were needed. The local `B ⊆ A` has the same geometric direction. The boundary
assignment is injective only on defined coordinate labels, so absent entries and an empty
boundary are possible. It is disjoint from `B`, with no disjointness condition on `A`,
which preserves centers lying in old boundary components.

The controlled ideal is an actual supremum. The global theorem identifies it by the
multiplication equation, including uniqueness, and the affine statement identifies its
sections with the colon by `e^c`. The component nonvanishing condition is about generic
stalk ideals, exactly equivalent to nonzero restriction on an integral smooth component;
it does not require every stalk to be nonzero as an extra assumption. The chart-ring
saturation is a kernel/contraction through localization and thus scheme-theoretic, and
the `i`-factor is removed from the strict product with `T.erase i`. The exceptional
exponent is precisely `sum_{A} a_j - c`, with the nonnegative-sum hypothesis present.

I also checked the smooth-base-change comparison map: the controlled equality uses the
existing named blowup isomorphism and projection, the support square is cartesian and
commutes over the source, and the boundary equality preserves every old label and adds
exactly the extended center ideal. The fourth theorem uses the canonical tensor-product
chart map already defined upstream and states its actual fraction formula; no arbitrary
comparison map is substituted. These checks found no remaining mismatch with the item.

The first complete `deliver2.py --no-push` passed compilation and server preflight
(commit `c3c52f99922`). The final cleanup places the colon import directly in the
item module that uses it, instead of exporting it through the ideal-quotient definition.
The final packet is checked again by the dry-run and delivery wrappers.

## Dependency modules

`def-nagata-strict-chart-to-extended-blowup-chart` receives a lean-only dependency
binding under §1(B), with `existing: true`; no replacement module is needed. The read
clone's audit names `AlgebraicGeometry.AffineBlowup.strictChartMap` upstream, but the
second server preflight did not recognize this node as a stated added prerequisite
without an explicit binding. The actual source definition in
`WeilConjectures.Blowup.Affine.StrictTransformChart` is exactly the node's canonical
map from `BaseChangeChart B I a = B ⊗[A] A[I/a]` to `B[IB/f(a)]`, restricting the
localization map and applying the tensor-product universal property. The source
`coe_strictChartMap_tmul` has the node's precise fraction normalization. This repair
sets only that dependency node's `lean` field, with an explanatory note; its statement,
Mathlib match and all other fields remain untouched. The module that uses the map
already imports its actual upstream module publicly.

On rereading this dependency binding, I checked both its source signature and the
fraction formula. It names the exact existing map used in the fourth theorem,
including the `a ∈ I` proof argument and the structural B-algebra map, with no
arbitrary choice or change of center. The final checks include a module-mode server
`#check` of this binding in addition to compiling each of the three delivered files.
