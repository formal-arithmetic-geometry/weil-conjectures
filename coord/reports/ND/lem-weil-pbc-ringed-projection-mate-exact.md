## Worker report

`lean/Sheaf/Paper/ProjectionMateExact.lean` states
`SheafOfModules.ringedProjectionMateExact`, with one postponed proof, `sorry`.
The natural statement is unchanged. The statement dependencies gain the two already
recorded nodes `def-weil-pbc-ringed-tensor-square-presentation` and
`def-weil-pbc-projection-formula-arrows`, whose actual public interfaces are used.
No dependency record is changed and no independent notion or new node is introduced.
The module's transparent abbreviations and two fully written predicates only expose
normalizations belonging to this theorem; all are listed in `lean.declarations`.

Hypotheses and objects, checked against the node:

- `Y X : RingedTensorCorner.{u,w}` carry small sites, their commutative ring sheaves,
  the existing module categories, derived categories with chosen Hom universe `w`,
  and derived tensor bifunctors. `mateModules` explicitly specializes the dependency's
  `ringedSiteModules.{u,u,u,u}`, and `mateDerived` is exactly `DerivedCategory`.
- `a : RingedTensorModel Y`, `b : RingedTensorModel X` identify those tensor bifunctors
  with the existing direct-sum total tensor on flat-term K-flat representatives.
  `mateFlat` is precisely the predicate in that recorded presentation. This is a
  choice of model for the node's derived tensor, not a new tensor operation.
- `e : RingedTensorEdge Y X` supplies the geometric inverse image, its right adjoint,
  finite-limit preservation, its algebraic lift and ring map, module pullback with
  its object and morphism formulas for scalar extension, its module adjunction, the
  total left-derived functor with its universal comparison `epsilon`, and a derived
  right adjoint with `derivedAdjunction`. As the presentation node specifies, any
  right-adjoint model identifies uniquely with derived direct image, compatibly
  with its adjunction; K-injective resolutions compute this model. There is no
  assumed flatness, properness, invertibility of the mate, or boundedness.

Every conclusion and normalization:

- The two existential `CommShift₂Int` structures provide coherent, natural shifts
  in BOTH tensor variables, with their signed interchange. `MateCanonicalShifts`
  identifies them with `CochainComplex.mapBifunctorShift₁Iso` (unsigned) and
  `mapBifunctorShift₂Iso` (the sign `(-1)^(np)` on first-factor degree `p`). Its
  equations use `a.representative`, `b.representative`, and `Q.commShiftIso`,
  so arbitrary shift structures cannot replace the canonical signed ones.
  Shift stability of the flat K-flat representatives is also explicitly included.
- The existential shifts of `e.left` and `e.right` are part of the conclusion.
  `NatTrans.CommShift e.epsilon ℤ` identifies the left shift with termwise pullback;
  `e.derivedAdjunction.CommShift ℤ` fixes the compatible right shift through the
  canonical unit and counit. Their `IsTriangulated` conclusions state exactness.
- For each object at each corner, the curried tensor functor and its flip are
  `IsTriangulated`: derived tensor is exact in each variable.
- `e.tensorComparison a b` is the already recorded, uniquely representative-normalized
  natural tensor isomorphism. No bare `Nonempty` isomorphism is chosen. The two
  equations indexed by `n U V` state its compatibility with first-factor and
  second-factor integer shifts separately.
- `mateUnitComplex` is the ring sheaf in degree zero, using `singleFunctor`, and
  `mateUnit` is its localization. The existential `unitL` identifies its pullback
  with the corresponding source unit. The existential right unitors `unitY` and
  `unitX` are normalized by `MateCanonicalUnit`: the unit complex is flat K-flat,
  and the representative unitor is multiplication on every `(n,0)` summand.
  The equation involving `mu`, `unitL`, and the right unitors states unitality.
- For each `E`, `alpha E` is a natural transformation from tensor with `e.right.obj E`
  to `e.left ⋙ tensor(E,-) ⋙ e.right`. Its components equal exactly
  `CategoryTheory.derivedProjectionFormulaMate`, whose definition is the adjunct
  of the canonical comparison followed by counit tensor identity.
- Exactness of `F` follows from the tensor conclusion; exactness of the composite
  `G` is also explicitly asserted in the clause for every `E`.
  `NatTrans.CommShift (alpha E) ℤ` states
  `alpha(P[n]) ≫ sG = sF ≫ alpha(P)[n]` for every integer, including `1`.
- The distinguished-triangle clause supplies a `Triangle` morphism with all three
  components equal to the components of `alpha`. Its third commutativity field is
  the connecting square. Both image triangles are distinguished by the two
  exactness conclusions. Naturality in `P` is built into the natural transformation;
  the explicit equation for `E E' q P` states naturality in `E`.
- The last equation identifies the unit component with identity after the canonical
  unit identifications, exactly the node's `alpha_(R_Y) = 1_(RE)`.

Dependency declarations read and used:

| Node | Module and declarations |
| --- | --- |
| def-weil-sheaf-of-modules-category | `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`; Mathlib `SheafOfModules` and its abelian structure |
| def-weil-abstract-derived-category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `Q`, shifts and distinguished triangles |
| def-pc-kflat-complex | `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat` and sheafification/tensor infrastructure |
| lem-pc-kflat-resolution | `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` |
| def-pc-tensor-complex-sheaves | `Mathlib.Algebra.Homology.BifunctorShift`: `mapBifunctor`, both signed shift isomorphisms; the existing sheaf monoidal tensor |
| def-pur-kinjective-complex | Mathlib `HomotopyCategory.KInjective`: `CochainComplex.IsKInjective` |
| prop-pur-kinjective-resolutions-exist | `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`: `grothendieckAbelian_and_functorial_kInjective_resolutions` |
| def-weil-pbc-ringed-tensor-square-presentation | `Sheaf.Paper.RingedTensorSquarePresentation`: `RingedTensorCorner`, `RingedTensorModel`, `RingedTensorEdge`, `tensorComparison` |
| def-weil-pbc-projection-formula-arrows | `Sheaf.Paper.ProjectionFormulaArrows`: `CategoryTheory.derivedProjectionFormulaMate` |

Every recorded proof-dependency module is imported as well: canonical tensor pullback,
site tensor descent, ringed derived pullback, module adjunction, module tensor comparison,
derived adjoint functors, and the upstream triangulated right-derived-functor module.
Mathlib `Shift.Adjunction` supplies the adjunction shift interface and its uniqueness;
Mathlib `KInjective` supplies the K-injective shift instance. These last two are the
recorded Mathlib leaves, which correctly have no separate `lean` record.

Edge cases checked: the zero ring and zero modules are allowed; all complexes are
unbounded and totalization is by direct sums. Empty sites impose no extra nonemptiness.
All shifts are indexed by `ℤ`, including negative and zero shifts; independently shifting
both factors produces the sum of shifts with the Koszul interchange sign, never one
copy of the shift. Identity geometric morphisms and identity adjunctions reduce to the
ordinary tensor and its unit. `u` is the small-site/coefficient size and `w` remains the
independent chosen derived Hom size, exactly as in the recorded small-site presentation.
The theorem has no arbitrary unit-object or exactness hypotheses.

Searches: `msearch.py` LeanFinder query "derived projection formula mate commutes with
shifts and distinguished triangles" returned eight abstract derived-category/adjunction
hits and no ringed-topos theorem. Loogle query `CategoryTheory.NatTrans.CommShift`
found the existing abstract shift class and its lemmas, used here. The Mathlib grep query
`Projection.*[Mm]ate|projection.*[Tt]riangulated` in `CategoryTheory` found no match.
The earlier recorded LeanFinder query "ringed topoi derived projection formula mate exact
shift natural transformation" returned abstract adjunction results; the earlier Loogle
query with unqualified `Adjunction.CommShift` failed name resolution, so the qualified
search was repeated. `rg` over upstream `WeilConjectures` and current `lean/Sheaf`, by
node id and declaration name, found only references to this still unstated theorem and
its existing presentation/arrow dependencies. `scompile.py --source
Sheaf.Paper.RingedTensorSquarePresentation` confirmed the published source agrees with
the local declaration used here. No duplicate declaration was found.

Source checks: the local literature checkout contains indexes rather than the TeX files,
so the exact source tags were opened at the Stacks Project:
[06YU](https://stacks.math.columbia.edu/tag/06YU),
[07A4](https://stacks.math.columbia.edu/tag/07A4),
[07A6](https://stacks.math.columbia.edu/tag/07A6), and
[0B56](https://stacks.math.columbia.edu/tag/0B56).
The module docstring carries the node's four proof steps, including the representative
signs, cone comparison, adjunction shift calculation, connecting square, and unit identity.
There is no mathematical dispute or correction of the natural statement.

Earlier-attempt repairs: removed arbitrary unit objects and unit identifications from the
hypotheses; replaced the ill-typed simultaneous-shift comparison by separate canonical
comparisons; moved shift structures and exactness to the conclusion; supplied canonical
representative normalizations and the explicit exactness of G. Removed the earlier
second-reading paragraph: the current delivery must receive an independent second reading.

## Repair of return L (immutable head 0f5467180563)

The return reports successful elaboration of the sandbox module followed by failure
creating `Sheaf/Paper/ProjectionMateExact.olean` in the temporary library output.
It reports no Lean type error. I inspected the current prescribed compilation path:
`scompile.py` uses `nt_local_compile.run`, whose library pass calls `lcompile.run`
with a private output directory. The current `lcompile.run` calls `output_parent`
before invoking Lean; that function creates every output ancestor and removes stale
ancestor symlinks. This is the output-directory handling required by the returned
failure. I did not modify these tools or any shared source.

I reread the sandbox module, its node, and the recorded dependency interfaces. The
statement signature still agrees verbatim with `lean.statement`; no mathematical
change is required by this filesystem failure. The mandated `scompile.py ND
lem-weil-pbc-ringed-projection-mate-exact` command on the delivered module now exits
successfully and reports a clean server-confirmed file compile in 11.6 seconds,
with nice 19, two threads, and the unchanged 60-second limit. The node record date
is refreshed to the UTC date of this repair. The previous second-reading section
is removed so that a fresh second reader reviews this repaired delivery.

## Second reading by ND

I independently read the node and the full module, then opened the actual dependency
signatures rather than relying on the worker's table. I read the Stacks source
`sites-cohomology.tex` at `definition-derived-tor`, `lemma-pullback-tensor-product`,
`lemma-adjoint`, and `equation-projection-formula-map`, including their preceding
construction and section hypotheses. The local literature directory has no TeX checkout;
I read the published source and the corresponding pages
[06YU](https://stacks.math.columbia.edu/tag/06YU),
[07A4](https://stacks.math.columbia.edu/tag/07A4),
[07A6](https://stacks.math.columbia.edu/tag/07A6), and
[0B56](https://stacks.math.columbia.edu/tag/0B56), as well as
[0A8D](https://stacks.math.columbia.edu/tag/0A8D) for the adjoint shift convention.
The projection-map construction precedes the perfect-coefficient lemma and explicitly
has no further assumptions. Thus perfectness, boundedness, properness and flatness of
the ringed morphism must not become hypotheses here; none does.

Here is my inventory of the node, matched in order with the Lean.

1. Two small ringed sites and their commutative ring sheaves: `Y X :
   RingedTensorCorner.{u,w}`. I opened `RingedTensorCorner`: its fields are `site :
   Type u`, `category : Category.{u} site`, `topology`, and `ring : Sheaf topology
   CommRingCat.{u}`. This is the recorded small-site presentation, with arbitrary
   topology and rings. Verdict: matches.
2. Their abelian module-sheaf categories and unbounded derived categories:
   `mateModules` is the transparent specialization of `ringedSiteModules`, whose
   definition is exactly Mathlib `SheafOfModules`. `mateDerived` is `DerivedCategory`
   with the corner's existing `HasDerivedCategory.{w}` instance. These are neither
   presheaves nor bounded derived categories; no chosen alternative abelian instance
   is introduced. Verdict: matches.
3. K-flat resolutions and direct-sum total derived tensor: `a : RingedTensorModel Y`
   and `b : RingedTensorModel X`. I opened `representative`: it is a natural
   identification of `tensor` with `map₂HomologicalComplex` followed by `Q` on pairs
   of K-flat flat-term complexes. `mateFlat` spells exactly its existing predicate.
   I also opened `IsKFlat` and the independent-coefficient resolution theorem.
   On these small sites the monoidal `IsFlat` in the presentation and the resolution
   theorem's `IsFlatOnSite` both express exactness of the sheafified sectionwise tensor;
   no new flatness notion is being assumed. Replacing both factors for the
   representative characterization determines the same derived tensor as replacing
   one, by K-flat resolution independence. Verdict: matches the dependency interface.
4. A geometric morphism with a structural ring map: `e : RingedTensorEdge Y X`.
   Its `inverse`, `direct`, `adjunction`, and `finiteLimits` are the geometric
   inverse image and its right adjoint; `algebraic` and `ringMap` supply the algebraic
   lift and map of ring sheaves. The `pullback`, `object_eq`, and `map_eq` fields fix
   extension of scalars on objects AND maps. The `ordinaryTensor` field fixes its
   comparison by scalar insertion and the generalized pure-tensor formula.
   Verdict: the actual ringed morphism, not an arbitrary tensor-preserving functor.
5. L, R, their canonical adjunction and counit: the edge's `left`, `epsilon`, and
   `isLeftDerived` give the total derived pullback with its universal comparison;
   `right` and `derivedAdjunction` give its right-adjoint model. The recorded
   presentation explicitly allows right-adjoint models identified uniquely and
   adjunction-compatibly with derived direct image; K-injective resolutions compute
   this model by 07A6. `epsilon` is the left-derived comparison, whereas the counit
   in the mate is `e.derivedAdjunction.counit`. These are not confused.
   Verdict: matches, with model choices transported through the adjunction.
6. Derived tensor exact in each variable: the two `∀ U` conjuncts assert
   `IsTriangulated` for both `curryObj tensor` and its flip at both corners.
   The existential `CommShift₂Int` structures precede these claims, so exactness
   is concluded rather than assumed. Verdict: every variable and both sites covered.
7. Canonical integer shifts: `a.MateCanonicalShifts` and `b.MateCanonicalShifts`
   compare representative shifts with the existing `mapBifunctorShift₁Iso` and
   `mapBifunctorShift₂Iso` through `Q.commShiftIso`. I read those Mathlib definitions:
   the first is unsigned and the second has sign `(p*n).negOnePow`.
   `CommShift₂Int` includes coherence and signed interchange, not two unrelated
   shift choices. `NatTrans.CommShift e.epsilon ℤ` fixes L's shift against
   termwise pullback; `e.derivedAdjunction.CommShift ℤ` fixes the compatible R shift
   through both unit and counit. L and R are also explicitly `IsTriangulated`.
   Verdict: canonical structures, all integers, and correct signs.
8. Natural, unital, shift-compatible mu: `e.tensorComparison a b` is the published
   `ringedTopoiCanonicalDerivedTensorComparison`, chosen from an existence-and-
   uniqueness theorem with its K-flat representative equation. I opened that theorem
   and its defining selection; this is not a choice from bare `Nonempty`.
   Naturality belongs to its natural isomorphism type. The two `∀ n U V` equations
   assert compatibility with each tensor-variable shift separately. `mateUnitComplex`
   is the ring sheaf in degree zero and `mateUnit` its image under Q. The `unitL`,
   `unitY`, and `unitX` clause, `MateCanonicalUnit` normalizations on total summands,
   and the equation with mu express precisely the unit compatibility. Verdict: matches.
9. For every E, F(P)=RE tensor P and G(P)=R(E tensor LP): the domain and codomain
   of `alpha E` are exactly these functors. F is exact by item 6 and G is explicitly
   exact in the `∀ E` conjunct. E and P range over the whole unbounded derived
   categories, with no K-flat or K-injective condition on the derived objects.
   Verdict: matches and has the required quantifier order.
10. The counit mate alpha: its component equation uses the existing
    `derivedProjectionFormulaMate`. I opened that definition and upstream
    `Adjunction.rightAdjointProjectionMap`: its adjunct is mu followed by tensor
    of the counit with identity, with the node's orientation. Verdict: exact map.
11. Shift compatibility: `NatTrans.CommShift (alpha E) ℤ` says, in Mathlib's
    composition order, `sF ≫ alpha_P[n] = alpha_(P[n]) ≫ sG`. This is the node's
    displayed equality with its sides reversed, for every integer including 1.
    Verdict: matches; evaluation at a shifted object is distinct from shifting a map.
12. Morphism of distinguished triangles, including the connecting square:
    for every distinguished T the theorem supplies a morphism between the two
    `Functor.mapTriangle` images, with its three components equal to alpha's.
    A `Triangle` morphism includes the third commutative square, with the shifted
    first component. Both images are distinguished by the exactness already
    asserted, so this does not merely state a morphism of arbitrary triangles.
    Verdict: all three squares covered.
13. Naturality in E and P: P-naturality is part of `alpha E`'s natural-transformation
    type; the `∀ E E' q P` equation is precisely E-naturality, using `right.map q`
    on the source and `right.map (q tensor 1)` on the target. Mu and the shifts
    are natural transformations as well. Verdict: both variables covered.
14. Alpha at the unit is identity: the last equation first identifies its target
    by `unitL` and `unitX` under `right.map`, and identifies its source by `unitY`.
    It therefore states exactly the identity of RE after both identifications,
    without attempting to equate differently typed arrows. Verdict: matches.

Edge cases: the zero ring and zero objects are allowed throughout. Neither site
needs to be nonempty, and an empty scheme is not excluded by any scheme hypothesis
(the statement concerns general ringed topoi). Total tensor uses all integer
bidegrees and direct sums, with no finite support or nonempty index assumption.
The shift index ranges over all of ℤ, including zero and negative integers, and
`CommShift` imposes the zero-shift identity and addition law. There is no
characteristic or torsion restriction. Identity geometric morphisms and arbitrary
adjunction-compatible models remain covered. The site/module universe u and
chosen derived Hom universe w remain separately bound; no equation between them
is imposed. The two sites use the common chosen small-site universe already
specified by the presentation dependency; it does not identify object and Hom
universes of a large pro-etale site behind an unstated assumption. This node's
small-site formulation can use a common enlarged small-site universe.

Independent searches: LeanFinder query "Counit projection formula transformation
is exact and compatible with translation in a triangulated category" returned
abstract triangle exactness and adjunction hits, not the ringed-topos assertion.
Loogle query `CategoryTheory.NatTrans.CommShift` returned the exact existing class
and its abstract lemmas, which the module uses. LeanSearch query "The projection
formula counit mate is a natural transformation of exact functors on unbounded
derived categories of sheaves of modules" returned service unavailable (Internal
Server Error); no mathematical verdict is inferred from that failure. I ran `rg`
over Mathlib's homological/category-theory sources, all upstream `WeilConjectures`,
and the project's `lean/Sheaf`, with `projection.*shift`,
`projection.*[Tt]riangulat`, `Projection.*Mate`, `MateCanonical`, and
`ringedProjectionMateExact`. The upstream `Adjunction.ProjectionMapShift` supplies
`commShift_rightAdjointProjectionMap_app`; I opened it. It assumes the shift
structures and comparison compatibility that this node constructs and also omits
the tensor exactness, representative normalization, units and triangle conclusion.
Thus it does not replace the present whole theorem. Scheme-specific exactness
and projection-mate modules likewise do not state this general-site result.
The existing canonical comparison and mate definitions are reused, not duplicated.

No new node or dependency module occurs in this delivery, so H12/H13 add no
unreviewed material. All helper declarations have actual abbreviation/predicate
data, and the only postponed theorem in this module is
`SheafOfModules.ringedProjectionMateExact`, with proof `sorry` and the matching DAG
node. Every declaration and the module have the required source/blueprint docstring.
All universes and variables are bound (`autoImplicit false`), all lines are at most
100 characters, and the node's `lean.statement` equals the theorem signature
verbatim. There is no `statement_change` and no source-based correction is needed.

Mismatch found and repaired: proof step 4's prose wrote both evaluation of alpha
at P[1] and the shift of alpha_P as "alpha[1]". I distinguished them explicitly
as `alpha_(P[1])` and `(alpha_P)[1]` in the docstring. This changes no declaration
signature, definition, hypothesis or conclusion. I refreshed the lean-record date.
The full original worker report and return-repair account above are retained.
The prescribed `scompile.py` compiled the complete module cleanly, with the
sandbox pass taking 37.1 seconds and the library pass 47.9 seconds, both under
the unchanged 60-second per-file limit. The final delivery dry run recompiles
the docstring clarification and performs the server preflight.
