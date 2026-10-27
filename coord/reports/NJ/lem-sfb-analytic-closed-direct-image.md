## Worker report

The module `Sheaf.AlgebraicGeometry.AnalyticClosedDirectImage` states
`AlgebraicGeometry.SmoothAnalytic.exists_analyticClosedDirectImage` with `sorry`.
It adds no definitions, axioms, helper theorems or new nodes. The node is unchanged
except for its `lean` record. No statement correction or disputed statement.

The canonical comparison is characterized on local tensors, not specified by an
arbitrary isomorphism. No choice of analytic space or map from an unspecified
existence theorem is made. The theorem accepts the dependency's fully specified
analytic data and asserts the induced analytic map and the specified comparison.
The complex points and the pullback-of-holomorphic-functions formula determine
that map. Its section formula determines the module comparison because local
inverse-image representatives and pure tensors generate the tensor sheaf locally.

Hypotheses and clauses, matched against the node:

- Schemes X and Y: `{X Y : Scheme.{u}}`.
- Schemes over C: `f` and `g` have target `Spec (.of (ULift.{u} ℂ))`, exactly the
  base and lift used by the recorded analytification dependency. `u` is arbitrary.
- Separated: `[IsSeparated f]`, `[IsSeparated g]`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]` and the same for `g`.
  These are the dependency's recorded conjunction, not an extra finiteness notion.
- Smooth: `[Smooth f]`, `[Smooth g]`.
- A closed immersion over C: `i : Over.mk f ⟶ Over.mk g` with
  `[IsClosedImmersion i.left]`; the Over morphism includes compatibility with the base.
- The analytic spaces and analytification maps: `D : Data f`, `E : Data g`, with
  `D.space`, `E.space`, `D.pi`, `E.pi`. These are the objects supplied by
  `exists_smoothAnalytification_cotangent`; their holomorphic rings, evaluations,
  point sets, topology and regular-coordinate atlases are specified in that API.
- The induced analytic closed embedding: the existential `j` has the complex-point
  formula `j.hom.base x = mapPoints D E i x` and the holomorphic-function evaluation
  formula saying its ring map is pullback. Its closed holomorphic embedding
  property is `IsClosedHolomorphicEmbedding D.atlas E.atlas j.hom.base`.
  These expand the node's phrase "the induced closed holomorphic embedding".
- The square of analytification maps, needed to identify composite direct images:
  `hpre U` identifies `π_X⁻¹(i⁻¹U)` with `j⁻¹(π_Y⁻¹U)` for every algebraic open U.
  Since restrictions are those of the same sheaf on the equal open, this gives the
  usual sectionwise identification `i_*π_X,* = π_Y,*j_*` used by the node.
- Every coherent algebraic module: `∀ F : X.Modules,
  RingedSpace.IsCoherent X.toRingedSpace F → ...`. This is the exact finite-type
  plus finite-type-kernel predicate exposed by the repaired coherence dependency,
  rather than its older quasi-coherent/finite-type conjunction alone.
- The analytic module isomorphism: `∃ e : analytify E
  ((Scheme.Modules.pushforward i.left).obj F) ≅ ... (analytify D F)`. The right side
  is Mathlib's actual `SheafOfModules.pushforward` along `Opens.map j.hom.base`
  and the ring-sheaf map obtained from `j.hom.c` by forgetting to RingCat.
  Thus the isomorphism is O_Yan-linear, with the target's scalar action induced by j.
- The formula `h ⊗ s ↦ h|_Xan ⊗ s`: the first conjunct quantifies over every
  algebraic open U, every analytic open W inside π_Y⁻¹U, every holomorphic h on W,
  and every `s : F(i⁻¹U)`. Its left side is e applied to h times the restriction
  of `tensorSection E (i_*F) U 1 s`; its right side is `j.hom.c.app (op W) h`
  times the restriction of `tensorSection D F (i⁻¹U) 1 s` to j⁻¹W. This is the
  local tensor formula even when h does not extend to all of π_Y⁻¹U.
  The quantified proof `hX` is the inclusion j⁻¹W ⊆ π_X⁻¹(i⁻¹U), which follows
  from hW and hpre. It adds no geometric hypothesis and cannot make the formula
  vacuous. Universal quantification allows every proof of this inclusion.
- Canonical maps `a_E`: `tensorSection ... 1 s` is precisely s mapped to 1 tensor s
  by the existing inverse-image adjunction unit followed by tensor sheafification.
  The second conjunct states that e on that section equals `tensorSection D F ...
  1 s`, transported to j⁻¹π_Y⁻¹U by
  `(analytify D F).val.map (eqToHom (hpre U).symm).op`.
  This is exactly `π_Y,*(e.hom) a_(i_*F) = i_*a_F` on every algebraic open and
  section, using the displayed direct-image identification. It is separately
  present even though it also follows from the first formula by h = 1.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; `Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.SmoothAnalytificationCotangent`:
  `AlgebraicGeometry.exists_smoothAnalytification_cotangent`; its public
  `SmoothAnalyticData` API supplies `SmoothAnalytic.Data`, `analytify`,
  `tensorSection`, `mapPoints`, `IsClosedHolomorphicEmbedding`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes the recorded
  `WeilConjectures.AlgebraicGeometry.Coherent` declaration
  `AlgebraicGeometry.RingedSpace.IsCoherent`. No dependency repair is necessary.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  is a transparent abbreviation for Mathlib's `SheafOfModules`; the latter is
  the carrier of the comparison and is already used by the analytification API.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`; the same module is already publicly
  imported by the analytic-data API, so no second tensor construction is added.
- `Mathlib.Topology.Sheaves.Functors`: `TopCat.Sheaf.pullback`, `pushforward`,
  `pullbackPushforwardAdjunction`; the analytic-data tensor construction uses the
  recorded explicit `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`
  of `Mathlib.CategoryTheory.Sites.Pullback`, avoiding a different chosen unit.
- Ordinary algebraic pushforward is `Scheme.Modules.pushforward` in
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`; analytic pushforward is
  `SheafOfModules.pushforward` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.

All the recorded proof-dependency modules that exist are available through the
public dependency imports or the explicit plain proof imports. In particular the
module imports `AnalyticClosedIdealLocalQuotient`, `StalkTensor`, `InverseImageStalk`,
`ClosedPushforwardStalks`, and `ClosedPushforwardAbelianStalks`. The generic
sheafification and stalkwise-isomorphism APIs are already imported transitively.
The theorem docstring reproduces all five proof steps, including the quotient
inverse, vanishing off the image, linearity of the inverse and unit compatibility.

Source read: Serre, GAGA, no. 10, Proposition 11, printed p. 18, and its use of
no. 6, Proposition 4; no. 11 specifies the canonical section map. The scan is at
https://www.college-de-france.fr/media/jean-pierre-serre/UPL1698785858825941763_Serre_GAGA.pdf
(NUMDAM's original article). Proposition 11 has no subclause (i); the inherited
node's source-place string still says "Prop.11(i)". This is a citation typo only;
the module cites Proposition 11 without (i), and the node statement is unchanged.

Edge cases checked before drafting:

- Empty X: the embedding conditions are vacuous on points; its direct image and
  both analytic modules are zero. No point or nonempty hypothesis was introduced.
- Identity immersion: both sides are the same analytification, and both formulas
  prescribe its identity map under the indicated section identification.
- Zero module: the section formulas say 0 = 0 and give the zero-object isomorphism.
- Empty opens: all maps use the existing sheaf restrictions, so remain defined.
- Zero-dimensional schemes and components of different dimensions: the Data/Atlas
  interface quantifies over chart dimensions pointwise, with no common dimension.
- Positive codimension: h may be any ambient holomorphic function, including one
  vanishing on the image; its image is the actual restriction along j, so the
  quotient relations in Proposition 4 are retained.
- Universes: the existing analytic-data API uses Scheme.{u}, ULift.{u} C and
  module sheaves in u; no new universe equality or nonemptiness condition is imposed.

Searches for an existing comparison (all on 2026-10-24):

- `msearch.py ... leanfinder "Analytification commutes with closed direct image of
  coherent module sheaves"`: eight hits, including ordinary algebraic
  `Scheme.Modules.pushforward` and its section formula; no analytic comparison.
- `msearch.py ... loogle '"analytification"'`: zero hits.
- `msearch.py ... grep 'analytification|analytic.*pushforward|pushforward.*analytic'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Analytification preserves closed direct images of
  coherent module sheaves"`: eight hits, including scheme pushforward instances,
  sheafification/pullback compatibility and unrelated analytic-function/set results;
  no comparison of analytified module sheaves.
- `rg -n 'analytif|Analytif|analyticClosed|analytic_closed'` in both project Lean
  roots: the analytic-data, cotangent and local-quotient declarations above, plus
  a prose occurrence in Statement.lean; no declaration of this comparison.
- The item-id search in `lean/WeilConjectures` has no hits.
- The existing coherence record and its full module/docstring were read: it now
  publicly exposes the exact coherence predicate, so its older main declaration
  is not mistakenly used as a replacement for coherence.

Validation: scompile.py compiled the single delivered file in module mode against
the live published build, cleanly (no errors or warnings). The recorded signature
is extracted verbatim from the theorem keyword to before `:=`; all universes and
variables are explicitly bound and every line is at most 100 characters.

## Second reading by NJ

No independent worker reading is claimed: the dispatcher brief requires this
worker to deliver directly, without starting other agents; the maintainer supplies
the independent review. On rereading the node alongside the compiled file, I
checked both base morphisms and all eight geometric property instances, the exact
coherence predicate, both sides and scalar action of the analytic module
isomorphism, the tensor formula on arbitrary analytic subopens, and the separate
unit equation with its correctly oriented equality-of-opens transport. No clause
was removed, no geometric assumption was added, and no new dependency is needed.
