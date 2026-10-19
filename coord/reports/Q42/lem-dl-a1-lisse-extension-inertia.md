## Worker report

The item is stated in `Sheaf.Paper.LisseExtensionInertia`, as
`AlgebraicGeometry.WeilSheaf.lisse_extension_iff_trivial_inertia`. Every theorem
has exactly `by sorry` as proof; all definitions and instances have explicit data.
The companion module repairs the geometric identification in the recorded
fundamental representation. No source statement is changed, and no new DAG node is added.
The existing recorded definition node `def-wf-fundamental-representation` is added
to the item's statement dependencies because the inertia action explicitly uses it.

Hypotheses, objects and clauses, read against the original node:

- `D : FiniteFieldDatum.{u}` retains the finite field, its prime-power cardinality
  and chosen closure. `l`, `[Fact l.Prime]`, `[Fact (l ≠ D.p)]` express precisely
  the coefficient-prime hypothesis. `lisseExtensionCharacteristic` derives
  `ringChar D.k₀ = D.p`, and the global instance derives the class needed by the
  existing Weil-sheaf API; characteristic inequality is not a second assumption.
- `c : Scheme.MiddleExtensionCurve D` is the recorded bundle of the actual schemes
  over `Spec D.k₀`, the morphism `c.j`, finite type and separatedness, open immersion,
  density (`c.dense`), smoothness (`c.smooth`) and pure dimension one
  (`c.pureDimension : c.C.left.IsPureDimension 1`). The open's finite-type and
  separatedness fields follow automatically from the stated dense open in a
  noetherian curve; they do not exclude any open in the node.
  `[GeometricallyConnected c.C.hom]` is geometric connectedness of the curve.
- `lisseExtensionCurves` derives the upstream `IsCurve` classes; it does not replace
  pure dimension one by dimension at most one. `lisseExtensionNonempty` derives
  nonemptiness of the open from geometric connectedness and density. No
  nonemptiness or extra connectedness is required as a separate input.
- `WU`, `WC`, `b : BoundaryDatum c.j.left WU WC`, `B` and `M` are the group,
  local-inertia, base-point/path, and usual lisse-monodromy data of the recorded
  boundary/fundamental-representation definitions. They express the choices in
  the source's local geometric generic stalk, not an additional representation
  supplied independently of the sheaf. `b.inertia x` is indexed by exactly
  `↥((Set.range c.j.left.base)ᶜ)`, the complement S₀.
- `F : WeilSheaf D.k₀ l c.U.left` with `hF : F.IsLisse` is an ordinary constructible
  sheaf on the geometric fibre with its Frobenius isomorphism, with underlying
  sheaf lisse. This is upstream's ordinary **fixed-pair sheaf** realization,
  reexported by `QbarCurveOrdinaryImage`, not its derived-of-pairs `WeilComplex`.
  In this realization coefficients are `PadicAlgCl l` and the geometric fibre
  uses `AlgebraicClosure D.k₀`. These are the canonical algebraic-closure models
  used by the recorded boundary and fundamental-representation interfaces; their
  identification with any chosen algebraic closures is by algebraic-closure
  isomorphism, not an extra equality of coefficient/site universes. On the smooth
  noetherian geometric curve, the lisse adic convention is the inverse-system,
  finite-coefficient-field convention of Weil II (1.1.1), realized pro-etale
  locally by finite free adic modules. No Frobenius-stable integral lattice is
  assumed.
- The first conjunct is the required iff. Its left side is
  `∃ G, G.IsLisse ∧ Nonempty ((WeilSheaf.upperStar c.j.left).obj G ≅ F)`.
  Isomorphisms in this category are Weil-equivariant. Its right side quantifies
  over every boundary point, every element of `b.inertia x` and every vector in
  `LisseMonodromy.StalkSpace B.t (F.toLisse hF)`, requiring
  `canonicalFundamentalRep M B F hF g.1 v = v`. Thus it says the actual specified
  inertia action is trivial, rather than merely that the invariant dimension
  has a bound. The canonical geometric identification is fixed in the companion.
- The second conjunct is conditional on this same pointwise triviality.
  Its first clause says `((curveWeilMiddleExtension c.j.left).obj F).IsLisse`.
  This is the recorded ordinary direct-image interface, whose underlying functor
  is ordinary adic `lowerStar`, with transported Weil structure; there is no
  derived direct image, shift, perverse extension or chosen substitute object.
- Its next clause quantifies over every lisse G and every specified restriction
  isomorphism alpha. It gives an isomorphism `e : G ≅ j_*F` and requires its
  underlying morphism `e.hom.hom.hom.f` to be exactly
  `(adicUpperStarLowerStarAdjunction l jbar).homEquiv G.carrier F.carrier
  alpha.hom.hom.hom.f`. Hence it identifies the canonical adjoint to alpha,
  including Weil equivariance, rather than asserting an unrelated isomorphism.
- The last clause quantifies over two such pairs and asserts `∃! e : G ≅ G'`
  with `j^*(e.hom) ≫ alpha'.hom = alpha.hom`. This is uniqueness up to unique
  isomorphism preserving the specified restriction, not uniqueness of the
  underlying isomorphism class alone.

Dependencies read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, via the
  recorded ordinary-image module and `MiddleExtensionCurve`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`, both in c.
- `Sheaf.Paper.LisseIntegralSmallCoefficients`: the current small-coefficient
  integral-system interface and its public `LisseAdicSheaves` module, read for
  finite-level local constancy, compatible reductions, rationalization and the
  common-field coefficient convention.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilSheaf` and
  `sfCommonStageWeilSheaf` describe the heart-carrier fixed-pair convention.
  The ordinary `AlgebraicGeometry.WeilSheaf` in
  `WeilConjectures.WeilSheaf.Category` is the existing sheaf realization imported
  by `Sheaf.Paper.QbarCurveOrdinaryImage` through `CurveWeilMiddleExtension`.
  No upstream `WeilComplex` is used.
- `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary`:
  `BoundaryDatum`, `BoundaryDatum.inertia`, its restriction and kernel fields;
  the current source of this recorded module was obtained with `scompile --source`.
- `Sheaf.Paper.QbarCurveOrdinaryImage` publicly retains
  `AlgebraicGeometry.WeilSheaf.curveWeilMiddleExtension` from
  `Sheaf.Paper.CurveWeilMiddleExtension`, specializing existing ordinary
  `WeilSheaf.directImage` and its canonical Frobenius transport.
- `WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation`:
  `WeilGroup.fundamentalRep`, `WeilMonodromyData`, and the closed upstream
  `exists_equivalence_fundamentalRep`; current source was read with
  `scompile --source`. The repair specializes this representation using the
  normalized geometric inclusion and degree-one lift.
- Proof imports retain `Sheaf.Paper.DenseOpenPiOneSurjective` (all five recorded
  clauses), `WeilConjectures.AlgebraicGeometry.Regular`
  (`isIntegrallyClosed_stalk_of_smooth`), and
  `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia`
  (`ker_restrictionHom_eq_boundaryInertia`). The representation equivalence
  is in the imported fundamental-representation module.

Sources checked: the full node statement and five-step proof; the source
`rem-dl-a1-conventions.md` in main-20261015, second paragraph; Stacks
`pione.tex`, lemma `lemma-normal-pione-quotient-inertia` (Tag 0BTD), including
its three descriptions of the closed normal subgroup and its proof.

Edge cases checked before drafting and again after compilation: the boundary
may be empty (all inertia quantifiers are then vacuous); j may be the identity;
the sheaf may have rank zero; Frobenius need not have finite order or preserve
an integral lattice. The empty ambient scheme is excluded by geometric
connectedness, and density then excludes an empty U. Spec of a field is
excluded by the retained pure-dimension-one condition. Nontrivial Kummer
monodromy on G_m does not satisfy triviality at the missing point. Trivial
geometric monodromy with arbitrary invertible Frobenius does satisfy it.
The conclusion records the identity and arbitrary restriction-isomorphism
cases through the actual homEquiv, not a selected restriction trivialization.
All universes are explicit, with no auto-bound variables or local notation,
local instances, private definitions or abbreviations.

Searches (performed with the prescribed wrapper):

- LeanFinder: `A lisse l-adic Weil sheaf on a dense open of a smooth curve extends
  uniquely if and only if all boundary inertia groups act trivially`.
  Eight results, on Galois-category nontriviality, isocrystals, inertia and
  Hilbert 90; none states the item.
- Loogle: `"inertia"`. Twelve results, defining additive-subgroup and ideal
  inertia; none is the lisse Weil extension criterion.
- LeanSearch: `Lisse Weil sheaf extension across a boundary iff inertia acts
  trivially`. Eight results, on valuation inertia, ramification and residue
  degrees; none matches.
- Mathlib grep wrapper: `lisse.*inertia|inertia.*lisse`; zero hits.
- `rg` in upstream WeilConjectures and side `lean/Sheaf` for lisse/extension/
  trivial-inertia phrases found the finite-cover extension results,
  `BoundaryDatum`, finite-level dense-open unit results and semicontinuity,
  but not this full iff plus canonical adjoint and uniqueness statement.
  Searching the item id and proposed declaration names in both trees and
  `dag/lean_names_upstream.json` found no duplicate.

Validation: both modules compiled separately, in dependency order, with
`scompile.py Q42 lem-dl-a1-lisse-extension-inertia`, including the private-overlay
and library confirmations. No compiler errors or warnings remain. The main
consumer checks the repaired canonical representation on the actual boundary
inertia subgroup and checks its generic stalk vector type.

## Dependency modules

`def-wf-fundamental-representation`: the recorded upstream `fundamentalRep`
takes `WeilMonodromyData B` as an input. Its `geomEquiv` is only an abstract
geometric-group equivalence satisfying a Frobenius conjugation relation; that
does not fix its relation to the actual arithmetic fundamental group used by
`BoundaryDatum.inertia`. Using it without normalization would silently permit
relabeling inertia. `Sheaf.Paper.CanonicalWeilFundamentalRepresentation` retains
the upstream construction and specifies the missing normalization:
`W.toFundamentalGroup (m.geomEquiv g).1 = B.geomAut g` for every geometric g,
and `W.toFundamentalGroup m.frobLift = B.frobAut`. The arithmetic exact sequence
and path identity supply unique such data. `canonicalMonodromyData` chooses
from this uniquely determining theorem, and `canonicalFundamentalRep` applies
the existing fundamentalRep to them. This is a lean-only repair to the
existing node, not a change to its statement or a second definition of a
notion already usable. Its new theorem has a source and complete proof plan.
The main module consumes the repaired declaration twice, in the iff and in
the equivalent-condition premise. Both modules compile separately.

## Second reading by Q42

Author's separate rereading of the node, the two complete modules and the
recorded dependency signatures; the maintainer supplies the independent review.
The first draft relied on an arbitrary `WeilMonodromyData`; this was corrected
by the dependency module, which fixes the geometric inclusion and Frobenius lift.
A temporary local instance was removed. Characteristic, upstream curve classes
and nonemptiness are derived globally, retaining pure dimension one and geometric
connectedness. I checked the iff in both directions, the literal complement
index, the all-vectors/all-inertia-elements quantification, lissity of the
ordinary image, the exact adic adjunction formula for every alpha, and the
compatibility equation in the unique-isomorphism clause. Alpha' occurs on the
right side of the restricted morphism, so the lifted arrow has direction
G -> G'. Neither an arbitrary adjoint map nor mere existence of an extension
is substituted for a clause. The dependency node changes only its lean record;
the item only gains lean and the already recorded definition dependency.
No source statement was corrected and no statement is marked disputed.
