## Worker report

Stage 2 statement of `lem-sfb-open-square-closed-unit-triangle`, in
`Sheaf.Paper.OpenSquareClosedUnitTriangle`. The only postponed proof is
`AlgebraicGeometry.ProEtale.OpenSquareClosedUnit.closed_unit_triangle`.
The three helper definitions have actual data and name composites, not new mathematical
notions: `directImage` is M ↦ Rb_* M[0], `extensionImage` is M ↦ Rj_* b_! M[0],
and `image` is i^* Rj_*. No definitions, dependency records, or statements were replaced.
The node is already split and reviewed by Q140, but has no `lean` record: that is exactly
the stage-2 input, and requires no re-splitting or released stage-1 repair note.

Clause-by-clause correspondence:

- The commutative condensed ring is the arbitrary abelian sheaf Λ on
  `coherentTopology Profinite.{u}`, with `[MonObj Λ] [IsCommMonObj Λ]`.
  This is the unbundled form of recorded `Profinite.CondensedRing`, not a restriction to
  topologically presented coefficients. All five schemes have universe u, and the sheaf
  value category is `Ab.{u+1}`, as in the published small pro-etale framework.
- R_T is `condensedRingObj Λ T`, the underlying object of `coefficientRing T (Mon.mk Λ)`.
  `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj Λ T)` is the actual
  category of internal R_T-modules. `DerivedCategory` is its ordinary unbounded derived
  category, never a category of underlying abelian sheaves or a constructible subcategory.
- Y Noetherian is exactly `[IsLocallyNoetherian Y] [CompactSpace Y]`. No separatedness,
  finite-type, nonemptiness, boundedness above, or additional quasi-compactness assumption
  on an immersion is imposed.
- j and b are arbitrary scheme arrows with `[IsOpenImmersion j] [IsOpenImmersion b]`.
  The reduced closed complement is presented as `h : H ⟶ V`, `[IsClosedImmersion h]`,
  `[IsReduced H]`, and `Set.range h = (Set.range b)ᶜ`. This allows any presentation of
  exactly that reduced closed subscheme. The independent i has only `[IsClosedImmersion i]`.
- M ranges over every internal module on W, as the common domain of all the natural
  transformations and the degree-zero `DerivedCategory.singleFunctor ... 0`.
- K and B_M are `directImage Λ b` and `extensionImage Λ j b`. Exact extension by zero
  acts on the single complex through `openImmersionLowerShriek.mapDerivedCategory`;
  its canonical single-functor comparison identifies this with `(b_! M)[0]`.
- The actual open restriction counit is the displayed equation for `c.hom.app M`:
  first use the inverse canonical `L b^* ≅ D(b^*)` comparison, then the counit of
  `derivedUpperStarLowerStarAdjunction Λ b`. The existential natural isomorphism c
  asserts precisely that this counit is invertible, without assuming that assertion.
- The first map is the natural transformation a, constrained componentwise to
  `(image Λ j i).map (D(b_!).map (c.inv.app M) ≫ openAdj.counit.app K)`.
  Thus it is the required b_! counit after the actual open-counit identification.
- The second map in `Triangle.mk` is literally `(image Λ j i).map
  ((derivedUpperStarLowerStarAdjunction Λ h).unit.app K)`. Its codomain is
  i^* Rj_* Rh_* Lh^* K. Closed direct image and inverse image are exact here, so
  these are the specified h_* and h^*, canonically identified with their derived
  functors; retaining the total-derived form preserves the actual prescribed unit.
- δ is a natural transformation from the third vertex family to the first family
  postcomposed with `shiftFunctor ... (1 : ℤ)`. `Triangle.mk ... ∈ distTriang _` for
  every M says exactly that the triangle is distinguished in D(Z,R). Together with
  a and c being natural, and the second arrow being the image of a natural unit,
  this states naturality of the whole triangle in M, including its connecting arrow.
- Bounded below is stated for each of K and B_M as `∃ n : ℤ, (...).IsGE n`.
  By `DerivedCategory.isGE_iff`, this is exactly vanishing of cohomology in sufficiently
  negative degrees. No uniform bound or upper bound is asserted.
- The final iff uses `IsZero (i^* B_M)` and `IsIso` of exactly the same image of the
  closed unit used in the triangle. Zero objects are expressed invariantly by IsZero.

Recorded statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (its transparent
  underlying sheaf/monoid encoding is used to accept arbitrary commutative rings).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, and the canonical coefficient comparisons implicit in push/pull.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its module category.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPushforward`,
  `moduleObjectDerivedPullback`; its public upstream framework provides
  `derivedUpperStarLowerStarAdjunction` and `leftDerivedUpperStarIsoMapDerivedCategory`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek`, reexported by the public derived-open module.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek`:
  `derivedOpenImmersionLowerShriekUpperStarAdjunction` (canonical exact adjunction).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.

All already stated proof-dependency modules, including Mathlib matches, are imported
privately. `lem-sfb-module-derived-functor-compositor-shifts` has neither a Lean record
nor a Mathlib match on the read base, so it has no module to import. It is needed only
by the future proof, not to state this theorem; its role is explicitly preserved in
the proof docstring. No new DAG nodes or dependency modules are needed.

Edge cases checked mathematically before writing: M=0 and the zero coefficient ring
make every term zero; W empty gives K=B=0 and the zero triangle; W=V has empty H and
reduces to an identity triangle with zero third term; Z empty gives zero restrictions;
V empty and empty Y are also allowed. A nonreduced V is allowed: only H is required
reduced, exactly as specified. No restrictions on the cohomological dimension of W,
V, Y, H or Z appear, and neither derived direct image is asserted bounded above.

Searches (2026-10-22):

- `msearch.py ... leanfinder`: “Closed unit localization distinguished triangle for pro
  etale internal modules after open direct image and closed pullback”. Eight hits,
  including generic triangulated localization and ring-hom etale localization, no match.
- `msearch.py ... loogle`: `"DerivedCategory", "triangle"`. Twelve hits, including
  `DerivedCategory.triangleOfSES` and its distinguishedness theorem; these do not state
  the specified internal-module functors, actual adjunction maps, and naturality.
- `msearch.py ... grep`: `(closedUnit|closed_unit|localizationTriangle|localization_triangle)`.
  Six hits in monoidal-closed and unitary topics, no match.
- `msearch.py ... leansearch`: “A natural distinguished localization triangle of internal
  modules on the pro etale site has the closed adjunction unit as its second arrow”.
  Eight hits, generic localization/derived-adjunction formulas, no matching theorem.
- `rg` in `lean/WeilConjectures/SixFunctors/ProEtale` and `lean/Sheaf/Paper` for those
  patterns and OpenClosed, and in both project roots for this exact node id. No theorem
  for this item. Nearby `CondensedOpenClosedRecollement` is a bounded-below recollement
  theorem, not this triangle on ordinary unbounded internal-module categories with
  the two specific direct-image families. `TransverseTameOpenShriekExchange` uses the
  localization argument but does not state it. Generic exact-open/closed calculus is
  an input and does not duplicate the scheme/module specialization stated here.

No STATEMENT-DISPUTED flag and no statement correction. The prior attempt's objection
concerned repeating a stage-1 split; this delivery changes only the stage-2 `lean` record.

## Second reading by Q97

I reread the completed statement against the node and the full signatures of its
recorded interfaces. The initial namespace ambiguity between `ProEtale.upperStar`
and `CondensedRing.upperStar`, and between their extension-by-zero functors, was fixed
by writing `CondensedRing` explicitly. The actual open-counit equation fixes c uniquely;
the equation for a fixes the prescribed first arrow; the middle map is the literal
actual derived closed unit. Both bounded-below statements, the full natural connecting
transformation, and the zero/isomorphism criterion are present. The scheme hypotheses
are exactly those of the node, including the reduced complement and arbitrary closed i.
This is the worker's own rereading, not a claimed independent agent review; the brief
assigns independent review to the maintainer, and forbids starting another agent.

Validation: `scompile.py` accepted both sandbox and library module modes. The initial
namespace errors were repaired, and the sole line-length warning was removed.
`deliver2.py Q97 lem-sfb-open-square-closed-unit-triangle --no-push` then returned
`OK (dry run)` for commit `160ae6315c3`: preflight and compilation both passed.
The node delta is only `lean`; its signature is verbatim; all Lean lines are at most
100 characters; exactly one `sorry` remains, in the named theorem.
