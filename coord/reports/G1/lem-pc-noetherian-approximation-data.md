## Worker report

The module states `AlgebraicGeometry.noetherian_approximation_data` in
`lean/Sheaf/AlgebraicGeometry/NoetherianApproximationData.lean`. It quantifies a directed
filtered diagram of Noetherian rings with colimit, a finitely presented morphism
`f : X ⟶ Spec c.pt`, a bounded complex `G` of finitely presented flat module sheaves with
proper support, and a perfect derived object `E`. The conclusion gives a stage `i`, a scheme
`Xi` and finitely presented morphism `fi`, a comparison map `g` over the canonical map to
`Spec (R.obj i)`, a bounded finitely presented flat complex `Gi` with proper support and
termwise tensor-pullback isomorphisms to `G`, and a perfect `Ei` whose derived pullback is
isomorphic to `E`.

The boundedness clauses are rendered by bounds `a b : ℤ` and `IsZero` outside `[a,b]`.
Finite presentation is `(G.X n).IsFinitePresentation`; flatness is
`SheafOfModules.IsFlat`; proper support is `Scheme.Modules.HasSupportProperOver`. The
scheme morphism hypotheses are `LocallyOfFinitePresentation`, `QuasiCompact`, and
`QuasiSeparated`. The base-change identifications are expressed by
`Scheme.Modules.tensorPullbackObj` and `derivedPullback`.

Dependencies used: `Sheaf.AlgebraicGeometry.PerfectComplex` (`Scheme.IsPerfect`,
`schemeDerivedCategory`), `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`
(`Scheme.Modules.HasSupportProperOver`), and `Sheaf.AlgebraicGeometry.DerivedPullback`
(`derivedPullback`). Schemes, cocones, colimits, and morphism properties are Mathlib.

Edge cases checked: the index type is the same universe as the rings and schemes; empty
complex terms are allowed by the bounded `IsZero` condition; no nonemptiness of the index
set is imposed beyond directedness; zero module terms satisfy all termwise clauses.

Searches: `msearch.py leanfinder` for Noetherian approximation/descent (no exact match),
`msearch.py loogle` for finite-presentation/flat/perfect inverse-limit descent (no hits),
Mathlib grep for `Noetherian.*approximation|proper support` (no match), and `rg` over
`WeilConjectures/` and `lean/Sheaf` (no existing declaration of this statement).

## Second reading by G1

I independently opened the node and the delivered module and read the Stacks source
from the local checkout `/home/ubuntu/c1-stacks-review/`. The tags table identifies
01ZM with `limits-lemma-descend-finite-presentation`, 01ZR with
`limits-lemma-descend-modules-finite-presentation`, 05LY with
`limits-lemma-descend-module-flat-finite-presentation`, 081G with
`limits-lemma-eventually-proper-support`, and 09RF with
`perfect-lemma-descend-perfect`. I read those statements, including the inherited
`perfect-situation-descent` assumptions, and the paragraph and lemma
`coherent-lemma-module-support-proper-over-base` (30.26.7, 0CYS). The last is
in coherent.tex, the Cohomology of Schemes chapter, rather than cohomology.tex.
The sources assume nonempty directed systems, affine transition morphisms and qcqs
stages; spectra supply affine transitions and qcqs bases, and a finite-presentation
morphism supplies qcqs total spaces. General filtered categories give the same
colimit situation, by passing to a cofinal directed system if applying the sources
literally. No additional separation, field or characteristic assumption occurs.

The following is my object/hypothesis/conclusion list, with its final Lean rendering.

| Node clause | Lean rendering and verdict |
| --- | --- |
| A commutative ring R, filtered colimit of Noetherian rings R_i | `I : Type u`, `[SmallCategory I] [IsFiltered I]`, `R : I ⥤ CommRingCat.{u}`, `[∀ i, IsNoetherianRing (R.obj i)]`, `(c : Cocone R) (hc : IsColimit c)`; c.pt is the colimit ring. Corrected the preorder-only encoding and its missing nonemptiness. No Noetherian hypothesis on c.pt. |
| Affine base S = Spec R | `Spec c.pt`; correct, no extra field assumption. |
| Scheme X and f : X → S of finite presentation | `(X : Scheme.{u}) (f : X ⟶ Spec c.pt)` with `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`; exact conjunction in def-pc-morphism-conventions. |
| Bounded complex G of O_X-modules | `{G : CochainComplex X.Modules ℤ}` and `hGb : ∃ a b : ℤ, ∀ n, n < a ∨ b < n → IsZero (G.X n)`; correct two-sided boundedness. |
| Each G term finitely presented | `[∀ n : ℤ, (G.X n).IsFinitePresentation]`; correct. Mathlib's class includes quasicoherent local presentation data and supplies IsQuasicoherent and IsFiniteType, as needed in the sources. |
| Each G term flat over S | `hGflat : ∀ n, (G.X n).IsFlatOver f`; repaired, using the existing relative flatness definition. |
| Each G term has support proper over S | `hGproper : ∀ n, Scheme.Modules.HasSupportProperOver f (G.X n)`; correct nonzero-stalk support, closedness and reduced-induced properness. Finite presentation of f supplies the locally-finite-type instance. |
| Perfect E in D(O_X) | `(E : schemeDerivedCategory X) (hE : X.IsPerfect E)`; exact recorded derived category and perfectness definition. |
| One common stage and finitely presented Xi over R_i | `∃ (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ Spec (R.obj i)), LocallyOfFinitePresentation fi ∧ QuasiCompact fi ∧ QuasiSeparated fi ∧ ...`; correct. `hfi : LocallyOfFiniteType fi` merely supplies the proof argument of proper support; it follows from finite presentation. |
| The base change of Xi is X over S | `∃ ... (g : X ⟶ Xi), IsPullback g f fi (Spec.map (c.ι.app i)) ∧ ...`; repaired. A cartesian square is exactly a base-change identification over S. |
| Bounded finitely presented Gi flat over R_i with proper support | `∃ Gi : CochainComplex Xi.Modules ℤ`, followed by the same bounds, termwise IsFinitePresentation, `(Gi.X n).IsFlatOver fi` and HasSupportProperOver fi using hfi; corrected relative flatness, other properties preserved. |
| Base change of Gi is the given complex G | `∃ e : ∀ n, tensorPullbackObj g (Gi.X n) ≅ G.X n`, with `∀ n m, tensorPullbackMap g (Gi.d n m) ≫ (e m).hom = (e n).hom ≫ G.d n m`; repaired. A family of isomorphisms commuting with all differentials is exactly an isomorphism of complexes. |
| Perfect Ei on the same Xi with base change E | `∃ Ei : schemeDerivedCategory Xi, Xi.IsPerfect Ei ∧ Nonempty ((derivedPullback g).obj Ei ≅ E)`; correct. The same i, Xi, fi and g are used for all three identifications. |

Dependency declarations were read, not inferred from their names:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme supplies schemes and morphisms;
  the node's convention record for def-pc-morphism-conventions explicitly defines
  finite presentation as locally finite presentation plus quasi-compact plus
  quasi-separated. These are the Mathlib morphism classes used here.
- def-pc-derived-category: Sheaf.AlgebraicGeometry.DerivedCategory defines
  `schemeDerivedCategory` on the shared moduleRings carrier. The statement uses
  this for E and Ei, not a separate derived category on X.Modules.
- def-pc-perfect-complex: Sheaf.AlgebraicGeometry.PerfectComplex defines
  `Scheme.IsPerfect` by local strictly-perfect representatives in that derived
  category; `IsStrictlyPerfect` has bounded terms that are summands of finite free
  modules. This matches the node on arbitrary schemes, including the empty scheme.
- def-weil-pbc-closed-subset-proper-over-base:
  Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase defines
  `Scheme.Modules.HasSupportProperOver` as closedness of the actual nonzero-stalk
  locus and properness of its reduced induced subscheme, exactly the dependency.
- Relative flatness is already recorded by def-pc-scheme-module-flat-over as
  `Scheme.Modules.IsFlatOver` in
  WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage (line 193).
  I opened the definition: sections on affine pairs, restricted scalars along
  f.appLE, are flat over the affine base ring. For these quasicoherent terms this
  is precisely flatness over S, not flatness over O_X.
- Module base change uses the already shared `tensorPullbackObj` and
  `tensorPullbackMap` in Sheaf.AlgebraicGeometry.TensorPullback. I read their
  formulas (inverse image followed by change of rings/sheafification) and functor
  laws. Derived base change uses `derivedPullback` in
  Sheaf.AlgebraicGeometry.DerivedPullback, chosen from its named existence theorem.
  Neither is redefined in this delivery.

Edge cases: an empty index category is not filtered (`IsFiltered` includes
Nonempty), so the repaired statement covers exactly the nonempty colimit systems
of the node/source. The original IsDirected-only hypothesis admitted an empty
preorder, for which a colimit exists but the existential stage cannot exist.
Empty schemes and zero complexes are allowed: pointwise perfectness is vacuous
on the empty scheme; zero terms and empty supports are permitted; there is no
nonzero condition. The bounds do not require a ≤ b and include complexes
concentrated in degree zero and in arbitrary integer degrees. No rank, positive
integer, field, nontrivial-ring or characteristic restriction was introduced;
zero rings and every characteristic are allowed. I and the rings/schemes have
universe u, and the derived morphism universe w is explicit. The shared universal
HasDerivedCategory binders are the project's derived-category infrastructure
for arbitrary Xi and their opens; duplicate X-specific binders were removed.
No independent smaller test universe or unbound variable remains.

Independent searches (2026-10-11):

- `msearch.py ... leanfinder "simultaneous spreading out schemes complexes perfect
  objects to noetherian subrings"`: eight generic hits (affine/quasi-affine limit
  lemmas and Noetherian predicates), no theorem descending these three data.
- `msearch.py ... loogle "IsPullback"`: unknown identifier, no hits; direct reading
  of Mathlib's IsPullback definition supplied its exact square orientation.
- `msearch.py ... leansearch "Descend bounded complexes with proper support and
  perfect complexes to a noetherian ring in a filtered colimit"`: unavailable,
  Internal Server Error, recorded without claiming a negative search result.
- `rg` on all pinned Mathlib, WeilConjectures and project lean/Sheaf with
  `noetherian.?approximation|approximation.?data|descend.*(complex|perfect)|descent.*(complex|perfect)`:
  related individual complex descent lemmas and Scheme.NoetherianApproximation,
  but no exact simultaneous tensor-data statement. The upstream scheme
  approximation structure has no complex/module/perfect data, so is not a match.
  A separate `rg` for IsFlatOver found the existing relative-flatness definition;
  it is used directly. The delivered full declaration name does not occur in
  dag/lean_names_upstream.json or the source/Mathlib. No second definition needed.

Mismatches repaired: (1) absolute O_X-flatness replaced by flatness over f and fi;
(2) commuting scheme square replaced by a cartesian square;
(3) unrelated termwise isomorphisms replaced by a differential-compatible family;
(4) index now represents an arbitrary nonempty filtered diagram, excluding the
spurious empty-index counterexample; (5) redundant X-specific derived instances
removed; (6) theorem docstring now carries all four proof steps with dependency
ids and source places, and the copyright header was added. Original correct
boundedness, finite-presentation, support and perfectness clauses were preserved.
The node's mathematical statement is unchanged, so no statement_change or citer
correction is needed. No new nodes or dependency modules were required.
The Worker report above describes the original attempt; this section records
its repairs and the final statement.

Verification: scompile.py G1 lem-pc-noetherian-approximation-data compiled the
75-line repaired module in 3.6 seconds, exit 0, with no errors or warnings.
Exactly one theorem remains, with proof `by sorry`; there are no definitions,
private notation, local instances, hidden lets, or proofs in this delivery.
The node lean.statement is verbatim the final theorem signature.
