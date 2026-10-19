## Worker report

The module `Sheaf.Paper.ProperUnboundedWindowIso` states the two canonical window
isomorphisms for proper derived module pushforward. Its two theorems cover precisely
the node's alternatives Λ = E and Λ = Qlb. Both proofs are `sorry`. No definitions,
new nodes, dependency repairs, or statement corrections are introduced.

The source read is blueprint main-20261015, sec-six-functors-basics,
`sk-lem-proper-unbounded-window/_section.md`, its detail
`sk-lem-proper-unbounded-window-iso.md`, and the node's three proof steps.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X and Y | `{X Y : Scheme.{u}}`, with unrestricted explicit universe `u` |
| A prime ℓ | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| A chosen algebraic closure of Qℓ | The project's existing model `PadicAlgCl ℓ`, carrying its extended valuation topology |
| A finite subextension E | `(E : PadicAlgCl.FiniteIntermediateField ℓ)` in the finite-coefficient theorem |
| Λ = E | `Profinite.continuousMapRingObj E`, the existing continuous-function condensed ring |
| Λ = Qlb | `Profinite.padicAlgClRingObj ℓ` in the second theorem; its sections have values in a finite subextension |
| Λ_T = p_T^*Λ | `condensedRingObj Λ T`, underlying `coefficientRing T (Mon.mk Λ)` |
| The ordinary unbounded D(Mod_ΛT) | `DerivedCategory (pulledBackModuleObjects Λ T)` |
| IndCons consists of filtered colimits of constructibles in the module category | `ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ T)` |
| K belongs to Dic(X,Λ) | `hK : ∀ n : ℤ, ... ((DerivedCategory.homologyFunctor _ n).obj K)` |
| Proper p:X→Y | `(p : X ⟶ Y) [IsProper p]` |
| Geometric fibres of dimension at most an integer d | `(d : ℤ)` and `hd`, quantified over `y : Y` and every natural integer below the geometric fibre's `topologicalKrullDim` |
| Geometric fibre itself | `pullback p (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y)` |
| The total derived pushforward Rp_* | `(CondensedRing.lowerStar Λ p).rightDerivedFunctor`, deriving the full underived module composite |
| Every q in Z | `(q : ℤ)` |
| A = τ≤q K | `(DerivedCategory.TStructure.t.truncLE q).obj K` |
| W = τ≥(q−2d−1) A | `(DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj A` |
| All three degree-q objects belong to IndCons(Y,Λ) | The first three conjuncts, for the direct images of K, A, and W respectively |
| The left-pointing canonical isomorphism | Fourth conjunct: `IsIso` of the image of `(DerivedCategory.TStructure.t.truncLEι q).app K` under Rp_* and H^q |
| The right-pointing canonical isomorphism | Fifth conjunct: `IsIso` of the image of `(DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app A` under Rp_* and H^q |

The two concrete coefficient declarations use the project's standard chosen algebraic
closure, as in the already published finite-subextension and condensed-Qbar interfaces.
The choice is a model of the chosen algebraic closure in the node, rather than an
additional hypothesis. The Qbar theorem does not need a redundant finite-subextension
parameter. No invertibility, characteristic, Noetherian, qcqs, boundedness, or base-field
hypothesis is added.

The dimension expression uses `topologicalKrullDim : WithBot ℕ∞`. The condition that
every natural n below that value satisfies `(n : ℤ) ≤ d` is exactly dim ≤ d for integer
d: for nonnegative d it excludes all dimensions above d, including infinity; for negative
d it forces dimension bottom, which is the empty fibre. Thus negative d is preserved.
The only coercion is the explicit scheme-to-type coercion `↥` needed by the dimension API.

IndCons is a full subcategory. Ambient inverses to maps between its objects automatically
lie in the full subcategory and satisfy the same inverse equations. Thus the five
conjuncts express exactly both specified canonical isomorphisms *in IndCons*, without
choosing arbitrary comparison maps or merely asserting abstract object isomorphisms.

Dependency declarations read and reused:

- `sk-def-sfb-condensed-ring`: the recorded
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` exports
  `Profinite.continuousCoefficientRingObj` and its commutativity instance. For the actual
  canonical finite subextension, whose carrier is Type 0, the original existing
  `Profinite.continuousMapRingObj E` specializes the same sectionwise construction and
  avoids lifting or changing the finite-subextension interface. This import is retained.
- `sk-def-sfb-qlbar-condensed`: its closed slopmaster2 audit, despite no `lean` record,
  names `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj` in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`. Read their actual
  definitions in the shared framework, including `padicAlgClSubfunctor`, whose values
  satisfy `PadicAlgCl.finiteIntermediateFieldValued`. The public finite-subextension
  import provides this exact coefficient construction.
- `sk-def-sfb-pulled-back-coefficients`: `coefficientRing` and `condensedRingObj` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, transported by
  `upperStarFromPoint` rather than an identification with a constant ring sheaf.
- `sk-def-sfb-module-objects`: `pulledBackModuleObjects` in
  `Sheaf.Paper.ModuleObjects`; this is the existing category of internal modules over
  `coefficientRing`, definitionally the category expected by `lowerStar`.
- `sk-def-sfb-constructible`: `IsConstantModelConstructible` in
  `Sheaf.Paper.CondensedConstantConstructibility`, including finite constant local
  models, finite constructible strata on qcqs schemes and the affine-local convention.
- `def-weil-derived-cohomology-sheaves`: its Mathlib match
  `DerivedCategory.homologyFunctor` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` is used directly.
  The recorded Qbar-pair specialization is not the ambient internal-module category;
  its note explicitly retains the general cohomology declarations. No second
  cohomology functor is defined.
- `sk-def-sfb-module-derived-pushpull`: the public recorded module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` supplies
  the generic `CategoryTheory.Functor.rightDerivedFunctor`; the module deliberately
  does not define a separate Rp_*.
- `def-kun-truncations`: public import
  `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` reexports the actual standard
  t-structure. Use its documented Mathlib truncations, not its unrelated primary
  sequential-hocolimit predicate. `truncLE`, `truncLEι`, `truncGE`, `truncGEπ` are the
  canonical t-structure functors and natural maps.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and its category from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, with the recorded universally-closed
  implication giving quasi-compactness and hence finite type.
- `def-weil-geometric-fibre`: its actual recorded `CategoryTheory.Limits.pullback`
  applied to the residue-field algebraic-closure point; no set of lifts is substituted.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, with bottom for the empty space.

Proof-only imports include the recorded Grothendieck module-category theorem,
K-injective resolution instance, triangulated right-derived-functor instances,
`TStructure.triangleLEGE_distinguished`, and `DerivedCategory.HomologySequence`.
`det-proper-unbounded-window-arbitrary` has no recorded statement or Mathlib match
in the read base, so there is no module to import for that proof dependency yet.
It is named in both natural-language proofs; it supplies the amplitude bounds in
stage 3. No unrelated theorem or extra axiom replaces it.

Edge cases checked before writing:

- Zero K: all three cohomology objects vanish and both arrows are zero-object identities.
- Empty X or Y: empty geometric fibres have dimension bottom; no nonemptiness is imposed.
- d < 0: `hd` forces all geometric fibres empty; these integer cases are retained.
- d = 0: the lower cutoff is exactly q−1, rather than q or q−2.
- Arbitrary positive or negative q: integer arithmetic and unbounded K are retained.
- Finite E including E = Qℓ, both coefficient alternatives, and arbitrary characteristic:
  there is no auxiliary restriction on any of them.
- Filtered presentations are computed in the actual module category in universe u+1,
  not an abstract Ind completion or a limit in the derived category.

Searches for an existing statement:

- `msearch.py ... leanfinder "canonical truncation window cohomology isomorphisms for
  unbounded proper derived pushforward"`: eight hits on cochain truncation
  quasi-isomorphisms and bounded representatives, including
  `CochainComplex.instQuasiIsoIntπTruncGEOfIsGE` and
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`; none states the proper-pushforward
  two-arrow window theorem.
- `msearch.py ... loogle "DerivedCategory.homologyFunctor,
  CategoryTheory.Triangulated.TStructure.truncLE"`: zero hits.
- `msearch.py ... grep "windowIso|proper.*window|[Ii]nd[Cc]onstruct"`: zero Mathlib hits.
- `rg` for `IndCons|indConstruct|IndConstruct|Dic|unboundedWindow|windowIso|proper.*window|
  WindowIso` across the named project and shared sources: existing IndCons uses and
  unrelated perfect-Hom window comparisons; no matching theorem.
- Direct search for `det-proper-unbounded-window-iso` in the upstream source: no match.
- Read `Mathlib.CategoryTheory.ObjectProperty.Ind`: `ind` is exactly existence of a
  small filtered `ColimitPresentation` in the ambient category and is already invariant
  under isomorphisms. No new IndCons definition is necessary.

There is no STATEMENT-DISPUTED issue. Compilation uses only the prescribed single-file
`scompile.py` wrapper; the initial elaboration failure was repaired by explicitly
coercing the geometric-fibre scheme to its underlying topological type.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
