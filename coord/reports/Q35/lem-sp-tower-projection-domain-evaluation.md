## Worker report

The new module `Sheaf.Paper.TowerProjectionDomainEvaluation` states
`AlgebraicGeometry.ProEtale.SpTowerProjection.tower_projection_domain_evaluation`.
Its only postponed theorem is this declaration, with the node's complete proof in its
docstring. `levelOpenComplex` has real data: the existing exact finite open extension
applied termwise using its published additive instance. No assertion is proved here.
The original statement, proof, dependencies, and all other node fields are unchanged.

Clause mapping:

- The prime and finite extension are `l`, `[Fact l.Prime]`, `E`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`. `SpTowerShriek.R l E n`
  is precisely O_E/(ell^(n+1)); natural index zero denotes the paper's positive level one.
- The compactification is `c : Compactification f`; its fields `i`, `g`, `Z`, `comm`,
  `isOpenImmersion`, `isProper` give exactly j, p, Xbar and f=pj. There is no assumption
  on a ground field, characteristic, constructibility, or normalization.
- `base : SpTowerShriek.Base l E` and `o : Operations l E base` instantiate the stipulated
  simultaneous section models already provided by tower-shriek-levels and the
  semilinear-derived-sections calculus. They are normalized constructions, not arbitrary
  functors or unconstrained comparison maps. `D`, `Ev`, `tensor`, `pull`, `push`, `openD`
  and `F` are precisely those recorded ordinary unbounded operations. `Base.realization`
  fixes every section and transition of the originally recorded varying-ring tower.
- The two objects are `C : D l E X` and `B : D l E Y`. The interval letters u,v in the
  node are v,w in Lean, to keep `u` for a universe. `_hab` and `_hvw` are the two orders.
  `_hC` is levelwise `IsGE a` and `IsLE b`, the standard cohomology-vanishing tests.
  `_hB` uses the recorded `HasRingedSiteTorAmplitudeOfUniverses`, whose definition tests
  the canonical K-flat derived tensor against every module sheaf in degree zero. It has
  no restriction on test modules. This is one of the dependency's recorded declarations,
  retained publicly by `ProEtaleTorAmplitudePresentations`.
- The first three conjuncts are boundedness below of C, B, j_!C, with their actual lower
  endpoints a,v,a. The next two paired conjuncts give `IsGE (a+v)` and `IsLE (b+w)`
  for the two specified tensor objects, using f inverse and p inverse respectively.
- `∀ n, ∃ T, ∃ P` states representatives independently at every level. `IsZero (T.X i)`
  and `IsZero (P.X i)` outside the two closed intervals express term support, not just
  cohomology support. `SemilinearSections.flatTerms` uses the recorded `IsFlatOnSite`;
  `IsKFlatIndependentCoefficients P` is the recorded acyclic-total-tensor test. The next
  two actual isomorphisms identify QT and QP with the evaluated C and B. The last two
  isomorphisms identify the evaluated tensor objects with Q of the signed total tensors
  of T and the termwise inverse image of P, and of j_!T and the termwise inverse image
  of P. `SemilinearSections.totalTensor` is the existing signed cochain total tensor.
  There is no family of transition maps for T or P and no tower compatibility premise.
- The proper map is the EXISTING `SpTowerProjection.properMap`; its body is the proper
  counit transpose after `Geometry.tensorPullback`. The open map is the EXISTING inverse
  of `Operations.openTensor`, characterized by `Operations.openTensor_mate` as the unit
  transpose; `openMap` is its Rp_* image. These are actual morphisms of derived systems.
  The naturality conjunct uses `source`, `middle`, `openSource` and arbitrary maps
  `C → C'`, `B → B'`, exactly the existing `maps_natural` equations. Naturality of the
  open map before Rp_* is explicitly stated in the next conjunct, using the actual
  open-unit transpose; no lifting of arbitrary families of finite derived maps is used.
- The proper evaluation equality displays all tensor, direct-image and pullback
  comparisons and ends in the existing `finiteProperMap`, the finite counit transpose.
  The open evaluation equality displays `openEvaluation` and ends in the existing
  `finiteOpenMap`, the finite unit transpose. Both finite words are independently
  defined by their finite adjunctions, not defined as evaluation of the tower arrow.
- The final equality is the naturality square for `Geometry.pushEvaluation` on the
  actual open transpose. Its left side evaluates Rp_*(pi_j); its right side applies
  finite Rp_* to evaluation of pi_j. `SpTowerShriek.Fcomparison` is the specified
  composite of this comparison and `openEvaluation`, so for D=C and for the first
  tensor (using `o.comp c.i c.g` and `c.comm` for f inverse), this is precisely the
  requested equality under `(FD)_n ≅ Rp_*j_!D_n`. The first and fourth conjuncts
  give those two bounded-below domains. No projection invertibility is concluded.

Dependency declarations read and used:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, through
  the existing `SemilinearSections.totalTensor`/`coefficientTotalTensor`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and its imported `Compactification`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its imported integer-ring constructions.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`:
  `CategoryTheory.HasRingedSiteTorAmplitudeOfUniverses` (the recorded ringed presentation).
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `spCoefficientCommRings`, `SpCoefficientTowersAbelian`, `sp_coefficient_towers_abelian`.
- `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `Base`, `Operations`, `D`, `Ev`, `tensor`,
  `pull`, `push`, `adjunction`, `Open`, `openD`, `openEvaluation`, `F`, `Fcomparison`,
  `Operations.openTensor_mate`, and `tower_shriek_levels` in `SpTowerShriek`.
- `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearDerivedSectionsData`, its `Data`,
  `Geometry`, `tensorEvaluation`/representative normalizations, and `evaluation_mate`.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers` and its quotients.
- Proof imports are the recorded modules of `def-kun-truncations`,
  `lem-sp-ringed-site-tor-flat-model`, `lem-weil-pbc-kflat-fixed-tensor-triangulated`,
  and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. The other proof modules are
  already public statement dependencies.

Reuse and import-cycle note: `Sheaf.Paper.TowerCompactSupportProjectionFormula` already
owns the proper/open arrow constructions, independent finite words and naturality
bifunctors. Reusing those published declarations avoids a second definition of these
notions. Its main theorem has this item as a DAG proof dependency. Therefore the
maintainer must omit the reverse proof-only import of this new module into that module
under stages/2-statements §3(7)'s explicit import-cycle exception. No declaration from
that module's main invertibility theorem is used by this statement. The existing
arrows themselves require no boundedness, constructibility or invertibility assumptions.

Edge cases read against the formulas: C=0 and B=0; singleton cohomology and Tor
intervals a=b and v=w; negative endpoints; empty schemes and identity open immersion;
natural index zero (positive exponent one); no characteristic or ell-invertibility
condition; B arbitrary outside the Tor tests; C need not be termwise flat; levels
need not be normalized; independent level representatives need not form strict towers.
The small pro-etale site retains object universe u+1 and morphism universe u.

Searches:

- `msearch.py ... leanfinder`: "Uniform bounded cohomology tensor finite Tor amplitude
  in derived category of varying coefficient sheaf towers and evaluation of proper and
  open projection maps" returned eight sheaf-cohomology/condensed-projectivity hits,
  none this statement.
- `msearch.py ... loogle`: "DerivedCategory.torAmplitudeIn, CochainComplex.mapBifunctor"
  returned zero, unknown identifier DerivedCategory.torAmplitudeIn (project declaration).
- `msearch.py ... grep`: "torAmplitude|TorAmplitude|projectionFormula" in
  `CategoryTheory` returned zero hits.
- `msearch.py ... leansearch`: "Bounded Tor amplitude and cohomology bounds for tensor
  of derived module sheaves and evaluation of projection maps" returned eight hits,
  including `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`, which supplies the
  bounded representative part but not this tower statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for projection-domain/tower-projection
  names found the existing `TowerCompactSupportProjectionFormula` helper arrows and
  evaluation laws, reused here, and unrelated projection formulas. `grep -rn` of the
  item id in `lean/WeilConjectures` found no match. Read the full recorded dependency
  signatures/docstrings and the current blueprint paragraph (3); read Stacks
  `sites-cohomology.tex` at lemma-tor-amplitude and lemma-bounded-flat-K-flat.

No statement correction, new node, dependency repair, or disputed statement.

## Second reading by Q35

The maintainer's independent second reader (cc review service, 2026-10-25) wrote
this section in place of the worker's in-thread self-check, which was not an
independent reading (delivery-errors H11). The Lean module and the node record
are unchanged.

Node statement, item by item, against the delivered Lean:

| Node | Lean | Verdict |
|---|---|---|
| prime ℓ, E/Q_ℓ finite, O_E | `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]` | exact |
| A_n = O_E/ℓ^n, n ≥ 1 | `SpTowerShriek.R l E n` = O_E/ℓ^(n+1), `n : ℕ` | exact (every positive level) |
| compactification X →j X̄ →p Y, f = pj | `c : Compactification f`; `c.i`, `c.g`, `c.Z` | exact |
| Tow(T,O_E), D(Tow), exact level evaluations | `SpTowerShriek.D`, `Ev` over `Base l E` | exact (recorded det-sp-tower-shriek-levels model) |
| simultaneous derived section models: ⊗^L, inverse image, j_!, Rp_* with adjunction | `base.calculus`, `tensor`, `pull`, `openD`, `push`, `adjunction`, `o : Operations` | exact; pinned package, not arbitrary functors |
| F = Rp_* j_! | `SpTowerShriek.F` = `openD ⋙ push` | exact |
| C ∈ D(Tow X), B ∈ D(Tow Y) | `C : D l E X`, `B : D l E Y` | exact |
| a ≤ b, u ≤ v (Lean v ≤ w) | `_hab`, `_hvw` | exact (renamed for universe `u`) |
| H^i(C_n) = 0 outside [a,b] | `_hC : ∀ n, IsGE a ∧ IsLE b` of `Ev n C` | exact |
| B_n Tor amplitude [u,v]: all degree-zero module sheaves N | `HasRingedSiteTorAmplitudeOfUniverses.{u+1,u,u+1,u+2}` (def-weil-proetale-tor-amplitude record): canonical K-flat derived tensor with every `L` in degree 0 | exact; no restriction on test modules; site universes u+1/u kept |
| C, B, j_!C bounded below | `C.IsGE a`, `B.IsGE v`, `(openD ..).obj C).IsGE a` | explicit lower bounds; slightly stronger wording than "bounded below", exactly what proof step 1 proves; accepted |
| C⊗^L f^{-1}B, j_!C⊗^L p^{-1}B have cohomology in [a+u,b+v] | `IsGE (a+v) ∧ IsLE (b+w)` for `tensor X (C, pull f B)` and `tensor Z (openD C, pull g B)` | exact |
| at every level: T_n supported in [a,b] for C_n | `∀ n, ∃ T`, `IsZero (T.X i)` outside [a,b], `Nonempty (Ev C ≅ Q T)` | exact (term support) |
| flat-term K-flat P_n supported in [u,v] for B_n | `IsZero (P.X i)` outside [v,w], `flatTerms` (IsFlatOnSite termwise), `IsKFlatIndependentCoefficients P`, `Nonempty (Ev B ≅ Q P)` | exact |
| signed total tensors T_n⊗f^{-1}P_n, j_!T_n⊗p^{-1}P_n represent the evaluated tensors | `Nonempty (Ev(tensor ..) ≅ Q (totalTensor (T, f^{-1}P)))`, the same with `levelOpenComplex` (termwise j_!) and `g^{-1}P` | exact; "represent" = isomorphic, no canonical iso claimed by the node |
| levels not required to form a strict tower | `∀ n ∃ T P`, no transitions | exact |
| π_p = counit transpose (ε⊗1 after pullback/tensor comparison) | existing `properMap` = `homEquiv (tensorPullback ≫ tensor.map (counit, 𝟙))` | exact |
| π_j = unit transpose (η⊗1) | `(o.openTensor c.i C (pull g B)).inv`, pinned by `Operations.openTensor_mate` as unit ⊗ 1 then tensorPullback⁻¹ | exact; source written with j^{-1}p^{-1}B, which node step 6 identifies with f^{-1}B |
| natural in both inputs | `maps_natural`-shaped conjunct (properMap, Rp_*π_j) and an explicit π_j naturality conjunct | exact |
| evaluations = finite proper/open projection maps | `properMap_evaluation`/`openMap_evaluation` equations ending in `finiteProperMap`, `finiteOpenMap` (independent finite counit/unit transposes) | exact |
| (Rp_*π_j)_n = Rp_*((π_j)_n) under (FD)_n ≃ Rp_* j_! D_n | last conjunct: `Ev(openMap) ≫ pushEvaluation = pushEvaluation ≫ Rp_*(Ev π_j)` | exact up to the exact `openEvaluation` coordinate change that `Fcomparison` composes on both sides |
| no constructibility/normalization/invertibility | none assumed or concluded | exact |

Edge cases: C = 0, B = 0; a = b, v = w; negative endpoints; empty X, Y;
j = id (then X = X̄); n = 0 (exponent 1); ramified E; C not termwise flat.
All covered: no hypothesis excludes them.

Searches: `rg` in lean/Sheaf and lean/WeilConjectures for `properMap`,
`finiteOpenMap`, `sfIntrinsicExtensionByZero .. mapHomologicalComplex`,
`HasRingedSiteTorAmplitudeOfUniverses`, `flatTerms`. The arrows and finite words
are those of the parent's module, reused. The termwise j_! complex functor has no
named owner, so `levelOpenComplex` (real data, the existing functor) is no duplicate.

Advisory (no change): `properMap`, `openMap`, `source`, `middle`, `openSource`,
`levelTensor`, `finiteProperMap`, `finiteOpenMap` are owned by the PARENT theorem
lem-sp-tower-compact-support-projection-formula. That node has this item in its
proof_deps, so citing it would close a DAG cycle. stmt_deps are unchanged from the
base. Stage 3 must leave out the reverse proof import of this module into
`Sheaf.Paper.TowerCompactSupportProjectionFormula` (stages/2-statements §3(7)
import-cycle exception). Moving the arrows into a definition node is
recommended. `SemilinearSections.flatTerms` is owned by
def-coef-semilinear-system-models (not a stmt_dep) and wraps the recorded
`IsFlatOnSite`.
