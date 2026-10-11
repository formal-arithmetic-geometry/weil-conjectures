## Worker report

The module states `moduleCohomologyFMap_basic_properties` for an h-map of scheme modules. Its four conjuncts render: (1) O_Y(Y)-linearity by existence of a morphism from H^p(Y,G) to the restriction of scalars of H^p(X,F), whose underlying additive map is `moduleCohomologyFMap`; (2) degree zero by existence of the derived-functor/global-sections isomorphisms and the commuting square with the global-sections map; (3) the identity case for every scheme and module morphism; and (4) restriction for every open, with the restriction/pullback isomorphism and the tensor pullback unit.

Dependencies used are `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap` (`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap`), `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` (`exists_tensorPullbackAdjunction`), and Mathlib `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, `restrictAdjunction`. The scheme notion is Mathlib `AlgebraicGeometry.Scheme`.

Edge cases checked include p = 0, arbitrary natural p, arbitrary schemes including empty schemes, arbitrary open U including ⊤ and ⊥, and zero module objects. The scalar action uses `h.appTop.hom` and restriction of scalars, so no injectivity or nonzero assumptions are imposed.

Searches: `msearch.py leanfinder` and `loogle` for module-cohomology functoriality and linearity (no exact declaration); grep of Mathlib sheaf cohomology and `WeilConjectures` (only abstract derived-functor maps); `rg` over `lean/Sheaf` (only the defining module and related resolution declarations). No existing statement matched.

No `STATEMENT-DISPUTED` flag.

## Earlier second reading (a previous round; superseded)

Read the node and module line by line. The binders h, G, F, φ, and p match the node. The linearity clause uses the stated h^sharp map (`h.appTop.hom`); degree zero explicitly records the two global-section identifications and the induced map; identity quantifies over arbitrary schemes and module morphisms; restriction quantifies over opens and supplies the restriction-to-tensor pullback isomorphism before comparing the two cohomology maps. No hypotheses or edge cases were dropped.

## Second reading by R1

I reread the DAG statement, its Stacks source, and the Lean declaration item by item.
The objects are `h : X ⟶ Y`, `G : SheafOfModules Y`, `F : SheafOfModules X`,
`φ : G ⟶ pushforward h F`, and `p : ℕ`; Lean binds exactly these over one scheme
universe. The first conclusion conjunct is the O_Y(Y)-linearity assertion: its witness
`L` is a `ModuleCat` morphism into `ModuleCat.restrictScalars h.appTop.hom`, and the
underlying additive map is exactly `moduleCohomologyFMap h φ p`. This matches the
source's h-sharp action and imposes no injectivity, finiteness, or nonzero hypothesis.

The second conjunct quantifies isomorphisms `eG` and `eF` from degree-zero derived
cohomology to the global-sections functors and states the commuting square with the
map induced by `φ`; this is precisely the stated section-map formula (composition
orientation agrees with the node). The third conjunct quantifies arbitrary `Z`, both
module objects, and `ψ`, and identifies the identity h-map with the ordinary functorial
map on `H^p(Z,-)`, exactly clause (3). The fourth conjunct quantifies every open
`U : Y.Opens`, supplies `κ : (restrictFunctor U.ι).obj G ≅ (tensorPullback U.ι).obj G`,
and states that the restriction-adjunction cohomology map followed by `H^p(κ.hom)`
equals the tensor-pullback unit map. Since `moduleCohomologyRestriction` is defined as
the former map and the node's `κ` is the same open-immersion comparison, this is the
node's `H^p(κ⁻¹) ∘ j*` equality with both sides written in the opposite composite
orientation. No clause is omitted or strengthened.

Edge cases checked: `p = 0` and arbitrary natural degree; empty and terminal opens
(including `⊥` and `⊤`); empty schemes; zero module objects; and arbitrary
characteristic. The shared universe `u` is the scheme/module universe required by the
Mathlib sheaf encodings and does not exclude these cases.

Searches were repeated with `msearch.py` LeanFinder and Loogle queries for module
cohomology functoriality, linearity, and restriction, plus `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`. Only the defining `moduleCohomologyFMap` and the
abstract derived-functor declarations were found; no existing declaration states this
four-clause result. The recorded dependency declarations were opened and match their
uses (`ModuleCohomologyFMap`, `TensorPullbackAdjunction`, and Mathlib restriction
functors).

The only repair was documentary: I expanded the theorem docstring with the source
proof plan and all comparison lemmas required by the node, satisfying the stage-2
proof-step documentation rule. The Lean signature and node statement were otherwise
already exact, and the module compiles cleanly with its sole `sorry` proof.
