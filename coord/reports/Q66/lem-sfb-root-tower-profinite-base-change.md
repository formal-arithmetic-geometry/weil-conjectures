# Full root towers and profinite base change

## Worker report

Stage 2 of `lem-sfb-root-tower-profinite-base-change`. The live node has a stage-1
split reviewed PASS by Q57, but no `lean` attachment. That stage-1 review does not
already supply the stage-2 statement. There was no retained sandbox report and no
released repair note for this item. This delivery changes only the item's `lean`.

Module: `Sheaf.Paper.RootTowerProfiniteBaseChange`. It states the algebra and scheme
comparisons, principal-open comparisons, affine pro-etale chart property, profinite
parameter comparisons, and naturality. Twelve named theorem proofs are `sorry`.
Five helper definitions have real data: quotient coefficient change, its base-change
specialization, the displayed tensor ring R_P, its tensor map, and its root-algebra
map. No arbitrary comparison map, choice of roots, or new root algebra is assumed.
The relation-inclusion proof required by the quotient map is its own named theorem.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| p prime | `(p : ℕ) (hp : p.Prime)` on the root comparison theorems. The coefficient-map helpers themselves work for any p. |
| R and S commutative rings | `R S : Type u`, `[CommRing R]`, `[CommRing S]`; no nontriviality or characteristic hypothesis. |
| r parameters | `J : Type u`, `[Fintype J]`, `t : J → R`, using precisely the recorded finite-family root algebra. Take `J = Fin r` for the node's enumeration; equivalently any finite parameter family can be enumerated. |
| The full compatible prime-to-p root tower | `FullParameterRootAlgebra p t` and `fullParameterRoot p t n i`, with `n : TameRootOrder p`. The dependency's actual polynomial quotient includes both power and divisibility relations; it is not an arbitrary algebra equipped with roots. |
| Every ring map f | `(f : R →+* S)` for `fullRootBaseMap`, scheme base change, and opens. `fullRoot_baseChange` uses `[Algebra R S]`, which specifies exactly a ring map and can be instantiated by `f.toAlgebra`. |
| Canonical S-algebra isomorphism | `fullRoot_baseChange`: `∃ e : S ⊗[R] FullParameterRootAlgebra p t ≃ₐ[S] FullParameterRootAlgebra p (fun i ↦ algebraMap R S (t i)), ...`. |
| s tensor 1 maps to s | The full pure-tensor formula sends `s ⊗ₜ[R] a` to the coefficient s times `fullRootBaseMap ... a`; put `a = 1`. Also follows from `≃ₐ[S]`. |
| 1 tensor x(i,n) maps to x(i,n) | Put `s = 1` in that formula and use the labelled-root equality in `fullRootFamilyMap_normalization`. This theorem also specifies the coefficient formula and uniqueness on coefficients and all roots. |
| Identity and composite base changes | `fullRootBaseMap_identity_composition` gives equality of the root maps. `fullRoot_baseChange_unit` gives `e (r ⊗ₜ a) = r • a`. `fullRoot_baseChange_composition` explicitly gives `e₂ (v ⊗ₜ[S] e₁ (s ⊗ₜ[R] a)) = e₃ ((v * algebraMap S V s) ⊗ₜ[R] a)`. Its h₁,h₂,h₃ are the already specified normalization formulas, not new assumptions on the rings. A scalar tower specifies exactly the composite ring map. |
| Base-changed tower spectra and their structural projections | `fullRoot_schemeBaseChange` gives a scheme isomorphism to the actual pullback, with equations for both `pullback.fst` and `pullback.snd`. |
| Each subset I and its principal open | `I : Finset J`; `fullRoot_openBaseChange` gives an isomorphism of `Scheme.Opens.toScheme` with the scheme pullback. The open is `PrimeSpectrum.basicOpen (algebraMap ... (∏ i ∈ I, t i))`. The two equations fix the map into the original tower and its map to Spec S. Thus the conclusion includes the restricted structure sheaf. |
| P,Q arbitrary profinite sets and the actual X[P] | `P Q : Profinite.{u}`, using `Scheme.UniversalCover.profiniteProduct`, its base projection and its mixed map, all from the recorded dependency. These unfold to `profiniteToProEtOf` and actual scheme pullbacks over the universe-lifted integer spectrum. |
| R_P = R tensor_Z LC(P,Z) | `rootTestRing R P` abbreviates exactly `R ⊗[ℤ] LocallyConstant P ℤ`. `rootTestRingMap f a` tensors f with `LocallyConstant.comapRingHom a.hom.hom`. |
| U[P] = Spec R_P with affine pro-etale structure map | `fullRoot_profiniteCharts` gives a family of scheme isomorphisms normalized by the R and LC projections, together with `IsAffineHom` and `WeaklyEtale` of the actual test projection. This is the site's stipulated weakly-etale convention, not the more restrictive literal pro-etale-morphism predicate. |
| T_R[P] is the root tower over R_P | `fullRoot_profiniteBaseChange` gives isomorphisms from the root spectrum with parameters `algebraMap R (rootTestRing R P) (t i)` to the actual `profiniteProduct` of the original tower. Both the root projection and LC projection are fixed. |
| The same indicated opens over R_P | The `∀ I, ∃ d` clause of that theorem is an isomorphism between the actual principal open over R_P and the inverse-image open inside T_R[P], with the equality `d.hom ≫ inclusion = inclusion ≫ e.hom`. |
| Maps of profinite parameters, ring base change, and original projections commute | The final quantified equalities of `fullRoot_profiniteCharts` and `fullRoot_profiniteBaseChange` state the simultaneous mixed naturality squares for every f and a. `fullRootTestMap` is the canonical quotient map on these mixed parameters. Projection equations are part of each isomorphism's conclusion. On open comparisons, the equality with the inclusions makes d exactly the restriction of e; monicity of the inclusions gives the same naturality on the opens. The two pullback projections uniquely determine the ring-base-change comparisons, so root-map identity/composition gives their scheme identity/composition coherence as well. |
| (X[P])[Q] is X[P times Q] for every affine X | `fullRoot_profiniteProducts` quantifies `X : Scheme.{u}` with `[IsAffine X]` and returns an isomorphism with `profiniteProduct X (P ⨯ Q)`. Its two projection equations use `prod.fst` and `prod.snd`; their further composite gives the projection to X. |
| Product isomorphism commutes with parameter maps and base change | The last clause of `fullRoot_profiniteProducts` quantifies every morphism `f : X' ⟶ X` between affine schemes and every `a : P' ⟶ P`, `b : Q' ⟶ Q`, and compares the nested map with `profiniteProductMap f (prod.map a b)`. Thus arbitrary affine ring base changes are included. |

The existential isomorphisms are canonical: the pure-tensor formula determines the
algebra map; the two projections determine each scheme comparison; and the monic
open inclusions determine each open restriction. There are no bare unconstrained
`Nonempty` comparisons. Different universes of input rings/finite parameters may
be placed in a common arbitrary universe u, matching the recorded dependency's
own universe convention. No universe is fixed to zero, and no site universe is
identified with a morphism universe.

Dependency declarations read and used:

- `Sheaf.Paper.FullParameterRootTower`: `AlgebraicGeometry.ProEtale.FullParameterRootAlgebra`, `fullParameterRoot`; the full signatures and quotient construction were read. The module also supplies the actual parameter indexing convention.
- `Sheaf.Paper.StrictLocalKummerTameModule`, imported by that dependency: `TameRootOrder`, `tameRootRelations`, `tameRootAlgebra`; both relation families were read.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`: `AlgebraicGeometry.Scheme.UniversalCover.profiniteProduct`, `profiniteProductBase`, `profiniteProductMap`; the actual scheme maps and their full definitions were read. No pointed-cover hypotheses are imposed on these definitions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `profiniteToProEtOf`, `profiniteToScheme`, `toSpecZ`, `weaklyEtale_toSpecZ_profiniteToScheme`, `preservesFiniteLimits_profiniteToProEt`. The source uses Spec of ULift Z for the common terminal scheme and ordinary locally constant integer functions for the charts.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` is the recorded weakly-etale over-category. The forgetful functor is full, and objects carry weakly-etale structural maps.
- Proof interfaces: `Ideal.quotientMap`, `MvPolynomial.map`, `Algebra.TensorProduct.map`, `AlgebraicGeometry.pullbackSpecIso`, `Scheme.preimage_basicOpen_top`, `isAffineHom_of_isAffine`, and categorical `pullback.fst` / `pullback.snd`. These implement the node's seven-step proof without restating its prerequisites.

Source reading: opened the current blueprint's direct-image proof (3). It gives the
ambient stability argument, not a separate root-tower theorem, exactly as the
node's source and proof_origin already disclose. The docstrings follow the live
node's explicit seven-step universal-property proof and the cited Stacks inputs.

Edge cases checked before and after writing:

- Empty J (r=0): no root equations or variables, no `[Nonempty J]`; the same quotient and maps give the base ring comparison.
- Empty I: the finite product is 1, so its open scheme is the whole tower and all projection equations remain well-typed.
- Empty P or Q: LC(empty,Z) is the zero ring. No label is chosen, no evaluation at a point is used, and products and affine scheme comparisons include the resulting empty schemes.
- R or S zero: only `CommRing` is assumed. Tensor products, quotient maps and basic opens remain the actual zero-ring constructions.
- p need not be invertible in the rings. There is no normality, strict henselianity, noetherianity, or flatness assumption on f.
- Identity f and identity parameter maps: quotient generation and the normalized tensor formula give the identity comparisons; composable maps give exactly the stated reassociation formula.

Searches for existing declarations:

- `msearch.py leanfinder`, query `Full compatible prime-to-p root towers commute with arbitrary scalar extension and profinite parameter products`: eight results about lifts/perfections and integral restriction; none is this statement.
- `msearch.py leansearch`, query `Compatible root algebra commutes with extension of scalars`: eight results about algebra towers, root pairings and scalar actions; none is this compatible-root assertion.
- `msearch.py loogle`, query `Algebra.TensorProduct, AlgEquiv`: no result; service reported the first identifier unknown. Repeated with the valid quoted-name query `"TensorProduct", "LocallyConstant"`: zero hits.
- `msearch.py grep`, query `(rootTower|tameRoot|fullParameterRoot|profinite).*(baseChange|base_change|tensorProduct|puncture)`: zero Mathlib hits.
- `rg` with that expression and the item id over the named `lean/WeilConjectures` and `lean/Sheaf` trees found downstream puncture/boundary modules, not the requested comparison statement. Their relevant definitions were inspected; no downstream module is imported by this delivery.
- `rg '(⊗\[ℤ\]|TensorProduct ℤ).*LocallyConstant|LocallyConstant.*(⊗\[ℤ\]|TensorProduct ℤ)|rootTestRing|fullRootFamilyMap'` over both source trees found no existing tensor-ring helper or root-family map.

No statement correction, new independent notion, dependency interface repair, or
STATEMENT-DISPUTED flag is needed. All helpers belong to the maps/comparisons
specified by this same node, and all are listed in `lean.declarations`.

## Second reading by Q66

I reread the live node and the finished module clause by clause after the first
clean compile. This is a second pass by this worker; no additional agent was
started, as required by the dispatcher. The maintainer's independent review remains
the independent reading.

The second pass added explicit tensor-unit and tensor-composition assertions,
rather than leaving tensor coherence only implicit in the coefficient-map law.
It checked that punctures are scheme isomorphisms (not merely an equality of
underlying opens), and that the profinite tower isomorphism has both projections
and simultaneous ring/parameter naturality. It checked the product comparison's
two projection maps and the joint naturality in f,a,b. It found no excluded empty
or zero-ring case, extra invertibility assumption, arbitrary comparison datum,
or unbound variable. The explicit Scheme.Opens constructors resolve the
type-alias field-notation issue without introducing another definition of an open.

## Validation

Every compile uses the prescribed `scompile.py` wrapper in module mode. The
initial version exposed a field-notation elaboration issue for opens of Spec;
fully qualified `Scheme.Opens.toScheme` / `Scheme.Opens.ι` fixed it. The version
before the explicit coherence additions compiled both as the sandbox probe and
as `Sheaf.Paper.RootTowerProfiniteBaseChange` without errors or warnings. The final module, including both tensor coherence assertions, also compiled cleanly
in both modes (5.8 and 5.6 seconds). The first preflight found that the JSON
signature extraction stopped at a named argument `X := ...`; the extraction now
stops at the theorem proof delimiter and records the complete signature verbatim.

Final `deliver2.py --no-push`: OK, commit `96b20ab58a5` passes preflight and
compiles. Static comparison also confirms the live node differs only in `lean`,
all 17 declarations are recorded, the 12 theorem proofs are named `sorry` proofs,
and every Lean line has at most 100 characters.
