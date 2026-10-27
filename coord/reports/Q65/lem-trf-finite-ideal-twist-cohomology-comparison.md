## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteIdealTwistCohomologyComparison` states
`AlgebraicGeometry.Scheme.Modules.finite_ideal_twist_cohomology_comparison` and
its section-normalization and naturality clauses. All three theorem proofs are
`sorry`. Five definitions assemble existing image and comparison constructions;
none chooses unspecified data or contains a postponed proof.

Hypotheses and objects:

- `X Y : Scheme.{u}` and `f : Y ⟶ X` are the schemes and the indicated morphism.
  `[IsFinite f]` is exactly finiteness; both locally Noetherian hypotheses are
  retained explicitly as `[IsLocallyNoetherian X] [IsLocallyNoetherian Y]`.
- `F : Y.Modules` and `hF : RingedSpace.IsCoherent Y.toRingedSpace F` give the
  coherent coefficient module. This is the full finite-type/kernel definition
  of coherence, not just the quasi-coherent-and-finite-type conjunction.
- `J : X.IdealSheafData` is the established encoding of a quasi-coherent ideal.
  Its `toModules` and `toModulesι` are the module and its actual inclusion.
  No finite generation hypothesis is added for J.
- `L : X.Modules` and `[L.IsInvertible]` are precisely the invertible module.
  No properness, surjectivity, ampleness, flatness or nonemptiness is assumed.
- G is always the actual `(pushforward f).obj F`. The helper
  `finiteTwistIdealMultiple f J F` is H, the existing `idealModuleProduct` of
  `(tensorPullback f).map J.toModulesι ≫ tensorPullbackObjUnitToUnit f` with F.
  Thus its multiplication is exactly pullback of the ideal inclusion followed
  by the adjoint structure-sheaf map, tensoring and the left unitor. Its helper
  inclusion is the existing image inclusion. JG is the existing
  `idealModuleProduct J.toModulesι ((pushforward f).obj F)`.

Clause (1): the first three conjuncts assert coherence of G, H and JG separately.
The fourth is equality of their `imageSubobject`s inside G. Both underlying maps
are inclusions (image inclusion, respectively its direct image), so this states
exactly equality as submodules, without requiring definitionally equal chosen
image objects. The existential isomorphism e respects the inclusions into G;
this equation determines e uniquely and prevents an arbitrary identification.

Clause (2): `L.tensorPow n` is N_n. The existing tensor-power convention is
right associated and retains a terminal tensor unit. Its zero power is literally
the structure module. Canonical associators and unitors identify its positive
powers with the convention in the node (in particular the right unitor identifies
the first power with L). No mathematical power, case, or map is changed.
`boundaryPullbackPowIso f L n`, already constructed in the landed dependency
`def-sc-tensor-pullback-power-comparison`, is the canonical comparison
f-star N_n to (f-star L)^n. It is defined for every morphism and every module;
no closed-immersion or square-zero assumption enters this delivery. Its zero
component is the adjunction comparison followed by the structure-module iso.

The next three conjuncts assert invertibility of N_n, f-star N_n, and f-star L.
`PreservesFiniteLimits` and `PreservesFiniteColimits` of each right-tensor functor
encode exactness in the respective abelian module categories. All four are
conclusions, not added hypotheses. The next conjunct makes the particular
`finiteTwistProjectionHom` an isomorphism. This map is the upstream ordinary
`projectionHom` followed by transport from Mathlib's chosen pullback to the
explicit tensor pullback via the uniquely normalized adjunction.
`finiteTwistProjectionHom_app` states its formula on every open and pure tensor:
h tensor s maps to h tensor `tensorPullbackSection f N U s`. This latter section
is the existing actual 1 tensor s construction. Specializing s to a local generator
e identifies source and target with f-star H by the two coordinates
h maps to h tensor e and h maps to h tensor f-star e, and the stated equation
says the projection is the identity in those coordinates. The next main conjunct
is quasi-coherence of H tensor (f-star L)^n.

Clause (3): `finiteTwistCoefficientMap` is the exact composite e tensor 1,
ordinary projection, then direct image of 1 tensor `boundaryPullbackPowIso`.
For every `p n : ℕ`, the main theorem asserts invertibility of H^p of this
coefficient comparison and of the named `moduleCohomologyEdgeMap`. These are
exactly the two arrows in the displayed calculation. `finiteTwistCohomologyMap`
is their composite, and its invertibility is also stated. Cohomology uses the
recorded right-derived `RingedSpace.moduleCohomology`, with forgetful functors
to additive groups only when source and target have different rings of scalars.
The first comparison remains a map of O_X(X)-modules before forgetting.

Naturality: `finiteTwistCohomologyMap_naturality` takes a map v of the original
coherent coefficients, and any map q of the invertible power factors N_n.
It supplies h and w restricting v and f-star v to H and JG, with both actual
inclusion equations. For any inclusion-normalized e and e', it states the
coefficient square and the induced cohomology square. The upstairs factor map
is written explicitly as c_n inverse, f-star q, c'_n; hence it is the corresponding
canonical map, not an arbitrary morphism. Maps of L induce these maps of powers
by tensor functoriality, so the node's naturality in L is included. Taking
q to be the identity gives naturality in F alone, and taking v to be the identity
gives naturality in the invertible factor alone.

Dependencies read and used (full names have prefix `AlgebraicGeometry` unless noted):

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the public full
  `RingedSpace.IsCoherent`, `SheafOfModules.IsQuasicoherent`, and finite-type API.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`, the monoidal tensor and unit.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionAdjunction`,
  `tensorPullbackSection` and the real-data pullback construction it exposes.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the existing
  sheaf tensor monoidal API, publicly retaining its statement-dependency module.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology` and
  `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`:
  `RingedSpace.moduleCohomology`, `Scheme.Modules.moduleCohomologyEdgeMap`.
- `WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk`:
  `Scheme.idealModuleProduct`, `Scheme.idealModuleProductι`, now owned by the
  new existing:true definition node `def-trf-ideal-module-product-image`.
- `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`:
  `Scheme.Modules.projectionHom` and its section formula.
- `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`:
  `Scheme.Modules.boundaryPullbackPowIso`; its landed owning node was added to
  stmt_deps through `def-sc-tensor-pullback-power-comparison` solely to reuse
  this existing canonical map. The square-zero theorem itself is not used.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `Scheme.Modules.tensorPullbackObjUnitToUnit`, now cited through
  `def-sfb-tensor-pullback-structure-sheaf-map`, gives the actual map used in H.
- Every recorded proof dependency is imported, using its actual upstream module:
  `FinitePushforwardCoherent.isCoherent_pushforward_of_isFinite`,
  `CoherentFiniteTypeLocallyNoetherian.isCoherent_iff_isQuasicoherent_and_isFiniteType`,
  `AffinePushforwardIdealProduct.affine_pushforward_ideal_product`,
  `CoherentKernelCokernelLocallyNoetherian.isCoherent_kernel_cokernel_biprod_and_submodule`,
  `Modules.InvertiblePullbackTensor.invertible_pullback_tensor`,
  `TensorPullbackStructureSheaf.tensorPullbackObjUnitToUnit_isIso`,
  `QuasiCoherentTensorProductAffineSections.quasiCoherent_tensor_product_affine_sections`,
  `AffineMorphismCohomologyEdge.affine_morphism_cohomology_edge`, and
  `ModuleCohomologyFMapFunctorial`'s coefficient naturality declarations.
  In this list the part before the final dot abbreviates the module suffix,
  and declarations lie in `AlgebraicGeometry.Scheme.Modules`, except
  `affine_pushforward_ideal_product`, which lies in `AlgebraicGeometry.Scheme`.

Source checks: read Stacks coherent.tex's proof of 0B5V, its ideal-product
paragraph and three-line twisted cohomology calculation; also read 01YP and
089W. The selected calculation uses none of the ambient properness, surjectivity
or ampleness assumptions. The comparison is about ordinary sheaves of modules
and their cohomology, not an identification of complexes or derived objects.

Edge cases checked before and after writing: J=0 and F=0 give zero ideal images;
J=O_X gives H=F up to the image/unitor identification; f=id gives the same
ideal multiple; a non-flat finite closed immersion still uses an image, never
injectivity of f-star J into O_Y. n=0 uses O_X, O_Y and the canonical structure
comparison. p=0 is the actual edge map on global sections. Empty schemes require
no point or nonzero module. The single scheme universe is the project's existing
Scheme category convention; there is no independent lower test-object universe.
The independent review found an H2 definition-ownership fault. The repair below
completes the definition citations; no mathematical assertion is corrected.
No STATEMENT-DISPUTED issue was found.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: "Finite morphism coherent ideal multiple twisted
  by invertible sheaf cohomology projection formula". Eight results concerning
  Proj restrictions and affine limits, none the combined statement.
- `msearch.py ... loogle`: "AlgebraicGeometry.IsFinite, SheafOfModules".
  Zero results.
- `msearch.py ... grep`: "projection[Ff]ormula|projection_formula|tensorPower"
  in AlgebraicGeometry. Zero results from that Mathlib search.
- `msearch.py ... leansearch`: "Finite direct image coherent ideal product tensor
  invertible sheaf and cohomology comparison". Eight results: algebraic invertible
  tensor products, affine ideal transport, finite affine properties and monoidal
  facts. None is the target statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id: no match.
  Searches for projection, tensor powers and ideal twists located the reusable
  `Modules.ProjectionFormula`, `IdealModuleProductStalk`, and
  `SquareZeroTensorBoundaryComparisons` constructions. No existing declaration
  states all three clauses and the specified cohomology comparison. A follow-up
  search for tensorPullback/projection combinations found no existing duplicate
  of the transported ordinary projection helper.

Validation: the repair run of scompile.py compiled both sandbox and actual
library module cleanly (31.1 seconds and 15.1 seconds respectively). An initial compile found that the
structure-module comparison needed a public import and that the chosen product
inclusions had no exported Mono instances. The final file publicly imports the
comparison and uses imageSubobject for the equality of submodules. Neither repair
changes the mathematical assertion.

## Second reading by Q65

I reread the node and the complete module after compilation. This is the worker's
own second pass; the maintainer supplies the independent delivery review.
The input binders preserve finite f, both locally Noetherian schemes, coherent F,
quasi-coherent ideal J and invertible L. I checked the three coherence conjuncts,
equality inside G and the normalization of e; all are present. I checked the
three invertibility assertions, exactness for both tensor functors, the actual
canonical power comparison, the normalized projection formula and quasi-coherence
of its upstairs twist. I checked both specified cohomology arrows, their composite,
and the explicit naturality squares. I also checked n=0, p=0, the absence of
flatness, and that the pullback comparison does not impose the square-zero
hypotheses of its owning module's separate theorem. The only presentation choice
is the existing tensor-power convention, compared by associators and unitors.
No mathematical mismatch or further change was found in this pass.


## Returned delivery repaired

The independent review of immutable head `00121a19e253` accepted the mathematics
and Lean and returned the dependency ownership metadata under H2. Each numbered
request is repaired:

1. Replaced `lem-sc-square-zero-ideal-tensor-unit` in stmt_deps with
   `def-sc-tensor-pullback-power-comparison`. Read that node and the complete
   `boundaryPullbackComparison`, `boundaryPullbackTensorIso` and recursive
   `boundaryPullbackPowIso` definitions. The node owns the exact construction
   used in the coefficient comparison, without a square-zero theorem assumption.
   The item's statement now cites that definition at its canonical power iso.
2. Added `def-sfb-tensor-pullback-structure-sheaf-map` to stmt_deps and cited it
   in the definition of H in the statement text. Read that existing:true node
   and `tensorPullbackObjUnitToUnit`'s adjunction construction. This is exactly
   the map used by `finiteTwistIdealMultiple` and its inclusion.
3. Added `def-trf-ideal-module-product-image` with existing:true on
   `AlgebraicGeometry.Scheme.idealModuleProduct` and
   `AlgebraicGeometry.Scheme.idealModuleProductι`, in the existing module
   `WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk`. The item cites
   this definition in both its statement and stmt_deps. There is no new Lean
   implementation. The two definitions are actual image data, and neither
   requires injectivity of the map J to O_X. The new node therefore covers
   the ordinary ideal multiple and the non-flat pulled-back ideal multiple.

The sandbox was compared with the current repository node and the accepted
returned Lean text: only definition ownership, citations and reporting change.
The mathematical theorem signatures and all auxiliary definition bodies stay
as accepted. The Lean module's documentation now names the three definition
owners. Delivery tooling rebases the complete repair on the current main branch.

## New nodes

`def-trf-ideal-module-product-image` records the existing ideal multiplication
image and image inclusion for any map i:J to O_X, without Mono i. Its source is
Stacks 01YP's image definition and the 0B5V ideal-product calculation, also
matching the existing source docstrings' 0CYV reference. Its primary Lean
signature is copied verbatim from the existing def, and lean.declarations lists
both definitions. Mathlib searches through LeanSearch, Loogle and grep found
only generic images and ring-ideal facts; direct source search found these two
exact existing definitions. A scan of every definition node's lean record found
no owner. blueprint_refs.py search ideal-module-product returned zero blueprint
nodes. The new node has no theorem or postponed data and creates no new module.
Edge cases i=0, J=0, F=0, i=id of O_X, and non-injective i all use the same
image construction; no quasi-coherence or injectivity hypothesis is smuggled in.

## Statement corrected

This is a citation-only H2 correction requested by the maintainer. The source
is Stacks 0B5V's ideal-product/twisted-cohomology calculation and 01YP's image
construction. The prior text described the correct maps but omitted their
plain-definition owners. The new text names the structure-sheaf map and cites
its owner, cites the image definition, and cites the canonical power-comparison
owner. The old mathematical assertion is preserved verbatim apart from those
citation insertions. A statement_change record is supplied because the JSON
statement text changes, even though no mathematics changes.

Every current direct citer was found by searching the exact item id and then
checking stmt_deps and proof_deps:

- `lem-trf-finite-surjective-ample-reflection`: holds true. Its use of coherence,
  equality of ideal multiples and the two cohomology isomorphisms in ideal
  devissage is unchanged.
- `lem-sfb-dominant-flag-line-kempf-vanishing`: holds true. The specialization
  J=O_Q, n=1 used with the finite Frobenius map has the same hypotheses and
  canonical projection/edge isomorphism.

No citer is edited. Proof steps and proof_deps stay unchanged. old_stmt_deps
records the current repository base, which had no extra square-zero theorem
statement dependency; that theorem was present only in the returned delivery.

Repair second pass: rechecked all three ownership records against the bodies
and ensured every added definition is cited in the item statement and stmt_deps.
The independent return already checked every mathematical clause, naturality
and the listed edge cases. This pass found and repaired exactly the three H2
ownership omissions and did not change the accepted Lean statements.

The old statement, verbatim from the current base, is:

```text
Let $f:Y\to X$ be a finite morphism [def-weil-finite-integral-morphism] of locally Noetherian schemes [def-pc-scheme, pqf-def-locnoeth]. Let $\mathcal F$ be a coherent $\mathcal O_Y$-module and $\mathcal J\subseteq\mathcal O_X$ a quasi-coherent sheaf of ideals [pqf-def-coherent]. Let $\mathcal L$ be an invertible $\mathcal O_X$-module [def-sc-invertible-module]. Write $\mathcal G=f_*\mathcal F$, with module direct image and pullback as in [def-pc-module-pullback]. Using the sheaf tensor product [def-pur-sheaf-tensor-product], let $\mathcal H=f^{-1}\mathcal J\cdot\mathcal F\subseteq\mathcal F$ be the image of the multiplication map $f^*\mathcal J\otimes\mathcal F\to\mathcal F$ induced by $\mathcal J\hookrightarrow\mathcal O_X$ and $f^\sharp$. Thus $\mathcal H$ is generated locally by products of sections pulled back from $\mathcal J$ with sections of $\mathcal F$. Likewise $\mathcal J\mathcal G\subseteq\mathcal G$ is the image of $\mathcal J\otimes\mathcal G\to\mathcal G$.
(1) $\mathcal G$, $\mathcal H$, and $\mathcal J\mathcal G$ are coherent, and $\mathcal J\mathcal G=f_*\mathcal H$ as submodules of $\mathcal G$.
(2) For $n\in\mathbf N$ put $\mathcal N_n=\mathcal L^{\otimes n}$, with $\mathcal N_0=\mathcal O_X$; likewise $(f^*\mathcal L)^{\otimes0}=\mathcal O_Y$. The modules $\mathcal N_n$, $f^*\mathcal N_n$, and $f^*\mathcal L$ are invertible; tensoring by either $\mathcal N_n$ or $f^*\mathcal N_n$ is exact. There is a canonical isomorphism $f^*\mathcal N_n\cong(f^*\mathcal L)^{\otimes n}$. The ordinary projection map
$$f_*\mathcal H\otimes\mathcal N_n\longrightarrow f_*(\mathcal H\otimes f^*\mathcal N_n)$$
is an isomorphism. On an open trivializing $\mathcal N_n$, its restrictions identify with the identity of $f_*\mathcal H$; it is the map multiplying a section of $\mathcal H$ by the pulled-back section of $\mathcal N_n$. The sheaf $\mathcal H\otimes(f^*\mathcal L)^{\otimes n}$ is quasi-coherent.
(3) For every $p,n\ge0$, the equality in (1), the projection map in (2), and the edge map $e_{f,\mathcal M}:H^p(X,f_*\mathcal M)\to H^p(Y,\mathcal M)$ of [def-weil-pbc-module-cohomology-fmap](c) for $\mathcal M=\mathcal H\otimes(f^*\mathcal L)^{\otimes n}$ give natural isomorphisms
$$H^p(X,\mathcal J\mathcal G\otimes\mathcal L^{\otimes n})\cong H^p(X,f_*(\mathcal H\otimes(f^*\mathcal L)^{\otimes n}))\cong H^p(Y,\mathcal H\otimes(f^*\mathcal L)^{\otimes n}),$$
where cohomology is [pqf-def-cohomology]. No properness, surjectivity, or ampleness hypothesis is imposed.
```
