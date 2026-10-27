## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQuasiCoherentGeometricStalkTensor` states
`AlgebraicGeometry.AlgebraicSpace.quasiCoherent_geometricStalk_tensor`, with its sole
proof `sorry`. It introduces no definitions and changes no mathematical statement.
The source was read in `literature/stacks-project/spaces-properties.tex`,
`lemma-stalk-quasi-coherent` (Tag 05VP), lines 5288–5328, and
`lemma-describe-etale-local-ring` (Tag 04KF), lines 3881–3905.

Hypothesis and clause correspondence:

- The scheme S is `{S : Scheme.{u}}`; the algebraic space is `{X : AlgebraicSpace S}`.
- The quasi-coherent module M is `(M : X.QCoh)`, the recorded full subcategory for
  Mathlib `SheafOfModules.IsQuasicoherent`. Its underlying module is `M.obj`.
- An arbitrary étale scheme map e:U→X is `(T : X.EtaleSite)`: the underlying scheme
  is `X.etaleForget.obj T`, its map is `T.obj.hom`, and `T.property` is precisely
  representable étaleness. No atlas or surjectivity is required.
- The algebraically closed field is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`.
  `(s : Spec (.of Ω) ⟶ S)` gives its structural map. The geometric lift ū is
  `(t : Over.mk s ⟶ T.obj.left)`. Thus x̄ is literally `yoneda.map t ≫ T.obj.hom`;
  there is no separate compatibility hypothesis or choice of its image.
- The ordinary center u is
  `(Scheme.SpecToEquivOfField Ω (X.etaleForget.obj T) t.left).1`, including the
  residue-field embedding through the existing scheme geometric-point equivalence.
- M_U is exactly `((schemeRestriction X T).obj M.obj)`. Its value on an open W is
  M evaluated on the composite open subscheme W→U→X, with scalars through the
  existing `schemeOpensRingHom`. This is restriction to opens, which the recorded
  Zariski/étale quasi-coherent equivalence specifies as its inverse. No arbitrary
  quasi-coherent Zariski object or unspecified descent isomorphism is introduced.
- A=O_{U,u} is the scheme's `presheaf.stalk` at that center.
  N=(M_U)_u is the value of the recorded `RingedSpace.moduleStalkFunctor` at M_U;
  its carrier is the ordinary additive-group stalk of `M_U.val.presheaf`.
- B=O_{X,x̄} is the existing `SingleComplex.stalkRing s x̄`.
  M_{x̄} is `(SingleComplex.stalkModel s x̄).modules.obj M.obj`. Both come with
  actual regular-function/module-section colimit cocones on the fixed small affine
  pointed étale basis. Affine cofinality identifies this with the source's
  all-pointed-neighbourhood stalk, without changing rings or section universes.
- The theorem supplies `φ : A →+* B`, together with its formula on every compatible
  ordinary function germ. An open W containing u, a pointed affine neighbourhood V,
  and `f : neighbourhoodChart.obj V ⟶ (schemeOpens X T).obj W` give a common
  refinement. The equation `(V.hom.left.left ≫ f.hom.left.left) ≫ W.ι = t.left`
  ensures that it is pointed over ū, not merely over x̄. The formula sends an
  ordinary germ r_u to the geometric germ of its pullback. `schemeOpensRingHom`
  makes the canonical identification of sections on W with global functions on
  its open subscheme explicit. These equations characterize φ on all ordinary
  germs, and hence uniquely characterize the natural germ homomorphism of 04KF.
  φ is not an unconstrained map or a stronger hypothesis.
- `E : (ModuleCat.extendScalars φ).obj N ≅ M_{x̄}` is an isomorphism in
  `ModuleCat B`, so is B-linear. Mathlib writes this scalar extension as B⊗_A N.
  Tensor symmetry identifies it canonically with the source's N⊗_A B; the same
  pure-tensor formula after swapping the factors gives the stated orientation.
- The final equation quantifies over the same common pointed neighbourhood,
  a section m of M_U on W, and an arbitrary regular function r on V. It says
  `E.hom (germ(r) ⊗ germ(m)) = germ(r • M.obj.val.map f.op m)`.
  The RHS is the actual restriction of m followed by multiplication, not an
  abstract module map. Every ordinary germ and ring germ has such simultaneous
  representatives after refinement; pure tensors generate the tensor product.
  The equation thus specifies exactly the canonical map on every element.
- No finite generation, finite presentation, Noetherian, quasi-compactness,
  separatedness, characteristic, or surjectivity hypothesis occurs. The only
  universe is the original scheme/section universe u, also used for Ω and the
  existing colimit modules; no equality of distinct site universes is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Scheme.SpecToEquivOfField`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `IsEtale`, `etaleForget`, the actual `structureSheaf`, and `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  the existing `SheafOfModules.IsQuasicoherent` specialization.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `Scheme.Modules.zariskiEtaleModuleRestriction`,
  `scheme_zariski_etale_quasiCoherent_equivalence`, with its section-normalized
  adjunction/counit. Its full theorem was read; the M_U object is defined by the
  already available, explicit restriction, rather than a choice of an equivalence.
- `Sheaf.AlgebraicGeometry.SpaceStrictLocalFlatness`: `strictLocalChartComparison`
  and `schemeStrictLocal_presentation`, both germ-normalized. The present ring
  equation is their chart local-ring map characterized directly on representatives.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, `stalkObj`, and Mathlib's ordinary germ
  carriers and scalar multiplication; `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor` bundles the same ordinary scheme stalk over
  the commutative local ring (the ringed-space specialization).
- `Mathlib.LinearAlgebra.TensorProduct.Basic` and
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: the existing `TensorProduct`,
  `TensorProduct.lift`, and `ModuleCat.extendScalars`, with ring-first pure tensors.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`,
  `schemeOpens`, and `schemeOpensRingHom` (the complete signatures and docstrings read).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels`:
  `SingleComplex.Neighbourhood`, `neighbourhoodChart`, `ringDiagram`, `StalkModel`,
  `stalkModel`, and `stalkRing`, with ring/module colimit and scalar-germ equations.
- Proof-only imports: `Mathlib.AlgebraicGeometry.Sites.EtalePoint` (the recorded
  cofiltered pointed-neighbourhood instance),
  `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap`
  (`Point.sheafFiberComapIso` and its unit/germ formula), and
  `Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative` (the point and
  germ-normalized inverse-image comparison). The proof dependencies
  `lem-sfb-etale-geometric-point-specified-lift` and
  `lem-sfb-ringed-topos-pullback-stalk` have neither usable Lean records nor
  Mathlib matches in the read DAG, so there is no module to import for them;
  they remain named in the natural-language proof and unchanged proof plan.

The item gains three already-landed statement dependencies:
`def-trf-space-module-scheme-restriction`, `def-sfb-space-geometric-stalk-models`,
and `def-pc-module-stalk-functor`. This is the permission in brief-stage2 §5 for
adding already-landed interfaces. No new node or dependency repair is needed.

Edge cases checked before drafting: an empty X or an empty chart has no t and is
therefore covered without adding nonemptiness; the zero module makes both stalk
modules and the tensor zero; Ω can have arbitrary characteristic; an identity
scheme chart gives the ordinary strict-henselization comparison; arbitrary
infinite free quasi-coherent modules remain allowed; a nonsurjective étale chart
is allowed; W may be any open containing u, and all scalar and section germs
are allowed, not only global sections of U. No disputed statement or source
correction was found.

Searches for an existing statement (msearch wrappers, 2026-10-24; exact service
results are in the sandbox `searches.jsonl`):

- LeanFinder: “The geometric stalk of a quasi coherent module on an algebraic
  space is its ordinary stalk on an etale chart tensored with the geometric
  local ring”. Eight hits, all `ModuleCat.Tilde` ordinary affine/Zariski stalk
  and localization comparisons (`toStalk`, `stalkIso`, `stalkToFiberLinearMap`,
  `localizationToStalk`, and their formula lemmas); none is this space comparison.
- Loogle: `"stalk", "tensor"`. Six hits: ring-surjective-on-stalks tensor maps,
  embeddings of prime spectra under tensor products, and `Module.rankAtStalk`
  tensor formulas. None concerns this geometric module stalk.
- LeanSearch: “Quasi coherent module geometric stalk equals tensor base change
  of ordinary etale chart stalk”. Eight hits on `SheafOfModules.IsQuasicoherent`,
  `ModuleCat.Tilde.toOpen_germ_apply`, and `Scheme.Modules.restrictStalkNatIso`;
  none gives the claimed map or its isomorphism.
- msearch grep: `stalk.*[Tt]ensor|[Tt]ensor.*stalk|AlgebraicSpace` in
  Mathlib/AlgebraicGeometry. One hit, `Morphisms/SurjectiveOnStalks.lean`, unrelated.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for geometric stalks,
  stalk/tensor comparisons and the item id: existing ordinary tensor stalk
  comparisons and space derived-pullback/stalk-calculus interfaces were found.
  None compares an arbitrary quasi-coherent space module's geometric stalk with
  its ordinary chart stalk. In particular the existing normalized geometric
  models provide the stalks, not this ordinary-to-geometric comparison.
  The exact item id has no upstream declaration; the existing chart-support
  theorem cites this item only in its proof documentation.

Validation: scompile.py compiled both its sandbox and library module form cleanly
in 5.1 seconds each before the final explicit dependency-import additions.
The mandatory delivery dry run recompiles the final module.

## Second reading by Q48

A separate pass over the node, its source, the full statement signature, and the
stalk/restriction declarations was performed by this dispatcher worker; no second
agent was launched. The maintainer performs the independent delivery review.

The check matched each binder and clause listed above to the node. In particular,
T really is an arbitrary scheme étale chart; t fixes the algebraically closed
field and its center; M is quasi-coherent for the original small étale structure
sheaf; N uses the ordinary Zariski stalk of the actual restriction; B and the
output are the recorded geometric colimits. Both ring and module formulas impose
the pointed compatibility through the specific ū. Ring-first scalar extension
has exactly the source's module-first meaning under tensor symmetry, and the
RHS formula fixes the map rather than merely asserting abstract isomorphism.
The φ-formula constrains its value on every ordinary ring germ, so scalar extension
uses the natural chart germ action. All variables and the universe are explicitly
bound, `autoImplicit` is disabled, and the file has no local notation or local
instance. The single postponed theorem has the source and all three proof steps
in its docstring. No hypothesis/clause mismatch was found. Explicit direct imports
of the scheme, space, and tensor-product dependency modules were added after the
first successful compile to make the dependency plan visible.
