## Worker report

The delivery states `AlgebraicGeometry.formal_functions_stalk` and the actual-section
specialization `formal_functions_stalk_structureSheaf`, in
`Sheaf.AlgebraicGeometry.FormalFunctionsStalk`. All theorem proofs are `sorry`.
Definitions contain real constructions; when existence or linearity is needed, a named
source-backed theorem supplies only that proof. The item statement is unchanged.

Hypothesis and clause correspondence:

- A morphism of schemes: `{X Y : Scheme.{uS}} (f : X ⟶ Y)`.
- Properness: `[IsProper f]`. Locally Noetherian base: `[IsLocallyNoetherian Y]`.
- Coherent module: `(F : SheafOfModules.{uS} (moduleRings X.toRingedSpace))` and
  `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`.
- Every base point and every nonnegative degree: `(y : Y) (p : ℕ)`.
- Local ring and maximal ideal: `Y.presheaf.stalk y` and `IsLocalRing.maximalIdeal`.
  No separate Noetherian-local-ring hypothesis is added; it follows from the base.
- The quotient morphisms are `formalFibreBaseMap`: `Spec.map` of the quotient homomorphism
  followed by the existing `Y.fromSpecStalk y`.
- The fibre products and their projections are `formalFibre` and `formalFibreι`, using
  Mathlib `pullback f (formalFibreBaseMap Y y n)` and `pullback.fst`.
  Index `n : ℕ` means the node's positive level `n+1`; at index zero this is the residue
  field fibre, since the first quotient is by the maximal ideal.
- The fibre module is `(Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F`.
- `formalFibreTransition` is fixed by both projection equations in
  `formalFibreTransition_exists`. Its quotient-spectrum component is
  `Ideal.Quotient.factorPow` of consecutive positive powers.
- `formalFibreTransitionModuleIso` is the canonical composition identification: compose
  its existence theorem uses composition and uniqueness of the canonical tensor-pullback
  adjunctions. `canonicalTensorPullbackCompositeUnitProperty` pins the chosen isomorphism
  by its unit equation, including `Scheme.Modules.pushforwardComp` and the projection
  equality. The postponed proof supplies this specified isomorphism.
- `formalFibreTransitionFMap` is the adjoint of this identification. The data field
  `transition_eq` fixes the underlying cohomology transition to
  `Scheme.Modules.moduleCohomologyFMap` of this h-map.
- `formalFibreScalarMap` uses the second projection and `Scheme.ΓSpecIso` to give the
  quotient-ring action. `formalFibreCohomologyLocal` restricts through the quotient map;
  `formalFibreCohomology` restricts through `AdicCompletion.evalₐ`. Thus the completed
  local-ring action is explicitly the componentwise quotient action.
- `formalFunctionsStalk` is the stalk of the actual
  `(RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p`, using the shared
  `RingedSpace.moduleStalkFunctor` for a sheaf on the scheme. Its module is not an arbitrary replacement of that stalk.
- `AdicCompletion (maximalIdeal ...) (formalFunctionsStalk ...)` is the node's
  `lim M/m^n M`. Mathlib includes the harmless zero quotient at exponent zero.
- The repaired dependency defines the *actual* presheaf `P` by deriving presheaf-valued
  direct image. Exact evaluation computes `H^p(f⁻¹V,F)` from section complexes of any
  injective resolution. Its comparison with the higher direct image is fixed on section
  cocycles for every resolution, using `higherDirectImageCocycleCompatibility`.
  `canonicalModuleSheafificationMap` is the actual adjunction transpose of the comparison.
  `higherDirectImageCohomologyStalkIso` is its induced stalk isomorphism.
- `formalFunctionsCohomologyGerm` sends a class of that presheaf to the higher direct
  image stalk through this canonical isomorphism.
- The data field `germ_eq`, via `formalFunctionsGermCompatibility`, fixes `theta n`
  on every such class: restrict the resolution
  comparison beta to `f⁻¹V`; identify sections of the pushed-forward fibre resolution with
  sections of the fibre using `i_n⁻¹(f⁻¹V)=⊤`; then require
  `H(mu)(theta_n(germ s)) = H(beta)(s)`. The section identity is fixed term by term.
  `mu` is invertible on cohomology by the same injective-resolution construction defining
  the recorded cohomology f-map. This is precisely pullback on the neighbourhood,
  including positive degrees, and uniquely specifies the map on all germs.
- `FormalFibreCohomologyData.compatible` and `.killed` state the transition compatibility
  and annihilation of the ideal power. `formalFunctionsThetaQuotient` is the induced
  quotient map using `Submodule.liftQ` and the named kernel-containment theorem.
- `formalFibreCohomologySystem` forms the actual inverse sequence in
  `ModuleCat (AdicCompletion m A)` using `Functor.ofOpSequence`.
- The existential `e` is an isomorphism **over the completed local ring**. Its first
  projection equation specifies the induced map on *every completed element* as
  `formalFunctionsThetaQuotient ... (AdicCompletion.eval ... (n+1) x)`. Its second
  equation specifies its composite with `AdicCompletion.of` as `(theta_n)_n`.
  Restriction of scalars also gives the asserted A-linear isomorphism.
- The structure-sheaf theorem uses the actual stalk of `pushforward f` of the unit module,
  and the inverse system `formalFibreSectionsSystem` of actual `Γ(X_n,⊤)` modules.
  For every germ of every section on `f⁻¹V`, each projection is exactly
  `(formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t`. This supplies the degree-zero clause
  explicitly, without requiring the reader to substitute an unspecified H^0 isomorphism.

Dependency declarations read and used: Mathlib `AlgebraicGeometry.IsProper`
(`Morphisms.Proper`), `AlgebraicGeometry.IsLocallyNoetherian` (`Noetherian`),
`CategoryTheory.Limits.pullback` and projections (`Pullback.HasPullback`),
`Scheme.Hom.fiber` (`AlgebraicGeometry.Fiber`, for the first-level identification),
`AdicCompletion`, `AdicCompletion.of`, `AdicCompletion.eval` (`AdicCompletion.Basic`),
`AdicCompletion.evalₐ` and its module action (`AdicCompletion.Algebra`);
`RingedSpace.IsCoherent` (`Sheaf.AlgebraicGeometry.Coherent`);
`Scheme.Modules.tensorPullback` (`Sheaf.AlgebraicGeometry.TensorPullback`), the canonical
adjunction from `exists_tensorPullbackAdjunction` (`TensorPullbackAdjunction`);
`RingedSpace.moduleCohomology` (`Sheaf.Topology.RingedSpaceModuleCohomology`),
`RingedSpace.moduleDirectImage` (`RingedSpaceDerivedDirectImage`), as used by the recorded
`sheafCohomologyAndHigherDirectImages` (`Sheaf.Paper.PQFCohomology`);
`Scheme.Modules.ModuleCohomologyFMapData`, `.moduleCohomologyFMap`, and the resolution
construction (`Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`). The presheaf dependency is
repaired in the accompanying module; its new declarations are used directly.
The shared `RingedSpace.moduleStalkFunctor`
(`Sheaf.Algebra.Homology.ModuleStalkFunctor`) and presheaf-level
`PresheafOfModules.stalkObj` and `.moduleStalkFunctor`
(`Sheaf.Topology.PresheafModuleStalkFunctor`) and `RingedSpace.openModuleSections`
(`Sheaf.Topology.OpenModuleCohomology`) are reused, not redefined.

Edge cases checked: the positive first level is n=0 in the implementation, while the
node's n=0 is excluded; the completed module still has its zero quotient component.
The zero module and the empty source give zero systems, and no nonempty source is
assumed. An empty base has no y and is handled by the universal point binder. Points
need not be closed in Y; only the corresponding point in Spec of the local ring is
closed. All nonnegative p are allowed, including zero and degrees above the dimension.
The construction imposes no field or characteristic condition. One universe is used
for schemes, their local rings, modules, and countable inverse systems, with no
independent smaller test-object universe and no finite-dimensionality restriction.

Searches made: LeanFinder, "completion of stalk of higher direct image of coherent
module under proper morphism equals inverse limit of infinitesimal fibre cohomology",
returned eight stalk and localization bookkeeping lemmas, no formal-functions theorem.
Loogle, "AdicCompletion, AlgebraicGeometry.Scheme", returned no hits. Mathlib grep,
"formal.functions|formalFunctions|FormalFunctions" in AlgebraicGeometry, returned no hits.
LeanSearch for "cohomology inverse system of infinitesimal neighbourhoods of scheme
fibre" was unavailable with Internal Server Error. LeanFinder for the canonical
infinitesimal fibre cohomology inverse system returned eight unrelated smooth-sheaf
stalk lemmas. Mathlib grep for "infinitesimal|formalFibre|formalFiber" found only the two
formally-unramified comments. Source and project ripgrep found no statement of the
requested theorem and no definition of this inverse system. Blueprint search found zero
nodes for "infinitesimal neighbourhoods"; DAG grep found the current theorem and its
uses, but no definition node for this system. The exact tool outputs are retained in
sandbox `searches.jsonl` and summarized in the new node.

Source read: Stacks https://stacks.math.columbia.edu/tag/02OD, the hypotheses, diagram,
completed-ring linearity, and flat-base-change/formal-functions proof. The local
`literature/stacks-project/coherent.tex` is absent on this machine, so the authoritative
Stacks page was read instead. No statement correction and no STATEMENT-DISPUTED flag.

## New nodes

`def-weil-pbc-formal-fibre-cohomology` introduces the canonical infinitesimal-fibre
cohomology inverse system, its quotient and completed-ring scalar actions, and the stalk
restriction maps and their quotient factorizations, including the actual-section system
in degree zero. Its module is `Sheaf.AlgebraicGeometry.FormalFibreCohomology`.
Source: Stacks 02OD and its proof, with the resolution construction of 01FB. The three
search kinds, local library searches, and DAG/blueprint searches above found no existing
notion carrying this construction. Its data contain no formal-functions isomorphism:
the existence theorem supplies only transitions and germ restriction maps; the
completed-stalk isomorphism is exclusively the item's theorem. All construction proofs
are named theorems with source and natural-language proof in the module.

## Dependency modules

`lem-weil-pbc-higher-direct-image-presheaf`: the old `higherDirectImagePresheaf` quantifies
over an unspecified P, gives neither its values on opens nor its restriction maps, and
does not tie its arbitrary map or stalk isomorphisms to cocycles. Therefore it cannot
specify the canonical germ maps required by the item. The replacement module
`Sheaf.Paper.CanonicalHigherDirectImagePresheaf` defines P by right-deriving presheaf-valued
direct image, computes its sections using exact evaluation, and states existence of the
comparison characterized on every section cocycle. Its adjoint sheafification map and
induced stalk maps are isomorphisms, giving the genuine universal sheafification
property and the canonical stalk comparison. A separate theorem states degree zero.
Only this dependency's lean record changes; the old module and declaration are untouched.

## Validation

The three delivery modules were compiled together by the prescribed server tool; the
check completed in 25.4 seconds with exit code zero. A final delivery dry run checks the
updated records and current modules together. Every universe and variable is explicit;
autoImplicit is disabled in each module. No budget or server timeout was increased.

## Second reading by R1

I reread the node statement, the Stacks source (Tag 02OD), the dependency signatures,
and all three delivered modules. The correspondence is as follows.

- `f : X ⟶ Y` is the scheme morphism; `[IsProper f]` and
  `[IsLocallyNoetherian Y]` are exactly the properness and locally-Noetherian hypotheses.
- `F : SheafOfModules (moduleRings X.toRingedSpace)` with
  `hF : RingedSpace.IsCoherent X.toRingedSpace F` is the coherent module.
- `y : Y` and `p : ℕ` render the point and arbitrary nonnegative cohomological degree.
- `formalFunctionsStalk f y F p` is the actual stalk of the right-derived module direct
  image, and the completed source is `AdicCompletion (maximalIdeal (Y.presheaf.stalk y))`
  of that stalk.
- `formalFibreCohomologySystem f y F p` is the inverse system of `H^p(X_n,F_n)` with
  index `n` representing source level `n+1`; its quotient map is
  `formalFunctionsThetaQuotient` and its components are the specified `theta` maps.
- The existential `e` is an isomorphism in `ModuleCat` over the completed local ring.
  The first conjunct gives its component on every completed element via `eval` at `n+1`;
  the second gives its composite with `AdicCompletion.of` on every stalk element.
  These are precisely the two clauses in the node.

The apparent indexing shift is deliberate: source `n ≥ 1` is represented by Lean index
`n-1`, so Lean's `n+1` quotient is the source's `m_y^n` quotient. Pullback orientation
(`pullback f (formalFibreBaseMap ...)`) gives the same fibre product as the source.
No extra field, characteristic, finite-dimensionality, or nonempty-point hypothesis is
introduced. The structure-sheaf theorem is the node's stated degree-zero specialization,
with an explicit germ formula.

Edge cases checked: `p = 0`, arbitrary larger `p`, zero `F`, empty `X` or `Y`, and no
assumption that `y` is closed. The empty-index issue does not arise because the inverse
system is indexed by `ℕ`; its zero component is the first (residue-field) fibre. The
completion includes the harmless exponent-zero quotient supplied by Mathlib.

Searches were repeated with LeanFinder/Loogle, ripgrep over Mathlib, `WeilConjectures`,
and `lean/Sheaf`, for formal-functions stalks, infinitesimal fibre systems, and the two
theorem names. No existing declaration matched. The source page confirms exactly the
three hypotheses and completed-local-ring conclusion.

No mismatch was found. The worker's repaired higher-direct-image-presheaf dependency is
used consistently by `formalFunctionsCohomologyGerm`; its canonical stalk comparison is
the one required by the source. The three modules compile together with only the intended
`sorry` theorem proofs.
