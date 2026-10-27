## Worker report

The module `Sheaf.AlgebraicGeometry.HypercoverDerivedUnitChainSquares` states all
clauses of the node, one declaration per clause, in
`AlgebraicGeometry.Scheme.HypercoverUnit`. All theorem proofs are `sorry`.
Definitions contain real constructions; the three choices are from unique
universal-property characterizations, never bare existence of arbitrary data.
The node copy changes only `lean`. There is no statement correction, new DAG
node, dependency-record repair or STATEMENT-DISPUTED flag.

The previous attempt's quoted refusal concerns a second stage-1 split. This is a
stage-2 statement delivery on top of Q36's unchanged reviewed split, not a split.
No split/review/status fields are modified.

Hypotheses and objects:

- `X Y : Scheme.{u}` and `h : Y ⟶ X` are arbitrary schemes and their morphism.
  The scheme universe is `u`, the actual small pro-etale site has object universe
  `u+1` and morphism universe `u`, and coefficient rings/modules have universe
  `u+1`. No equality of site object and morphism universes is imposed.
- `R : Sheaf (ProEt.topology X) CommRingCat.{u+1}` and similarly `S` are the
  arbitrary commutative ring sheaves. `c` is the specified isomorphism from
  `proEtaleSheafInverseImage h` of R to S. There is no finite, constant,
  completed or torsion coefficient restriction.
- `proEtaleRingModules`, `pull` and `push` use the existing module category and
  the existing identified-coefficient pullback and direct-image functors,
  termwise. They do not introduce a second module or inverse-image construction.
- `W : X.ProEt`, `U : SimplicialObject (Over W)` expresses the augmented
  diagram. For the node's global sections take `W = ProEt.mk (𝟙 X)`.
  Its base change along h is the terminal object used for global sections on Y.
  `V : SimplicialObject (Over ((proEtaleBaseChange h).obj W))` is the other
  augmented diagram. The helper construction also permits arbitrary W'.
- `g : V ⋙ Over.forget W' ⟶ U ⋙ Over.forget W ⋙ proEtaleBaseChange h`
  specifies each factorization V_p -> Y x_X U_p. A natural transformation
  commutes with *all* simplicial operators, including degeneracies.
  In `augmentation_square`, `hg` says explicitly that g commutes with
  augmentation. Factoring maps over h through the fibre product is universal
  and imposes no cartesian-square condition on V_p -> U_p.
- `E I : CochainComplex.Plus (proEtaleRingModules X R)` and J in the analogous
  category on Y impose strict boundedness below of terms. `hI` and `hJ` say
  `∀ n : ℤ, Injective (I.obj.X n)` and likewise for J. The maps i and j have
  precisely the sources E and h^*E and the specified targets I and J, with
  `[QuasiIso i] [QuasiIso j]`. No monomorphism assumption is added to i or j.
- The abelian-group derived category has the explicit metatheoretic choice
  `[HasDerivedCategory.{w} AddCommGrpCat.{u+1}]`, with independent universe w.
  This is the node's choice of localization universe, not a constraint on a
  scheme, sheaf or resolution. Ordinary module derived categories and their
  localizations are those already fixed by the operations interface.

Clause-by-clause rendering:

1. `comparison` gives existence of b and
   `Nonempty (Homotopy ((pull ...).map i ≫ b) j)`, and says *any* two b's
   satisfying this condition are homotopic. This is uniqueness up to homotopy,
   not uniqueness of chain maps. h^*I is not assumed injective.
2. `transpose` is literally the complex adjunction unit followed by `push.map b`.
   `unit_representative` proves I, J and h_*J K-injective and gives
   `Nonempty (Homotopy (i ≫ transpose ... b) (transpose ... j))`.
3. The final equation of `unit_representative` is
   `Q(i) ≫ Q(a) ≫ gamma_J = etaD_QE ≫ Rh_*(phi_E ≫ Q(j))`.
   Here `gamma_J` is the *actual* `rightDerivedFunctorUnitQ J`, `phi_E` is
   `proEtaleRingDerivedPullbackFactors.hom.app E`, and `etaD` is the unit of
   `proEtaleRingDerivedAdjunction`, constructed from the published normalized
   ordinary adjunction. Inverting gamma_J, Q(j) and phi_E gives exactly the
   node's resolution interpretation of Q(a) Q(i). No existentially chosen
   derived adjunction or arbitrary functor isomorphism occurs.
4. `sections` is existing module evaluation followed by forgetting scalars.
   `directImageSections` is `Iso.refl`: sections of h_*J at W are literally
   sections of J at h^{-1}W. `derivedSectionsComposition` uses the canonical
   `rightDerivedFunctorCompIso'`, with K-injective preservation supplied by
   the *actual exact-left-adjoint* adjunction. `sections_composition_representative`
   gives its unit-preserving normalization including the derived unit at J;
   when J and h_*J are K-injective this uses their identity resolutions.
   `derivedSectionMap` is RΓ of the actual derived adjunction unit followed by
   this canonical composition comparison. `sections_representative` gives
   the equality with QΓ(a), recording invertibility of the evaluation-derived
   units at I and J. Q(i) and Q(j) are invertible by the input quasi-isomorphisms.
5. `total` uses the recorded `ProEt.hypercoverTotal` *without changing its
   summands or differential*, then forgets its global scalar action. This is
   the faithful underlying abelian complex needed to compare two different
   global coefficient rings, as in the source's D(Ab) section calculation.
   `summand` is the actual zero-extension isomorphism followed by `ιTotal`.
   It is not a replacement direct-sum construction.
6. `restrictSection` is the specified module unit at U_p, followed by
   restriction along g_p. `RestrictionFormula` says the image of every
   actual (p,q) summand is this restriction followed by b^q.
   `restriction_existsUnique` is well-definedness and the coproduct universal
   property for these exact components; `restriction` chooses that *unique*
   map. With b = identity it is c_{g,E}; with coefficients I,J and the
   given b it is G. In particular the construction fixes every component,
   rather than allowing an unconstrained natural map. The existence theorem
   asks for a morphism of cochain complexes, so it includes compatibility
   with the signed differential delta + (-1)^p d of the recorded total.
7. `augmentation` is the recorded `ProEt.hypercoverAugmentation` under the
   same forgetful functor, hence the actual restriction augmentation.
   `augmentation_square` states `alpha_I ≫ G = Gamma(a) ≫ alpha_J` as a
   strict equality of chain maps (Lean writes composition left to right).
8. `coefficient_homotopy` gives a homotopy from `T_U(i) ≫ G` to
   `c_g,E ≫ T_V(j)`. Its second clause prescribes, on *every* summand,
   `H = (-1 : ℤ)^p • summand (... (s.hom q (q-1)) (r_p x))`.
   Both equations p+q=n and p+(q-1)=m are explicit binders, so the target
   degree and the sign are not hidden in a comment or unspecified homotopy.
9. `coefficient_naturality` is the strict square for every coefficient chain
   map t. `RefinementFormula` prescribes actual restriction along r_p on
   every summand; `refinement_existsUnique` and `refinement` construct that
   unique total map. `refinement_naturality` assumes precisely the degreewise
   commuting square on g,g',r,s and gives equality of the two total composites.
10. `compositeDiagram` uses the canonical `Over.pullbackComp` pasting.
    `restriction_comp_section` is the explicit equality of successive
    restrictions on any section, after the published `compositionIso`.
    `restriction_comp` is the resulting equality of total maps; the ring
    identification is exactly `proEtaleRingCompositeCoefficients`, and the
    coefficient map is the termwise published ordinary comparison.
11. `identity_directImage_existsUnique` characterizes identity pasting by its
    section formula using `Over.pullbackId`. `identityDirectImage` chooses
    this uniquely determined comparison; `identityPullback` is its adjunction
    mate. `restriction_id` gives the identity total chain map after precisely
    this ordinary comparison and the existing `proEtaleRingInverseImageId`.

The helpers are parts of this node's very restriction/unit construction. The
brief's missing-helper rule permits them in the owning module and lists them
in `lean.declarations`. Their named well-definedness theorems have this node's
source and full proof docstrings. No independent missing notion is introduced.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `def-weil-size-convention` is explicitly a metatheoretic convention, with
  no declaration; the universes above render it.
- `Sheaf.CategoryTheory.RingedToposMorphism`: its general ringed-topos signature
  and docstring were read; this concrete scheme-induced morphism is given by
  the recorded pro-etale operations, rather than a new abstract topos datum.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`: `SimplicialObject`, its
  natural transformations and faces/degeneracies.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`; `proEtaleRingModules` specializes it.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverTotal`: `hypercoverSections`,
  `hypercoverSectionRows`, `hypercoverTotal` in `Scheme.ProEt`.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverAugmentation`:
  `Scheme.ProEt.hypercoverAugmentation`, with its actual restriction formula.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction` and module construction.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` reexports the full
  arbitrary-ring-sheaf operations, defined in `ProEtaleOperations` and normalized
  in the current `ProEtaleOperationsCanonicalAdjunction`. The latter was read
  with `scompile.py --source` because it is newer than the read checkout.
  We use `proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`,
  `proEtaleRingModuleAdjunction`, `proEtaleRingDerivedPullbackFactors`,
  `proEtaleRingDerivedDirectImage`, `proEtaleRingDerivedAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`:
  `proEtaleRingCompositeCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleOrdinaryPullbackComparison`:
  `AlgebraicGeometry.Scheme.AcyclicHypercover.compositionIso`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the general arbitrary-quasi-isomorphism universal pair was read and imported.
  For the actual operations we use their already fixed upstream universal pair
  `Functor.rightDerivedFunctor` and its `rightDerivedFunctorUnitQ`, not a new
  copy or a redefinition of a derived functor. This fixes the unit normalization
  required by the node, and imposes no mono condition on the supplied resolutions.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`:
  `CategoryTheory.Injective`; the separate `InjectiveResolution` object-of-an-
  abelian-category signature was read and is deliberately not used in place of
  a resolution of the given whole complex.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`; `Homotopy` is Mathlib's actual coefficient
  chain-homotopy type, including the two-index component `hom`.

Edge cases checked:

- Zero coefficient sheaf/complex and the empty scheme: no nonemptiness or
  nonzero hypothesis is used, and every formula still types and is zero.
- No hypercover/matching/weak-contractibility/affineness/qcqs/cartesian
  condition is assumed. An arbitrary augmented simplicial diagram is allowed.
- p=0 gives H=s r and the actual (0,q) augmentation; p=1 gives H=-s r.
  Horizontal cancellation uses the two opposite signs, while the vertical
  factor is always (-1)^(2p)=1. Arbitrarily negative coefficient lower bounds
  are permitted by Plus; no nonnegative coefficient-degree restriction appears.
- Identity scheme maps and genuine arbitrary coefficient isomorphisms are
  permitted in the general construction; the identity normalization uses the
  canonical coefficient identification, not a newly chosen one.
- Composition uses the induced composite coefficient identification, never
  an independently supplied third coefficient isomorphism.
- The total construction also makes sense for unbounded complexes. Only its
  elementary construction/naturality helpers use that wider domain; the
  given injective-resolution and signed-homotopy conclusions retain Plus.

Searches for an existing statement:

- `msearch.py ... leanfinder`: "An exact inverse image of module sheaves
  represents the derived adjunction unit by a chain map of injective resolutions,
  compatible with cross-site simplicial signed totals and augmentation squares".
  Eight hits: `Adjunction.derivedη`, `derived'_unit`, `derived_unit`,
  `derivedε_fac_app`, and injective-resolution/right-derived component lemmas.
  These are general infrastructure and do not give the signed cross-site squares.
- `msearch.py ... loogle '"Adjunction", "rightDerived"'`: zero hits.
- `msearch.py ... grep
  '(hypercover|Hypercover).*(unit|homotop)|(unit|homotop).*(hypercover|Hypercover)'
  CategoryTheory`: 12 hits, concerning truncated PreOneHypercover homotopies,
  saturation and a coproduct sheaf condition, not this full simplicial signed total.
- `rg` of `crossSite|cross.site|AcyclicHypercover|hypercover.*[Rr]estrict` in
  `lean/Sheaf/AlgebraicGeometry` and `lean/WeilConjectures`: existing augmentation,
  row and comparison infrastructure; no theorem with these cross-site clauses.
- `rg` of the exact node id in both `lean/WeilConjectures` and `lean/Sheaf`:
  no hits. A final search for `HypercoverUnit|derivedUnitChain|derived.unit.chain.square|
  cross.site.*total` in both roots also gave no hits before this sandbox module.

Validation: the full 590-line module compiled as sandbox and library module
through the prescribed `scompile.py`, with no errors or warnings (apart from
permitted sorry diagnostics). After making the abelian localization universe
explicitly independent, compilation and the prescribed delivery dry run are
repeated below. No local/global library build was run and no live source was edited.

## Second reading by Q139

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
