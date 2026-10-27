## Worker report

The module `Sheaf.Paper.PointProjectiveDualTensorModels` states
`WeilConjectures.PointProjectiveDualTensorModels.point_projective_dual_tensor_models`.
Its sole theorem has proof `by sorry`. All other declarations are transparent aliases,
the actual termwise adjunction unit, or the explicit conjunction `Result`; none chooses
unspecified data or contains a postponed proof. The mathematical statement is unchanged.
Two already landed nodes are added to stmt_deps: `def-pod-point-derived-hom-models`
and `def-sc-module-total-hom-complex`. They own the exact interfaces used below;
no dependency node is modified and no new node is introduced.

Source read: the current blueprint point-dualizing-complex proof, second sentence,
and the third paragraph of `thm-pod-identification-of-the-comparison.proof.md`.
The former computes the point dual over the coefficient ring; the latter requires
actual adjunction/evaluation maps. The seven steps in the item's node supply the
finite-projective expansion. The theorem docstring includes each of these steps.

Hypotheses and objects, in namespace `WeilConjectures.PointProjectiveDualTensorModels`:

- The global finite-field datum is `D : FiniteFieldDatum`; the site is literally
  `Scheme.ProEt (Spec (.of D.k))`, with objects in universe u+1 and arrows in u.
  The coefficient prime is `l` with `[Fact l.Prime]` and `_hl : l ≠ D.p`.
- `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` express the finite coefficient extension.
  `R l E` is the canonical `ULift` of `Padic.coefficientExtensionIntegers l E`.
  This changes universe size only, with its existing ring structure.
- `B D l E` is `PointDerivedHom.coefficientSheaf D.k l E 1 true`: its integral
  branch is the actual inverse limit of positive quotient sheaves. The dummy finite
  level argument is ignored in that branch. `alpha` is its canonical constant-to-limit map.
  `constantModules`, `extensionObject`, `extensionMorphism`, `generator`, `sections`,
  and `ExplicitAdjunction` are used directly from `PointDerivedHomModels`.
- `L`, `hobj`, and `_hmap` specify exactly constant-module sheafification followed
  by ordinary change of rings, on objects and morphisms. These are presentation
  equations for the L defined in the node, not a different or arbitrarily chosen functor.
  `adj` and `_hexplicit` specify the given adjunction in both directions: h is sent
  to x mapped to h(1 tensor x), and the inverse is b tensor x mapped to b times
  the restriction of t(x). `extensionComplex` applies L termwise; `unit` is
  `(adj.mapHomologicalComplex (.up ℤ)).unit.app P` with its actual component maps.
- `[IsNoetherianRing (R l E)]` is the explicitly assumed Noetherianity.
  Finite-limit and finite-colimit preservation for L and `sections` are exactly
  their assumed exactness in these abelian categories. `_hsections` is bijectivity
  of the canonical constant-value ring homomorphism at the final site object,
  expressing the assumed R ≅ Gamma(B), rather than any abstract ring isomorphism.
- `P`, `a`, `b`, `_ha : P.IsStrictlyGE a`, `_hb : P.IsStrictlyLE b`, and
  `_hP : ∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)` express a
  bounded finite-projective representative. No a ≤ b restriction is needed for
  input bounds: the zero complex also admits bounds with b < a.
- `ringComplex` and `coefficient` are the existing degree-zero single complexes.
  `dual` is the existing `CochainComplex.moduleHomComplex P (ringComplex l E)`;
  its linear-cochain differential is d_target f - (-1)^n f d_source, hence the
  specified -(-1)^n f d_P. `tensor` is the ordinary signed module totalization.
  `model` gives C and J by the existing termwise L. `tensorModel` is their
  existing ordinary sheaf total tensor D. No totalization is redefined.

Every conclusion is expanded in `Result`:

1. The first conjunct quantifies over `[dual P, tensor P]`: integer lower/upper
   strict support bounds and finite projectivity of every term give precisely
   bounded finite-projective P-dual and T.
2. The second conjunct quantifies over `[P, dual P, tensor P]`:
   `Module.Finite R (Q.homology i)` states finite cohomology, and the universal
   acyclic test `F.Acyclic → (moduleTotal F Q).Acyclic` is K-flatness over R.
3. The third conjunct quantifies over C,J,D. It states boundedness,
   `IsKFlatIndependentCoefficients`, and termwise `IsFlatOnSite`. Each term has
   maps s into and t out of `SheafOfModules.free (ULift (Fin r))` with s ≫ t = id.
   The recorded `free` is the coproduct of that finite family of copies of B.
   This is exactly a finite-free summand and permits r=0.
4. `beta : D ≅ L(T)` is a chain isomorphism whose homogeneous generator equation
   sends (b tensor x) tensor (b' tensor f) to bb' tensor (x tensor f).
   The following derived-category isomorphism identifies Q(D) with the existing
   `siteDerivedTensorIndependentCoefficients` of Q(C),Q(J), retaining the actual
   tensor models rather than only per-degree cohomology comparisons.
5. The next conjunct ranges over `[B[0],C,J,D]` and applies
   `finiteTorConstructibleIntegral` to their standard localizations. By its read
   definition this is `sfIntegralConstructible` (derived completeness, all positive
   constructible reductions, one uniform cohomological interval) together with
   `∃ a b, a ≤ b ∧ ∀ n, HasProEtaleTorAmplitude (reduction at n+1) a b`.
   Thus both the membership and the single Tor bound for every positive reduction
   are asserted for each of the four complexes.
6. Over `[R[0],P,dual P,tensor P]`, `QuasiIso (unit ... Q)` and the component
   equation assert exactly the actual adjunction units x mapped to 1 tensor x.
   The kappa clause identifies L(R) with the unit B-module by b tensor r mapped
   to b alpha(r), and states that the unit on R becomes its actual constant-value
   scalar map. Under the assumed identification Gamma(B)=R this is r mapped to r.
7. `h : J ≅ sheafHom C B[0]` is a chain isomorphism. Its homogeneous formula uses
   the recorded Hom product projection, identity slice evaluation, and canonical
   single-complex coordinate. In bidegrees p+j=0 it is exactly bb' alpha(f(x)).
   Other target degrees are zero by the single-complex definition. The final
   `IsIso (sheafQ.map h.hom ≫ IntegralHom.homModelMap C B[0])` makes precisely
   its composite with the canonical ordinary-Hom-to-derived-Hom map invertible.
   The latter is the Hom map to the fixed K-injective replacement followed by the
   localization comparison. This is the specified canonical RHom isomorphism.

Dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`,
  publicly preserving the exact integer ring, uniformizer and finite-quotient constructors
  from `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the same quotient cone and completion.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, reexporting the existing sheaf tensor.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, whose finite-projective representative
  conditions are written explicitly here because P is an actual complex.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`; ordinary-module K-flatness is
  its defining acyclic-total-tensor condition, with the ordinary module tensor.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleIntegral`, publicly
  retained from `FiniteTorAmplitude`; finiteTorConstructibleEtale is not substituted
  for the completed-coefficient integral predicate.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`: its public generic
  `derivedInternalHomOfUniverses`; the added ordinary-module abbreviation is not
  used in place of the required sheaf internal Hom.
- Added landed dependency `Sheaf.Paper.PointDerivedHomModels`: the exact point
  constructions listed above, including `ExplicitAdjunction`, `moduleTotalElement`,
  `homValue`, `coefficientSheaf` and `coefficientMap`.
- Added landed dependency `WeilConjectures.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex`, using the existing Mathlib linear cochains.
- For the canonical derived comparison, `IntegralHom.homModelMap` is read from
  the published `IntegralHomReductionModels` interface. For representing the
  derived tensor, the existing `siteDerivedTensorIndependentCoefficients` is used.
  Available proof-dependency modules are imported without public visibility unless
  their declarations occur in this statement's types. The node proof is preserved.

Searches actually run (recorded by msearch.py in searches.jsonl):

- LeanFinder: "Bounded finite projective complexes on a pro etale geometric point have
  canonical completed coefficient dual tensor and internal Hom models": eight hits,
  chiefly LightCondensed internal projectivity and formally smooth Kahler differentials;
  none states this completed-coefficient point package.
- Loogle: "Module.Projective, Module.Finite": twelve hits, including
  `Module.Finite.exists_comp_eq_id_of_projective`, `Module.dual_finite`,
  `Module.dual_projective`, reflexivity and `dualTensorHomEquiv`; these are ingredients.
- Mathlib grep: "dual_projective|dual_finite" in LinearAlgebra: two hits in
  Dual/Lemmas. A later grep "point_projective|constantCoefficient.*Extension|finiteProjective.*dual"
  returned zero hits. A later LeanFinder completed-point query returned eight condensed
  category hits and no exact package. The later Loogle query containing
  `CochainComplex.IsKFlat` reported that identifier unknown; not an exact match.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` found `PointCompletedEvaluation`,
  `PointDerivedHomModels`, the constant-realization modules and scalar-dual descent.
  They provide the actual constructions, reused here; none is exactly this conditional
  package. The parent completed-evaluation theorem asserts further completed-evaluation
  identities and is not an existing declaration of this prerequisite. Searching the
  item id in WeilConjectures found no exact declaration. Searching the chosen full
  namespace/name in both libraries and dag/lean_names_upstream.json found no clash.

Edge cases read against the definitions: P=0 and r=0 finite splittings; a single
finite projective term in arbitrary integer degree; a nonfree projective summand;
a two-term complex (Hom sign -(-1)^j and tensor sign (-1)^p); reduction exponent one;
every larger positive exponent via n+1; negative support bounds. No nonzero rank,
free basis, positive cohomological degree, or bound depending on reduction is assumed.
The input interval may be empty, accounting for the zero complex.

Compilation: prescribed scompile.py, both sandbox and library-module passes, clean.
The universe failure was diagnosed by separate module-mode probes: the imported
`scalarReductionSiteSmall` and `integralReductionSiteEssentiallySmall` instances
have a coefficient-universe parameter beneath a max and left it unresolved during
instance selection. They are disabled while this module elaborates; the unchanged
small site has its standard essentially-small instance. Auxiliary competing instance
selections are fixed locally in the definition's body. Every temporarily disabled
instance is restored at the end of the module. No local instance declaration or
extra mathematical hypothesis is introduced. Diagnostic files are removed.

No STATEMENT-DISPUTED flag or source correction is needed.

## Second reading by Q88

A second pass by the dispatched worker, without claiming a separate reviewer:
I reopened the node and Result and matched all seven groups of conclusions above.
In particular I checked that the integral Bool branch ignores its finite-level
argument and uses the completed inverse limit, that finiteTorConstructibleIntegral
includes BOTH constructibility/completeness and the forall-level Tor bound, and
that the last composite uses homModelMap rather than merely an unspecified isomorphism.
I checked the order s ≫ t for the finite-free retract, the product b*b' in both
normalizations, the single coordinate at p+j=0, and the actual adjunction unit.
The source separates the algebraic dual from its scalar realization; the file does
also. The two explicit landed dependency citations were added on this reading so
the ordinary Hom complex and point-interface aliases are grounded in their owning
nodes. No mathematical statement changed. The maintainer's independent review
remains the independent reading required by this dispatched-worker workflow.
