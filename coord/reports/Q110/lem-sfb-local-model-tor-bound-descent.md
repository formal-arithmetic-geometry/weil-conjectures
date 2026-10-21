## Worker report

The module `Sheaf.Paper.LocalModelTorBoundDescent` states
`AlgebraicGeometry.ProEtale.localModel_torBound_descent`. Its only theorem proof is
`sorry`; no definition or instance is introduced. The natural-language proof in its
docstring follows all six steps of the node. The source read was
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-ctf.proof.md`,
paragraph (2), including the finite-ring/field bullet asserting the common Tor bound.
The node's statement is unchanged.

The encoding is the internal module category used by the recorded
`det-def-sfb-constructible-tor-amplitude` interface. Its recorded dependency
`def-weil-pbc-internal-abelian-sheaf-module-equivalence` identifies these objects with
sectionwise module sheaves, retaining underlying abelian sheaves, sections and
restrictions. The flatness hypothesis deliberately applies the recorded
`SheafOfModules.IsFlatOnSite` to the image under this equivalence. This avoids
introducing a second notion of flatness or assuming a topological presentation of
the condensed ring. That existing equivalence node is added to `stmt_deps` under
brief-stage2 section 5's permission to add landed nodes; its node and module are
not changed. No dependency repair or new node is needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A scheme S | `(S : Scheme.{u})`. |
| An arbitrary commutative condensed ring Gamma | `(Γ : Profinite.CondensedRing.{u}) [IsCommMonObj Γ.X]`; its ring structure is the bundled `Mon` structure. |
| Gamma_T is the pullback from the point | Every coefficient object is the existing `condensedRingObj Γ.X T`, the underlying object of `coefficientRing T Γ`. |
| Q in the unbounded derived category of Gamma_S-modules | `Q : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Γ.X S))`. This is the internal encoding identified with sectionwise modules by the cited equivalence. |
| Finite covering family g_i : V_i to S in the pro-etale site | `(n : ℕ) (V : Fin n → S.ProEt)`; each scheme is `(V i).left` and each map is `(V i).hom`. `hcover` requires the actual `Presieve.ofArrows` to belong to `Scheme.proetalePrecoverage S`, including its fpqc quasi-compact-refinement requirement. This is stronger than mere joint surjectivity only because the node explicitly asks for a covering. |
| Integers r at most s | `(r s : ℤ) (hrs : r ≤ s)`. |
| Cochain complexes L_i of Gamma_V_i-modules | `L : ∀ i : Fin n, CochainComplex (Mod ... (condensedRingObj Γ.X (V i).left)) ℤ`. |
| L_i^q = 0 outside [r,s] | `hbound : ∀ i q, q < r ∨ s < q → IsZero ((L i).X q)`. |
| Every term flat | `hflat` is `SheafOfModules.IsFlatOnSite` of the sectionwise module supplied by `InternalAbelianSheafModule.sectionModuleEquivalence`. The ring parameter is exactly `sectionRingSheaf` of the pulled-back coefficient ring object. |
| Given isomorphisms g_i^* Q with L_i in the derived category | `model : ∀ i, (CondensedRing.upperStar Γ.X (V i).hom).mapDerivedCategory.obj Q ≅ DerivedCategory.Q.obj (L i)`. |
| Exact inverse image with pulled-back coefficients | The functor is the actual `CondensedRing.upperStar`; its finite-limit and finite-colimit preservation instances are supplied by its upstream definition. `mapDerivedCategory` is the termwise induced functor, so no arbitrary functor, coefficient map or extra exactness assumption is substituted. |
| Every Gamma_S-module N, placed in degree zero | Both conclusions quantify over all `N : Mod ... (condensedRingObj Γ.X S)`; `(DerivedCategory.singleFunctor _ 0).obj N` is its degree-zero object. There is no flatness, constructibility or finiteness condition on N. |
| Local isomorphism for every i | The first conjunct quantifies over N and i and asserts `Nonempty` of the displayed isomorphism. Its left side is `mapDerivedCategory.obj (Q ⊗ single N)`; this tensor is the canonical relative derived tensor. |
| Ordinary tensor of complexes on the right | `DerivedCategory.Q.obj (CochainComplex.mapBifunctor (L i) ((CochainComplex.singleFunctor _ 0).obj ((CondensedRing.upperStar Γ.X (V i).hom).obj N)) (curriedTensor _))`. Thus ordinary relative tensor is totalized before localization, with the signed cochain total differential. |
| Global H^q vanishes for every N and q outside [r,s] | The second conjunct is `∀ N q, q < r ∨ s < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj (Q ⊗ single N))`. |
| Equivalently, Q has Tor amplitude in [r,s] | The last conjunct is exactly `DerivedCategory.torAmplitudeIn ... r s Q`, the predicate named in the recorded Tor-amplitude node. It restates the same cohomology condition with the project's designated predicate, as the node explicitly does. |

Declaration and dependency audit (source signatures and docstrings read):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and its `Hom`.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`, transparently `Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u+1})`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `coefficientRing`, `coefficientRing_X`, `condensedRingObj` and `isCommMonObj_condensedRingObj` in `AlgebraicGeometry.ProEtale`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`, the general-site abbreviation for Mathlib `SheafOfModules`. The internal-module interpretation is transported by the existing equivalence, rather than a second module category.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`; cohomology is `DerivedCategory.homologyFunctor` from `HomologySequence`.
- `sk-def-pe-site`: its `mathlib_match`, `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt`, `Scheme.proetalePrecoverage` and `Scheme.ProEt.topology`. Read `ProEt.mk`, the object weak-etaleness instance and the precoverage/topology definitions, along with `AlgebraicGeometry.QuasiCompactCover`.
- `def-pc-cochain-complex-modules`: `Mathlib.Algebra.Homology.HomologicalComplex`, `CochainComplex` and its `HomologicalComplex` object/differential data.
- `def-pc-flat-sheaf-modules`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`, defined by `exactFunctor _ _ (siteSheafTensorRight F)`.
- `det-def-sfb-constructible-tor-amplitude`: `Sheaf.Paper.ConstantModelTorAmplitude`, `AlgebraicGeometry.ProEtale.constantModelConstructibleFiniteTor_wellDefined`; its documented Tor predicate is `DerivedCategory.torAmplitudeIn` from `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`. That predicate uses the canonical relative derived monoidal structure and every module in degree zero.
- Added landed dependency: `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`, `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` and `sectionRingSheaf`. Its size assumption holds at object universe u+1, morphism universe u and coefficient/module universe u+1. All these universes are retained; none are equated to force a specialized interface.
- Inverse image: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.upperStar`, and `Derived.UpperLowerStar` for its termwise derived API. The coefficient morphism is the canonical invertible `condensedPullbackHom`; extension along it is exact.
- Ordinary total tensor: `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`, the recorded declaration of `def-pc-tensor-complex-sheaves`.

All recorded statement-dependency modules are available through the public imports.
The modules of all recorded proof dependencies having Lean declarations or Mathlib
matches are imported for stage 3. In particular these are:
`ProEtaleWeaklyEtaleLocalization`, `Sheaf.PushforwardContinuous`,
`ModuleObject.Basic` (via its public importers), `ShortComplex.PreservesHomology`,
`KFlatResolutionIndependentCoefficients`, `RingedTopoiDerivedPullback`,
`RingedTopoiCanonicalTensorPullbackOfUniverses`, `BoundedAboveFlatSheafKFlat`,
`SiteDerivedTensorRestriction`, `BifunctorShift`, `DerivedCategory.Basic`,
`SiteCoveringAxioms` and `ConstantModelTorAmplitude`. These names are shorthand
for the full import paths in the delivered module. No import cycle was encountered.
No sorried auxiliary theorem is introduced to manufacture data.

Edge cases checked before stating:

- n=0 is allowed. There is no `Nonempty (Fin n)` or positive-n assumption. The
  empty pro-etale cover forces the empty scheme, where the sheaf condition gives
  zero objects. The local conclusion is empty and the global conclusion remains valid.
- r=s, including r=s=0, is allowed. The strict outside-interval condition excludes
  neither endpoint. Negative endpoints and negative q are allowed by ℤ-indexing.
- Q=0, zero local complexes, N=0 and the zero coefficient ring are allowed; no
  nontriviality or positive-rank assumption appears.
- N can be nonflat. Flatness is required only of the local model terms.
- No quasi-compactness, quasi-separatedness or Noetherianity of S is added.
- The family is a genuine pro-etale cover, not a jointly surjective family with
  the required fpqc-refinement property forgotten.
- Schemes remain in arbitrary universe u; site objects have universe u+1 and
  morphisms universe u. Modules and coefficients live in u+1, as the upstream
  condensed-coefficient framework specifies. The empty-cover case is not lost
  by a universe or indexing hypothesis.

Searches run through the assigned msearch wrapper:

1. LeanFinder: `A bounded complex of flat module sheaves on a finite pro-etale cover gives Tor amplitude in the same interval`.
   Eight hits, including `Algebra.FormallyEtale.instTensorProduct`,
   `CategoryTheory.isZero_Tor'_succ_of_projective`,
   `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective` and
   `Module.Flat.lTensor_shortComplex_exact`; none gives pro-etale local-model descent.
2. Loogle: `DerivedCategory.torAmplitudeIn`. Unknown identifier in the Mathlib
   search service (an unavailable query, not evidence the project predicate is absent).
3. Loogle: `DerivedCategory.IsGE, DerivedCategory.IsLE`. Two hits:
   `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE` and
   `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`. These concern abstract
   boundedness and do not state the node or the local tensor comparison.
4. Mathlib grep: `torAmplitude|tor_amplitude|local.*[Tt]or`, restricted to
   `Algebra/Homology`. Twenty-five returned hits, including generic localization
   and local-cohomology declarations; none gives the required theorem.
5. LeanSearch: `A bounded complex of flat sheaves on a finite cover has Tor amplitude in that same interval`.
   Eight hits, including the flat-module short-complex exactness lemmas,
   `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE` and
   `SheafOfModules.hasLimitsOfSize`; no exact match.

Project searches: `rg` and `grep -rn` of the exact node id in `lean/WeilConjectures`
returned no matches, and `rg` of it in `lean/Sheaf` returned no matches.
`rg` for `localModel_torBound_descent|torBound_descent|torAmplitudeIn_of.*cover`
in both source trees found only the existing principal-open ring-module theorem
`torAmplitudeIn_of_principal_cover` and its caller. Those concern localizing a
ring and do not state this theorem for arbitrary condensed coefficients and
pro-etale sheaf local models. Broader searches for Tor-amplitude and local-model
interfaces exposed the existing Tor and equivalence definitions reused above.
No exact theorem was found and no existing notion was redefined.

Compilation uses only the authorized scompile.py wrapper. The initial flatness
call required explicit J and R parameters; its coefficient universe then needed
explicit instantiation on `sectionRingSheaf` and `sectionModuleEquivalence`.
The diagnostic `#check` commands were removed. The final module compiled cleanly
as both `Sheaf.Stage2.Sandbox0` (28.6 s) and
`Sheaf.Paper.LocalModelTorBoundDescent` (23.2 s), under the default 60 s limits.
No warning remained. No statement correction or disputed mathematical statement
was needed.

## Second reading by Q110

A separate reading pass compared the node and final signature clause by clause.
The finite family uses Fin n without assuming it inhabited; membership in the
actual pro-etale precoverage retains the fpqc condition. The source permits
arbitrary condensed rings, and the input is the general bundled condensed ring
with its commutativity instance, not a continuous-function presentation.
The local model object and Q use the same internal-module category as the
recorded Tor predicate. Applying the existing equivalence solely to express
flatness checks the exact sectionwise module notion of the flatness dependency.
No arbitrary coefficient morphism, chosen replacement functor, extra universe
equality, boundedness of Q, or flatness of N has appeared.

The first conclusion has a derived tensor before exact inverse image and an
ordinary total tensor before localization on its right. The second conclusion
quantifies independently over all N and all integer q outside the common closed
interval. The third uses the precise recorded Tor predicate. The supplied local
isomorphisms have the correct direction and local site. The six-step proof
explanation retains the sheaf-separatedness argument for empty covers. The only
changes during this pass were explicit universe instantiations and adding the
already-landed equivalence node to stmt_deps. There is no change to the node's
mathematical statement or proof, and there are no new nodes or dependency modules.
