## Worker report

Item: `lem-sp-open-exceptional-scalar-locality`, stage 2, group Q139.
Module: `Sheaf.Paper.OpenExceptionalScalarLocality`.
Primary declaration: `AlgebraicGeometry.ProEtale.OpenScalarLocality.openExceptionalScalarLocality`.

The module states equality of the two specified ambient derived morphisms, in the full
intrinsic constant-ring Dctf subcategory, after the adjunction-preserving source-open
identification demanded in the node. Its sole postponed theorem is the primary declaration.
All eight helper declarations have real definitions/structure fields. They package or
restrict existing functors and construct their normalized adjunctions and transposes;
none introduces another tensor, constructibility predicate, Tor predicate or localization.
There are no dependency repairs, new DAG nodes, or statement corrections.

### Hypotheses and clauses

* Field of characteristic p > 0 and prime ell different from p: `k : Type u`, `[Field k]`,
  `[CharP k pchar]`, `_hp : 0 < pchar`, `[Fact ℓ.Prime]`, `_hℓ : pchar ≠ ℓ`.
* Standing separated finite-type schemes: `U X Z Y : Scheme.{u}`, each with `.Over
  (Spec (.of k))`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure
  map. All scheme arrows carry `.IsOver (Spec (.of k))`. These are geometric hypotheses,
  not finiteness assumptions on the underlying point sets or on k.
* Arbitrary separated finite-type f: `f : X ⟶ Y` with `[LocallyOfFiniteType f]`,
  `[QuasiCompact f]`, `[IsSeparated f]`. No smoothness or relative dimension occurs.
* Quasi-compact open immersion: `j : U ⟶ X`, `[IsOpenImmersion j]`, `[QuasiCompact j]`.
  The restricted map g is `j ≫ f`, represented by `(j ≫ i, p)` below.
* Chosen compactification with standing middle scheme: `i : X ⟶ Z` open,
  `p : Z ⟶ Y` proper and `_hf : i ≫ p = f`; Z satisfies the same standing hypotheses.
  Use the permitted canonical composition/refinement coordinates for g: `U -> Z -> Y`
  with open `j ≫ i`. The module does not assume equality between independently chosen
  functors: `supportComposition` constructs the canonical left-functor comparison using
  the inline left-adjoint-uniqueness comparison of the composite open adjunctions, and `composite` transports the composed adjunction along
  precisely that comparison. A different chosen compactification is identified by the
  canonical comparisons stipulated in the node, before reading this equality.
* Finite unital coefficient map: `{A B : Type u}`, `[CommRing A]`, `[CommRing B]`,
  `[Finite A]`, `[Finite B]`, `φ : A →+* B`. No flatness or Tor dimension of B/A is bound.
* Common annihilator N = ell^n >= 1: `n : ℕ`, `_hA : (ℓ ^ n : A) = 0`, and
  `_hB : (ℓ ^ n : B) = 0`. Positivity of ell^n follows from ell prime. Annihilation of 1
  is equivalent to annihilation of the whole coefficient module.
* Constant-module derived categories: the existing `proEtaleDerivedCategory` is used
  by all ambient functors. `spFiniteConstructibleTorCategory T R` is the existing full
  subcategory with bounded cohomology, intrinsic constructibility in every degree, and
  `HasFiniteProEtaleTorAmplitude`. Its Tor definition tests all degree-zero module sheaves
  in one ordered integer interval. No etale-origin restriction is added.
* The setting paragraph mentions both sites; the actual adjunctions and asserted equality
  are on the pro-etale finite-Tor categories, exactly as the node specifies. Etale/pro-etale
  transfer and coefficient compatibility are imported; no separate ordinary-etale equality
  is asserted by this node.
* Scalar extension T_T: `scalarExtensionFunctor φ T`, the existing universal derived
  extension along the actual constant-ring map. `hSU`, `hSX`, `hSY` only certify its
  Dctf membership, as the node's notation already requires.
* The Tate-line paragraph fixes a coefficient convention, but no twist or d occurs in
  the asserted locality equation. The existing `finiteEtaleTateTwist` module is available through the preservation dependency;
  no Tate variable or trivialization is added to the theorem.
* F_f,R adjoint G_f,R: `a`, `b : SupportAdjunction ...`. The structure packages the
  preservation proof, arbitrary right functor, and its adjunction to the actual restricted
  `reductionCompactSupport R i p`. This includes the Brown restriction. Right-adjoint
  uniqueness makes the result independent of its presentation. `preserves` is just a proof
  allowing a full-subcategory lift, not a replacement lower-shriek functor.
* J_R adjoint U_R and actual counit v_R: `extension` restricts the published termwise
  `sfIntrinsicDerivedOpen R j`; `restriction` restricts the published
  `proEtaleConstantRingDerivedPullback R j`. `openAdjunction` localizes the actual ordinary
  `sfIntrinsicOpenAdjunction`, changes pullback coordinates by the unique unit-preserving
  `openSquareDerivedPullbackModel`, then calls `restrictFullyFaithful`. Thus its counit is
  the actual open counit, not arbitrary adjunction data. `hJA`, `hJB`, `hUA`, `hUB` only
  witness membership in the stated categories.
* F_g = F_f J and G_g = U G_f, preserving adjunctions: `composite` uses
  `Adjunction.comp` and `ofNatIsoLeft (supportComposition ...).symm`. Its right functor
  is literally `a.right ⋙ restriction ...`; its counit is the composite counit with the
  canonical left comparison inserted. `hGA`, `hGB` only witness the membership of the
  actual restricted compact-support functors in these full categories.
* The specified b_f, b_g: `(reductionDirectImageComparison φ i p).app M.obj` and
  `(reductionDirectImageComparison φ (j ≫ i) p).app L.obj`. Their construction is the
  proper-counit mate followed by the canonical open tensor map. `hbf`, `hbg` record only
  invertibility of these already specified morphisms on Dctf; no free comparison is chosen.
* The unique counit transpose c_h: `component` applies `b.adjunction.homEquiv` to
  `inv (reductionDirectImageComparison ... .app (G_A K).obj)` followed by
  `(scalarExtensionFunctor φ Y).map (a.adjunction.counit.app K).hom`. This constructs the
  exact morphism with the defining counit equation; the Hom equivalence gives uniqueness.
  Neither c_f nor c_g is introduced as an arbitrary map or assumed invertible.
* Canonical a_j: `(directImageScalarPullbackIso φ j).inv.app (a.right.obj K).obj`.
  The recorded lambda has direction U_B T_X -> T_U U_A, so its inverse has exactly
  the direction T_U U_A -> U_B T_X specified for a_j in this node.
* Every K in C_Y,A: `K : spFiniteConstructibleTorCategory Y A` is unrestricted.
* Conclusion c_g,K = U_B(c_f,K) after a_j: the left side is `component` for `(j ≫ i,p)`
  and the two `composite` adjunctions; the right side is the inverse lambda component
  followed by `(proEtaleConstantRingDerivedPullback B j).map (component ... K)`.
  Lean's `≫` reverses the written order of the mathematical composition symbol.
  Equality is of the actual derived arrows. Fullness gives the equivalent Dctf equality.

All preservation and b-invertibility proof arguments spell out properties implicit in the
node's named restricted functors/isomorphisms. They do not change a functor on objects or
arrows, impose an etale-origin condition, or assume the locality identity. Those properties
are supplied by the statement dependencies (scalar extension, finite exceptional preservation,
and compact-support scalar isomorphism).

### Dependency declarations read and used

* `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.
  BoundedConstructible`, `CondensedRing.compactificationOverField`; the theorem writes the
  setting explicitly and takes a specified compactification rather than choosing another.
* `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `Etale.DerivedCategoryModule`, the ordinary derived-category/cohomology conventions.
* `def-weil-proetale-constructible-sheaf`: `Sheaf.Paper.ProEtaleFixedModuleConstructible`,
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, publicly retaining the intrinsic
  `Scheme.IsConstructibleProEtaleModuleSheaf` used by the existing Dctf category. The module
  uses that intrinsic declaration, already publicly imported by the scalar/support dependencies;
  the unused fixed-module-only specialization need not be directly imported.
* `def-weil-proetale-tor-amplitude`: `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`,
  `Scheme.HasFixedCoefficientProEtaleTorAmplitude`, publicly retaining the intrinsic
  `Scheme.HasFiniteProEtaleTorAmplitude` used here through the scalar/support imports.
  The unused fixed-coefficient specialization is not imported directly. No incompatible fixed-module object is
  supplied to a ringed-module predicate.
* `det-sp-et-proet-adjunction-transfer`: `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`,
  `AdjunctionTransfer.etaleProEtaleAdjunctionTransfer`; adjunction transport background.
* `det-sp-scalar-extension-functor`: `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`,
  `scalarExtensionFunctor`, used directly in component and the preservation binders.
* `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`,
  `ModuleCat.OrdinaryDerivedChangeOfRings`, publicly retaining the generic ringed cochain
  model; the scalar functor above uses that canonical ringed construction.
* `def-asd-finite-etale-tate-twist`: `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`,
  `Scheme.finiteEtaleTateTwist`; convention only, no twist appears in the equality.
* `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `IsOpenImmersion`.
* `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.RefinementCategory`,
  `Compactification.Refinement`; the explicit factorization is its compactification data.
* `sk-prop-sf-rf-shriek-preservation`: `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`,
  `CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible` supplies the
  restricted adjunctions used as data. The theorem works with their ordinary intrinsic
  presentation; it does not identify incompatible module-object and ringed categories by fiat.
* `det-sf-mate-open-restriction`: `Sheaf.Paper.MateOpenRestriction`,
  `CondensedRing.mateOpenImmersion` and `mateOpenSourceLowerShriek` fix the open/composition
  convention. The intrinsic presentation is constructed from its ordinary exact open adjunction.
* `def-weil-pbc-composite-adjunction`: Mathlib `CategoryTheory.Adjunction.comp`, used
  directly in `composite`; `comp_counit_app` gives its counit formula.
* `lem-sp-et-proet-coefficient-compatibility`: `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`,
  `CoefficientCompatibility.etaleProEtaleCoefficientCompatibility` and the refinement,
  composition and counit clauses. Imported to retain the specified refinement convention.
* `det-sp-reduction-direct-image`: `Sheaf.SecSmoothPurity.ReductionDirectImage`,
  `reductionDirectImage_isIso`, whose comparison map is used directly here.
* `def-sp-constant-scalar-pullback-comparison`: `Sheaf.SecSmoothPurity.DirectImageScalarOperations`,
  `directImageScalarPullbackIso`, used directly with the orientation described above.

Four landed definition-owning nodes were added to stmt_deps, as allowed by brief-stage2 §5:
`sk-def-sp-normalized-towers` owns the Dctf predicate/full category
(`Sheaf.Paper.SmoothPurityNormalizedTowers`, `spFiniteConstructibleTor` and
`spFiniteConstructibleTorCategory`);
`def-sp-finite-intrinsic-open-square` owns the intrinsic open functor and adjunction
(`Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`, `sfIntrinsicDerivedOpen` and
`sfIntrinsicOpenAdjunction`); `def-trf-finite-pullback-coordinate-comparison` owns the
unit-preserving coordinate comparison
(`Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`, `openSquareDerivedPullbackModel`).
The open compositor is constructed inline from the composite open adjunctions using
`Adjunction.leftAdjointUniq`, followed by exact termwise descent; no unowned compositor
or open-square exchange theorem is used;
`def-sp-reduction-direct-image-comparison` owns the actual compact-support functor and scalar
map (`Sheaf.SecSmoothPurity.ReductionDirectImageComparison`, `reductionCompactSupport`,
`reductionDirectImageComparison`). Their definitions are used, never copied.

The proof dependencies `lem-sp-open-scalar-restricted-transpose-expansion` and
`lem-sp-open-scalar-inverse-transpose-factorization` have no Lean record/module on the
read base. They are therefore named in the theorem's step-by-step proof docstring but
cannot yet be imported. They are proof-only prerequisites and need no statement modules
in this delivery. The stated composite-adjunction proof dependency is imported via Mathlib.

### Edge cases and source checks

Read the node's full three-step proof and its Locality source paragraph in
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md`. The equality follows there from composing
adjunctions, open/scalar compatibility and uniqueness of counit transposes. The accepted
stage-1 re-split is preserved: the released repair note concerns that earlier split, now
completed in the node; this delivery does not re-collapse its two separate proof arguments.

Checked empty U, empty X/Y, zero complexes, zero coefficient rings, n=0 (forcing A and B
zero), identity j, identity coefficient map, non-surjective coefficient maps and non-flat
coefficient maps. No Nontrivial, Nonempty, positive-relative-dimension, smoothness, or flatness
hypothesis excludes them. Composition uses the actual open counit for j, including j=id.
The chosen coefficient universe is the existing intrinsic convention: rings and schemes
in u, constant scalar sheaves in u+1, with the original small pro-etale site. No site
universes are equated and no essential-smallness assumption is imposed as extra data.
The right-adjoint choices are quantified with their adjunctions, so all counit-preserving
presentations are covered. There is no claim about invertibility of c_f or c_g.
No statement fault or STATEMENT-DISPUTED finding.

### Searches

Used the prescribed msearch.py wrapper for LeanFinder:
"Exceptional inverse image scalar coefficient comparison commutes with source open
restriction" (8 unrelated restriction/section lemmas); Loogle:
"CategoryTheory.mateEquiv, CategoryTheory.Adjunction" (generic mate/pasting API);
Mathlib grep: "mateEquiv_hcomp|exceptional.*scalar" under CategoryTheory (7 general
mate identities); LeanSearch: "Exceptional inverse image coefficient comparison commutes
with restriction to an open subset of the source" (8 scheme/open restriction lemmas).
None states this geometric equality with the specified canonical b maps.

Searched `lean/WeilConjectures` and `lean/Sheaf` with rg for exceptional/scalar,
reductionExceptional, open/scalar/locality and counit transpose patterns; also searched
the exact node id in WeilConjectures. Found `ReductionExceptional`, which assumes smoothness
and asserts a different isomorphism/chart theorem; `ExceptionalCoefficientComparison`,
which concerns ordinary-etale coefficient quotients and other compatibilities; and the
canonical constructions reused above. No exact locality theorem was found. Search results
are retained in the sandbox's searches.jsonl. This is not an existing:true match.

### Validation

The prescribed scompile.py server compile is used for the delivered module. The first
version passed in both sandbox and library module modes. An expanded interface revision
hit the fixed 60-second library limit; generated auxiliary structure declarations were
then disabled (genInjectivity/genSizeOf/genSizeOfSpec/genCtorIdx), without changing the
mathematical interface or raising the limit. A confirmation of that revision passed on the server in 52.6 seconds. Redundant direct
imports of unused presentations were then removed; dependency notions remain available
through their used intrinsic declarations. A reducible name for the large support lift was
restored to avoid repeated expansion. Final compile and dry-run results follow below.

## Second reading by Q139

A separate self-review pass read the node and complete module side by side, checking the
bijection defining component, the inverse orientation of lambda_j, the source and target
of both concluding paths, and the counit-preserving compositor. The compact-support lift is only a reducible `support` abbreviation for the standard
ObjectProperty lift. Giving that large type a name keeps elaboration bounded; it is not
an independent construction or a second derived functor. The existing Dctf/compositor/comparison owner nodes were added to
stmt_deps. The exact proof-only dependencies remain separate and are named in the docstring.
No hypothesis in the conclusion requires smoothness or invertibility of an exceptional mate.
No independent second worker was spawned: the dispatch explicitly forbids other agents;
the maintainer's independent review remains the actual independent reading of this delivery.

### Final checks

The final module passed the prescribed scompile.py server confirmation in 56.4 seconds
under the unchanged 60-second limit, with no diagnostics. The prescribed deliver2.py
--no-push run printed OK (dry run), commit 2c6fca4302e, confirming preflight and compilation.
The recorded signature matches the source verbatim; every source line is at most
100 characters; the sole sorry is the complete proof of the named primary theorem.

## Repair of return L, head fe7317499ec5

H2 is repaired: removed `lem-trf-open-square-exchange` from `stmt_deps` and cited
`def-sp-finite-intrinsic-open-square` for `sfIntrinsicDerivedOpen`/`sfIntrinsicOpenAdjunction`
and `def-trf-finite-pullback-coordinate-comparison` for `openSquareDerivedPullbackModel`.
Replaced the unowned `sfIntrinsicDerivedOpenComp` call inside `supportComposition` by
its inline construction: compose the two actual open adjunctions, transport their right
adjoint by the inverse canonical pullback compositor, apply `leftAdjointUniq` against
the composite-open adjunction, invert, descend termwise, and use the derived-composition
comparison. This is definitionally the same normalized map, including its unit and counit.
It uses no conclusion of the exchange theorem. No new node or dependency module is needed.

The fresh dry run of the saved packet passed at ea2e8266f60 before this repair; that
confirmed the retained packet was usable but did not discharge the independent H2 return.
After repair, the theorem signature and all hypotheses/conclusion are byte-identical to
the saved version. A renewed self-reading checked the actual counit, inverse scalar
comparison, both transpose paths, and identity/empty-open cases. The only Lean change is
the definitionally identical inline construction of the existing support comparison.
The current live node differs from this packet only in `lean` and the authorized added
definition-owner dependencies. No shared repository file or launcher script was edited.

The repaired file passed scompile.py in both sandbox (17.1 s) and library (24.5 s)
modes, with no diagnostics. The final signature check confirmed exact agreement with
lean.statement, a single sorry, explicit variables/universes, and maximum line width 97.
