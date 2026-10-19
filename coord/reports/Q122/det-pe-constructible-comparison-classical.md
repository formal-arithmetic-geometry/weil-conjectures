## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical` states the global and Zariski-local assertions of `det-pe-constructible-comparison-classical`, with `sorry` as the entire proof of each. The declarations are `AlgebraicGeometry.ProEtale.constructible_isClassicalModule` and `AlgebraicGeometry.ProEtale.locallyConstructible_isClassicalModule`. There are no definitions, new nodes, dependency repairs, or statement corrections. The existing node `def-constructible-stratification` is added to statement dependencies because its recorded scheme stratification is used directly.

Source checked: the full current blueprint detail `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-pe-constructible-comparison/sk-thm-pe-constructible-comparison-classical.md`; `literature/stacks-project/proetale.tex`, `lemma-compare-locally-constant` (099Y), `definition-constructible` (09AJ), and `lemma-compare-constructible` (09AK). The supplied node's ten proof steps are rendered in the theorem docstrings. The first docstring contains steps 1--9, including the Isom torsor, descent of its transitions, induction on nonempty strata, the open--closed exact sequence, both comparison terms, and the nonreduced one-stratum issue. The second contains step 10: affine refinement and Zariski locality.

Clause-by-clause check for the global assertion:

- The scheme is `(X : Scheme.{u})`. Quasi-compactness and quasi-separatedness are `[CompactSpace X] [QuasiSeparatedSpace X]`, with no separation or Noetherian condition on X.
- A discrete Noetherian coefficient ring is `(Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]`. Discreteness is the constant-sheaf construction; no topology or continuity structure on Λ is imposed, and there is no `[Finite Λ]` hypothesis.
- A sheaf of Λ_X-modules is `F : ringedSiteModules.{u + 1} ((sheafCompose ... (forget₂ CommRingCat RingCat)).obj (Scheme.proEtaleConstantRing X Λ))`. This is exactly Mathlib's `SheafOfModules`, retaining the action of the sheafified constant ring, not a replacement by an arbitrary constant scalar action.
- The finite partition is `S : Scheme.LocallyClosedStratification X`. It has `n : ℕ` and strata indexed by `Fin S.n`. In the current compiled upstream `Topology.Stratification`, the inherited fields are `isLocallyClosed_stratum`, `isConstructible_stratum`, `iUnion_stratum_eq_univ`, and `pairwise_disjoint_stratum`. Thus each part is both locally closed and constructible, the parts cover X, and distinct parts are disjoint. No closure-incidence or nonemptiness conditions occur. I checked `@Topology.Stratification.isConstructible_stratum` through scompile; the compiler printed the expected `Topology.IsConstructible (self.stratum i)` result. The temporary check has been removed.
- The scheme structure on a stratum is `S.domain k`, with immersion `S.immersion k` and the recorded `range_immersion` equality. `_hred : ∀ k, IsReduced (S.domain k)` makes these precisely the reduced induced representatives of their locally closed subsets. This is a choice of representative up to the unique isomorphism over X; it does not ask that X itself be reduced. On an open in which the stratum is closed, this identification is exactly the reduced-induced-closed-subscheme dependency. Every locally closed subset has such a reduced immersed representative, so no partition is excluded.
- Restriction F|Z_k is the actual canonical `Scheme.proEtaleConstantModulePullback (S.immersion k) Λ F`. Its construction applies inverse image and tensors along the canonical constant-ring comparison, rather than selecting a map or coefficient identification.
- Local constancy of finite type is `_hmodels`: for each k there are an index type `I : Type (u + 1)`, site objects `V : I → (S.domain k).ProEt`, and arrows to `ProEt.mk (𝟙 (S.domain k))` whose presieve belongs to `ProEt.precoverage`. For every cover member there is `M : ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)` with `Module.Finite (ULift ... Λ) M` and a module-sheaf isomorphism between the slice restriction and `Scheme.proEtaleConstantModuleSheafOver ... M`. These are the exact localized constant-module construction and covering condition of the recorded locally-constant-sheaf dependency, with finitely generated models added as the node requires. The models may vary over the cover and over the strata. Neither free models, finite underlying sets, nor a uniform rank are required.
- The conclusion is `IsClassicalModule Λ F`: for every recorded affine pro-etale presentation, its canonical restriction-induced colimit map in coefficient modules is an isomorphism. This is the recorded classicality definition, not an unproved replacement by essential image.

For the final local clause, `locallyConstructible_isClassicalModule` retains precisely the same X, Λ, F and qcqs/Noetherian hypotheses. `_hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ...` says that the partition exists on a Zariski neighborhood of each point, with no global partition fixed. The remaining existential `S : LocallyClosedStratification U.toScheme` carries exactly the partition conditions above, with reduced domain schemes and the same finite constant local models. Its sheaf on a stratum is pullback along `S.immersion k ≫ U.ι`; this is restriction of F to that stratum, independent of factoring through U. The conclusion is again `IsClassicalModule Λ F`. The neighborhood U is not required to be affine, quasi-compact, reduced, or equipped with a bound on its number of strata; affine refinement belongs to the proof.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`; `Mathlib.Topology.Defs.Filter`: `CompactSpace`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`, with its scheme characterization `QuasiSeparatedSpace`; `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the recorded small `Scheme.ProEt`/`Scheme.ProEt.topology` and intrinsic constant coefficient convention; these are publicly available through the imports. The site objects have universe u+1 and morphisms have universe u. The coefficient lift and module values have universe u+1, without equating the site universes.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`; `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparently Mathlib's `SheafOfModules`.
- `Mathlib.Topology.Defs.Basic`: `IsLocallyClosed`; `Mathlib.Topology.Constructible`: `Topology.IsConstructible`; `Sheaf.AlgebraicGeometry.LocallyClosedStratification`: `Scheme.LocallyClosedStratification` and its inherited `Topology.Stratification` fields. The current compiled inherited type has constructibility even though the old wrapper's docstring predates that addition; this is exactly a requirement of this item, so it needs no weakened or repaired dependency.
- `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`: the recorded `Scheme.IsLocallyConstantProEtaleFixedModuleSheaf` publicly imports `Sheaf.Paper.ProEtaleLocallyConstantSheaf`, whose `proEtaleConstantModuleSheafOver` is used. I read both definitions. The arbitrary-ring intrinsic construction in this existing module is the appropriate encoding of F here. The fixed-coefficient predicate has the same covering and constant-model conditions; the theorem spells out those conditions with the required finiteness and intrinsic ring action, instead of introducing a second local-constancy predicate.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, finite generation of the top submodule.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`: its public import closure retains the arbitrary-ring inverse-image construction in `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`. The declarations used are `Scheme.proEtaleConstantRing` and `Scheme.proEtaleConstantModulePullback`. The primary recorded finite-ring adjunction `sfIntrinsicConstantModuleAdjunction` is not applied; its `[Finite A]` condition is not imposed on this theorem. The existing arbitrary-ring construction already has the required signature and is used directly.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`: `Scheme.IdealSheafData.reduced_induced_closed_subscheme`. The source was absent from the older local checkout, so I read its complete current source with `scompile.py --source`; it supplies reducedness, immersion, image, and unique isomorphism over the ambient scheme.
- `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`: `AlgebraicGeometry.ProEtale.IsClassicalModule`, and its canonical `moduleContinuityMap`. The currently landed `sk-def-pe-classical-definition` record already points to this module, as does its detailed continuity-map dependency. No duplicate predicate or record repair is needed.

All proof dependencies with a recorded module are imported; dependencies recorded as Mathlib leaves have the corresponding Mathlib imports. Unstated proof-only nodes need no new theorem in this statement delivery. The statement adds no arbitrary comparison map, chosen equivalence, or proof placeholder inside a definition.

Edge cases checked: the empty scheme and `S.n = 0` are permitted, and the local hypothesis on the empty scheme is vacuous; empty individual strata are permitted. The zero coefficient ring and zero module are allowed. The one-stratum case uses a reduced representative of X_red, not an assumption that X is reduced or a silent identification of F and its restriction to X_red. Arbitrary Noetherian commutative coefficients, including infinite rings, are retained. Finite generation is not confused with finiteness of the underlying set. Cover index types and module values use the common larger universe, and no independent lower test universe or object/morphism universe equality is added. Every universe and variable is explicit; `autoImplicit false` is set. No statement dispute or node correction is needed.

Searches for an existing declaration:

- `msearch.py ... leanfinder "Constructible pro-etale sheaves of modules over a Noetherian ring are classical"`: eight hits, including `SheafOfModules.IsFiniteType`, `IsFinitePresentation`, `isFinitePresentation`, and condensed-module constructors. None states classicality on a scheme's pro-etale site.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.ProEt, IsLocallyConstant, IsClassical"`: zero hits; the service reports that `IsClassical` is unknown.
- `msearch.py ... leansearch "Constructible proetale sheaves of modules are classical"`: eight hits, including `SheafOfModules`, its constructors, and abelian-category instances; no matching comparison theorem.
- `msearch.py ... grep "IsClassical|classical.*sheaf|constructible.*[Cc]lassical" AlgebraicGeometry`: zero Mathlib hits.
- `rg` searches for classicality, constructibility and local constancy in the named upstream and side source directories found `ClassicalContinuityMap`, the intrinsic and fixed-coefficient constant-module definitions, and the finite-ring constructibility/origin interfaces. Their signatures were opened. The finite-ring interfaces impose `[Finite A]` and do not state this arbitrary-Noetherian-ring theorem. The continuity module defines the conclusion but contains no such constructibility theorem.
- Exact identifier search `grep -rn "det-pe-constructible-comparison-classical"` in the upstream `WeilConjectures` source returned no hit. Searches for both proposed declaration names in Mathlib/project/side code and the upstream-name table also found no declaration.

Validation: the single module passed `scompile.py Q122 det-pe-constructible-comparison-classical ...` with both the sandbox and library-path checks, without errors or warnings. The final delivery dry run is recorded below once complete. No global build or live-source edit was run. The two theorem proofs are the only `sorry` terms.

## Second reading by Q122

I read the item node, its blueprint source, the Stacks passages at Tags 099Y, 09AJ,
and 09AK, the added dependency `def-constructible-stratification`, and every
declaration used by the module. The node's statement decomposes as follows:

1. Introduce a discrete Noetherian commutative coefficient ring `Λ`; this is
   rendered by `(Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]`, with discreteness
   supplied by the constant-ring construction.
2. Introduce a quasi-compact, quasi-separated scheme `X`; this is rendered by
   `(X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]`, with no separation,
   Noetherian, finite-ring, or reducedness assumption.
3. Introduce a `Λ_X`-module sheaf `F` on `X_Proet`; the first theorem uses the
   intrinsic `ringedSiteModules` over
   `sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat RingCat)` applied
   to `Scheme.proEtaleConstantRing X Λ`.
4. Introduce a finite partition by constructible locally closed strata. This is
   `S : Scheme.LocallyClosedStratification X`, whose `Fin S.n` strata inherit
   local-closedness, constructibility, pairwise disjointness, and coverage from
   `Topology.Stratification`; no stratum nonemptiness or closure ordering is added.
5. Interpret each stratum with its reduced structure. The explicit hypothesis
   `_hred : ∀ k, IsReduced (S.domain k)` and the immersion/range fields of `S`
   provide reduced immersed representatives of the locally closed subsets.
6. State finite-type local constancy on each stratum. `_hmodels` gives a genuine
   pro-etale covering of each `S.domain k`; on every cover member it supplies a
   finitely generated `ULift Λ`-module and a module-sheaf isomorphism from the
   canonical `proEtaleConstantModulePullback (S.immersion k) Λ F` to
   `proEtaleConstantModuleSheafOver`. Models may vary with the member and stratum.
7. Conclude classicality with the recorded predicate `IsClassicalModule Λ F`.
8. Render the locally-on-`X` variant with the same `X`, `Λ`, `F`, and qcqs
   hypotheses, and `_hlocal : ∀ x, ∃ U : X.Opens, x ∈ U ∧ ...`; the inner
   stratification and reduced finite-type models use the composite immersion
   `S.immersion k ≫ U.ι`, and the conclusion is again `IsClassicalModule Λ F`.

The theorem declarations match every item above, in the same quantifier order.
The canonical inverse-image construction is used throughout; no arbitrary map,
chosen equivalence, or extra coefficient identification appears. The source's
one-stratum torsor argument, transition descent and gluing, induction on strata,
open--closed sequence, extension-by-zero comparison, reduced closed term,
and affine/Zariski-local reduction are carried in the two declaration docstrings
with the node's proof dependencies. Both theorem bodies are `sorry` only.

Edge cases are covered: `S.n = 0`, the empty scheme, empty individual strata,
the one-stratum nonreduced ambient scheme, the zero ring and zero module, and
infinite Noetherian coefficient rings. The index and module universes are
`Type (u + 1)` with `ULift.{u + 1, u} Λ`, while `X`, `Λ`, and the pro-etale
scheme universe remain at `u`; no independent smaller test universe is introduced.
The local open is not required to be affine, qcqs, reduced, or finite-stratified
uniformly; affine refinement is part of the proof.

I searched Mathlib, the project `lean/Sheaf` tree, the read-only upstream
`WeilConjectures` tree, and the upstream-name table with grep, LeanSearch,
Loogle, and LeanFinder for constructible pro-etale classicality and both proposed
declaration names. The only relevant matches were the existing classicality
predicate, constant-ring/module constructions, and stratification/local-constancy
infrastructure; no matching theorem exists. The existing
`def-constructible-stratification` declaration was opened and used directly.

No mismatch was found, so no Lean or node repair was needed beyond the worker's
recorded addition of that existing dependency and the two declarations. The
module compiled cleanly with the required `scompile.py` wrapper; there are no
warnings other than the permitted postponed theorem proofs. No statement
correction, new node, dependency repair, or citer audit applies.
