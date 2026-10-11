# Standing brief for a stage-2 worker

Written by the lead (rules: decision of the human, 2026-10-11). Your prompt names your group `<G>` and your item; this page says what to deliver. Read `AGENTS.md` §3–5, `roles/worker.md`, `stages/2-statements.md` and `SETUP.md` ("Stages 1 and 2 are open") first, then `coord/delivery-errors.md` section H (stage 2). You write Lean statements and definitions; nothing is proved. Temporary files go into a scratchpad subdirectory named after your item.

## 0. What you read

- The node `dag/nodes/<chapter>/<id>.json`: `statement`, `kind`, `source`, `stmt_deps`, `proof` (statement nodes), `mathlib_searches`.
- Every node in `stmt_deps`, its statement and its `lean` record (`module`, `declaration`) or `mathlib_match`.
- The source module of each recorded declaration: `~/weil-conjectures-slopmaster2/<module path>.lean` (module `A.B.C` is file `A/B/C.lean`; compiled, read-only). Read the declaration and its docstring, not only its name.
- Mathlib: `~/weil-conjectures-slopmaster2/.lake/packages/mathlib/Mathlib/` (read-only).
- The node's source place: for Stacks, `literature/stacks-project/` (`stacks-project/tags/tags` maps a tag to its label).
- The example module `lean/Sheaf/CategoryTheory/CompactObject.lean` (node `def-pc-compact-object`, in git): header, docstrings, namespace as in §3.

## 1. Your item

One DAG node that a target reaches, split in stage 1, with no Lean declaration yet, whose `stmt_deps` all have a recorded `lean` or are Mathlib leaves. You write its module `lean/Sheaf/<Topic>/<Name>.lean`: the definition (definition node) or the statement with `sorry` as its proof (statement node). Nothing else is proved in it.

**One definition per notion.** Before writing, search whether Mathlib or the source repository (`~/weil-conjectures-slopmaster2/WeilConjectures/`) already defines the notion or states the statement: three kinds of search as in stage 1 (`coord/brief-stage1.md` §5: LeanSearch; Loogle or LeanFinder; grep of Mathlib and of `WeilConjectures/`), and the source's names in `dag/lean_names_upstream.json` (`tools/lean_names_upstream.py show`; `grep -rn "<id>" ~/weil-conjectures-slopmaster2/WeilConjectures`). If one exists and says exactly what the node says, record it as the node's `lean` with `"existing": true` and write no file. Likewise, when another node of this project already states your node's statement or defines its notion, record that declaration with `existing: true`, `branch: "sheaf-dag"`, `module: Sheaf.<…>` (no file; the declaration is read from `lean/Sheaf` on the base, nothing is compiled).

Claim with `tools/claim.py next <G> --stage 2` (nearest to Mathlib first).

**You add what is missing (STAGE 2 EXTRA NODES, decision of the human, 2026-10-11 05:55 UTC; `coord/STATE.md`).** You do not abandon for a missing or unusable dependency:

- **(A) A missing notion** (the statement needs a notion that no node, no Mathlib declaration and no source declaration gives): add a NEW DEFINITION NODE in the same delivery, `dag/nodes/<chapter of the item>/<id>.json` with the fields of §5, with its own module (or an `existing: true` record when Mathlib or the source has the notion and no DAG node carries it), and cite it from the item: the item's `stmt_deps` gains its id (the one other field of the item you may change). Search first (three kinds) that the notion is not already a node (`tools/blueprint_refs.py search`, grep of `dag/nodes`), not in Mathlib, not in the source.
- **(B) An unusable dependency** (a node in the item's `stmt_deps` whose recorded declaration or `mathlib_match` does not give the notion as the node states it, e.g. the general notion where the node means a specialization): write, in the same delivery, a module stating the dependency node's notion as the node says it, and set that dependency node's `lean` to its record with a `note` saying why the old record was unusable; nothing else of the dependency node changes (its `mathlib_match` stays).
- **(B) with a statement correction** (2026-10-11, T-depcorr): a dependency module may also be delivered for a node your statement correction adds to the item's `stmt_deps` (e.g. a definition node of the base the corrected statement now cites); the rules of (B) are otherwise the same.
- **(C) A wrong statement is CORRECTED, not abandoned (STAGE 2 STATEMENT CORRECTION, decision of the human, 2026-10-11; `coord/STATE.md`).** When the item's own statement is wrong or cannot be written (false, ill-typed, ambiguous, or leaving out what is needed to state it: an object not introduced, an action or a structure not specified, a hypothesis the source assumes throughout), correct the node in the delivery and write the Lean for the corrected statement. The correction makes the node say what the SOURCE says (the Stacks tag, the blueprint unit's intent), never something easier. The item may then change in `statement`, and only as far as the correction forces it in `stmt_deps`, `proof` and `proof_deps`; it gains `statement_change` (§5) and the report gets `## Statement corrected` (§6). Find the citers with `grep -rl '"<item>"' dag/nodes`: every node whose `stmt_deps` or `proof_deps` name the item; read each and write one line per citer (does its use of the item still hold?). A citer that breaks is named (`holds: false`), never edited. A correction that would change a UNIT's own statement is written up for `coord/HUMAN.md` and that item alone is still released: `tools/claim.py release <G> <item> "abandon: unit statement: <the precise reason>"`.

## 2. The statement says exactly what the node says

- Hypothesis by hypothesis, clause by clause, with the same objects (`stages/2-statements.md` §3). No hypothesis added or dropped; no weaker conclusion; no stronger one either.
- Write out the hypotheses the source assumes throughout (base field, Noetherian, separated, characteristic …) as binders; the node's statement or its source place says which.
- Check the edge cases before writing: empty index sets, zero objects, the empty scheme, `n = 0`, the characteristic. A universe or a `Type` choice must not exclude a case the node covers (as `I : Type w` in the example covers every set).
- Use the dependency nodes' recorded declarations (import their `lean.module`) and Mathlib's definitions whenever they exist; never a private copy of a notion.
- No hollow definition (`AGENTS.md` §5): a def's data is never `sorry`. A proof a definition needs (a well-definedness, an instance) is a named theorem with `sorry` of its own, in the same module, with its own docstring.
- No hollow hypotheses: a hypothesis that holds for every instance (`QuasiCompact (𝟙 Y)`, `True`, an unconstrained map) is an H-fault; test with `inferInstance`/a small example (M1 66c7139de, H1 0c1f0b8d2).
- Universes: a hypothesis quantifying over test algebras or schemes must not use an independent universe variable below the ring's or scheme's — it becomes vacuous and the statement false; use `Type (max u v)` as M1 c8ddf5893 (E1 49bcfd276).
- Finite products of abelian categories: Mathlib has no `Abelian` instance on a product category; state the Abelian structure existentially as H1 6a6d5fc0b does, one shared form (siblings lem-weil-pbc-finite-product-injective-resolutions, lem-weil-pbc-finite-product-functor-left-exact).
- Index universes: the index type of a limit or filtered colimit lives in the objects' universe (`I : Type u` with `Scheme.{u}` / `CommRingCat.{u}` / `CommAlgCat.{u} A`), with `[Nonempty I]` when no stage is fixed; an independent `I : Type w` makes the statement false (C1 02bc80ff3, G1 117cfd333; STATE line INDEX UNIVERSES FOR LIMITS AND FILTERED COLIMITS).
- Smooth at a prime is the recorded `Algebra.IsSmoothAtPrime` (K1 e46109f71), never Mathlib `Algebra.IsSmoothAt` (formal smoothness of the local ring).
- `[EssentiallySmall.{u+1} C]` on the `Type (u+1)`/`Category.{u}` site encoding is inherited from slopmaster2 and derivable: it is exempt from the hollow-hypotheses rule (C1 14336d5e8).
- Zigzag family: A^rt (the row cokernel complex) is `A.opcycles 0` (E1 18d13aade), not an arbitrary complex with coforks.
- Ext of modules: two landed forms, Mathlib's `ModuleCat` `HasExt` instance + `ULift` (F1 e0b94df4a) and `letI := HasExt.standard` + `Shrink` (E1 RegularLocalExtVanishing); either is accepted, the bridge is stage 3.
- `let` binders in a statement elaborate as `have`, so stage 3 cannot unfold them: prefer explicit terms (J1 c634916b4).
- A killed merge leaves an inflight landing record that makes `land.sh` exit 3: when the merging process is gone, run `tools/landing.py abort <id>` (G1 a29f681a4).
- `NoetherianApproximation.gluedLimitComparison` takes `[HasLimit N.D]`: citers supply `haveI : HasLimit N.D := ⟨⟨⟨_, N.isLimit⟩⟩⟩` (K1 a5be8ed2e).
- The siblings of module-base-change-map-open-restriction (-pasting, -algebra) cite C1's `Scheme.Modules.moduleBaseChangeMap` (1798df265), never a second definition.
- Λ-module étale sheaves: constructible material uses `Sheaf … (ModuleCat.{u+1} Λ)` with `Λ : Type (u+1)`; the `ULift` `SheafOfModules` encoding does not apply there (F1 c208eb7a6; STATE line Λ-MODULE ÉTALE SHEAVES: TWO ENCODINGS).
- No `let` in statements: they elaborate as `have` and stage 3 cannot unfold them; write the terms out (21 lets removed in C1 14d642f46).
- Never run `cat` (or any reader) without a file or heredoc: it waits on stdin and stalls the agent (F1 e681a69a6 reviewer, 16 min).
- `IsZero` on a bare `Type` is unprovable; state vanishing as `Subsingleton` (J1 bd3f9a579).
- Rebase on sheaf-dag before delivering: a stale-base re-record of a landed node is reverted (F1 394d93d01).
- A dead inflight landing record (merging process gone): `tools/landing.py abort <id>` (C1 2556ce25a).
- ⨁ on sheaves of modules needs a local `HasFiniteBiproducts.of_hasFiniteProducts` instance (`Abelian.hasFiniteBiproducts` is a theorem, not an instance) (E1 45deb4957).
- Support of a module is inline `{x | ¬ Subsingleton (F.presheaf.stalk x)}` (C1 14e331910; STATE line SUPPORT OF A MODULE); stalks as objects/maps `RingedSpace.moduleStalkFunctor` (STATE line MODULE STALKS).
- A finitely generated field extension is `(⊤ : IntermediateField k K).FG`, never `Algebra.FiniteType k K` on a field (that forces K/k finite) (C1 7d950be5e; STATE FG FIELD EXTENSION).
- Short exact sequences of modules: `Function.Injective f`, `Function.Exact f g`, `Function.Surjective g`, independent universes (C1 5230e4cc1). Surjective scheme morphisms: class `Surjective f` (F1 b47d9c774). Sheaf Hom: `SheafOfModules.homObj`.
- Ring sheaves on a space are `moduleRings X` of `X : RingedSpace.{u}`; no unbundled TopologicalSpace + RingCat sheaf, no inline sheafCompose/forget₂ (G1 3fcb1ccf8, K1 fa0c6ab80). Quasi-coherent ideals are `X.IdealSheafData`, not an abstract mono (G1 7fec07874, C1 9a5a7bbfd).
- Ring-map existentials of the relative-global-complete-intersection family are replaced by the presentation predicate; an enlarged presentation is `Fin (n+1)` via `Fin.snoc`/`Fin.castSucc`, not `Option` (H1 cc8512bcd).
- Never re-push a returned branch of an item that has landed (C1 6b3a3b9a4, K1 7dc59c357); clear a STATEMENT-DISPUTED flag once the second reading resolves it (H1 07ce24a3e).
- No `show … from` in statements: it elaborates as a hidden `have`; name equivalences with `Equivalence.functor (C := …) (D := …)` and cast sections with `@id T x` (G1 ce180b4c0, M1 991a80c11).
- No file-local `notation`, `local instance`, `private` definition or abbreviation in a statement module; a statement must read outside its file and namespace (`Module.Basis`, not `Basis`) (F1 91b674ef5, J1 f048a280a, E1 b5d12a0ed; STATE line FILE-LOCAL NOTATION).
- Derived tensor on schemes: new statements use the global `schemeDerivedTensorMonoidal` (def-pc-scheme-derived-tensor-structure, M1 0ec9b24af) with `⊗`, `▷`, `𝟙_`; landed K-flat-representative statements stay valid; never a second derived-tensor definition (STATE line DERIVED TENSOR ON SCHEMES).
- No tautological conjunct (`pullback.condition`, `0 ≤ h`) and no clause the node does not state (C1 f683186fb, 52041d948; J1 6b2c20148).
- Compile under the default 120 s limit; never raise SHEAF_FILE_TIMEOUT to pass (G1 61a26ce2c). `Additive` of a three-fold functor composite needs `set_option synthInstance.maxSize 2048` (H1 8f2941a40).
- Conventions added at B-1418 (STATE): PSEUDO-COHERENT, PERFECT, TOR AMPLITUDE, DERIVED PULLBACK, DERIVED FIBRES, EXTENSION BY ZERO, KOSZUL COMPLEX, P-BASIS, POWER SERIES, POPESCU FAMILY, RELATIVE SPEC AND QUASI-COHERENT ALGEBRAS, PROJ TWISTS, REGULAR and FAITHFULLY FLAT RING MAPS — read them before stating a node of these families.
- Derived restriction to an open U of a scheme is `(SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U ⋙ Equivalence.functor (C := …) (D := …) (Scheme.Modules.overEquiv U)).mapDerivedCategory` into `schemeDerivedCategory U.toScheme` (G1 ce180b4c0, M1 f526a6fea); between opens `overMap ... |>.mapDerivedCategory`, Hom restriction `AlgebraicGeometry.derivedOpenHomRestriction`; the exactness instances `moduleOverFunctor_*`/`moduleOverMap_*` in lean/Sheaf/Paper/DerivedHomMayerVietoris.lean are shared, a restatement fails H4 (STATE line DERIVED RESTRICTION TO AN OPEN).
- A statement you find false or untypable: correct the node by (C) of §1, following the source, with `statement_change` and the report section. Never write it weaker, never change the statement silently (H7).
- A statement you only doubt (no counterexample, the source agrees with it): write it as the node says, mark `STATEMENT-DISPUTED: <reason>` in the report.

## 3. Conventions (upstreamable by renaming module paths `Sheaf.X -> WeilConjectures.X`)

- Directory by topic as in `WeilConjectures/`: `AlgebraicGeometry`, `CategoryTheory`, `RingTheory`, `FieldTheory`, `GroupTheory`, `Topology`, …; paper-specific under `Sheaf/Paper/`, targets under `Sheaf/Targets/`. File name: the main declaration in UpperCamelCase.
- Namespace: the one upstream would use, with NO `Sheaf.` prefix (only the module path starts with `Sheaf.`; upstreaming renames module paths, no declaration). Example: `open CategoryTheory CategoryTheory.Limits`, `namespace CategoryTheory`, `def IsCompactObject …`, `end CategoryTheory`. The full name must not already exist in Mathlib or the source repository: check with `mcp__lean-lsp__lean_local_search` (`index: consulted`) and grep of `dag/lean_names_upstream.json`, Mathlib and `WeilConjectures/`; the preflight checks it too. Names follow Mathlib's naming (`IsFoo` for a Prop-valued def, `foo_of_bar` for a theorem).
- Module docstring after the imports: `/-! # <title>` then `Source: <document, place> (blueprint: <node id>)`, and for several declarations a `## Main definitions` / `## Main statements` list as in `AlgebraicGeometry/Curve.lean`.
- Every declaration has a docstring naming the source place and carrying `(blueprint: <node id>)`. A statement's docstring also carries the node's proof in natural language, step by step (its `proof` steps, with the nodes they use), so that stage 3 can take it from there.
- Lines of at most 100 characters. Imports only `Mathlib.*`, `WeilConjectures.*`, `Sheaf.*`; no import the file does not use. Header as in the example module.
- The source's lakefile options hold: `relaxedAutoImplicit = false` (bind every variable, every universe); `warn.sorry = false`.
- Module pullback of O_X-modules = `Scheme.Modules.tensorPullback` (def-pc-module-pullback; adjunction `exists_tensorPullbackAdjunction`), never Mathlib's `Scheme.Modules.pullback`; a node's literal `Modules.pullback`/`g^*` names that node. Invertible = `Scheme.Modules.IsInvertible`, not `SheafOfModules.IsInvertible`. This binds the second reading too.
- "X a scheme over k" is `[X.Over (Spec (.of k))]` with properties as instances on `X ↘ Spec (.of k)` (def-weil-scheme-over-base); explicit `(f : X ⟶ Spec (.of k)) [P f]` only when the node names f, involves base change/several morphisms over the base, or a recorded declaration takes f (`Scheme.Hom.genus`, `f.picZero`, `f.picDegree`, `IsConnectedCurve f`). Both are the same notion: not H4, never convert one acceptable form to the other (STATE line SCHEMES OVER A FIELD). (08:29 UTC, L) Bundled `CategoryTheory.Over (Spec (.of k))` objects (`X Y : Over (Spec k)`, `f : X ⟶ Y`) are also acceptable when the node concerns morphisms between k-schemes or base change of a morphism (as landed K1 181333b23, C1 f5ae2762f, E1 6a5137809; the h_T form of def-pc-base-change).
- Cartan–Eilenberg resolutions are stated as E1's landed `CategoryTheory.exists_cartanEilenberg_resolution` (lem-sp-cartan-eilenberg-exists, 733ed5a76): `HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)`, `I.X p = 0` for p < 0, augmentation one bicomplex morphism `e` from the `single₀` complex, columns via `InjectiveResolution` fields, horizontal cycles/boundaries/cohomology via `cyclesMap`/`image.map`/`homologyMap` of the same `e`; J1's exchanged-index lem-sp-cartan-eilenberg-properties (0f91f06a8) is bridged in stage 3, not restated; H^q(G C^{p,•}) tied to the d_I-induced differential is a natural comparison isomorphism, never bare `Nonempty` (STATE line CARTAN–EILENBERG RESOLUTIONS).
- O_X-module cohomology H^p(X,F) (ringed spaces and schemes) is `AlgebraicGeometry.RingedSpace.moduleCohomology` = right derived functors of `AlgebraicGeometry.RingedSpace.globalSectionsFunctor` (def-sc-ringed-space-module-cohomology, 4b0b00fd2); `Scheme.Modules.H` and `Sheaf.H (structureSheafAb X)` (4431da60d) are abelian-sheaf Ext, bridged by a stage-3 comparison node; `Scheme.Modules.globalSectionsFunctor` (88cbf2b3b, into `AddCommGrpCat`) stays for Γ as additive functor, related by a bridge lemma (STATE line COHOMOLOGY OF O_X-MODULES).
- H^p(U, F) for an open U of a ringed space X is `openModuleCohomology X p U`, restriction `openModuleCohomologyRestriction` (def-sc-open-module-cohomology, K1 657edd2b1); at U = ⊤ bridged to `RingedSpace.moduleCohomology` at stage 3 (`openModuleCohomology X p ⊤ ≅ moduleCohomology X p ⋙ forget₂`); do not define a third cohomology (STATE line COHOMOLOGY ON OPENS).
- ℓ-adic coefficients (pod family): a finite extension E of ℚ_ℓ gets its topology by `letI := spectralNorm.nontriviallyNormedField ℚ_[l] E` inside the statement, V gets `moduleTopology E V`, O_E / m_E are `Padic.coefficientExtensionIntegers` / `Padic.coefficientExtensionMaximalIdeal` (E1 1a2c6f80c lem-pod-profinite-stable-lattice); later pod nodes use the same form (STATE line ℓ-ADIC COEFFICIENT TOPOLOGY).
- k(X): for an integral scheme Mathlib `Scheme.functionField` (the integral clause of def-sc-function-field, fe8e51bb7; landed DivisorModule, InvertibleModuleGenericStalk, SmoothConnectedCurveLocalRings, E1 79512e034 use it); for a general scheme the recorded `rationalFunctionRing` (def-sc-rational-functions); not a third carrier (STATE line FUNCTION FIELD).
- f étale at x is `∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)` (J1 etale_of_faithfullyFlat_fieldExtension, K1 496a0cd49); no `IsEtaleAt` node; 'étale over a neighbourhood of the image point' is a different and false reading of Stacks 0B2G (STATE line ÉTALE AT A POINT).
- D⁺ truncation is `DerivedCategory.TStructure.t.onPlus.truncLE`/`truncLEι` (F1 79f258e3d); `DerivedCategory.truncLE` does not exist in the pinned Mathlib (STATE line D⁺ TRUNCATION).
- Abelian curve pairs and C1–C8 feed through the Ab ≃ Mod(ULift ℤ) bridge `E` of E1 7631c4992 (lem-weil-pbc-curve-assertions-finite-pushforward); no second bridge (STATE line ABELIAN CURVE PAIRS AND C1–C8).
- A normal ring (def-weil-pbc-normal-ring) is written inline as `∀ (p : Ideal A) [p.IsPrime], IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)` (K1 ccd06d885, H1 a96cb269b); for a domain `IsDomain ∧ IsIntegrallyClosed`; no named predicate (STATE line NORMAL RING).
- κ(p) ⊗[R] S is Mathlib `p.Fiber S` (`Ideal.Fiber`, `Algebra.TensorProduct.includeRight`, `PrimeSpectrum.preimageEquivFiber`); never a hand-written `S ⊗[R] κ(p)` (E1 846bd08dc, F1 c84d7f11f, G1 e8f0036eb, J1 609956747, K1 de4006636) (STATE line FIBRE RING).
- Filtered colimits of rings: `{I : Type u} [SmallCategory I] [IsFiltered I]`, `F : I ⥤ CommRingCat`, `[HasColimit F]`, `colimit F`, `colimit.ι` (K1 ccd06d885, H1 e6c93b368, J1 8231d9091, F1 6ebcba30e); directed systems keep the DIRECTED SETS line (STATE line FILTERED COLIMITS OF RINGS).
- f unramified at x is `∃ U : X.Opens, x ∈ U ∧ LocallyOfFiniteType (U.ι ≫ f) ∧ IsOpenImmersion (pullback.diagonal (U.ι ≫ f))` (recorded def-weil-unramified-morphism match; E1 c97916d2e) (STATE line UNRAMIFIED AT A POINT).
- Geometric fibre: the scheme X ×_Y Spec Ω along ȳ is `Limits.pullback f ȳ` and its cardinality is the number of points of that scheme (J1 024846f33); def-weil-pbc-geometric-fibre (`Scheme.Hom.GeometricFiber`, the set of Ω-lifts) is a different object — cite the one the node's stmt_dep names (STATE line GEOMETRIC FIBRE).
- Étale sheaves: global sections at `op (Scheme.Etale.mk (𝟙 X))` (H1 f92914c51, J1 33fd4728f, F1 14053efbd); a clopen/coproduct cover as `(ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι))` (E1 5d9bb8370) unless the node names Mathlib's chosen `∐` (STATE line ÉTALE SHEAF SECTIONS AND COVERS).
- Never build an `Abelian` instance on `SheafOfModules` from `(moduleSheaves_abelian_enoughInjectives X).1.some` (or any `Nonempty.some`): use Mathlib's `SheafOfModules.instAbelian` and a `[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]` binder as the landed modules do (M1 5399578d1 fix); a chosen instance makes a second D(O_X).
- General-site restriction of module sheaves to U is `SheafOfModules.overFunctor` on `J.over U`; cite H1's `CategoryTheory.module_overFunctor_preservesZero` (lem-pur-rhom-into-kinjective-local, 38d166329) for zero preservation, never restate; ringed-space `moduleOverFunctor_*` instances are separate (STATE line GENERAL-SITE RESTRICTION).
- Cohen–Macaulay: no Mathlib declaration; state CM local rings inline exactly as `Ideal.mem_minimalPrimes_of_depth_ge` (lem-weil-pbc-cm-local-associated-prime-minimal, e10ccd492): `ringKrullDim T = (e : WithBot ℕ∞)` and `(e : ℕ∞) ≤ IsLocalRing.depth (R := T) T`; maximal CM modules analogously; no private CM definition (STATE line COHEN–MACAULAY).
- π₁ via abstract models `G : Type u` with `[IsFundamentalGroup (fiber s) G]` as `fundamentalGroupMap` requires (lem-galois-pi1-finite-etale-image-stabilizer, 7d4a5b1c8), identified with `Aut F` via `CategoryTheory.PreGaloisCategory.toAutContinuousMulEquiv`; not literally `Aut (fiber s)` (STATE line FUNDAMENTAL GROUP).
- Module-pullback unit: the unit of `Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)` (lem-pc-module-pullback-adjunction); `Classical.choice (nonempty_tensorPullbackAdjunction g)` (C1, M1, H1 landed) is the older form, bridged in stage 3, not restated; new statements use `exists_tensorPullbackAdjunction` (STATE line TENSOR-PULLBACK UNIT).
- Étale: morphism of schemes `AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom φ))` (def-weil-etale-morphism) or ring map `Algebra.Etale`/`RingHom.Etale`, as the node speaks; both acceptable, no conversion; bridge `HasRingHomProperty @Etale RingHom.Etale` (STATE line ÉTALE RING MAPS).
- Directed set (Stacks 00D3): `[Preorder I] [IsDirected I (· ≤ ·)]`; landed `[PartialOrder I]` modules are not rewritten (STATE line DIRECTED SETS).

## 4. Compiling

You have no compiled Lean. Compile on the server:
`ssh <server> 'cd ~/weil-conjectures-sheaf && tools/compile_remote.sh <G> <item>' < <file>.lean`
(120 s limit; prints the errors; compiled against the last green global build plus your group's landed modules). Compile until the file is clean: no error, no warning (fix unused variables). A declaration you can read in `lean/` but that does not compile for you has landed since the last green build: wait, do not write it again. A timeout is a fault of a definition, not of the limit.

## 5. The node records

The delivery changes the item's node file ONLY in the field `lean` (and in `stmt_deps`, only by adding the new definition nodes of (A) or a node that already exists on sheaf-dag with a `lean` record, e.g. a notion another group landed meanwhile that a return asks you to cite: STMT_DEPS MAY GAIN LANDED NODES, `coord/STATE.md`):

```
"lean": {"module": "Sheaf.<Topic>.<Name>", "declaration": "<full name>",
         "declarations": [...] (optional, when several), "file": "lean/Sheaf/<Topic>/<Name>.lean" (absent when existing),
         "statement": "<signature verbatim from the file, from the keyword to := or where>",
         "branch": "sheaf-dag" | "mathlib" | "slopmaster2", "by": "<G>", "date": "<date -u>", "existing": true|false,
         "note": "<free text>" (optional)}
```

`status` stays `split`; keep the JSON layout (`indent=1`, `ensure_ascii=False`, final newline).

**A corrected item (C)** changes also in `statement`, and only as far as the correction forces it in `stmt_deps`, `proof`, `proof_deps`, and gains

```
"statement_change": {"date": "<date -u, YYYY-MM-DD>", "by": "<G> stage 2",
  "old_statement": "<the old TeX, verbatim>",
  "what": "<what was wrong: the counterexample, or what could not be typed and why>",
  "source": {"document": "...", "place": "..."} <the source place the correction follows>,
  "citers": [{"id": "<node>", "holds": true|false, "note": "<one line: does its use of the item still hold>"}, ...],
  "old_stmt_deps": [...], "old_proof": [...], "old_proof_deps": [...]   <each present exactly when that field changed, verbatim from the base>,
  "previous": {...}   <exactly when the node already had a statement_change: the old record, whole>}
```

`citers` names exactly the nodes on `sheaf-dag` whose `stmt_deps` or `proof_deps` contain the item (`grep -rl '"<item>"' dag/nodes`, then keep those). The corrected statement cites every `[id]` it names in `stmt_deps`. Nothing else of the item changes (`status`, `source`, `kind` stay). The preflight checks every key (`tools/node_fields.py check_statement_change`).

**A dependency node of (B)** changes ONLY in `lean`: the record above for its module (`existing: false`, `by` = your group), with `note` required (why the recorded declaration or `mathlib_match` was unusable, what the module states). Its `mathlib_match` and every other field stay.

**A new definition node of (A)** is written whole, with exactly these fields (the preflight checks each):

- `id` = file name, `def-<chapter prefix>-<short-name>`, not existing on `sheaf-dag`; the file in the item's chapter directory;
- `kind`: `"definition"`; `title`; `status`: `"split"`;
- `statement`: self-contained TeX introducing its own objects and citing as `[id]` the definition node of every notion it is built from; `stmt_deps`: exactly the cited ids (existing nodes or other new nodes of the delivery);
- `source`: `{document, place}` (the Stacks tag and label, or the document in `literature/`);
- `proof`: `[]`, `proof_deps`: `[]`, `proof_origin`: `null`; `mathlib_match`: `null`;
- `mathlib_searches`: at least the three kinds (LeanSearch; Loogle or LeanFinder; grep of Mathlib, of the source repository and of `lean/Sheaf`), each `{tool, query, results, date, verdict}`;
- `created`: `{by: "worker", item: <the item>, date, group: <G>}`;
- `blueprint`: `{is: null, from: {node: <python3 tools/blueprint_refs.py ancestor <item>>, place: <the place in that blueprint proof the notion serves>, via: <the item's via with the item in front>}, same_as: [...]}`;
- `lean_audit`: `{"master": {"state": "none"}, "slopmaster2": {"state": "none"}}`; `chapter`, `unit`: the item's;
- `lean`: the record above for its module (`existing: false`), or an existing declaration (`existing: true`, no module); a declaration already landed in `lean/Sheaf` by another node is recorded with `existing: true`, `branch: "sheaf-dag"`, `module: Sheaf.<…>` (§1), also for a dependency node of (B).

No other field (`reviewed`, `reviewed_lean`, notes): the merge sets `reviewed` and `reviewed_lean`. The new node must be cited by the item (its `stmt_deps`), directly or through another new node.

## 6. Delivering

One commit on top of `sheaf-dag` with: the item's module and node file; for each new definition node (A) its node file and its module (none when `existing: true`); for each dependency module (B) the dependency node file and the module; the report `coord/reports/<G>/<item>.md` (for an item with `existing: true` and nothing else, only the node and the report). Every module is the `lean.file` of exactly one of these nodes, and its declarations carry `(blueprint: <that node's id>)`. The report has:

- `## Worker report`: what the module defines or states; for each hypothesis and each clause of the node's statement, the Lean that renders it; the dependency declarations used (module, name); the edge cases checked; the searches for an existing definition (tool, query, result); `STATEMENT-DISPUTED:` or node faults, if any.
- `## Second reading by <G>`: an independent reading by another worker of the group, with the node and the file open, answering above all: does the Lean say exactly what the node says? Name each mismatch found and what changed. It reads the new nodes and dependency modules too.
- `## New nodes` (when there are new nodes): one paragraph per new node, naming its id: its statement, its source, its searches and why it is not an existing node or declaration.
- `## Dependency modules` (when there are dependency modules): one paragraph per dependency node, naming its id: why its record was unusable, what the module states.
- `## Statement corrected` (when the item is corrected, (C)): the old statement, what was wrong, the source place the correction follows, and one line per citer naming its id (holds or not, why): the content of `statement_change`.

Before pushing: `python3 tools/preflight_delivery.py <G> <item> --stage 2` (shape, records, the new nodes' fields, the `statement_change` of a corrected item, docstrings, line width, sorry-only proofs) until it passes; for a corrected item it prints `item corrected: <n> citers, <k> marked holds:false` (n must be the number of citers you found), and a clean compile on the server of each module. A module that imports another module of the same delivery cannot compile on the server before that one has landed (the preflight and the packet print `compile: deferred`; the merge lands the modules in dependency order): compile it as one temporary file, the sibling's body followed by the module's body without the sibling import, under a scratch name (`tools/compile_remote.sh <G> <item>-check`). Push to `deliver/<G>/<item>` as in stage 1 (`coord/delivery-errors.md` A1: one commit, based on `sheaf-dag`, never on another delivery). The lead's reviewer checks the statements against the nodes, reads each new node against its source, compiles and lands the modules with `tools/land.sh`; returns go to `coord/returns/<G>.md`, and are repaired point by point (section G of that file).

merge_delivery.py, land.sh and landing.py take coord/.merge.lock themselves and are NEVER wrapped in `flock`; `flock coord/.merge.lock -c …` is only for a plain git add/commit.
