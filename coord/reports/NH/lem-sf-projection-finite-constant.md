## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula` states
`AlgebraicGeometry.Etale.isIso_finiteConstantProjectionMap`, with its entire proof `sorry`.
It also constructs the concrete helper natural transformation
`AlgebraicGeometry.Etale.finiteConstantProjectionMap`; it contains no postponed proof or
chosen arbitrary map. There are no new nodes, dependency repairs, or statement corrections.

Hypothesis and conclusion correspondence:

- The scheme morphism is `{X Y : Scheme.{u}} (f : X ⟶ Y)`; no geometric hypothesis on it
  is added. In particular neither properness nor finite type is assumed.
- The Noetherian commutative coefficient ring is `(A : Type (u + 1)) [CommRing A]
  [IsNoetherianRing A]`. This is the existing coefficient-size convention, allowing every
  coefficient ring after choosing an ambient universe; the site and coefficient category
  are exactly the recorded unbounded etale module-category encoding.
- One nonnegative integer bound is `(N : ℕ)`. The hypothesis `hcd` quantifies over every
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` and every `q : ℕ` with `N < q`.
  It asserts `IsZero` of degree `(q : ℤ)` cohomology of the K-injective total direct image
  of `F[0]`, which is precisely the sheaf `R^q f_* F`. Using naturals loses no degree
  because every integer greater than the nonnegative N is positive.
- `K : DerivedCategoryModule A X` is an object of the UNBOUNDED derived category;
  `hK : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (H^q K)` says exactly `K ∈ D^-`.
  No lower bound, Tor-amplitude bound, or constructibility condition is imposed.
- `M : ModuleCat.{u + 1} A` with `[Module.FinitePresentation A M]` is the finitely
  presented module. Its underlying type is the bundled module coerced to a sort.
- The source of `finiteConstantProjectionMap A f K` at M is the ordinary derived tensor
  of `Rf_*K` with `((constantSheaf Y.smallEtaleTopology (ModuleCat A)).obj M)[0]`.
  Its target is `Rf_*(K ⊗^L ((constantSheaf X.smallEtaleTopology (ModuleCat A)).obj M)[0])`.
  Thus both constant sheaves in the displayed node conclusion occur literally in the
  transformation's type, not merely as unspecified isomorphic objects.
- The helper is formed from the RECORDED `rightDerivedLowerStarProjectionMap`, followed
  by `singleFunctorCompLeftDerivedUpperStarIso` and `Scheme.upperStarConstantSheafIso`.
  These are the canonical pullback identifications in the source's first paragraph.
  No inverse of a hoped-for projection isomorphism is used in defining it.
- The conclusion `IsIso ((finiteConstantProjectionMap A f K).app M)` is exactly the
  assertion about the canonical map. Naturality in M is part of the helper's `⟶` type
  in a functor category on ALL A-modules: its `naturality` field is constructed by
  whiskering and composing the existing natural transformations and is not assumed.
  Restriction to finitely presented modules therefore retains the requested naturality.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (available through the framework imports).
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-pbc-derived-categories`: `AlgebraicGeometry.Etale.DerivedCategoryModule`,
  via the recorded `Sheaf.AlgebraicGeometry.DerivedCategories` and upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`;
  `_root_.DerivedCategory.homologyFunctor` and `singleFunctor` use the same category.
- `def-sc-finitely-presented-module`: its Mathlib match `Module.FinitePresentation`,
  `Mathlib.Algebra.Module.FinitePresentation`. It is the finite generating presentation
  with finitely generated kernel, equivalent to the node's finite free presentation.
- `def-kun-constant-sheaf`: the dependency explicitly records the specialization of
  `CategoryTheory.Functor.mapHomologicalComplex` to `constantSheaf`; here only a module
  in degree zero is needed, so `constantSheaf ⋙ DerivedCategory.singleFunctor _ 0` is
  exactly that construction on `M[0]`. `constantSheaf` is sheafification of the constant
  presheaf in `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `def-kun-derived-tensor`: `AlgebraicGeometry.Etale.derivedTensor`,
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, reexported by LowerStarProjection.
- `def-kun-projection-formula-map`: `rightDerivedLowerStarProjectionMap`,
  `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`, with its full signature
  and adjunction-mate equation read. The direct image is the same generic
  `Functor.rightDerivedFunctor` applied to `Etale.lowerStar`, with no alternate definition.
- Canonical target identifications: `singleFunctorCompLeftDerivedUpperStarIso`,
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`, and
  `Scheme.upperStarConstantSheafIso`, `WeilConjectures.ConstructibleSheaf.Defs`.
  The latter is uniqueness of left adjoints to global sections of direct image.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat` supplies the existing
  `upperStarPreservesFlat_moduleCat`, with no added flatness hypothesis on M.

Every recorded proof-dependency module is imported without `public` when it is not
already a statement import. The sole unrecorded proof dependency
`lem-sf-finite-cd-derived-upper-bound` has no Lean module yet and is not imported; it
is named with its Stacks 07K7 argument in the complete proof docstring. It is not
needed to type this theorem. The proof docstring gives all six DAG steps, including
finite free syzygies, the cone at m=0, the unbounded upper-bound input, the tensor
support estimate, and the degreewise naturality-square comparison.

Edge cases checked before writing: M=0, K=0, the zero coefficient ring (no Nontrivial
assumption), either scheme empty, f the identity, N=0, arbitrary negative upper bound b,
and the nonterminating finite free resolution. No argument assumes finite projective
dimension of M. At m=0 the cone can have H^{-1} but not H^0, as the docstring says.
The site object and morphism universes are not identified; the existing framework's
Scheme.{u}, ModuleCat.{u+1} convention is retained. All universes and variables are explicit.

Searches for an existing statement (actual tool outputs are in searches.jsonl):

- `msearch.py leanfinder`: “Derived projection formula with finitely presented constant
  module over Noetherian ring for bounded above complex and finite cohomological dimension”.
  Eight hits, concerning K-projective complexes and ordinary left-derived/Tor functors;
  no etale finite-cd projection formula.
- `msearch.py loogle`: `Module.FinitePresentation`. Twelve hits, confirming the existing
  finiteness predicate and its Noetherian equivalence to finite generation.
- `msearch.py grep`: `projectionFormula|projection.formula`. Three irrelevant Mathlib
  hits (Witt vectors and a manifold comment); no match.
- `msearch.py leansearch`: “Projection formula with a finitely presented constant module
  and finite cohomological dimension”. Service returned Internal Server Error; the
  unavailable search was supplemented by the successful LeanFinder, Loogle and grep.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for projection/finite and
  constant-pullback names found the recorded canonical map and existing proper/torsion
  projection formulas. Their hypotheses and coefficient objects differ from this node;
  in particular `EtaleConstantProjectionFormula` concerns global sections with a torsion
  ring, while `ProperProjectionFormula` assumes properness and finite coefficients.
- `grep -rn lem-sf-projection-finite-constant WeilConjectures` returned no upstream match.
  The exact new declaration names were searched in upstream and side sources: no collision.

Source read: the archived blueprint lemma (same relative path as node.source, under the
available work-bp/sheaf literature archive), all six proof paragraphs in the DAG, all
statement-dependency records, and the full signatures/docstrings of the declarations above.
No mathematical fault or STATEMENT-DISPUTED issue was found. The node is changed only in lean.

### Repair of the independent immutable-head compile timeout

The returned head timed out at the default 60-second limit in the local
`Sheaf.Stage2.Sandbox0` check. I reproduced that failure with the original module.
An import-only file compiled successfully. A diagnostic scratch file with a reduced
heartbeat limit and profiling showed that the original definition elaborated in
under one second but spent most of its time in kernel type checking. Neither
increasing the timeout nor dropping proof-dependency imports was used.

The repair changes only the body of `finiteConstantProjectionMap`. It names the
existing coefficient, single-degree, tensor, and derived-image functors locally
inside the definition, gives the three natural transformations explicit types,
and inserts Mathlib's `Functor.associator` maps between their composites.
The associators have identity components. Thus the component at every module is
the same canonical projection map followed by the same two canonical constant
pullback identifications. The natural transformation's signature, the theorem's
signature, all hypotheses, all imports, and the sole `sorry` are unchanged.
There is no new notion, new theorem, proof, node, or statement correction.

Validation: `scompile.py NH lem-sf-projection-finite-constant` on the final
`FiniteConstantProjectionFormula.lean` returned exit 0 with no warnings, entirely
locally: sandbox check 20.6 seconds, library-path check 18.5 seconds. Both retained
the unchanged 60-second per-invocation limit. No server fallback was needed.
The helper and theorem signatures are verbatim unchanged, every line is at most
100 characters, and the only `sorry` is the original theorem's proof.
The required `deliver2.py NH lem-sf-projection-finite-constant --no-push`
returned exit 0: “OK (dry run): commit 3426350330 passes the preflight and compiles;
nothing pushed”. Only this module, the item's node record, and this report were
staged. The earlier second-reading section is retained as the historical reading
of the returned version; the dispatched second reader must review this body
repair before delivery.

## Earlier second reading (a previous round; superseded)

I opened the node record, its source-place description, the complete Lean module, and
the recorded declarations of every statement dependency. The item-by-item match is:

- The node's scheme morphism `f : X → Y` is rendered by `{X Y : Scheme.{u}}`
  and `(f : X ⟶ Y)`. No properness, separatedness, finite-type, or nonempty-scheme
  hypothesis is added.
- The Noetherian commutative ring is `(A : Type (u + 1)) [CommRing A]
  [IsNoetherianRing A]`. The universe is the recorded module-sheaf convention and
  introduces no extra characteristic or nontriviality assumption.
- The one bound `N ≥ 0` is `(N : ℕ)`. The hypothesis `hcd` quantifies over every
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)` and every natural `q` with
  `N < q`, and renders `R^q f_* F = 0` as `IsZero` of the corresponding
  `homologyFunctor` applied to the K-injective `rightDerivedFunctor` of `lowerStar`.
  This is exactly the node's uniform all-sheaf cohomological-dimension bound.
- The unbounded derived object is `K : DerivedCategoryModule A X`. The binder
  `hK : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (H^q K)` is precisely the stated `D^-`
  condition, with no lower bound or Tor-amplitude condition.
- The coefficient object is `M : ModuleCat.{u + 1} A` with
  `[Module.FinitePresentation A M]`, matching the finitely presented module in the
  node. The zero module and zero ring remain permitted.
- `finiteConstantProjectionMap A f K` is a natural transformation whose value at
  `M` has source `Rf_*K ⊗ᴸ M_Y` and target `Rf_*(K ⊗ᴸ M_X)`: the displayed
  `constantSheaf` functors, degree-zero `singleFunctor`, `derivedTensor`, and
  `rightDerivedFunctor` make both associated constant sheaves explicit. Its first
  component is the recorded `rightDerivedLowerStarProjectionMap`; the two following
  components are the canonical single-degree derived inverse-image and
  `upperStarConstantSheafIso` identifications. Thus it is the canonical map named by
  the node, rather than an arbitrary isomorphic replacement.
- The conclusion is `IsIso ((finiteConstantProjectionMap A f K).app M)`. Since the
  helper is a natural transformation in the full module category, the required
  naturality in `M` is retained while the theorem adds only the finite-presentation
  instance at the chosen object.

I found no mismatch and made no mathematical or Lean change. In particular, the
empty schemes, identity morphism, `M = 0`, `K = 0`, `N = 0`, arbitrary negative upper
bound `b`, and a zero coefficient ring are all admitted by the binders; no finite
resolution length is assumed. The site and coefficient universes are kept distinct
as required by the module-category encoding.

For the duplicate-definition check I reran the recorded LeanSearch, LeanFinder,
Loogle, and grep searches in `searches.jsonl`, and searched both the upstream
`WeilConjectures` tree and project `lean/Sheaf` for projection-formula, finite,
constant-sheaf, and the exact declaration names. The only relevant existing notions
are the recorded generic derived tensor, projection map, constant sheaf, and derived
category declarations used by the module; no existing theorem states this bounded
above finitely-presented constant-coefficient result. The finite-presentation
dependency is exactly Mathlib's `Module.FinitePresentation`, so no private copy was
introduced. No dependency record is unusable and no statement correction or citer
audit is required.

## Second reading by NH

This is a fresh independent reading of the repaired body, not an adoption of the
superseded reading above. I opened the sandbox node, the complete module, every
statement-dependency record, and the actual definitions/signatures they record.
I read the archived source lemma and its containing section in
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/sec-six-functors/`.
The lemma explicitly introduces arbitrary schemes and a Noetherian coefficient
ring; the containing exceptional-inverse-image proposition's finite-type and
finite-coefficient setting is not a hypothesis of this separately stated lemma.
I also read Stacks `sites-cohomology.tex`, equation 0B56 and lemma 0944, and
`derived.tex`, lemma 07K7, including (4)(c). These impose no further geometric
hypothesis on the map in this lemma. The perfect-complex assumption in 0944 is
used only for the bounded finite free case in the proof, not for the final M.

The node's objects, hypotheses and conclusion clauses, matched individually:

1. Schemes X,Y and their morphism f: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
   Verdict: exact. Mathlib's `Scheme` and `Scheme.Hom` give the recorded objects;
   no properness, separation, finite-type or field hypothesis appears.
2. A Noetherian commutative ring A: `(A : Type (u + 1)) [CommRing A]
   [IsNoetherianRing A]`. Verdict: exact. The recorded Noetherian predicate is
   `IsNoetherian A A`, meaning every ideal is finitely generated. There is no
   nontriviality, characteristic, torsion, or finite-ring condition.
3. One nonnegative integer N and a uniform vanishing bound for all sheaves:
   `(N : ℕ)` and `hcd : ∀ (F : Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} A)) (q : ℕ), N < q → IsZero (...)`.
   The expression inside IsZero is H^q of the unbounded right-derived lowerStar
   on `singleFunctor _ 0` applied to F. Verdict: exactly R^q f_* F = 0.
   N precedes the universal F,q. Natural indices omit no integer q>N since N≥0.
4. The unbounded derived category on the small etale site:
   `(K : DerivedCategoryModule A X)`. Verdict: exact. I opened
   `Sheaf.AlgebraicGeometry.DerivedCategories` and upstream `Derived.Coefficients`;
   the abbreviation is literally `DerivedCategory (Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} A))`, not a bounded category or another site.
5. K belongs to D^-: `hK : ∃ b : ℤ, ∀ q : ℤ, b < q →
   IsZero ((DerivedCategory.homologyFunctor _ q).obj K)`.
   Verdict: exact vanishing in all sufficiently large degrees; no lower bound,
   strict term bound, constructibility or finite Tor amplitude is required.
6. A finitely presented A-module M: `(M : ModuleCat.{u + 1} A)
   [Module.FinitePresentation A M]`. Verdict: exact. I read Mathlib's class and
   `exists_fin`: a finite generating presentation has finitely generated kernel,
   equivalently the finite free presentation in the dependency node.
7. M_X and M_Y are the associated constant sheaves placed in degree zero:
   `constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
   DerivedCategory.singleFunctor _ 0`, and the corresponding expression on Y.
   Verdict: exact. Mathlib's constantSheaf is constant presheaf followed by
   sheafification; on M[0] this is the specialization of the recorded termwise
   `Functor.mapHomologicalComplex`, with no new constant-sheaf notion.
8. The source is Rf_*K tensor^L M_Y, the target is Rf_*(K tensor^L M_X):
   these are the source and target functors of `finiteConstantProjectionMap`.
   Verdict: exact. I read upstream `Derived.Tensor` and `Derived.LowerStarProjection`;
   these are the recorded ordinary uncompleted unbounded tensor and K-injective
   right-derived direct image, not a completed tensor or f_!.
9. The map is the canonical adjunction mate: the body's π is
   `Functor.whiskerLeft (C_Y ⋙ S_Y)
   ((rightDerivedLowerStarProjectionMap (ModuleCat A) f).app K)`.
   Its α is the hom of `singleFunctorCompLeftDerivedUpperStarIso`, and β is
   `Scheme.upperStarConstantSheafIso` whiskered by S_X. Verdict: exact. I read
   the projection-map definition and its explicit adjunction-mate equation,
   the single-degree comparison, and the constant-sheaf comparison defined by
   uniqueness of left adjoints. No unspecified map or chosen isomorphism occurs.
10. The conclusion is invertibility of that map:
    `IsIso ((finiteConstantProjectionMap A f K).app M)`. Verdict: exact.
11. Naturality in M: `finiteConstantProjectionMap` has natural-transformation
    type on the category of all A-modules. Verdict: included constructively,
    hence also for every morphism between finitely presented modules; naturality
    is not an additional assumption.

I checked the timeout repair itself by following each intermediate type. Write
C_Y,C_X for the constant functors, S_Y,S_X for degree-zero inclusion, L for derived
pullback, R for derived direct image and T_X,T_Y for tensoring with K,RK.
After π, the successive reassociations change
`(C_Y ⋙ S_Y) ⋙ L ⋙ (T_X ⋙ R)` to
`(C_Y ⋙ (S_Y ⋙ L)) ⋙ (T_X ⋙ R)`; whiskering α then replaces S_Y⋙L by
upperStar⋙S_X. The final reassociation allows β to replace C_Y⋙upperStar by C_X.
I opened `Mathlib.CategoryTheory.Functor.Category`: both hom and inv components
of `Functor.associator` are identities. Their images under whiskering are
identities too. Thus the repaired body has exactly the original canonical
component followed by the two prescribed comparisons. Its local lets are
inside a definition body, not in either declaration's statement. There is no
new theorem, hidden sorry, or private copy of any dependency notion.

Edge cases: N=0 is admitted and requires precisely positive-degree vanishing;
M=0 and K=0 are admitted; the zero coefficient ring is admitted. Either scheme
may be empty, and f may be the identity. Negative upper bounds b are quantified
over all integers. Empty finite free sums in the proof include rank zero.
There is no arbitrary index-set binder in the statement and no assumed finite
resolution length. The site object and morphism universes are not equated;
the Scheme.{u}/ModuleCat.{u+1} convention is exactly the recorded dependency
encoding and allows arbitrary coefficient size after increasing the ambient
universe. All variables and the single universe u are explicitly bound.

Independent duplicate searches (recorded by msearch in searches.jsonl):

- LeanFinder: “When does derived pushforward commute with tensoring by a finite
  constant module for a bounded above etale complex?” Eight hits: Tor and
  Kaehler differential declarations, none this statement.
- Loogle: `CategoryTheory.Functor.associator`. Twelve hits, confirming the
  existing associator and identity-component API used in the repair. An earlier
  notation query `IsIso (_ ≫ _)` was rejected by the service parser and provides
  no mathematical evidence.
- LeanSearch: “Derived projection formula for constant coefficients and finite
  cohomological dimension”. Unavailable: Internal Server Error. I do not count
  that as a negative search result; LeanFinder, Loogle and source searches were
  available.
- Direct rg on Mathlib for projection-formula and the new names found only
  unrelated Witt-vector/manifold uses. Source/project searches used projection,
  finite, constant, and the exact new names. I opened the relevant existing
  `EtaleConstantProjectionMap` and `EtaleConstantProjectionFormula`: they concern
  RΓ with a qcqs/torsion-coefficient theorem, not this arbitrary morphism and
  Noetherian coefficient theorem. The upstream integral/finite projection
  formulas use compactifications or completed/finite coefficients and f_!.
  The generic `rightDerivedLowerStarProjectionMap` is correctly reused.
  Neither new name occurs in upstream declarations, project modules, or
  `dag/lean_names_upstream.json`.

Docstrings give the blueprint source and id for both declarations. The theorem's
six-step proof plan matches the node, including the m=0 cone case, the unbounded
07K7 upper-bound input and the degreewise naturality square. Exactly one sorry
occurs, as the entire theorem proof. The helper's data are constructed from
existing maps. All delivered Lean lines are at most 100 characters. A direct
comparison confirms lean.statement equals the theorem signature verbatim.
Only lean differs between the sandbox and base node; no statement correction,
new node, dependency module, or citer audit is needed. The proof-only
lem-sf-finite-cd-derived-upper-bound still has no recorded module and does not
enter the statement's type; its omission from imports remains justified.

Mismatches found: none. Changes made by this second reader: this report section
only; the Lean and node record were retained unchanged after checking the
repaired helper body.

Fresh validation by this second reader: scompile.py completed with exit 0 and no
warnings. Sandbox compilation took 23.5 seconds and library-path compilation
8.3 seconds, both with the default 60-second limit. Every delivered module
(the sole FiniteConstantProjectionFormula.lean) was compiled separately.
