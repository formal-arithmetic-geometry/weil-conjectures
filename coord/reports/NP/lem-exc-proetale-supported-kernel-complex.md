## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleSupportedKernelComplex` states
`AlgebraicGeometry.ProEtale.finiteSupportedKernelComplex_shortExact`. Its only theorem proof
is `sorry`. The module constructs the kernel functor F, its inclusion, H = i*F, their
termwise complex functors, and the actual termwise open unit. All definition data is real.
The finite-ring adjunction is supplied by the dependency repair described below; its one
existence-and-uniqueness theorem also has proof `sorry`.

The node's statement and proof were read together with the current blueprint
`main-20261015/.../sk-prop-sf-localization/lem-exc-proetale-support-triangle.md` and its
separate `.proof.md`, the older source named in the node, and Stacks
`sites-modules.tex`, lemma-adjoint-push-pull-modules, lines 1043–1098.
No mathematical statement correction is needed.

Clause-by-clause rendering:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| T Noetherian | `[IsLocallyNoetherian T] [CompactSpace T]` |
| closed immersion i | `(i : Z ⟶ T) [IsClosedImmersion i]` |
| quasi-compact open immersion j | `(j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]` |
| j is the complement of i | `hU : Set.range j = (Set.range i)ᶜ` |
| finite ring A, possibly noncommutative | `A : Type (u + 1)`, `[Ring A] [Finite A]` |
| discrete topology | `[TopologicalSpace A] [DiscreteTopology A]` |
| left modules over the specified coefficient sheaves | existing `FiniteCoefficientModules T A`, and the same category on U and Z |
| actual inverse images and units | existing `finiteCoefficientModulePullback` and the normalized `finiteModuleAdjunction` of the dependency repair |
| n is the positive additive order of 1, B = Z/n | `ZMod (addOrderOf (1 : A))`; positivity follows from finite A, and the zero ring gives n = 1 |
| assumed commutative essential-image and unit criterion | `hB`, for every module N over the canonical constant-ring presentation of B: the essential-image iff and the actual closed-unit `IsIso` clause |
| supported N has invertible actual A-linear closed unit | first conjunct, quantified over all `N : FiniteCoefficientModules T A` with `IsZero` open pullback |
| naturality in N | the map is the component of the fixed adjunction's natural unit, not an existential isomorphism |
| open restriction of i_*M vanishes for all M | second conjunct, using `finiteModulePushforward i A` and the recorded open pullback |
| every termwise open unit of I is epic | `finiteOpenEpicComplex j A`; its full subcategory retains every chain map between complexes satisfying this hypothesis |
| F^q is the kernel of the specified unit | `finiteSupportedKernel.obj N := kernel ((finiteModuleAdjunction j A).unit.app N)` |
| restricted differentials | `kernel.map`, applied by `Functor.mapHomologicalComplex` to each differential; the kernel-square equality is exactly unit naturality |
| H(N) = i*ker(unit N) | `finiteSupportedH i j A := finiteSupportedKernel j A ⋙ finiteCoefficientModulePullback i A` |
| closed units assemble into a complex isomorphism | natural isomorphism e between the two complex functors, restricted to the stated epic-unit hypothesis; `∀ I q`, its degree-q map equals exactly the closed unit on F^q |
| first arrow is inverse closed unit followed by kernel inclusion | `e.inv ≫ Functor.whiskerLeft ... (finiteSupportedKernelComplexInclusion j A)` |
| second arrow is the actual open unit | `finiteOpenComplexUnit j A`, prolonged from the specified adjunction unit, with the canonical identity-complex comparison |
| these arrows form a sequence | witness w states that their composite natural transformation is zero |
| short exact sequence of complexes | evaluation of the natural `ShortComplex` at each admitted I is `.ShortExact` |
| short exact in every integer degree | the final conjunct uses `.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) q)` and `.ShortExact`, for every integer q |
| naturality of the entire sequence | both arrows are natural transformations on the full category of admitted complexes; this includes arbitrary chain maps, not only isomorphisms |

The coefficient presentation in hB is explicit. `ULift.{u} (ZMod n)` is a universe lift of B,
not another ring. `Scheme.proEtaleConstantRing` is the constant-sheaf presentation of the
same commutative coefficient sheaf. The existing constant-preserving coefficient
comparisons `finiteCoefficientConstantComparison_isIso`,
`finiteCoefficientInverseImageMap_constant`, and `finiteCoefficientModulePullback_tensor`
identify this presentation with the continuous-function presentation, including its
canonical coefficient maps. The commutative adjunction is the tensor-unit-normalized
`proEtaleConstantRingAdjunction`, exactly the closed-essential-image dependency's
adjunction specialized to these coefficient sheaves. Thus hB is the input the node
assumes, expressed in the dependency's usable commutative coefficient convention.
No arbitrary ring identification or extra coefficient hypothesis is introduced. The
central map B → A is the unique unital residue map r ↦ r1; it is needed in the proof,
not an additional datum quantified by the statement.

Dependency declarations used, with their owning modules:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` supplies `QuasiCompact j`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules` and
  `finiteCoefficientRingSheaf` use the existing continuous-function coefficient sheaves.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, unfolded by
  the coefficient category. This is Mathlib's `SheafOfModules` with its abelian structure.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`: `finiteCoefficientModulePullback`,
  its additive instance and exactness theorem; the existing module is reexported by the
  dependency repair. The definition is used unchanged, including its transported action.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`: `finiteCoefficientDirectImageMap`,
  `finiteCoefficientInverseImageMap` and its isomorphism theorem, via the existing exact
  pullback. These determine the scalar map in both adjoint functors.
- `Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage`:
  `Scheme.proEtaleRingModule_closed_essImage_iff_and_unit_isIso`. hB is exactly its two
  conclusions for B; the theorem is assumed here as requested, rather than omitted.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingPullback`, `...Pushforward`, and `...Adjunction`, which
  specialize the recorded commutative ringed-site operations used by that dependency.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction`: the repaired
  inverse-image dependency, `finiteModulePushforward` and `finiteModuleAdjunction`.
  It reexports the previously recorded `SfIntrinsicRealizationTransport` module and
  all earlier inverse-image constructions, so no old declaration is deleted.
- `Mathlib.Algebra.Homology.HomologicalComplexAbelian`:
  `HomologicalComplex.shortExact_iff_degreewise_shortExact` and the complex abelian
  instance. `ShortComplex.ShortExact.gIsCokernel` supplies the dependency's cokernel
  interpretation; `.ShortExact` is the existing Mathlib predicate.
- Proof imports include `Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation`
  (`Scheme.proEtaleOpenUnitEvaluation`) and Mathlib's module `ChangeOfRings`
  (`SheafOfModules.restrictScalars`). The scalar-unit-comparison proof node has no
  recorded Lean module at this read; its mathematical use is recorded in the theorem
  docstring, and no fictitious import or prerequisite hypothesis is inserted.

Edge cases were checked before choosing the binders. The zero coefficient ring is allowed:
1 has additive order 1 and B = ZMod 1, so no `[Nontrivial A]` or positive-characteristic
hypothesis is added. Empty T, U, or Z are allowed; their coefficient sheaves are sheafified
and have the correct singleton sections on empty objects. If U is empty the open unit
has zero target and the kernel is the original complex. If Z is empty the kernel is zero
and the open unit is invertible. The zero complex and unbounded complexes are admitted.
Every q ranges over all integers. There is no injectivity, boundedness, constructibility,
flatness, or commutativity assumption on A or I. The site object universe remains u+1,
its morphism universe u, and the coefficient/module universe u+1.

Searches actually performed:

- `msearch.py leanfinder`, query “For a finite noncommutative coefficient ring the kernel
  of open restriction on proetale sheaves is canonically the closed direct image of its
  closed restriction and gives a natural short exact sequence of complexes”: eight hits,
  including `Profinite.NobelingProof.succ_exact`, `Scheme.kerFunctor`, Mayer–Vietoris
  exactness, and cotangent exactness; none states this lemma.
- `msearch.py leansearch`, query “The kernel of the open restriction unit for a sheaf of
  modules is supported on the closed complement”: eight hits, mainly Zariski
  `Scheme.Modules.restrict*` and `ModuleCat.Tilde.toOpen`; no pro-etale finite-ring match.
- `msearch.py loogle`, query `"kernel", "map"`: twelve hits, including `kernel.map`,
  `kernel.mapIso`, and their cokernel counterparts. The draft uses `kernel.map`.
- `msearch.py grep`, pattern `supportedKernel|kernelComplex|finiteCoefficient.*Adjunction`,
  in Mathlib CategoryTheory: no hits. The broader Mathlib grep
  `sectionsWithSupport|supportedKernel|finiteModuleAdjunction|supported.*kernel` also
  returned no hits.
- Direct `rg` in upstream `WeilConjectures`, the project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json`; direct blueprint-id search upstream: no exact theorem
  or matching declaration name. The upstream generic `sectionsWithSupport` in
  `SixFunctors/ProEtale/Derived/ClosedImmersion.lean` acts on `Sheaf J D` for one fixed
  abelian value category D. It does not act on `SheafOfModules` over the varying
  continuous-function coefficient sheaf. The side `sfIntrinsicSectionsWithSupport`
  likewise requires commutative intrinsic coefficients. Both were opened and inspected;
  neither supplies the kernel of the present noncommutative ringed-module unit.
  Other hits concern Zariski finite-structure kernels or completion-site adjunctions.
  They do not supply this statement or its module adjunction.

No new independent notion, new DAG node, or statement correction was needed. Auxiliary
kernel and complex declarations merely give names to the F, H, units and arrows explicitly
introduced by the item's own statement. All are listed in its `lean.declarations`.

## Dependency modules

`def-weil-proetale-inverse-image`: the recorded primary declaration
`Scheme.sfIntrinsicConstantModuleAdjunction` in
`Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` requires `[CommRing A]` and
`A : Type u`; its intrinsic scalar presentation cannot give the actual adjunction
for the possibly noncommutative `FiniteCoefficientModules` used here. The new module
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction` imports and reexports that
entire module, and adds the required canonical finite-ring module adjunction on the
already recorded transported-action pullback. Its direct image is exactly
`SheafOfModules.pushforward` through `finiteCoefficientDirectImageMap`.

`finiteModuleAdjunction_existsUnique` fixes each Hom transpose by undoing scalar transport,
transporting to the existing small site model, and applying the actual
`SheafOfModules.pullbackPushforwardAdjunction` there. The intermediate g has exactly the
original h's section maps. This completely characterizes the adjunction, so choosing
its unique witness does not choose an unspecified isomorphism or a hollow object.
The theorem's docstring gives the linearity argument, the coefficient-unit compatibility,
the natural Hom bijections and their uniqueness. Only this dependency's `lean` record
changes, with the required explanation in `lean.note`.

Validation: both delivered modules compiled cleanly with `scompile.py`, one file at a
time, with the unchanged 60-second per-file limit. The delivery preflight first found
that the dependency record included the `noncomputable` modifier before the `def` keyword;
the record now starts at `def`, exactly as the signature reader requires. No Lean statement
or definition changed in this metadata repair.

## Second reading by NP

Independent maintainer reading of immutable delivery
fc19d59f89a9eaf29518690d4652c7a2e870c692, on 2026-10-17. This section replaces the
placeholder; the original worker report above is retained as a record of the submitted
version. The corrections below are supplied only in the maintainer review's fixes directory.

I read the item node, all eleven statement dependency nodes and their recorded interfaces,
both delivered modules and their docstrings. I compared the source paragraph in
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-localization/lem-exc-proetale-support-triangle.md`
with the main-20261015 statement and separate proof at the same blueprint location.
I also read Stacks `sites-modules.tex`, `lemma-pullback-module` and
`lemma-adjoint-push-pull-modules` (03D2/03D3, lines 1020–1098), the module-sheaf definition
and abelian lemma (03CV/03DA), and `homology.tex`, `lemma-cat-cochain-abelian` (0114).
The supplied Lean states exactly the supported-kernel part of this argument.

Hypotheses and conclusion checked individually:

- `T U Z : Scheme.{u}`, `i`, `j`, the locally Noetherian and compact-space instances,
  the closed/open immersion instances, `QuasiCompact j`, and the complementary range
  equality give precisely the geometric hypotheses. CompactSpace imposes no separation
  condition. The independent `QuasiCompact j` hypothesis is the one in the node.
- `Ring A`, `Finite A`, and the discrete topology retain noncommutative coefficients.
  `FiniteCoefficientModules` unfolds to the existing `ringedSiteModules`/`SheafOfModules`
  of the sheafified continuous-function coefficient ring, not an etale or Zariski substitute.
- `addOrderOf (1 : A)` is the stated n; finiteness ensures n is positive. `ULift.{u}`
  of `ZMod n` is just B in the intrinsic constant-coefficient convention. The extra
  internal lift in `proEtaleConstantRing` is inherited from that convention. The
  constant-preserving comparisons and transported pullback identify its hB criterion
  with the recorded closed-essential-image criterion. No arbitrary coefficient map
  is introduced. The central residue map is determined by 1 and is proof data.
- hB states both essential-image equivalence and invertibility of the supported
  closed unit, for every B-module. Its two operations and adjunction specialize the
  recorded arbitrary-commutative-ring-sheaf operations.
- The first conjunct asserts invertibility of the actual A-linear closed unit for
  every N with zero open restriction. Its naturality is built into the chosen unit.
  The second conjunct asserts zero open restriction of every closed direct image.
- The kernel functor uses `kernel` and `kernel.map` of precisely the open unit.
  Its map on a differential is the restricted differential, so functoriality yields
  the square-zero equation. H is exactly this functor followed by i pullback.
- The full subcategory defined by `finiteOpenEpicComplex` imposes exactly the epic
  unit hypothesis in every integer degree. It includes all maps between its objects.
  The natural isomorphism e has each component explicitly equal to the closed unit
  on that degree's kernel. Thus it is the asserted canonical complex isomorphism.
- The first arrow is e inverse followed by the kernel inclusion; the second is the
  termwise actual open unit. The witness w makes their composite zero. Evaluation
  states short exactness in complexes and separately in every degree. Both arrows
  are natural transformations on the full subcategory, giving the entire stated
  naturality, including noninvertible chain maps. No boundedness or injectivity is added.

Dependency repair checked: the old `sfIntrinsicConstantModuleAdjunction` requires
commutative coefficients and cannot supply the noncommutative interface. The repair
reexports it without deleting any of its declarations. Its pushforward is the existing
Mathlib pushforward through `finiteCoefficientDirectImageMap`; its left adjoint is the
recorded `finiteCoefficientModulePullback`. In `finiteModuleAdjunction_existsUnique`,
the section formula uniquely determines g, and the model adjunction formula determines
every Hom transpose, hence the entire adjunction. Restriction along c and its inverse
undo one another, since the coefficient map is invertible; the model transports retain
sections. This is a genuine uniquely characterized construction, not a bare existential
choice or a hollow definition. The dependency's explanatory lean.note is appropriate.

The five proof steps in the main docstring track the node: scalar restriction and unit
comparison; the assumed commutative supported criterion; open-unit evaluation and exact
pullback; kernel differentials and the closed unit chain isomorphism; and degreewise
short exactness and naturality. The scalar comparison remains a proof dependency, not
an unrecorded hypothesis or a prerequisite needed to type the statement. No missing
statement-level DAG prerequisite was found.

Edge cases: zero ring (n = 1, B = ZMod 1), arbitrary finite matrix rings, empty T, U or Z,
zero sheaves and complexes, and all integer degrees are retained. For empty U, the
kernel is the original sheaf; for empty Z, the supported kernel is zero. Identity
scheme maps are allowed in the repaired adjunction. There is no Nontrivial, flatness,
constructibility or boundedness assumption. The original site has object universe u+1
and morphism universe u; AsSmall raises only the latter for the model API. The module
universe u+1 agrees with the recorded coefficient convention; no site universes are
silently identified and no test-object quantification is restricted.

Independent searches: rg for `sectionsWithSupport`, `kerFunctor`, `finiteSupportedKernel`,
`finiteModuleAdjunction` in Mathlib, both upstream/side WeilConjectures trees and the
side Sheaf tree. The exact side-framework `Derived/ClosedImmersion.lean` definition
was opened: it concerns `Sheaf J D` for a fixed abelian category D. The side
`sfIntrinsicSectionsWithSupport` requires commutative intrinsic coefficients. Neither
is this variable-ring `SheafOfModules` construction. The completion-site adjunction
with a similar name changes scalars along a quotient of a commutative ring, so is also
not this scheme inverse-image adjunction. The worker's LeanSearch, LeanFinder, Loogle
and grep searches are recorded above. No usable duplicate was found.

Findings and repairs: H6, definition-law proofs were present as local `by simp`,
`equalizer.hom_ext`, and `rfl` proofs. I moved the kernel identity/composition laws,
kernel additivity, inclusion naturality, and pushforward additivity to named theorem
statements with `sorry`, source/blueprint references and proof explanations. The
induced kernel map remains the same actual `kernel.map`; every definition refers to
these laws, with no hidden sorry data. The added declarations are listed in the item's
lean.declarations. H11 (and the real-section requirement of H1): the submitted
second-reading section was a placeholder, now replaced by this independent reading.
No mathematical statement correction or new notion was needed; both primary signature
strings remain verbatim unchanged. The worker report's earlier count of theorem proofs
therefore describes the original version; the fixed version also has the named
structural-law theorems just described.

Compiler reproduction: the prescribed scompile.py wrapper was invoked with both immutable
snapshot files, in dependency order. It returned exit 0 with no diagnostics: sandbox/library
times 2.9/3.1 seconds for the adjunction and 3.3/3.4 for the kernel module. It was then
invoked on both corrected complete files, again exit 0 with no diagnostics: sandbox/library
3.1/3.3 seconds and 2.4/2.7 seconds respectively. Every invocation retained the 60-second
per-file limit; preliminary/private overlay compilations also passed. The installed
scompile.py currently performs its private side overlay and confirmation on the server;
this review used only that authorized wrapper, not direct ssh. No global build,
repository edit, live Lean write, delivery, claim, merge, or branch mutation was performed.

Verdict: FIX for the complete replacement modules, updated item lean record and this report.
