## Worker report

The module `Sheaf.AlgebraicGeometry.SupportedKernelFlatPullback` constructs the supported
subsheaf and inclusion as `supportedSectionsKernel` and `supportedSectionsKernelι` and states
`supportedSectionsKernel_flatPullback`. Its only postponed proof is this named theorem,
whose docstring contains the six-step DAG argument. Both definitions have real data:
`kernel` and `kernel.ι` of the existing restriction-adjunction unit. These are helpers
for the supported sheaves explicitly defined in this item's statement, rather than new
independent mathematical notions. No new nodes or dependency repairs are needed.

Hypothesis and clause correspondence:

- Schemes and flat map: `{Q P : Scheme.{u}} (u : Q ⟶ P) [Flat u]`.
- Closed support: `D : Closeds P`. Its complement is `D.compl`.
- Locally principal support: `hD` gives, for every `x`, an affine open `V` containing
  it and a section `a`, with `V.1 ⊓ D.compl = P.basicOpen a`. Equality of complements
  inside V is precisely `D ∩ V = V(a)`; `basicOpen` tests invertibility of the germ.
- The quasi-coherent input is `(H : P.Modules) (hH : H.IsQuasicoherent)`.
- The inverse-image support is `D.preimage u.base.hom.continuous`; its complementary
  open is definitionally `u ⁻¹ᵁ D.compl`.
- K is `supportedSectionsKernel D H`. L is the same kernel construction applied to
  the inverse-image support and `(tensorPullback u).obj H`. Restriction uses
  `restrictAdjunction (Scheme.Opens.ι D.compl)`. Thus these are canonical kernels,
  not arbitrary morphisms or choices from an existence assertion.
- The first two conjuncts give quasi-coherence of K and L separately.
- The third conjunct identifies the range of `supportedSectionsKernelι D H` on
  every open V with sections whose restriction to `V ⊓ D.compl` is zero. A kernel
  inclusion is already a monomorphism; its domain is the prescribed submodule.
- The fourth conjunct, for every open W of Q, states `Function.Injective` for the
  pulled-back inclusion, equality of its `Set.range` with the inclusion of L,
  and the defining zero-restriction characterization of that latter range.
  This states the image equality for actual sections on every open, hence also
  for the image subsheaf.
- The final conjunct quantifies over every affine pair `V W`, its containment `e`,
  every section `a`, and the equality cutting out D on V. There is no chosen
  special affine cover or selected equation.
- A, C and M are `Γ(P,V.1)`, `Γ(Q,W.1)` and `Γ(H,V.1)`. The ring homomorphism is
  `(u.appLE V.1 W.1 e).hom`, so a_C is its value on a.
- Its first subclause says that the image of K(V) in H(V) is exactly
  `{s | ∃ n : ℕ, a ^ n • s = 0}`. This supplies the displayed identification
  `Γ_a(M) = K(V)` including n = 0; the kernel inclusion identifies the modules.
- `cK` and `cH` are `≃ₗ[Γ(Q,W.1)]`, hence C-linear bijections with the two required
  sources and targets. The sources are existing Mathlib `ModuleCat.extendScalars`
  objects, `C ⊗_A K(V)` and `C ⊗_A H(V)`. Tensor symmetry identifies these with
  the node's `K(V) ⊗_A C` and `M ⊗_A C`. This convention changes neither the
  comparison nor its formula: `c ⊗ s` corresponds to `s ⊗ c`.
- The next two subclauses give exactly `c • η(s)|W` on pure tensors, using the
  unit of the recorded `tensorPullbackSectionAdjunction u` and the actual
  presheaf restriction along e. No arbitrary bijections are substituted.
- The next subclause is the commutative square on every tensor t. The bottom
  arrow is `(ModuleCat.extendScalars ...).map` of the sectionwise inclusion,
  namely the tensor of inclusion (after the same tensor symmetry).
- The next conjunct asserts injectivity of that tensor map.
- The penultimate subclause identifies its range with elements killed by some
  power of a_C. The last subclause says cH carries exactly those elements to
  the range of L(W). Since cH is bijective, this is the claimed bijection
  between the power-torsion submodule and L(W).

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`; the scheme module is a public transitive import of Flat.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` (equivalent to stalkwise flatness by
  `Flat.iff_flat_stalkMap`). This import also supplies the affine-flatness
  Mathlib match `AlgebraicGeometry.flat_iff` of the proof dependency.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, exposing
  `SheafOfModules.IsQuasicoherent`. The module's main conjunction
  `Scheme.Modules.IsQuasiCoherentFiniteType` also assumes finite type, which
  this node does not assume; the correct publicly exposed quasi-coherence
  predicate is used on its own.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, with
  `Scheme.Modules.tensorPullback` and its section-normalized
  `tensorPullbackSectionAdjunction`. Read its construction and unit
  normalization, as well as the explicit pullback it publicly imports.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf` supplies `restrictAdjunction` and
  its section formula `restrictAdjunction_unit_app_app`. `kernel` and
  `kernel.ι` are Mathlib's existing constructions in this abelian category.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` supplies `extendScalars`
  and its map, as well as the `ChangeOfRings` pure tensor notation.
- Stated proof dependencies are imported privately:
  `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
  (`Scheme.Modules.exists_tensorPullback_affine_sections`),
  `WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackQCoh`
  (`RingedSpace.tensorModulePullback_isQuasicoherent`), and
  `Mathlib.RingTheory.Flat.Basic` (`Module.Flat.lTensor_exact`, `rTensor_exact`).
  The other two proof dependencies, `lem-trf-locally-principal-supported-kernel`
  and `lem-trf-supported-sections-quasi-coherent`, have no recorded Lean yet;
  no import is invented for them. Their proof uses remain in the docstring.

Edge cases checked before writing:

- Empty P or Q: local-principality is vacuous where appropriate, and all
  section and affine-pair quantifiers still make sense. No nonempty binder.
- D empty: choose unit equations; the kernel and power-torsion are zero.
- D all of P: choose a = 0; restriction is to the empty open and the kernel
  is all of H. Exponent 1 witnesses every element's power torsion.
- Zero sheaf and the empty affine open (zero coordinate ring) are allowed.
- Nilpotent equations: no regularity or Cartier-divisor hypothesis is added.
- n = 0 remains explicitly allowed (`ℕ`); a^0 annihilates only zero.
- No noetherian, finite-type, separatedness, global-equation or affine-map
  assumption is imposed. Q and P have the project's standard scheme universe.

Searches on 2026-10-24 (all through the prescribed msearch.py where applicable):

- LeanFinder: `Flat pullback commutes with the subsheaf of sections of a quasi
  coherent module supported on a locally principal closed subset`. Eight hits:
  `Scheme.Hom.flat_appLE`, `Flat.flat_appLE`, `ModuleCat.Tilde.res_const`,
  `Flat.instResLE`, `Flat.instMorphismRestrict`,
  `Scheme.IdealSheafData.mkOfMemSupportIff_ideal`, `Scheme.Modules.restrict`,
  `Scheme.IdealSheafData.support_comap`. These describe flat charts, ordinary
  restriction or ideal supports, not this module-kernel comparison.
- Loogle: `Module.Flat, LinearMap.ker`. Ten hits including `tensorKerEquiv`,
  `tensorKerInv`, `Module.Flat.ker_lTensor_eq`, and related tensor-kernel
  formulas. These are algebraic ingredients, not the sheaf statement.
- LeanSearch: `Supported sections of a quasi coherent module commute with flat
  pullback along a scheme morphism`. Eight hits, on `IsQuasicoherent`, its
  data and constructors, and `Flat.flat_appLE`/`instMorphismRestrict`; no match.
- Mathlib grep via msearch:
  `(supportedSections|sectionsSupported|supported_sections).*(pullback|flat)|(pullback|flat).*(supportedSections|sectionsSupported|supported_sections)`:
  zero hits.
- `rg` of `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf` for
  `supportedSections|sectionsSupported|supportedKernel|supported.*[Kk]ernel|affineSections.*[Pp]ullback|tensorPullback.*[Ss]ection`:
  affine comparison and etale/pro-etale support functors found. The latter
  have constant etale coefficients and different categories; none is a
  Zariski O-module kernel of this statement. Read the affine-comparison file.
- `rg` of upstream for `lem-trf-supported-kernel-flat-pullback`: no hit.
- Checked proposed declaration names in Mathlib, upstream, Sheaf and
  `dag/lean_names_upstream.json`: no conflict. Searched DAG support/kernel
  notions as well: related theorem nodes exist, no declaration of this item.

No statement dispute or correction is needed. Only the item's `lean` field changes.

## Second reading by Q74

Independent reading (maintainer second reader, 2026-10-24), with the node
`lem-trf-supported-kernel-flat-pullback`, its four stmt_deps and the module
`Sheaf.AlgebraicGeometry.SupportedKernelFlatPullback` open. It replaces the
author's own second pass. Does the Lean say exactly what the node says? Yes.

Node objects and hypotheses:

- u : Q → P flat morphism of schemes: `{Q P : Scheme.{u}} (u : Q ⟶ P) [Flat u]`
  (def-pc-scheme, def-weil-flat-morphism recorded declarations). Exact; one scheme
  universe as in every recorded scheme interface.
- D ⊆ P closed: `D : Closeds P`. Exact.
- Locally principal: `hD : ∀ x, ∃ V affine, ∃ a : Γ(P,V), x ∈ V ∧ V ⊓ Dᶜ = P.basicOpen a`.
  Since `basicOpen a ⊆ V` is the non-vanishing locus of a, this is V \ D = V \ V(a),
  i.e. D ∩ V = V(a). Exact; no global equation, no nonzerodivisor condition.
- D_Q = u⁻¹D: `D.preimage u.base.hom.continuous`, complement `u ⁻¹ᵁ D.compl`. Exact.
- H quasi-coherent: `(H : P.Modules) (hH : H.IsQuasicoherent)`, Mathlib
  `SheafOfModules.IsQuasicoherent`, listed in the pqf-def-coherent record. Exact,
  no finite type assumed.
- K: `supportedSectionsKernel D H = kernel ((restrictAdjunction (Opens.ι Dᶜ)).unit.app H)`.
  By Mathlib `restrictAdjunction_unit_app_app` the unit on V is restriction
  H(V) → H(V ⊓ Dᶜ); kernels in P.Modules are sectionwise, so K(V) = {h : h|_{V∖D} = 0}.
  The third conjunct states this characterization on every open V. Real data, not
  hollow; helper declared in the item's own module with source/blueprint docstrings.
- L: the same construction for D_Q and `(tensorPullback u).obj H` (def-pc-module-pullback
  recorded functor, not Mathlib `Modules.pullback`), characterized on every W in the
  fourth conjunct. Exact.

Conclusion clauses:

- K, L quasi-coherent: first two conjuncts. Exact.
- u^*(K ↪ H) injective with image exactly L: for every open W, sectionwise
  injectivity and `Set.range` equality with the L-inclusion. For sheaf morphisms this
  is equivalent to mono with image subsheaf L (the image presheaf of a mono is a sheaf).
  Exact.
- Affine pairs: `∀ V W (e : W ≤ u⁻¹ᵁ V) a, V ⊓ Dᶜ = basicOpen a → …`, every pair, every
  equation. A = Γ(P,V), C = Γ(Q,W), M = Γ(H,V), a_C = `(u.appLE V W e).hom a`.
  - Γ_a(M) = K(V): `(∃ t, ι t = s) ↔ ∃ n : ℕ, a ^ n • s = 0`. Exact (n = 0 allowed).
  - The two C-linear bijections with formula s ⊗ c ↦ c·η(s)|_W: `∃ cK cH : … ≃ₗ[C] …`
    with the pure-tensor formulas through the unit of the normalized
    `tensorPullbackSectionAdjunction u` and `presheaf.map (homOfLE e).op`. Since pure
    tensors span, the formulas pin cK, cH, so the existential is the node's
    "the given maps are bijective". Source is Mathlib `extendScalars` C ⊗_A M, the
    node's M ⊗_A C up to tensor symmetry (c ⊗ s ↔ s ⊗ c); no content change.
  - Square: `(u^*ι)_W ∘ cK = cH ∘ extendScalars.map ι_V`. Exact.
  - The tensor of inclusion injective: separate clause. Exact.
  - Its image = Γ_{a_C}(M ⊗ C): range ↔ ∃ n, a_C^n • t = 0. Exact.
  - cH carries Γ_{a_C} onto L(W): `(∃ n, a_C^n • t = 0) ↔ cH t ∈ range L.ι_W`;
    with cH bijective this is the bijection onto L(W). Exact.

Edge cases: D = ∅ (a = 1), D = P (a = 0, restriction to ∅), empty P/Q or empty affine
W (zero ring), H = 0, nilpotent a, n = 0: all covered, no binder excludes them. Flatness
is needed (Z → Z/2, a = 2) and is assumed exactly as the node does; no Noetherian,
finite-type, separatedness or affine-map hypothesis added.

Searches (own wording): `rg` of lean/Sheaf, lean/WeilConjectures and Mathlib
AlgebraicGeometry for `supportedSections|SupportedKernel|restrictAdjunction.*unit|
withSupport.*Modules`: only étale/pro-étale `supportedSectionsFunctor` and
`finiteSupportedSections` (constant-coefficient étale sheaves, other categories) and
uses of `restrictAdjunction` units; no Zariski O-module supported-section kernel. DAG:
no definition node for this subsheaf; the sister theorem nodes
lem-trf-locally-principal-supported-kernel and lem-trf-supported-sections-quasi-coherent
define the same K inline and have no Lean yet (when stated they should reuse
`supportedSectionsKernel` rather than copy it — advisory).

Records: only the item's `lean` field differs from the base; `lean.statement` is
verbatim the file's signature; imports are public for statement deps and plain for the
stated proof-dependency modules (ModulePullbackAffineSections,
RingedSpaceTensorPullbackQCoh, Mathlib.RingTheory.Flat.Basic); no line over 100 chars;
the theorem docstring carries the six proof steps; proof is `sorry`.

Mismatches found: none in the Lean or the records. Changed: this section only
(the author's own second pass was replaced by this independent reading).
