## Worker report

Item: lem-sfb-relative-flat-tensor-charts-sheaf-exact (Q07, stage 2).

The module `Sheaf.AlgebraicGeometry.RelativeFlatTensorChartsSheafExact` states
`AlgebraicGeometry.Scheme.Modules.relativeFlat_tensorCharts_sheaf_shortExact`.
Its sole theorem has proof `sorry`. There are no new definitions, helper axioms,
new nodes, dependency repairs, statement corrections, or disputed statements.
The node copy changes only `lean`; the accepted stage-1 split stays verbatim.
The previous unchanged-item stage-1 rejection does not apply: the current node
has no Lean record, is queued at stage 2, and brief-stage2 section 0 expressly
permits this handoff. The sandbox initially contained only dispatcher markers.

Hypotheses, matched individually to the node:

- The scheme Y is `{Y : Scheme.{u}}`; the three O_Y-modules are `(F G H : Y.Modules)`.
  The three `[F.IsQuasicoherent]`, `[G.IsQuasicoherent]`, `[H.IsQuasicoherent]`
  use the existing `SheafOfModules.IsQuasicoherent`; finite type and coherence
  are not imposed. The arrows are `(f : F ⟶ G)` and `(g : G ⟶ H)`.
- The arbitrary affine open cover is `(ι : Type w) (Q : ι → Y.Opens)` with
  `hcover : ⨆ i, Q i = ⊤` and `haffine : ∀ i, IsAffineOpen (Q i)`.
  There is no finite, inhabited, or universe-equality assumption on the cover.
- The ring families R, A, S have independent universes r, a, s and individual
  `CommRing` instances. `[Algebra (R i) (A i)]` and `[Algebra (R i) (S i)]`
  encode precisely the two supplied ring homomorphisms. Every unital map of
  commutative rings gives that algebra structure, so this loses no case.
- `e : ∀ i, Γ(Y, Q i) ≃+* (A i ⊗[R i] S i)` is the specified ring isomorphism,
  in the direction stated in the node. Its inverse transports tensor scalars
  to the existing section-ring action.
- L, M, N have independent universes l, m, n, additive commutative groups and
  A-module structures. The R-module structures and three `IsScalarTower`
  instances express restriction along R to A. The tower laws force precisely
  the restricted action, rather than a new compatibility assumption.
- `(p : ∀ i, L i →ₗ[A i] M i)` and `(q : ∀ i, M i →ₗ[A i] N i)` are the displayed
  A-linear arrows. `hp`, `hpq`, `hq` say respectively injectivity of p,
  `Function.Exact p q`, and surjectivity of q. This is the module short exact
  sequence convention recorded by def-weil-pbc-exact-sequence, including zero
  at both endpoints and arbitrary module universes.
- `[∀ i, Module.Flat (R i) (N i)]` is flatness of the LAST TERM over R.
  There is no flatness assumption on A, S, L or M.
- `eF`, `eG`, `eH` are the three section-to-tensor additive equivalences.
  `heF`, `heG`, `heH` express their tensor-ring linearity. Specifically, for
  b in A and c in S, the action of b tensor c on L tensor S is b acting on
  L and c acting on S; `TensorProduct.comm` moves the second action to the
  left and back. The displayed equation is therefore exactly
  eF(e.symm(b tensor c) smul x) = (b tensor c) smul eF(x), and likewise
  for G, H. Since every ring tensor is a sum of pure tensors and both sides
  are additive in that tensor, these equations are equivalent to linearity
  for EVERY tensor scalar. This avoids introducing a duplicate tensor action
  or an unconstrained module structure on the tensor products.
- `hf` and `hg` assert the two commuting squares on every section. Their
  right sides are `((p i).restrictScalars (R i)).rTensor (S i)` and the
  corresponding q map, namely exactly p tensor 1 and q tensor 1.

Conclusions, matched individually to the node:

- The first conjunct states injectivity, exactness, surjectivity of the two
  section arrows on every Q i.
- The next conjunct quantifies over EVERY `c : Γ(Y, Q i)` and states the same
  three properties for `f.app (Y.basicOpen c)` and `g.app (Y.basicOpen c)`.
  `Y.basicOpen c` is the ambient principal open inside Q i.
- For that c, `dF`, `dG`, `dH` identify the respective localized section
  modules `LocalizedModule (Submonoid.powers c) Γ(F,Q i)` (and G,H) with
  sections on the principal open. The first equation for each d sends the
  denominator-one fraction to actual restriction along `Y.basicOpen_le c`.
  The second equation is linearity over the original chart ring via its
  actual restriction to the principal-open ring. These determine the
  canonical localization identification: multiplication by c is invertible
  on both sides, and every fraction is c to a negative power times a
  denominator-one fraction. They also give linearity over the localized ring.
- The two final equations under these d's quantify over every numerator in
  L tensor_R S or M tensor_R S and every denominator in `Submonoid.powers c`.
  They say that the principal-open arrows send x/t to (p tensor 1)(x)/t and
  (q tensor 1)(x)/t, using eF/eG/eH to identify chart sections with the supplied
  tensors. Thus the conclusion explicitly identifies the localizations of
  the DISPLAYED tensor maps, not just some exact arrows on the open.
- `∃ hfg : f ≫ g = 0` records the complex relation as a conclusion rather
  than assuming it. `(ShortComplex.mk f g hfg).ShortExact` is exactly the
  sheaf short exact sequence in the node's abelian category.
- `IsIso (kernel.lift g f hfg)` identifies the CANONICAL kernel factorization
  as an isomorphism; the last equation is its stated composite with
  `kernel.ι g`. No arbitrary kernel map or merely nonempty iso is used.
- No cover or module finiteness hypothesis occurs anywhere.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and its category of morphisms,
  `Mathlib.AlgebraicGeometry.Scheme` (available through the sheaf-module imports).
  Read Scheme's local_affine field and Scheme.Hom.
- pqf-def-coherent: public import `Sheaf.AlgebraicGeometry.CoherentFiniteType`;
  its `Scheme.Modules.IsQuasiCoherentFiniteType` is an AND of the already existing
  `SheafOfModules.IsQuasicoherent` and `IsFiniteType`. Only the former notion
  is required here, and is used directly; assuming that AND would incorrectly
  add finite type. Its Mathlib definition and the upstream Coherent module
  docstring were read. No dependency repair is needed.
- def-weil-sheaf-of-modules-category: public import
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`;
  it is the transparent abbreviation for Mathlib `SheafOfModules`.
  `Scheme.Modules` is exactly that category for Y.ringCatSheaf with module
  universe u, with the existing abelian instance and linear morphisms.
- def-weil-pbc-exact-sequence: `Mathlib.Algebra.Homology.ExactSequence`,
  `CategoryTheory.ComposableArrows.Exact`; its recorded alternative
  `CategoryTheory.ShortComplex.ShortExact` is used for the sheaf conclusion.
  The separate injective/exact/surjective convention is used for modules.
- def-weil-pbc-flat-ring-map: `Mathlib.RingTheory.RingHom.Flat`, `Module.Flat`.
  The node's module-flatness declaration, not ring-map flatness, is used.

Proof-only imports are kept non-public as required. The proof plan is the
accepted node's four steps: `LinearMap.lTensor_injective_of_exact_of_flat`
from Mathlib.RingTheory.Flat.Equalizer; basic-open affine/localization and
point facts from Mathlib.AlgebraicGeometry.ResidueField/AffineScheme; the
basic-open basis from Mathlib.RingTheory.Spectrum.Prime.Topology (transitive);
`quasiCoherent_affine_section_baseChange` from
WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange;
`IsLocalizedModule.isBaseChange` from Mathlib.RingTheory.Localization.BaseChange;
`LocalizedModule.map_exact` from Mathlib.Algebra.Module.LocalizedModule.Exact;
`isQuasicoherent_kernel` and `epi_of_surjective_app` from
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel; and
`Hom.isIso_of_bijective_on_affine_open_cover` from
WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover.
The theorem docstring gives the complete four-step proof with the DAG ids.

Sources opened: algebra.tex lemma-flat-tor-zero (00HL),
proposition-localization-exact (00CS), lemma-Zariski-topology (00E0);
schemes.tex lemma-spec-sheaves (01HV), lemma-standard-open-affine (01I3);
constructions.tex lemma-spec-inclusion (01LN). This is the node's stated
agent-assembled affine-cover criterion, not a claim that 00HL alone states
its complete sheaf conclusion. No blueprint unit is changed.

Edge cases checked before writing:

- Empty index type: hcover then says bottom = top, forcing the empty scheme;
  its module category and all section modules are zero. No Nonempty is added.
- c = 0: the principal open and its section modules are empty/zero, and the
  localization inverts zero and is zero, so all three properties remain true.
- Zero chart rings and zero modules: allowed by CommRing/AddCommGroup with
  no Nontrivial assumptions. A zero-ring unital module is zero as required.
- c = 1: localization is the original chart, and denominator-one normalization
  is the identity under the section restriction identifications.
- N = 0: flatness is allowed and the original exact sequence has p an iso;
  tensoring preserves it with arbitrary S, even when S is not flat.
- Flatness is essential on the quotient: the short exact Z-module sequence
  Z --2--> Z --> Z/2, tensored with Z/2, loses injectivity, and the quotient
  fails the required flatness hypothesis. A split sequence with flat quotient
  remains exact when tensoring with the nonflat S = Z/2, which is permitted.
- Ring, module and index universes are explicitly independent and all variables
  bound with autoImplicit false. No finite generation or cover cardinal bound.

Searches for an existing complete declaration (2026-10-23):

- msearch leanfinder: "Short exact sequence of quasi coherent sheaves from
  relative flat tensor presentations on affine charts". Eight component hits,
  including Module.Flat.rTensor_shortComplex_exact and lTensor_exact, but no
  full relative-flat quotient affine-chart sheaf criterion.
- msearch loogle: `LinearMap.lTensor_injective_of_exact_of_flat`. One hit,
  the tensor injectivity component, not the sheaf/localization/kernel result.
- msearch grep: `ShortExact|shortExact` in Mathlib/AlgebraicGeometry/Modules.
  Zero hits. Direct reads of module-category and sheaf exactness definitions
  supplied the constituent notions.
- msearch leansearch: "Short exact sequence of quasi coherent sheaves detected
  by relative flat quotient tensor charts on an affine cover". Eight hits,
  tensor-exactness and quasi-coherence components, no exact full match.
- rg in lean/Sheaf and lean/WeilConjectures for relative flat/tensor charts,
  exact-localization, and the chosen declaration name, plus the item id in
  lean/WeilConjectures: no full match and no item declaration. Existing affine
  section base change, quasi-coherent kernel, localization and tensor-action
  APIs were read and reused. dag/lean_names_upstream.json has no chosen-name hit.

Validation: the prescribed scompile.py compiled both its sandbox probe and
`Sheaf.AlgebraicGeometry.RelativeFlatTensorChartsSheafExact` separately on the
server in 3.6 s and 3.5 s, with no errors or extra warnings. The source has
one theorem, a whole-proof sorry, no local notation/instances, no implicit
variables, no let binders or show terms in the signature, and no lines over
100 characters. The Lean record stores the verbatim full theorem signature.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
