## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction` states
`AlgebraicGeometry.derivedInternalHom_pullback_adjunction`, with proof `sorry`.
It uses the shared, unbounded categories of sheaves of modules and the shared K-flat
monoidal structure. No boundedness, quasi-coherence, properness, flatness, or separation
hypothesis is introduced. The item's natural-language statement is unchanged.

Hypothesis and clause correspondence:

- A morphism of schemes `g:T → S` is `{T S : Scheme.{u}} (g : T ⟶ S)`.
- The two derived categories are `schemeDerivedCategory S` and `schemeDerivedCategory T`.
  The explicitly bound `HasDerivedCategory.{w}` instances are the shared localization
  parameters, not extra geometric hypotheses. The universe parameters are explicit.
- `Lg*` is `derivedPullback g`; `Rg_*` is `schemeDerivedDirectImage g`.
- The adjunction and its counit are the witness `a : derivedPullback g ⊣
  schemeDerivedDirectImage g` and `a.counit.app E`. This asserts existence of that
  adjunction rather than assuming an unconstrained counit.
- Internal Hom is `derivedInternalHom (Opens.grothendieckTopology X)
  X.toRingedSpace.sheaf` on each scheme. It uses the actual structure sheaf.
- The tensor/internal-Hom adjunction witnesses `bS` and `bT` have their inverse Hom
  equivalences identified with `Classical.choose (scheme_derivedInternalHom_adjunction X)`.
  Thus these witnesses use the dependency's recorded bijections. Their counits are
  evaluation, the transpose of the identity.
- The pullback/tensor comparison is `t`. Its equality with
  `Classical.choose (exists_derivedPullback_tensorComparison g)` fixes its components to
  the canonical maps on K-flat representatives; it cannot be an arbitrary tensor iso.
- `γ` is a natural transformation from internal Hom on S to direct image of internal
  Hom of the two pullbacks. This gives the displayed arrow for every `K,L` and naturality
  in both arguments. The first construction equation specifies the adjoint of `γ.app`:
  apply `t.inv` to identify the tensor of pullbacks with pullback of the tensor,
  follow by pullback of evaluation `((bS K).counit.app L)`, and transpose using `bT`.
- `d` is a natural isomorphism on `(schemeDerivedCategory S)ᵒᵖ ×
  schemeDerivedCategory T`. It states invertibility and naturality in M and E together.
  Its component equation is exactly `γ` followed by `Rg_*` of internal Hom applied
  to `(identity, a.counit.app E)`; contravariance in M uses the opposite category.
- `z` is the natural H⁰ global-sections/pushforward identification
  `Rg_* ⋙ H⁰(S,-) ≅ H⁰(T,-)`, using `ringedSiteZerothHypercohomology` from the
  recorded internal-Hom global-sections dependency. This is the degree-zero form
  of the whole-open instance of derivedSectionsPushforwardComparison, transported
  through its exact open-restriction equivalences and the K-injective models.
- The last equation takes every section `x` of the source H⁰. It applies H⁰(S,-)
  to `d.hom`, transports through `z`, and uses the chosen `rhom_global_sections` on T.
  On the other side it identifies `x` with a derived morphism on S by the chosen
  `rhom_global_sections`, applies `derivedPullback g`.map, and composes with the
  counit. Equivalently, after the node's displayed identifications, phi is sent to
  `Lg*(phi) ≫ ε_E`. Both H⁰(RHom)=Hom identifications are the recorded declarations;
  no new Hom or hypercohomology model is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `AlgebraicGeometry.derivedPullback`,
  `exists_derivedPullback` and its K-flat computation.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`, specializing
  `RingedSpace.derivedModuleDirectImage`.
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral`:
  `AlgebraicGeometry.RingedSpace.derivedModulePullback_adjunction` supplies the existence
  of the adjunction in the proof route, transported to the recorded scheme functors
  by their left-derived universal properties. No new pullback functor is used.
- `Sheaf.Algebra.Homology.DerivedInternalHom`: `CategoryTheory.derivedInternalHom`.
- `Sheaf.Algebra.Homology.RhomGlobalSections`: `CategoryTheory.rhom_global_sections`
  and the imported `CategoryTheory.ringedSiteZerothHypercohomology`.
- `Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison`:
  `AlgebraicGeometry.derivedSectionsPushforwardComparison`; the proof route uses the
  whole-open restriction equivalences to obtain the stated H⁰ comparison `z`.
- `Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction`:
  `AlgebraicGeometry.scheme_derivedInternalHom_adjunction` (its chosen first bijection).
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct`:
  `AlgebraicGeometry.derivedPullback_tensorProduct`, including its full signature,
  summandwise characterization, naturality, and K-flat invertibility clause. The
  dependency module below supplies its shared-derived-monoidal interface.

Source read: Stacks Tags 08I3, 079W and 08DJ at
https://stacks.math.columbia.edu/tag/08I3,
https://stacks.math.columbia.edu/tag/079W and
https://stacks.math.columbia.edu/tag/08DJ. The local literature checkout lacks
`cohomology.tex`; the official source pages were used. 08I3 specifies pullback of
internal Hom by transpose of pullback of evaluation, exactly the construction equation.
The node's three proof steps are included in the theorem docstring. The lead's note
about choosing compatible H⁰ identifications is realized as an explicit equation,
not left as an unnamed assumption.

Edge cases checked before the final signature:

- `g = identity`: the canonical comparisons identify γ and d with identity; the
  H⁰ formula is the identity adjunction map.
- M or E zero: both internal-Hom groups vanish as appropriate; the unique map
  between the resulting zero objects is invertible. No nonzero hypothesis appears.
- Empty schemes: no nonemptiness assumption is needed; the module categories are
  zero categories and the same adjunction and natural-isomorphism statements apply.
- Non-flat g and unbounded complexes: all tensors and pullbacks are genuinely derived;
  no underived substitution is made. The K-flat comparison is used only to pin the
  canonical data, not to restrict M,E to chosen complexes.
- All characteristics and arbitrary schemes are admitted.

Searches (via the project msearch logger unless specified):

- leanfinder: `Derived internal Hom adjunction for derived pullback and derived direct
  image on schemes`: eight hits, chiefly Scheme.Modules.pullbackPushforwardAdjunction
  and underived or over-category adjunctions; none is this derived internal-Hom statement.
- loogle: `Adjunction.homEquiv, MonoidalClosed`: no hits; unknown identifier in Loogle.
- leansearch: `Derived internal Hom of a pullback and derived pushforward adjunction`:
  service unavailable (Internal Server Error); no negative verdict attributed to it.
- grep: `derived.*[Ii]nternalHom|[Ii]nternalHom.*[Pp]ullback`: three unrelated
  simplicial-set/Leibniz pullback hits in Mathlib; no exact derived scheme match.
- grep: `tensorPullback.*[Aa]djunction|derivedPullback.*⊣`: no Mathlib hits.
- rg of source WeilConjectures for derivedInternalHom, internalHom and pullback tensor:
  underived module projection formula and étale constant-coefficient tensors, with
  different categories; no exact statement. Search by the item's node id gave no hits.
- rg of `lean/Sheaf` found DerivedDirectImageInternalHom, which is the other-direction
  comparison RHom(L,M) after pushforward to RHom(Rg_*L,Rg_*M). Its full statement was
  read: it neither asserts this isomorphism nor gives the H⁰ counit formula, so it is
  not reused as an exact match. The existing DerivedInternalHomAdjunction and
  DerivedPullbackTensorProduct were read in full and are used.
- rg in Mathlib Monoidal/Functor and upstream derived-monoidal modules located
  `Functor.LaxMonoidal.μ` and its Qh instance. These are used by the dependency adapter;
  it does not implement a second localization or tensor comparison.

Local validation: both delivery modules compiled together without warnings or errors;
all theorem proofs are `sorry`, and every auxiliary definition has actual data.
No new definition node and no correction of the item's statement is needed.

## Dependency modules

`lem-pc-derived-pullback-tensor-product`: its previous declaration describes the canonical
comparison on K-flat complexes, with a file-local sheaf monoidal instance; it does not
provide a natural isomorphism between the shared derived tensor bifunctors, which the
item's γ construction needs. `Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparison`
states `AlgebraicGeometry.exists_derivedPullback_tensorComparison`. It provides that
same isomorphism on derived objects and fixes it by a commuting diagram on every pair
of K-flat representatives. The witnesses F, its object and morphism identifications
with tensorPullback, additivity, the left-derived counit, and the summandwise φ are the
same data as the old statement. The summand equation uses the old dependency's chosen
`Scheme.Modules.module_pullback_tensor`. The K-flat invertibility clause is retained.
The naturality in derived objects is carried by the natural isomorphism t; φ is pinned
by its components on every direct-sum inclusion, so its naturality follows from that of
those same module tensor comparisons. The final diagram uses the existing lax monoidal
comparison of localization, which is invertible on K-flat representatives; hence it
uniquely specifies t through localization.

The four auxiliary definitions only specialize existing APIs by supplying the shared
sheaf tensor instances: `schemeTensorComplex` calls `CochainComplex.mapBifunctor`,
`schemeTensorComplexι` calls `HomologicalComplex.ιMapBifunctor`, `schemeModuleTensorMap`
calls `tensorHom`, and `schemeLocalizationTensorComparison` calls
`Functor.LaxMonoidal.μ` for Qh. They contain no `sorry` and no alternative tensor data.
They are public specialization adapters belonging to this dependency's statement,
not new mathematical notions. Only this dependency's `lean` field is changed.

The dependency's source is Stacks 079U, used also by 08I3. Its two-step proof is carried
in the new theorem docstring. Identity g, zero complexes, non-flat g, arbitrary
characteristic and empty schemes impose no additional hypotheses. The new form uses
the same shared module category and derived monoidal instance as the main theorem.

## Second reading by K1

Independent second reading, 2026-10-12. I opened the item node, both delivered
modules, the node and former module of lem-pc-derived-pullback-tensor-product,
and the declarations of every statement dependency. I independently obtained
Stacks' cohomology.tex and read section-internal-hom, lemma-internal-hom,
remark-prepare-fancy-base-change, lemma-pullback-tensor-product and lemma-adjoint.
The section assumes a ringed space, commutative structure rings and the unbounded
module derived category. Specializing to schemes adds no finiteness, flatness,
boundedness, quasi-coherence or separation condition. The node agrees with this
source; there is no statement correction and no new definition node to review.

Here is my object/hypothesis/conclusion list and its Lean correspondence:

1. Arbitrary schemes T,S and their morphism g: `{T S : Scheme.{u}} (g : T ⟶ S)`.
   Verdict: exact. Both schemes use the universe of their morphism category;
   arbitrary larger schemes are covered by arbitrary `u`.
2. D(O_S), D(O_T): `schemeDerivedCategory S`, `schemeDerivedCategory T`.
   Verdict: exact unbounded localizations of the shared
   `SheafOfModules.{u} (moduleRings X.toRingedSpace)` carrier. The two
   `HasDerivedCategory.{w}` binders are the same localization parameters as
   `derivedPullback`, not geometric or boundedness assumptions.
3. Derived pullback and direct image: `derivedPullback g`,
   `schemeDerivedDirectImage g`. Verdict: exact. I opened their definitions:
   the former chooses the total left derived tensor pullback, computed on
   K-flat resolutions; the latter specializes the K-injective ringed-space
   direct image. Mathlib's different `Scheme.Modules.pullback` is not used.
4. Pullback/direct-image adjunction and its counit: existential witness `a`
   and `a.counit.app E`. Verdict: a genuine adjunction of the fixed functors,
   with no assumed arbitrary map or extra hypothesis. The recorded
   ringed-space dependency supplies an adjunction for a left-derived witness;
   its universal property transports it to this fixed `derivedPullback`.
5. RHom for the actual structure sheaves: `derivedInternalHom
   (Opens.grothendieckTopology X) X.toRingedSpace.sheaf`. Verdict: exact.
   I opened the dependency's localization of the Hom complex into a functorial
   K-injective replacement. The opposite first coordinate gives the required
   contravariance; this is neither Hom of global sections nor RHom of rings.
6. Tensor-Hom bijection and evaluation: witnesses `bS`,`bT` use `tensorRight K`;
   their inverse `homEquiv` equals the first chosen equivalence in
   `scheme_derivedInternalHom_adjunction`. Verdict: exact orientation:
   Hom(A,RHom(K,L)) = Hom(A tensor K,L), so `(bS K).counit.app L`
   is evaluation RHom(K,L) tensor K -> L, the transpose of the identity.
7. Pullback commutes with the derived tensor: witness `t`, fixed to the
   delivered dependency's chosen natural isomorphism. Verdict: exact direction
   for `t.hom` is Lg*(A tensor K) -> Lg*A tensor Lg*K, hence `t.inv` is
   precisely the direction in the node's construction of gamma.
8. For every K,L, gamma is the mate of pullback of evaluation: `γ` is a
   natural transformation on D(O_S)^op x D(O_S); the first construction
   equation applies `(a.homEquiv ...).symm` to `γ.app (op K,L)` and equates
   it with the `bT` transpose of `t.inv.app (RHom(K,L),K)` followed by
   `(derivedPullback g).map ((bS K).counit.app L)`.
   Verdict: exact, including both quantifiers and naturality.
9. For every M,E the displayed two-arrow composite is an isomorphism:
   witness `d` is a natural isomorphism on D(O_S)^op x D(O_T), and
   `d.hom.app (op M,E)` is equated with gamma at `(M,Rg_*E)` followed by
   Rg_* of RHom on `(identity.op,a.counit.app E)`.
   Verdict: exact composite and invertibility, natural in both arguments;
   merely asserting existence of an unrelated object isomorphism would fail
   this check, but the component equation prevents that.
10. The two H^0(RHom)=Hom identifications are the chosen
    `rhom_global_sections` additive equivalences on S and T. The middle
    H^0(S,Rg_*F)=H^0(T,F) identification is the natural isomorphism `z`
    between the fixed `ringedSiteZerothHypercohomology` functors.
    Verdict: the correct degree-zero global hypercohomology, with the
    whole-open pushforward comparison transported to these shared models.
    The dependency's original comparison is on the restricted schemes and
    in D(Ab), so that transport is necessary, not definitional equality.
11. Its H^0 map sends phi to Lg*(phi) followed by epsilon: the last equation
    quantifies M,E and every source section x, applies H^0 to `d.hom`,
    transports through `z`, then applies the recorded T equivalence.
    Its right side is `(derivedPullback g).map` of the recorded S
    equivalence at x, followed by `a.counit.app E`.
    Verdict: exact, including order of composition. Compatibility is a
    conclusion of this theorem, not an extra assumed hypothesis. The
    lead_note about constructing compatible dependency equivalences is
    addressed by this explicit equation and remains a requirement for
    their eventual proofs; naturality alone is not a proof of it.

Dependency-module reading (H13):
`lem-pc-derived-pullback-tensor-product` states the canonical bifunctorial
isomorphism of Stacks 079U for arbitrary derived objects. Its former module
only has K-flat-representative comparisons, using a file-local sheaf tensor
instance. It cannot be substituted for a natural isomorphism between the
shared derived tensor bifunctors. The new `exists_derivedPullback_tensorComparison`
provides exactly that interface. I checked the source/target of its final
commuting diagram: both are Lg*(Q(P) tensor Q(N)) -> Q(g*Tot(P tensor N)).
Its summand equation uses the same chosen `module_pullback_tensor`, and
identifies F on objects and maps with the recorded tensor pullback. Its
K-flat invertibility clause matches the old module. The naturality of t
states the node's naturality; the summand characterization also determines
phi and implies its representative-level naturality, so omitting a separate
phi-naturality conjunct does not weaken the node's mathematical claim.
The four adapter definitions supply instances to existing `mapBifunctor`,
`ιMapBifunctor`, `tensorHom` and localization `LaxMonoidal.μ`. I opened the
shared `schemeDerivedTensorMonoidal` definition; the adapters use that
structure and create no second derived tensor or localization. They contain
actual data, with proposition witnesses taken from named existing theorems.
The dependency node differs only in its lean record and explains the old
interface's deficiency. No new definition node is appropriate for these
explicit-instance specialization adapters.

Edge cases: zero M or E, empty schemes, arbitrary characteristic and
non-flat g impose no added assumptions. The identity morphism recovers the
identity comparison after transporting the derived models and adjunctions;
this need not be literal equality of chosen functors. Unbounded complexes
are admitted. There is no external index set or numerical n to restrict;
total tensors include every integer degree and every summand p+q=n,
including n=0. The universe binders are explicit and match the recorded
pullback API; no implicit variable, lower-universe test-object quantifier,
nonemptiness assumption or finite-generation restriction appears.

Independent searches, using words different from the worker's queries:

- leanfinder: `internal Hom isomorphism inverse image direct image counit
  unbounded sheaves`: eight hits about sheaf equivalences, ordinary global
  sections and light condensed modules; none states this result.
- loogle: `MonoidalClosed, Adjunction`: unavailable identifier MonoidalClosed;
  no negative existence conclusion inferred from the failed query.
- leansearch: `sheaf derived tensor inverse image internal Hom right adjoint
  compatibility`: HTTP Internal Server Error, recorded as unavailable.
- rg in Mathlib, upstream WeilConjectures, and project Sheaf for
  `internalHom.*(adjunction|Pullback)`, `pullback.*internalHom`,
  `pushforward.*internalHom`, `RHom.*pullback` and the delivered adapter names.
  Mathlib's Leibniz internal-Hom pullbacks concern simplicial sets;
  upstream homotopy internal Hom concerns complexes, and its perfect-object
  RHom comparisons require perfectness and are different statements.
  No duplicate statement or adapter was found. I also checked the upstream
  name index and overlap notes.
- I opened the full signature of the project's
  `exists_derivedDirectImage_internalHom_comparison`: it maps
  Rg_*RHom(L,M) -> RHom(Rg_*L,Rg_*M), without this isomorphism or H^0
  counit formula. Its differently directed comparison is not an exact match.

No Lean or node-statement mismatch was found, so their correct text was
preserved. This reading adds the independent correspondence and validation
record only. Every delivered theorem proof remains `sorry`, all declaration
source/blueprint docstrings are present, and the main docstring follows all
three proof steps of the node. Both modules compiled together locally in
15.3 seconds, exit code 0, with no errors or warnings. Delivery dry run and
server compilation are the final checks.
