## Worker report

The delivery states `def-pur-vector-bundle-zero-section` in
`Sheaf.Paper.PurityVectorBundleZeroSection`. The main declaration is
`AlgebraicGeometry.PurityVectorBundle`; the companion declarations are
`PurityVectorBundle.zeroSection`, `PurityVectorBundle.zeroSection_spec`, and
`PurityVectorBundle.Trivialization`. Definitions have actual data. The sole
postponed proof is `zeroSection_spec`, whose docstring gives the construction,
affine computation, closedness argument, and transport through the chosen isomorphism.

I read the item's complete statement and all thirteen original statement dependencies,
including their recorded Lean declarations or Mathlib matches. The source is the archived
blueprint file `sec-smooth-purity/sk-def-purity-conv/def-pur-vector-bundle-zero-section.md`
(order 1895), together with that unit's `_section.md`. I also read Stacks Constructions,
`definition-vector-bundle` (Tag 01M2), and the existing relative-Spec module's object,
morphism and affine-chart interfaces. No statement correction was needed.

Each hypothesis and clause has the following rendering:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| The fixed purity setting | `P : WeilConjectures.PurityFiniteSetting.{u}`; its `field.k` is the fixed algebraic closure field. The coefficient and six-functor data remain the existing setting. |
| A `k`-scheme `Z` | `Z : Scheme.{u}` and its explicit structure morphism `hZ : Z ⟶ Spec (CommRingCat.of P.field.k)`. |
| Separatedness of the structure morphism | `[IsSeparated hZ]`, rather than an unrelated property of the total-space projection. |
| Finite type of the structure morphism | `[LocallyOfFiniteType hZ] [QuasiCompact hZ]`, the recorded interpretation of finite type. |
| Constant rank `c ∈ ℕ` | The external parameter `(c : ℕ)`, including `c = 0`. |
| Total scheme and projection `p : E → Z` | Structure fields `E : Scheme.{u}` and `p : E ⟶ Z`. |
| A locally free `O_Z`-module of constant rank `c` | Fields `𝓔 : Z.Modules` and `[locallyFree : 𝓔.IsFiniteLocallyFreeOfRank c]`, reusing the dependency class. |
| `A = Sym(E)` with the actual degree-one inclusion | The target of `phi` is the existing `VectorBundleZeroSection.scheme Z c 𝓔`; that construction uses `algebraObject`, `SymmetricAlgebraSheaf.algebra` and `SymmetricAlgebraSheaf.inclusion`, with no replacement symmetric-algebra datum. |
| Quasi-coherence and affine-open algebra identification | The reused `VectorBundleZeroSection.algebraObject` uses `quasiCoherentSymmetricAlgebra_affine_comparison`; its `affineChart` composes the canonical relative-Spec chart with the sectionwise symmetric-algebra comparison. |
| Relative Spec with projection `π` | The same existing `scheme` and `VectorBundleZeroSection.π`, constructed from the characterized anti-equivalence of `affine_morphism_relative_spec`. |
| A chosen isomorphism over `Z` and `π ∘ phi = p` | Field `phi : E ≅ ...` is actual chosen data. Field `over_commutes` is `phi.hom ≫ π = p`. No identification of `E` with one canonical representative is imposed. |
| Unique augmentation `epsilon : A → O_Z` killing `j` | Reused `VectorBundleZeroSection.augmentation` and `augmentationToBase`, selected using `exists_quasiCoherentSymmetricAlgebra_core` with the zero linear map. `augmentation_spec` gives uniqueness, vanishing on `inclusion`, and the sectionwise comparison with `SymmetricAlgebra.algebraMapInv`. |
| The corresponding canonical section `bar z` | Reused `VectorBundleZeroSection.zero`, defined by the fully faithful preimage of the augmentation under the relative-Spec anti-equivalence. |
| The chosen bundle's zero section `z = phi⁻¹ ∘ bar z` | `zeroSection V := VectorBundleZeroSection.zero ... ≫ V.phi.inv`. It is determined by the given module and `phi`, never an arbitrary section. |
| `p ∘ z = id_Z` | The first conjunct of `zeroSection_spec`: `V.zeroSection ≫ V.p = 𝟙 Z`. |
| The zero section is a closed immersion | The second conjunct: `IsClosedImmersion V.zeroSection`. Its docstring gives the affine-cover criterion using the augmentation's surjectivity. |
| On every affine open, the section is induced by the ring augmentation fixing constants and killing generators | The final conjunct quantifies `U : Z.affineOpens` and a restriction `zU` to the canonical total-space open. Its first equation identifies this restriction with `U.ι ≫ V.zeroSection ≫ V.phi.hom`. Its second equation identifies the chart composite with `U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom SymmetricAlgebra.algebraMapInv.toRingHom)`. This is the full scheme-map formula, not just surjectivity of a ring map. |
| An étale morphism `u : Z' → Z` | `Trivialization` fields `Z' : Scheme.{u}`, `u : Z' ⟶ Z`, `[etale : Etale u]`; precisely an object of the small étale site. |
| Base-change restriction `E ×_Z Z'` | `pullback V.p u`, with projection `pullback.snd V.p u`, as prescribed in the base-change node's recorded note. |
| Isomorphism to `A^c_(Z')` over `Z'` | Field `tau : pullback V.p u ≅ AffineSpace (ULift.{u} (Fin c)) Z'`, with `tau.hom ≫ (AffineSpace ... Z' ↘ Z') = pullback.snd V.p u`. |

The Noetherian argument passed explicitly to `VectorBundleZeroSection.scheme`, `π`,
`zero` and `affineChart` is the existing
`isNoetherian_of_locallyOfFiniteType hZ`. Its hypotheses follow from the two finite-type
instances and the Noetherian spectrum of the fixed field. Thus the already landed
Noetherian construction is usable without an additional hypothesis on `Z` and without
any new class instance or copied definition. The rank is a parameter of the bundle
type, rather than extra variable-rank data inside a bundle.

Dependencies used, with the interfaces read:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and the
  underlying `FiniteFieldDatum` (including its field instances).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, with `IsSeparated` supplied
  by its public imports. I read `IsSeparated`'s diagonal closed-immersion definition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType` and `QuasiCompact` with their affine/topological definitions.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank` (lines 127–135), whose local generator
  index sets are equivalent to `Fin c`, and `isLocallyFree`.
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`:
  `SymmetricAlgebraSheaf.algebra`, `sectionMap`, `inclusion` and the sectionwise
  symmetric-algebra restrictions.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine`:
  `quasiCoherentSymmetricAlgebra_affine_comparison` (quasi-coherence and bijective
  comparison on every affine open).
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`:
  `exists_quasiCoherentSymmetricAlgebra_core`, the unique extension for any algebra
  sheaf and linear map, specialized to the zero map by the reused augmentation.
- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`:
  `affine_morphism_relative_spec`, specifically its anti-equivalence, object
  characterization, and affine object/morphism charts.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `IsClosedImmersion`, `Scheme.Hom.app_surjective` and
  `IsClosedImmersion.hasAffineProperty`; `HasAffineProperty.iff_of_iSup_eq_top`
  from `.Morphisms.Basic` and `IsAffineOpen.preimage` from `.Morphisms.Affine`
  give the recorded affine-cover criterion. These are available through the reused
  relative-Spec bundle module and the proper-morphism import.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` with its full affine-ring-map
  definition, used on the trivialization's morphism.
- `def-pc-base-change`'s record explicitly prescribes `Limits.pullback`, `pullback.fst`
  and `pullback.snd` for scheme base change; its main declaration `moduleBaseChange`
  concerns module pullback, which this statement does not need or duplicate.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, its canonical projection,
  and the coordinate type `ULift.{u} (Fin c)` prescribed by `def-sbc-affine-space`.
- `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: the canonical `scheme`, `π`,
  `zero`, `augmentation`, `augmentation_spec`, `zero_spec`, `affineChart` and
  `affineChart_spec` above. I checked the current published source with
  `scompile.py --source Sheaf.AlgebraicGeometry.VectorBundleZeroSection` as well as
  the local file. The already landed node `def-asd-vector-bundle-zero-section` is
  added to `stmt_deps` under the rule allowing landed dependencies. Its Zariski
  trivialization type is not used for this item's distinct étale trivialization.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`:
  `isNoetherian_of_locallyOfFiniteType`, read with its full three instance hypotheses.

One-definition search and results (all the following searches actually ran in this turn):

- `msearch.py ... leanfinder "scheme vector bundle relative spectrum symmetric algebra locally free module augmentation zero section"`:
  eight hits, including `SheafOfModules.freeSection`, `ιFree`, and `ModuleCat.tilde`;
  none defines this bundle datum with its chosen total space and étale trivialization.
- `msearch.py ... loogle "SymmetricAlgebra"`: twelve hits including `SymmetricAlgebra`,
  `algebraMapInv`, `lift` and `ι`. These provide ring-level component notions; none
  states the whole item.
- `msearch.py ... grep "VectorBundle|zeroSection|relativeSpec|SymmetricAlgebra" AlgebraicGeometry/`:
  zero hits in the service's Mathlib/AlgebraicGeometry search.
- `msearch.py ... leansearch "vector bundle over scheme symmetric algebra augmentation zero section"`:
  service unavailable, Internal Server Error; this is not recorded as a no-match verdict.
- Direct `rg` searches of the source `WeilConjectures` for the node identifier, vector
  bundle and zero-section terms: no declaration attached to this item. The source has
  affine-space zero sections and explains the lack of a general scheme-bundle API in
  `EtaleCohomology/Purity/Smooth/AffineSpace.lean`.
- Direct `rg` searches of project `lean/Sheaf` found the landed
  `VectorBundleZeroSection` module, owned by the same-as node. I read it in full and
  reuse its construction rather than making another symmetric algebra, relative
  spectrum, augmentation or canonical zero section. Its declarations do not package
  arbitrary chosen total spaces or the étale trivialization required here.
- Direct `rg` checks for the new `PurityVectorBundle` names in Mathlib, the source and
  project Lean returned no pre-existing declaration.

Edge cases: `c = 0` is allowed throughout, using the empty coordinate type `Fin 0`;
the symmetric-algebra augmentation then fixes all scalars, and the zero-dimensional
projection is an isomorphism. There is no nonemptiness assumption on the base or an
étale object's source; the empty scheme and empty affine opens are included.
A trivialization need not have a surjective étale map, nor preserve the zero section:
translation of affine space is a permissible scheme isomorphism in the node's literal
definition. Neither an open-immersion hypothesis nor a zero-preserving condition was
added. No characteristic restriction beyond the fixed purity datum was introduced.

Validation: `scompile.py` compiled the final module both under the sandbox module path
and its library module path, without errors or warnings (4.9 s and 5.0 s in the recorded
run). The local stage-2 text checker also checks the exact main signature, declaration
list, blueprint docstrings, 100-character line limit, and sole `sorry` theorem proof.
No new nodes, dependency modules, statement correction, or disputed statement.

## Second reading by Q32

I independently read the repository node, the sandbox node and module, and the
source blueprint definition at order 1895 together with `sk-def-purity-conv/_section.md`.
The literature is absent from the local mirror, so I read those exact files and
`constructions.tex`, lines 792–864, in the project server's literature checkout by
read-only SSH. Stacks `definition-vector-bundle` (01M2) defines Spec Sym of a
quasi-coherent module over an arbitrary scheme; the blueprint specializes to constant
finite rank and separated finite type over the fixed field. Those restrictions come
from this node, not from an accidental specialization of Stacks. The unit adds the
finite coefficient purity context, but no further restriction on this geometric datum.

My object/hypothesis/conclusion inventory and item-by-item verdict is:

| Node item | Actual Lean rendering and verdict |
| --- | --- |
| Fixed purity setting and its field k | `P : WeilConjectures.PurityFiniteSetting.{u}` and `P.field.k`. Correct: I opened the setting structure and its fixed-field dependency, rather than assuming the names identified the right fields. The unused coefficient data belong to the fixed setting. |
| Z a scheme over k | `Z : Scheme.{u}` and `hZ : Z ⟶ Spec (CommRingCat.of P.field.k)`. Correct: the structure morphism is named explicitly and is the morphism constrained below. |
| Separatedness | `[IsSeparated hZ]`. Correct: Mathlib's class says its diagonal is a closed immersion. No separatedness assumption is imposed independently on the bundle projection. |
| Finite type | `[LocallyOfFiniteType hZ] [QuasiCompact hZ]`. Correct: these are precisely the two clauses recorded by the finite-type node. |
| Arbitrary nonnegative constant rank | `(c : ℕ)`. Correct, with no positive-rank binder. |
| Chosen total scheme and morphism | Structure fields `E : Scheme.{u}` and `p : E ⟶ Z`. Correct: an arbitrary chosen representative is retained. |
| Locally free module of that constant rank | `𝓔 : Z.Modules` and `[locallyFree : 𝓔.IsFiniteLocallyFreeOfRank c]`. Correct: I read the dependency class's open-cover generator data and its equivalences with `Fin c`. |
| Spec of the actual symmetric algebra, with its generator map and quasi-coherence | `phi` targets `VectorBundleZeroSection.scheme Z ... c 𝓔 locallyFree`. Correct: I followed `scheme` through `over` and `algebraObject` to `SymmetricAlgebraSheaf.algebra` and `inclusion`, and opened the sheaf construction and affine-comparison declarations. There is no arbitrary replacement algebra. |
| Relative Spec, projection, and chosen isomorphism over Z | `phi : E ≅ ...` and `over_commutes : phi.hom ≫ VectorBundleZeroSection.π ... = p`. Correct: I read the relative-Spec equivalence's object, morphism, counit-chart and restriction clauses. The direction of both `phi` and the equality is correct. |
| Unique augmentation fixing scalars and killing degree one | The reused `augmentation`/`augmentationToBase` specialize `exists_quasiCoherentSymmetricAlgebra_core` to the zero linear map. Correct: the core theorem is an `∃!`, and `augmentation_spec` explicitly records vanishing, uniqueness, and the sectionwise `algebraMapInv` formula. Choices therefore determine the prescribed object; they are not choices from an unconstrained existence assertion. |
| Canonical relative-Spec zero section, transported to the chosen E | `zeroSection V := VectorBundleZeroSection.zero ... ≫ V.phi.inv`. Correct: `zero` is the fully faithful inverse image of that augmentation, with the counit identification. Composition order is exactly the node's formula. |
| Section identity | First conjunct of `zeroSection_spec`, `V.zeroSection ≫ V.p = 𝟙 Z`. Correct. |
| Closed immersion | Second conjunct, `IsClosedImmersion V.zeroSection`. Correct: the Mathlib closed-immersion class and affine-cover criterion are the recorded dependency interfaces. |
| Formula on every affine open | Final conjunct quantifies every `U : Z.affineOpens` and gives a restricted morphism `zU`. Its inclusion equation is exactly the restriction of `V.zeroSection` after `phi`, and its chart equation is `U.2.isoSpec.hom ≫ Spec.map (...algebraMapInv.toRingHom)`. Correct: this fixes constants and kills all generators, specifies the full scheme morphism, and has the right contravariant direction. The open inclusion is a monomorphism, so the existential `zU` does not weaken the restriction formula. |
| Étale open Z' over Z | `Trivialization` has `Z'`, `u : Z' ⟶ Z`, and `[etale : Etale u]`. Correct: the node explicitly means an object of the small étale site; neither surjectivity nor a Zariski open embedding is required. |
| Restricted bundle and affine-space trivialization over Z' | `tau : pullback V.p u ≅ AffineSpace (ULift.{u} (Fin c)) Z'` and `tau.hom ≫ (... ↘ Z') = pullback.snd V.p u`. Correct: I checked the base-change node's explicit pullback convention and Mathlib's affine-space construction/projection. No preservation of the zero section is asserted by the node or added by the Lean. |

I opened the statements and recorded interfaces of all thirteen original dependencies
and the added, already landed `def-asd-vector-bundle-zero-section`. The latter supplies
canonical Spec Sym, its augmentation, zero section and affine charts, but its
`Trivialization` is a Zariski module frame. It does not package this node's arbitrary
chosen total scheme or its arbitrary étale scheme trivialization. Reusing its
construction while adding these data is appropriate; replacing this whole item by
`existing: true` would lose clauses. No new definition nodes or dependency modules are
part of this delivery, and no statement correction or citer audit is required.

The apparent extra Noetherian requirement is discharged by the actual theorem
`isNoetherian_of_locallyOfFiniteType hZ`, whose only hypotheses are local finite type,
quasi-compactness, and a Noetherian target. The spectrum of `P.field.k` satisfies the
last hypothesis. Every occurrence passes that same derived proof explicitly. There
is no added Noetherian binder and no extra mathematical hypothesis.

Edge cases: `c = 0` uses `Fin 0`, so includes the zero module and zero-dimensional
bundle. The empty base, empty affine open, and empty étale source are allowed; no
nonemptiness assumption appears, and the affine formula also covers the zero section
ring. No characteristic restriction beyond `P` is introduced. The single arbitrary
universe `u` matches `Scheme`, the fixed field, its Zariski module coefficients, and
the small étale objects in the recorded convention; `ULift.{u} (Fin c)` is the required
finite coordinate type in `Type u`. There is no quantification over test schemes in
an independent smaller universe, and no unbound variable or universe.

Independent one-definition searches, using terms different from the first reading:

- LeanFinder: `algebraic bundle total space Spec Sym sheaf and section from zero
  morphism, etale local coordinates`. Eight hits: `AffineSpace.homOverEquiv`,
  `homOfVector`, coordinates and Gamma-Spec declarations. I checked their displayed
  signatures: they concern affine space or general maps to spectra, not this datum.
- Loogle: `AffineSpace.homOfVector` was rejected as an unknown identifier by the
  service, so it is not evidence of absence. The valid `SymmetricAlgebra.lift` query
  returned six ring-level extension lemmas; none packages a scheme vector bundle.
- Logged Mathlib grep: `vector.bundle|augmentation|zeroSection` in
  `AlgebraicGeometry/` returned no hits. Direct `rg` additionally searched upstream
  `WeilConjectures` and project `lean/Sheaf` for vector-bundle, zero-section,
  relative-Spec, augmentation, and bundle-trivialization terms. Upstream has
  `AffineSpace.zeroSection`, and its purity affine-space module explicitly explains
  that the general vector-bundle form is absent. The project has the canonical
  `VectorBundleZeroSection` construction already reused here. Searches for all
  `PurityVectorBundle` names in Mathlib, upstream, project Lean and the upstream name
  index found no existing declaration.

H5/H6/H8/H9 checks: the structures contain actual data and `zeroSection` is an explicit
composite. The sole postponed theorem is `zeroSection_spec`, rendering the properties
in this definition node; it has `by sorry` and a detailed proof docstring tracing the
augmentation, affine comparison, relative-Spec map, closedness, and transport. The node
has no proof steps to omit. Each declaration has its source and exact blueprint tag.
There is no file-local notation, private definition, local instance, extra theorem
proof, overlong Lean line, or hollow construction. I compared `lean.statement` with
the source text before `where` character-for-character; they agree.

Mismatches found: none. I preserved the Lean and node, and appended this independent
review only. Fresh verification through the prescribed `scompile.py` succeeded for
both sandbox and library module paths, in 7.5 s and 7.1 s, without errors or warnings.
