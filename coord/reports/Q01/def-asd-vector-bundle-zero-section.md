## Worker report

The module `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` defines
`AlgebraicGeometry.VectorBundleZeroSection.scheme`, the canonical relative
spectrum of the constructed symmetric-algebra sheaf, together with its
projection, augmentation, zero section, affine charts, frames, and coordinate
maps. All auxiliary declarations are listed in `lean.declarations` and belong
to the clauses of this same definition node. No new nodes, dependency modules,
or statement correction are needed; the node copy changes only `lean`.

The original blueprint definition was read in the source archive at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/def-asd-vector-bundle-zero-section.md`.
It specifies a Noetherian base, constant finite rank, `Spec Sym(F)` without
dualization, the augmentation section, Zariski module frames, and invertible
matrix changes of frame. Stacks `constructions.tex`,
`definition-vector-bundle` (01M2), was also read. Its more general
quasi-coherent input is restricted here by the blueprint's own hypotheses.

Each hypothesis and clause is rendered as follows (declaration names below
are in `AlgebraicGeometry.VectorBundleZeroSection`).

| Node clause | Lean rendering |
| --- | --- |
| Scheme S, Noetherian in the finite-affine-cover sense | `S : Scheme.{u}` and `[IsNoetherian S]` on the bundle, projection, zero section, and all geometric assertions. Mathlib's `isNoetherian_iff_of_finite_iSup_eq_top` identifies this class with the stated finite cover by spectra of Noetherian rings. |
| Natural rank d and locally free module of that constant rank | `(d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]`. This is the dependency's recorded class, without a separate quasi-coherence assumption. |
| Explicit symmetric algebra and generator j | `SymmetricAlgebraSheaf.algebra F` and `.inclusion F`; `algebraObject` supplies its quasi-coherence using local freeness and the recorded affine comparison. |
| Relative affine scheme, projection, algebra identification | `over`, `scheme`, `π`, and `algebraIso`. The object `over` lies in the full subcategory on `IsAffineHom`. It is the inverse image of `algebraObject` under the anti-equivalence of `affine_morphism_relative_spec`, whose functor is calibrated to the structure algebra and canonical section maps. The counit gives `algebraIso`. |
| Spec Sym of affine sections, structural constants inclusion, and gluing by restriction | `affineChart` is the spectrum map of the sheafification unit followed by `algebraIso`. `affineChart_spec` states it is an isomorphism and identifies its projection with the constants inclusion. `affineChart_naturality` identifies its change on each affine inclusion with the spectrum of `SymmetricAlgebraSheaf.restriction`. |
| Unique augmentation killing degree-one generators | `augmentation` is selected from the recorded `∃!` symmetric-algebra universal property for the zero linear map. `augmentation_spec` gives its generator formula, uniqueness, and its sectionwise equality with `SymmetricAlgebra.algebraMapInv`. The latter fixes scalars. The under-category morphism also contains the compatibility with the structural inclusion. |
| Corresponding S-morphism z | `augmentationToBase` is the same unique zero-generator extension with target the anti-equivalence's structure algebra for the identity S-scheme. `zero` is the fully faithful inverse image of this morphism after the counit. This fixes the section canonically; no arbitrary retraction is an input. |
| Identity πz = id and closed immersion | `zero_spec` states `zero S d F ≫ π S d F = 𝟙 S` and `IsClosedImmersion (zero S d F)`. |
| Affine zero section induced by augmentation | The final clause of `affineChart_spec` identifies `zeroRestricted ≫ affineChart` with `Spec.map SymmetricAlgebra.algebraMapInv`, after the affine base's `isoSpec`. This augmentation is surjective since it fixes scalars, giving the quotient-by-kernel closed-subscheme interpretation. |
| Trivialization on a Zariski open V | `Trivialization S d F V` is precisely `F.restrict V.ι ≅ SheafOfModules.free (ULift (Fin d))`. |
| Induced affine-space coordinates and zero origin | `frameSection` evaluates the inverse module frame on each standard basis section; `coordinate` is its image under j and `algebraIso`. `trivializationMap` is `AffineSpace.homOfVector` of these coordinates. `trivializationMap_spec` states it is an isomorphism over V and sends the restricted zero section to `AffineSpace.zeroSection`. |
| Invertible matrix on overlaps and the stated, nondual coordinate substitutions | `transition_spec`, for any two frames on a common open W, gives matrices G,H over `Γ(S,W)` with `G*H=1`, `H*G=1`, `e'_j=∑ᵢ Gᵢⱼ • eᵢ`, and `x'_j=∑ᵢ π*Gᵢⱼ * xᵢ`. Applying it to the restrictions of frames on their overlap is the node's overlap clause; no affineness of W is assumed. |

The data definitions have no `sorry`. The anti-equivalence choice is from the
relative-spectrum theorem with its specified forward functor, section maps,
and compatible affine charts. This characterizes its inverse up to the
algebra-compatible isomorphism appropriate for relative Spec. The augmentation
choices are from unique extensions. No object is chosen from an unconstrained
existence assertion. The only proof used while defining `zeroRestricted` is
its named section theorem `zero_spec`.

Six theorem proofs are deliberately `sorry`, each recording a property already
stated in this node: `augmentation_spec`, `zero_spec`, `affineChart_spec`,
`affineChart_naturality`, `trivializationMap_spec`, and `transition_spec`.
Their docstrings give the source and full natural-language proof, including
which dependency constructs each map. This is stage 2; these properties are
stated, not claimed proved.

All eleven statement dependencies were read, including the full signatures
and docstrings of their recorded declarations or Mathlib matches:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`, used by the imported Noetherian scheme API.
- `def-amb-finite-locally-free-module`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`,
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`;
  its scheme-frame interface is
  `Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`.
- `lem-weil-pbc-symmetric-algebra-sheaf-construction`:
  `SymmetricAlgebraSheaf.algebra`, `.inclusion`, `.sectionMap`, and `.restriction`,
  `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`.
- `lem-weil-pbc-quasi-coherent-symmetric-algebra-affine`:
  `quasiCoherentSymmetricAlgebra_affine_comparison`,
  `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine`.
- `lem-weil-pbc-quasi-coherent-symmetric-algebra-core`:
  `exists_quasiCoherentSymmetricAlgebra_core`,
  `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`.
- `lem-weil-pbc-affine-morphism-relative-spec`:
  `affine_morphism_relative_spec`,
  `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`.
- `def-weil-affine-spectrum`: `Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-closed-immersion`: `IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-sbc-affine-space`: `AffineSpace`, `.over`, and its polynomial charts,
  `Mathlib.AlgebraicGeometry.AffineSpace`; the actual standard zero section is
  `AffineSpace.zeroSection` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`.
- `lem-weil-pbc-symmetric-algebra-free-module-polynomial`:
  `SymmetricAlgebra.equivMvPolynomial` and `.equivMvPolynomial_ι_apply`,
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`, imported for the frame-chart
  property and its specified proof.

Edge cases were checked before completing the signatures. Rank zero is allowed:
the standard basis and matrix index are empty, Sym(0)=R, and the section and
projection are identities up to the canonical relative-spectrum identification.
The empty scheme is included; there is no nonempty-cover or nontrivial-ring
hypothesis. A nonreduced Noetherian affine base gives the usual polynomial
augmentation and is not excluded. All frame and transition formulas apply to
nonaffine opens and intersections, using global sections of the sheaf, not an
assumption that intersections of affine opens are affine. Universes are
explicit, and affine-space coordinates use `ULift.{u} (Fin d)` as prescribed by
the recorded affine-space dependency.

Searches actually performed in this worker session (see `searches.jsonl`):

- `msearch.py ... leansearch "A finite locally free sheaf over a scheme defines its relative symmetric-algebra spectrum and augmentation zero section"`
  returned `UNAVAILABLE`, with `Internal Server Error`; no absence verdict is
  inferred from that unavailable service.

- `msearch.py ... leanfinder "relative Spec symmetric algebra locally free sheaf zero section"`
  returned eight ring-level symmetric-algebra, affine-space, and spectrum facts,
  including `SymmetricAlgebra.algebraMapInv`; none constructs the scheme bundle.
- `msearch.py ... loogle "SymmetricAlgebra"` returned twelve ring-module
  symmetric-algebra declarations; the augmentation and polynomial comparison
  are useful components, not an existing statement of the entire node.
- `msearch.py ... grep "vector.?bundle|zero.?section|relative.?spec|symmetric.?algebra" AlgebraicGeometry`
  returned zero hits.
- `rg` in `WeilConjectures` for vector bundles, zero sections, relative Spec,
  and symmetric algebras, and the exact blueprint-id `grep -rn`, found no
  declaration implementing this item. The upstream affine-space zero section
  and `NormalConeData` are different notions; upstream explicitly notes the
  missing general scheme vector-bundle construction.
- `rg` in `lean/Sheaf` found the recorded symmetric-algebra/relative-spectrum
  components and results about locally free modules, but no general vector
  bundle scheme or this node. The names of all added declarations were checked
  against the source and Mathlib declaration names by the text preflight.

The earlier tool failure concerned an unchanged stage-1 node. This delivery
preserves the reviewed split and adds its missing `lean` record and source
module. It does not re-split the node. The dry run is required before handoff;
the independent second reader supplies the second-reading section afterwards.

Validation: the final module compiled cleanly through `scompile.py` in both
sandbox and actual library-module mode (25.5 s and 27.6 s, with the default
60-second limit). The local stage-2 text checks report no faults, all module
lines fit within 100 characters, and comparison with the shared node confirms
that `lean` is the only changed field.

## Second reading by Q01

I independently read the sandbox node and the complete module, then compared them
with the archived blueprint definition at order 1968 and Stacks
`constructions.tex`, `situation-relative-spec`, `definition-relative-spec`,
`lemma-spec-properties`, `section-vector-bundle`, and
`definition-vector-bundle` (01M2). The local shared clone omits these untracked
literature files; I read the source copies under the launcher's literature
archive. The blueprint explicitly assumes a Noetherian scheme and constant
finite rank and uses Sym(E), without a dual. Stacks assumes only a scheme and a
quasi-coherent algebra/module in the relevant sections, so it contributes no
hidden separatedness, field, characteristic, or nonemptiness hypothesis.
The blueprint's narrower assumptions are retained. There is no
`statement_change`, and no correction or citer audit is needed.

Here is my list of the node's objects, hypotheses and clauses, matched against
what the file actually declares. Names are in
`AlgebraicGeometry.VectorBundleZeroSection` unless qualified otherwise.

| Object, hypothesis or clause of the node | Lean rendering and verdict |
| --- | --- |
| A scheme S, with a finite affine cover by Noetherian rings | `S : Scheme.{u}` and `[IsNoetherian S]` on `over`, `scheme`, `π`, `zero` and their geometric properties. I read Mathlib's class and `isNoetherian_iff_of_finite_iSup_eq_top`: locally Noetherian plus compact is exactly the stated finite-affine-cover condition. Pass. |
| A natural number d and an O_S-module F locally free of constant rank d | `(d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]`. I read the recorded class and the two scheme-module open-cover equivalences, including `exists_restrict_iso_free`; this is constant rank on a Zariski cover, with zero rank permitted. Quasi-coherence follows from local freeness, without an added assumption. Pass. |
| The constructed symmetric algebra A and generator j | `algebraObject` uses the dependency's `SymmetricAlgebraSheaf.algebra F` and its quasi-coherence theorem; all generator occurrences use `.inclusion F`. I read their actual sheafification, section-map and restriction definitions. There is no private replacement. Pass. |
| E = relative Spec of A, affine over S, with projection π | `antiEquivalence` selects the recorded structure-algebra anti-equivalence; `over` is its inverse on `algebraObject`, `scheme` its underlying scheme, and `π` its structural map. The full subcategory contains the affine-morphism property. `algebraIso` is the counit followed by the dependency's specified object identification, so it identifies A with π_*O_E as O_S-algebras. Pass. |
| Affine pieces Spec Sym_R(F(U)) with structural constants map | `affineChart` is defined from `toSpecΓ`, the sheafification unit and `algebraIso`. `affineChart_spec` asserts its invertibility and the equation with `Spec.map (algebraMap R ...)` and the affine base's `isoSpec.inv`. Thus its source is exactly π⁻¹U and its projection is the intended constants inclusion. Pass. |
| Gluing by symmetric-algebra restriction maps | `affineChart_naturality`, for every pair of affine opens U ≤ V, equates restriction followed by the V chart with the U chart followed by `Spec.map (SymmetricAlgebraSheaf.restriction ...)`. The variance is correct: the ring map goes V to U and Spec goes U to V. Pass. |
| The unique O_S-algebra augmentation ε killing j | `augmentation` selects the unique extension of the zero module map from `exists_quasiCoherentSymmetricAlgebra_core`. `augmentation_spec` asserts vanishing on every open's generators, uniqueness among algebra maps, and the sectionwise formula with `SymmetricAlgebra.algebraMapInv`. Its under-category type supplies ε composed with the structural inclusion = identity. Pass. |
| The corresponding S-morphism z, rather than an arbitrary section | `augmentationToBase` is the same unique zero-generator extension into the structure algebra of `baseObject`. `zero` uses the fully faithful inverse image of the counit followed by that extension. I read the dependency's object and morphism calibrations: they fix the forward functor to direct-image structure algebra and the usual pullback on sections. Thus this is the augmentation's morphism, with the required contravariance. Pass. |
| π composed with z = identity, and z a closed immersion | `zero_spec` states `zero S d F ≫ π S d F = 𝟙 S ∧ IsClosedImmersion (zero S d F)`. The order is Lean's left-to-right composition. I read Mathlib's closed-immersion class; it is the required closed embedding with surjective stalk maps. Pass. |
| On affine pieces z is Spec of the scalar-fixing, generator-killing augmentation, hence the quotient by its kernel | `zeroRestricted` and the last clause of `affineChart_spec` identify z with `Spec.map SymmetricAlgebra.algebraMapInv`, after the affine-base identification. This is the actual surjective ring map, so the quotient closed-subscheme description follows from the standard affine criterion; no arbitrary ideal or immersion replaces it. Pass. |
| A Zariski trivialization on any open V is F restricted to V ≅ O_V^d | `Trivialization S d F V` is precisely the module-sheaf isomorphism to `SheafOfModules.free (ULift.{u} (Fin d))`. Neither V nor its intersections are assumed affine. Pass. |
| Its induced E restricted to V ≅ affine d-space over V | `frameSection` uses the inverse module frame on the standard basis, `coordinate` applies j and the structure-algebra identification, and `trivializationMap` uses `AffineSpace.homOfVector` of these coordinates. `trivializationMap_spec` states invertibility and the equation over V. I read both Mathlib's affine-space definition and its morphism-by-coordinates interface. Pass. |
| In frame coordinates z is x_1 = ... = x_d = 0 | The final clause of `trivializationMap_spec` identifies the composite with the existing `AffineSpace.zeroSection`. I read its definition: `homOfVector (𝟙 V.toScheme) 0`. Pass. |
| Overlap frames differ by an invertible d-by-d matrix of regular functions | `transition_spec` quantifies over arbitrary W and both frames on W, then gives G,H over `S.presheaf.obj (op W)` with `G * H = 1` and `H * G = 1`, and `e'_j = ∑ i, G i j • e_i`. Restricting any two original frames to their overlap gives exactly this case. Pass. |
| Coordinate substitutions use the same coefficients x'_j = ∑ i g_ij x_i | The final clause of `transition_spec` states this formula, pulling coefficients to π⁻¹W through the restricted projection's `appTop` and the canonical open/global-sections identification. Matrix indices are i,j in the same order as the node. There is no dual or transposed substitution. Pass. |

All eleven statement dependencies were opened as node records and actual source
signatures. Besides those discussed above, I checked `Scheme`/`Scheme.Hom`,
`IsNoetherianRing`, `Spec`/`Spec.map`, and
`SymmetricAlgebra.equivMvPolynomial` together with its generator formula.
The relative-Spec theorem provides object, morphism and open-restriction
characterizations; it is not a bare existence of an unrelated equivalence.
The symmetric-algebra universal property has `∃!` for the prescribed generator
map, so both augmentation choices determine the needed algebra morphism.
All dependency interfaces are usable as recorded. This delivery has no new
nodes or dependency modules requiring H12/H13 repairs.

Edge cases: d = 0 has empty `Fin d`, empty sums and the unique mutually inverse
empty matrices; Sym(0) gives the base and affine zero-space has its canonical
identity identification. The empty scheme and empty opens remain allowed, as
do zero section rings and the zero module; there is no `Nonempty`,
`Nontrivial`, positive-rank or inhabited-cover binder. Arbitrary characteristic,
nonreduced Noetherian bases and nonaffine overlaps are included. The one
explicit universe `u`, `S.Modules` and `ULift.{u} (Fin d)` follow the recorded
scheme and affine-space size conventions. No test-scheme quantifier or hidden
universe equation excludes a case. Every variable is bound, with
`autoImplicit false`.

I performed fresh searches with words different from the first reader's main
query (recorded by `msearch.py` in `searches.jsonl`):

- LeanFinder: `augmentation ideal symmetric algebra total space finite locally free module scheme`.
  Eight hits concerned ring-level symmetric algebras, bases and smooth algebra;
  none defined this total-space scheme and its zero section.
- Loogle: `SymmetricAlgebra.algebraMapInv`. Four hits gave the existing ring
  augmentation, its scalar left-inverse and zero-generator formulas, and the
  bialgebra counit identification. These are components used here, not a
  scheme-level duplicate.
- LeanSearch: `Relative spectrum of a finite locally free module symmetric algebra with its augmentation section`.
  The service returned `UNAVAILABLE: Internal Server Error`; I infer no absence
  from that failure.
- The search wrapper's grep for `SymmetricAlgebra|VectorBundle|zeroSection` in
  AlgebraicGeometry returned no hits. I also searched the local Mathlib,
  complete `WeilConjectures` and project `lean/Sheaf` trees myself with `rg`
  for augmentation, total space, vector bundle, relative spectrum and Spec Sym.
  I opened the relevant upstream affine-space zero section, normal-cone datum,
  deformation datum and purity comments, and the project's Frobenius
  vector-bundle kernel and relative-spectrum interfaces. The former treat
  affine space or unspecified geometric data; the latter are the existing
  building blocks used by this file. None constructs Spec Sym(F) with this
  section and frames. `VectorBundleLineSubbundle` concerns a module-sheaf
  subbundle, not the associated scheme. The DAG's
  `def-pur-vector-bundle-zero-section` has no Lean declaration and has the
  separate narrower purity setting; it supplies no existing implementation.
  Searches for the added namespace and blueprint id in upstream source and
  the upstream names table found no collision.

H5/H6/H8/H9 review: all definitions have real data. Choices are from the unique
symmetric-algebra extension or the calibrated relative-Spec equivalence, whose
inverse is determined up to the algebra-compatible isomorphism used downstream.
The proof needed by `zeroRestricted` invokes the named `zero_spec`; it contains
no anonymous sorry. Exactly six named theorem bodies are `sorry`, each stating
clauses of this definition node and carrying a source/blueprint docstring with
the construction and proof steps. All other declarations and the module have
source/blueprint docstrings. There are no private notions, file-local notations
or instances, extra axioms, or lines over 100 characters. Imports supply the
actual dependency interfaces and the basis-polynomial proof ingredient.
The stored `lean.statement` is exactly the signature returned by
`tools/stage2_delivery.py signature`; `lean` is the only changed node field.

No mathematical or interface mismatch was found, so I left the correct module
and node record unchanged. My change is this independent second-reading
section. Validation through the required `scompile.py` wrapper completed
cleanly, both in sandbox mode (19.8 s) and actual module mode (18.9 s), with no
warnings or errors. Delivery preflight and dry run follow this reading.
