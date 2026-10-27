## Worker report

The module `Sheaf.AlgebraicGeometry.ProjLocalizedGradedComparison` states
`AlgebraicGeometry.Scheme.Modules.existsUnique_proj_localized_graded_comparison`.
Its only postponed proof is this named theorem, with the six-step source proof in
its docstring. All auxiliary definitions have explicit data and use existing
objects. The node is unchanged outside `lean`; no statement correction, new DAG
node, or dependency repair is needed.

Source read: `literature/stacks-project/constructions.tex`, Tag 01NK,
`lemma-invertible-map-into-proj` (lines 3217–3323), particularly the unique extension
from A to A_f and its degree-zero part; Tag 01N8,
`lemma-converse-construction` (lines 2449 onward), division by a generating section
and compatibility on overlaps. The current blueprint ancestor is
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`;
this item is an auxiliary construction, not that unit's statement.

Hypotheses and objects, in the order of the node:

- A nonnegatively graded commutative ring is `{A : Type u} [CommRing A]`,
  `𝒜 : ℕ → AddSubgroup A`, `[GradedRing 𝒜]`. This is an internal grading of
  the same ring, not a degree-one-generation hypothesis.
- The scheme is `{T : Scheme.{u}}`; the line module is `L : T.Modules` with
  `[L.IsInvertible]`, the recorded notion of local rank-one freeness.
- The graded ring map is `ψ : 𝒜 →+*ᵍ sectionRingGrade L`, using the recorded
  direct-sum section ring. `ψ a n` is its degree-n section. For homogeneous a of
  degree n the graded-map condition identifies this with its full homogeneous
  image; no extra choice of a section-ring identification is made.
- U is exactly `projComparisonDomain 𝒜 L ψ`: the supremum over all e, proofs
  of `0 < e`, and `f : 𝒜 e` of `generatingLocus (ψ f.val e)`. The recorded
  generating locus is the nonvanishing open for an invertible module. No cover
  of all T and no quasi-compactness is assumed.
- P is the existing `Proj 𝒜`.
- `r : (projComparisonDomain 𝒜 L ψ).toScheme ⟶ Proj 𝒜` is the fixed map in
  the node. `hr_preimage` identifies the ambient image of each inverse-image
  chart with `generatingLocus (ψ f.val e)`. Since U is an open subscheme of T,
  this is exactly the stated inverse-image equality, with no change of domain.
- `hr_formula` renders `r^sharp(b/f^q) = ψ(b)/ψ(f)^q` for every positive e,
  homogeneous f, every q including zero, and b in degree `q • e`.
  `HomogeneousLocalization.Away.mk` is the actual degree-zero fraction,
  `Proj.awayToSection` its section, and `r.app` the structure-sheaf map.
  `U.ι.appIso` identifies sections on U with ambient sections on their image.
  The displayed equality multiplies the scalar image by the restricted section
  `ψ(f^q)` and sets it equal to `ψ(b)`. Since ψ is a ring map, `ψ(f^q)=ψ(f)^q`.
  On this open that section is a free generator, so the equality is equivalent
  to the node's division formula, including a nilpotent or zero-divisor f.

Conclusions, clause by clause:

- The existential witness `θ : ProjComparisonFamily 𝒜 L ψ r` is the entire
  family over `m : ℕ` of actual module morphisms
  `(tensorPullback r).obj (Proj.twist 𝒜 (m : ℤ)) ⟶ (L.tensorPow m).restrict U.ι`.
  Morphisms are linear by their module-sheaf type; no arbitrary replacement
  for pullback, twists, tensor powers, or restriction is introduced.
- `ProjComparisonChartNormalized` quantifies over every m, positive e,
  `f : 𝒜 e`, q, and `b : 𝒜 (m + q * e)`. `Proj.comparisonFraction` is an
  actual locally homogeneous fraction with value `degreePart.mk b (f^q)`
  at every chart point. Its local-fraction proof is the existing
  `ProjectiveSpectrum.Twist.isLocallyFraction_mk`.
  `projComparisonValue` first uses `tensorPullbackSection`, the actual
  `1 ⊗ s`, then `θ m`, then the existing `restrictAppIso`. The normalization
  multiplies this value by the section `ψ(f^q)` using `tmulSection` and
  `(L.tensorPowAddIso m (q * e)).inv`, and requires the result to equal the
  restricted `ψ(b)`. Multiplication by the displayed free denominator is
  invertible, so this is precisely the required fraction formula in degree m.
- The first conjunct after normalization is restriction compatibility for
  all opens V, W, all inclusions `h : W ≤ V`, and all sections s of the twist.
  On the left s is restricted before comparison; on the right the compared
  value is restricted along the image of `r⁻¹W ≤ r⁻¹V` in T. This includes
  every standard-open restriction and, by restricting both charts to their
  intersection, agreement on overlaps. There is a single global map in every
  degree, not separately chosen local maps.
- The next conjunct sends every global homogeneous `b : 𝒜 m` to its
  restricted ψ-image. Its source is the existing `Proj.unitToTwist b.property`
  applied to 1; the sole `eqToHom` transports the integer index `0+m` to m.
  This is the existing section b/1, not a new global-section construction.
- The unit conjunct uses the existing `Proj.unitToTwistZero` and
  `unitSectionsEquiv`. On every open V and every scalar a it says that the
  degree-zero comparison is the structure-sheaf map `r.app V`, transported
  through the inclusion section isomorphism. It in particular sends 1 to 1.
- The multiplication conjunct quantifies over all m,n,V,s,t and says that
  comparing their product equals tensor multiplication of their compared
  values. `Proj.comparisonProduct` is the actual pointwise product in the
  existing homogeneous-localization fibres; its proof of local-fraction
  membership is the existing `isLocallyFraction_mul`. Thus it is the section
  pairing defining μ^P, without any assumption that μ^P is invertible.
  The other side uses `(L.tensorPowAddIso m n).inv` and `tmulSection`, exactly
  μ^L. This sectionwise formulation is equivalent to the node's equality
  of whole module-sheaf arrows: the canonical tensor-pullback comparison
  identifies `1⊗(s⊗t)` with `(1⊗s)⊗(1⊗t)`; these sections and their scalar
  multiples generate locally, by the inverse-image and tensor sheafification
  constructions. Equality of linear maps on them is equality of the maps.
  No unspecified tensor comparison or stronger hypothesis is supplied.
- The last conjunct quantifies over every other family θ' satisfying just
  the chart normalization and asserts `θ' = θ`. Thus uniqueness is from the
  chart formula alone, and not merely among families also satisfying the
  additional unit and multiplication clauses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, the locally ringed space and actual scheme morphisms.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` and its `Scheme`
  import: `AlgebraicGeometry.Proj`, `projIsoSpec`, `Proj.basicOpen`,
  `Proj.awayToSection`; actual projective spectrum and its scalar charts.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`, `tensorPowAddIso`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules` and
  `.UnitToTwist`: `Proj.twist`, `Proj.unitToTwist`, `Proj.unitToTwistZero`;
  the same twists recorded on def-weil-pbc-proj-twisting-sheaf.
- `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`:
  `InvertibleSectionRing`, `sectionRingGrade`, `sectionRingGradedRing`;
  `SectionRingComponent`, `sectionRingGMul`, and `sectionRingGOne` identify
  the direct-sum degrees, multiplication, and unit used by ψ.
- `WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus`:
  `generatingLocus`, `isFreeGenerator_generatingLocus`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullback`, `tensorPullbackSection`,
  `tensorPullbackSectionAdjunction`; these are the recorded pullback and its
  normalized section map, with no choice of an unconstrained morphism.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded tensor interface;
  the scheme specialization is also exposed by `.Modules.Invertible`, and
  the actual section tensor is `Scheme.Modules.tmulSection` in
  `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`.
- Proof imports: `WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists`,
  `Proj.gradedModuleSheaf_exists`; `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`,
  `Scheme.Modules.exists_tensorPullbackAdjunction`; and
  `Mathlib.Topology.Sheaves.SheafCondition.Sites`,
  `TopCat.Sheaf.restrictHomEquivHom`, `extend_hom_app`, `hom_ext`,
  `isIso_iff_isIso_basis`. Their signatures and docstrings were read, and
  their modules are ordinary proof imports.

Edge cases checked before writing and on second reading:

- U empty (including no positive-degree elements, or all ψ(f) vanishing):
  its module maps are unique and every section equality takes place in a
  zero section module. No nonemptiness binder occurs.
- Empty T and the zero graded ring: same empty-domain case, valid throughout.
- q=0: the denominator is `ψ(1)` in degree zero; the normalization is b/1,
  with no positive-power premise.
- m=0, n=0: the family, product, and unit formulas all include these degrees.
- A weighted ring k[x] with deg x=2: there is no degree-one generation
  premise; `Proj.twist 𝒜 1` may be zero and θ_1 may be zero. No inversion
  of twist multiplication or global invertibility of a twist is assumed.
- Zero-divisor or nilpotent f: fractions are the actual localization
  fractions, and the formula cancels only the generator in the target on
  its generating open; it never cancels f in A.
- Infinite charts and a non-quasi-compact T: U uses the full supremum and
  the statement imposes no finiteness or quasi-compactness restriction.

Searches (2026-10-24):

- `msearch.py ... leanfinder` with query "A graded ring map into the section
  ring of an invertible sheaf gives a unique multiplicative comparison from
  pulled back Proj twists by homogeneous fractions": 8 hits, including
  `ProjectiveSpectrum.Proj.awayToΓ`, `Proj.awayMap_awayToSection`, and
  `Proj.fromOfGlobalSections_*`. These concern scalar chart maps, not this
  family to powers of a general line module.
- `msearch.py ... leansearch` with query "graded localization line bundle
  section ring Proj twist multiplicative comparison": 8 scalar localization
  and chart-map hits, no matching comparison theorem.
- `msearch.py ... loogle 'AlgebraicGeometry.Proj, ModuleCat'`: no hits.
- `msearch.py ... grep 'fromOfGlobalSections|twistTensor|twist.*[Cc]omparison'
  AlgebraicGeometry/ProjectiveSpectrum`: 5 hits on `fromOfGlobalSections`,
  which constructs a morphism from a map into ordinary global functions.
- `msearch.py ... grep 'sectionRingGrade|comparisonFraction|comparisonProduct'
  AlgebraicGeometry`: no Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for localized/graded
  comparisons, Proj comparisons, twist multiplication and section-ring maps:
  the related `ProjCanonicalMapTwistComparison` only asserts sufficiently
  divisible twist isomorphisms under quasi-compactness and a cover of all Z;
  `ProjTwistGluedComparison` is a projective-line/glued-data theorem;
  the tensor-power homogeneous-section modules concern polynomial Proj over
  a field. None is this general normalized family. The generic
  `twistTensorIso` needs a degree-one cover and cannot be used here.
- Exact item-id search in `lean/WeilConjectures` and `lean/Sheaf`: no hits.
  Exact searches for the new full helper names in Mathlib, both project
  roots and `dag/lean_names_upstream.json`: no conflicting declarations.

Validation: prescribed `scompile.py Q35 lem-trf-proj-localized-graded-comparison`
compiled the complete file in sandbox and library module modes, with no errors
or warnings (8.3 s and 5.4 s reported on the successful run). The initial probes
required an explicit integer cast type and an explicit `Scheme.Modules.Hom.app`
for the degree-zero map; both elaboration issues were fixed. There are no `#check`
commands, private helpers, local notation, local instances, or auto-bound variables.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q35

I reopened the node and the final complete module for a separate clause-by-clause
pass; no other agent was started, as required by the dispatcher's explicit brief.
I checked all objects and hypotheses against the list above. In particular the
family uses the recorded tensor pullback, the canonical r is assumed only with
its stated preimage and scalar fraction properties, normalization includes every
positive e and q=0, and uniqueness quantifies over every chart-normalized family.
The multiplication equation is on all opens and all pulled-back pure tensors,
not just global homogeneous generators, so it detects the full sheaf-map equality.
The restriction clause supplies the overlap clause without an additional gluing
choice. Degree zero uses the structure map and the actual twist unit. I checked
that no assumption of degree-one generation, invertible twists, nonemptiness,
compactness or a field was introduced. No mismatch remained after the two compiler
elaboration fixes described above; no mathematical statement change was needed.
