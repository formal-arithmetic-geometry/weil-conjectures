## Worker report

The delivery states `AlgebraicGeometry.Proj.commonDegreeTwistInvertible` in
`Sheaf.TraceFormula.ProjCommonDegreeTwistInvertible`. Its only proof is `sorry`.
There are no new definitions or dependency repairs, and the natural-language node is unchanged.

Hypotheses and clauses, matched to the node:

- The nonnegatively graded commutative ring is `{A σ : Type u} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]`.
  The scheme is the recorded Mathlib `AlgebraicGeometry.Proj 𝒜`.
- The quasi-compact open subscheme is `(V : (Proj 𝒜).Opens)
  [CompactSpace V.toScheme]`; its inclusion is `V.ι`, which has Mathlib's
  `IsOpenImmersion` instance. Thus the exact open subscheme is used, rather than
  another scheme equipped with an arbitrary morphism.
- The finite list is `(I : Type v) [Finite I]`, `(f : I → A)`, and `(d : I → ℕ)`.
  The binders `hf : ∀ i, f i ∈ 𝒜 (d i)` and `hd : ∀ i, 0 < d i` give precisely
  homogeneity and positive degrees. An arbitrary finite type is equivalent to a
  finite list for this assertion and includes the empty list.
- The covering assumption is `hcover : V ≤ ⨆ i, basicOpen 𝒜 (f i)`.
  It does not require the standard opens to be contained in V.
- The positive common multiple is `(e : ℕ) (he : 0 < e)` and
  `hdiv : ∀ i, d i ∣ e`. No generation-in-degree-one assumption is imposed.
- `W : (Proj 𝒜).Opens` and `hW` describe W_e by the node's explicitly equivalent
  union of `D_+(ab)`, with `α = β + e`. The degree β may be zero, so the crucial
  choice b = 1 is included. This is the same encoding as the recorded statement
  `Proj.twistSectionBasicOpen`; no new invertibility-locus notion is introduced.
- The first conjunct is `V ≤ W`, a conclusion, not a hypothesis.
- The integer-twist conjunct states invertibility of every restricted O(ne).
  The next conjunct gives each binary multiplication morphism with `IsIso μ`.
  Its action on `Scheme.Modules.tmulSection s t` over every open Q equals the
  pointwise product of the two sections in each homogeneous localization.
  `restrictAppIso V.ι Q` is the recorded canonical identification of restricted
  sections with sections on `V.ι ''ᵁ Q`. The formulas are precisely ordinary
  multiplication of local homogeneous fractions, not a chosen abstract iso.
  These two conjuncts unpack the defining property of W_e on V.
- The next conjunct states, for each positive natural k, that the restricted
  `twist 𝒜 (Int.ofNat (e * k))` is invertible, the requested O_V(ek).
- The last conjunct gives a family `μ k` from the existing
  `((twist 𝒜 (e : ℤ)).restrict V.ι).tensorPow k` to O_V(ek), with `IsIso (μ k)`
  for positive k. At zero its unit section has value 1 at every point. At k+1,
  its value on `tmulSection s t` is the first section times the image of t
  under `μ k`, for every local section t of the preceding tensor power.
  Linearity and local generation by pure tensors make these formulas a unique
  characterization of canonical iterated multiplication. The zero component
  merely specifies the starting unit map for this recursion. The upstream
  tensorPow uses M tensor (M tensor ... tensor unit), canonically identified
  with the node's positive tensor powers by the unitors and associators.

Dependency declarations read and used:

- `def-pc-proj`: Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme,
  `AlgebraicGeometry.Proj`, `AlgebraicGeometry.projIsoSpec`; standard-open
  predicate `ProjectiveSpectrum.basicOpen` in ProjectiveSpectrum.Topology,
  used on the scheme through `AlgebraicGeometry.Proj.basicOpen`.
- `def-weil-pbc-quasi-compact-scheme`: Mathlib.Topology.Defs.Filter,
  `CompactSpace`, applied to V.toScheme. This imposes no Hausdorff condition.
- `def-weil-open-immersion`: Mathlib.AlgebraicGeometry.OpenImmersion,
  `AlgebraicGeometry.IsOpenImmersion`, supplied by V.ι.
- `def-weil-pbc-proj-twisting-sheaf`:
  WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules,
  `AlgebraicGeometry.Proj.twist`, the actual sheaf of local homogeneous fractions.
- `def-sc-invertible-module`:
  WeilConjectures.AlgebraicGeometry.Modules.Invertible,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; also its existing tensorObj
  and tensorPow. No separate invertibility predicate is used.
- `def-pur-sheaf-tensor-product`: its current recorded module
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses is publicly
  imported. Scheme.Modules.tensorObj and tensorPow use the same existing
  sheafification tensor monoidal structure. The existing TensorSection module
  supplies Scheme.Modules.tmulSection and unitSectionsEquiv.
- The proof-only imports are the two recorded modules
  Sheaf.AlgebraicGeometry.ProjStandardOpenProperties and
  Sheaf.AlgebraicGeometry.ProjTwistSectionBasicOpen. Their standard-open basis
  and union characterization are described in the proof docstring. Importing
  the downstream ProjQcOpenTwistAmple merely to reuse its tuple helper would
  create a dependency cycle; the statement instead uses existing binary tensor
  sections and recursively characterizes the multiplication family directly.

Edge cases checked before finalizing the signature:

- Empty I is permitted: the cover forces V empty. Compactness, containment,
  local invertibility, and all isomorphism assertions remain valid there.
- Empty Proj, including the zero ring or a ring concentrated in degree zero,
  is permitted. No nonempty or nontrivial assumptions were added.
- A zero or nilpotent f_i gives an empty standard open and can be redundant;
  no nonzeroness assumption was imposed. The declared homogeneous degree,
  including for zero elements, is the d_i used in divisibility.
- e = 1 is permitted; e = 0 and d_i = 0 are excluded exactly as in the node.
- The W_e union includes β = 0, α = e. No positive-degree condition was added
  to b. Integer n,m include zero and negative twists as required by the
  defining property of W_e; the requested power assertion quantifies k > 0.
- I has an independent universe v, so the finite index set is not restricted
  to the ring universe. All Lean universes and variables are bound explicitly.

Source check: read constructions.tex, lemma-where-invertible and its proof,
lemma-principal-open, and lemma-ample-on-proj including all seven clauses and
its proof. The source label lemma-where-invertible is Tag 01MU, whereas the
node's source record calls it 01MS (which is lemma-when-invertible). This
inherited citation typo does not affect the mathematical statement; the
module cites 01MU and 01MW and does not change the node's source field.
The natural-language proof is reproduced in five steps in the theorem docstring.
No STATEMENT-DISPUTED issue or statement correction is needed.

Searches made:

- msearch.py grep: `twist|IsInvertible` in `AlgebraicGeometry/ProjectiveSpectrum`. Result: 0 hits; no hits. No exact theorem.
- msearch.py loogle: `"Proj", "twist"`. Result: 0 hits; no hits. No exact theorem.
- msearch.py leanfinder: `For a finite cover by positive degree homogeneous standard opens in Proj, a common positive multiple of the degrees makes restricted twists invertible with canonical tensor multiplication isomorphisms`. Result: 8 hits; AlgebraicGeometry.Proj.openCoverOfISupEqTop, AlgebraicGeometry.Proj.affineOpenCoverOfIrrelevantLESpan, AlgebraicGeometry.Proj.fromOfGlobalSections_morphismRestrict, AlgebraicGeometry.Proj.awayι. No exact theorem.
- msearch.py leansearch: `Common positive degree twists on quasi compact open of Proj invertible canonical tensor multiplication`. Result: 8 hits; ProjectiveSpectrum.basicOpen_pow, AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf, ProjectiveSpectrum.basicOpen_eq_union_of_projection, AlgebraicGeometry.Proj.fromOfGlobalSections_resLE. No exact theorem.
- Direct rg of Mathlib, upstream WeilConjectures, and lean/Sheaf for
  `commonDegreeTwistInvertible|common_degree.*invertible`: no existing declaration.
- Direct rg of the item id in upstream WeilConjectures: no match.
- Direct rg for Proj twist tensor declarations found the upstream
  `Proj.isInvertible_twist` and `Proj.nonempty_tensorObj_twist_iso`; read their
  full signatures and docstrings. They require a global degree-one cover and
  the latter only gives Nonempty of an unspecified iso, so neither states this
  node. Existing ProjectiveSpace declarations concern a different scheme.
- Direct rg in lean/Sheaf found the downstream ProjQcOpenTwistAmple and the
  sibling ProjTwistSectionBasicOpen. Read both: the former asserts an existential
  ample common degree, not this prescribed common-degree result; the latter
  concerns nonvanishing loci and bases, not invertibility/tensor maps.

Validation: scompile.py compiles this delivery file separately against the published
library. The final checked file has no errors and no warnings. Only the named
main theorem is postponed; there are no definitions with postponed data.

## Second reading by Q82

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
