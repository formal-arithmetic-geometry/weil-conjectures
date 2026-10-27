## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFlatCartierSupport` states
`AlgebraicGeometry.Scheme.Modules.relative_flat_cartier_support`, with one whole-proof
`sorry` and no new definitions. The accepted node statement and its dependencies are
unchanged; only its `lean` record is added. No dependency repair or new node is needed.

Hypotheses and clauses, matched against the node:

- Any morphism of schemes: `{Y T : Scheme.{u}} (g : Y ⟶ T)`. The explicitly bound
  universe `u` is arbitrary; no flatness, affineness, separatedness, finite type or
  Noetherian condition is imposed on `g`, `Y` or `T`.
- Effective Cartier divisor: `(D : T.IdealSheafData) (hD : D.IsInvertible)`.
  This uses the recorded effective-Cartier predicate, whose actual definition is
  that each point has an affine neighbourhood with a regular principal ideal.
  `D.subscheme` and its canonical closed immersion `D.subschemeι` are the divisor,
  with underlying space `D.support`. This is the usual ideal-sheaf presentation of
  a closed subscheme, not a different object or an extra invertibility assumption.
- A quasi-coherent O_Y-module: `(M : Y.Modules)` and
  `[SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M]`. The recorded
  `pqf-def-coherent` module publicly exposes this predicate. The finite-type
  conjunction declared in that module is not used: the item only assumes
  quasi-coherence. Specifying `R` explicitly resolves universe inference without
  restricting any universe.
- Flat over T through g: `(hflat : M.IsFlatOver g)`, using exactly the recorded
  affine-pair definition. It means flatness of the sections module after restricting
  scalars along the scheme morphism, not flatness of Y over T.
- Every open H and injectivity of restriction to H minus the inverse-image support:
  the first conjunct is `∀ H : Y.Opens, Function.Injective (M.presheaf.map ...)`.
  Its arrow is `(homOfLE (inf_le_left : H ⊓ g ⁻¹ᵁ D.support.compl ≤ H)).op`.
  `D.support.compl` is the open complement of the divisor, its inverse image is the
  complement of `g⁻¹|D|`, and intersection with H is exactly the open in the node.
  `M.presheaf.map` is the actual restriction on sections, not an arbitrary map.
- Every affine base chart V and affine source chart W inside g⁻¹V:
  `∀ (V : T.affineOpens) (W : Y.affineOpens) (e : W.1 ≤ g ⁻¹ᵁ V.1)` in the
  second conjunct. These are all affine opens, with their canonical spectrum
  identifications. The chart ring A is `Γ(T, V.1)`.
- A non-zero-divisor local Cartier equation:
  `(a : Γ(T, V.1)), a ∈ nonZeroDivisors Γ(T, V.1) →
  D.ideal V = Ideal.span {a} → ...`. Both the regularity condition and its role
  as a defining equation of D on V are stated.
- Multiplication by the image of a^n is injective for every n ≥ 0:
  `∀ n : ℕ, Function.Injective
  (fun s : Γ(M, W.1) ↦ (g.appLE V.1 W.1 e a) ^ n • s)`.
  `g.appLE` is the canonical map from Γ(T,V) to Γ(Y,W); its ring-hom property
  identifies the power of the image with the image of a^n. Natural-number
  quantification includes zero and all nonnegative exponents.
- Vanishing on the principal open implies the section is zero: the final clause
  quantifies every `s : Γ(M, W.1)` and says its restriction along
  `homOfLE (Y.basicOpen_le (g.appLE V.1 W.1 e a))` being zero implies `s = 0`.
  This is exactly the principal open defined by the image of a in Γ(Y,W).

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, publicly exposing
  `SheafOfModules.IsQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`. Its conjunction
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType` was read but would
  add an unwanted finite-type hypothesis and is not assumed.
- `def-nagata-effective-cartier-ideal`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`, declaration
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`. Its regular-principal
  predicate is `Ideal.IsRegularPrincipal` in
  `WeilConjectures.Mathlib.RingTheory.Ideal.RegularPrincipal`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, declaration
  `AlgebraicGeometry.IsClosedImmersion`. The ideal's canonical closed immersion
  and support are supplied by `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`;
  `IdealSheafData.range_subschemeι` identifies its image with `D.support`.
- `def-pc-scheme-module-flat-over`:
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`, declaration
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`.
- Proof dependency `lem-trf-flat-tensor-preserves-injection`: the Mathlib match is
  `Module.Flat.lTensor_preserves_injective_linearMap`, in
  `Mathlib.RingTheory.Flat.Basic`, imported without `public`.
- Proof dependency `lem-weil-pbc-affine-module-basic-open-localization`:
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`, declarations
  `AlgebraicGeometry.Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen` and
  `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isAffineOpen`,
  imported without `public`.

Sources opened: `literature/stacks-project/divisors.tex`,
`lemma-strict-transform-flat` (Tag 080F), clause (2) and its power-torsion proof;
`properties.tex`, `lemma-sections-supported-on-closed-subset` (07ZP), especially
clause (2) and the restriction-kernel sequence; `morphisms.tex`,
`lemma-flat-module-characterize` (01U4), all affine-pair equivalences; `algebra.tex`,
`lemma-flat` (00HD), flatness preserving injections. The module's theorem docstring
contains the four accepted proof steps: affine relative flatness, tensoring the
regular-element injection and taking powers, affine localization, and sheaf
uniqueness on an affine cover of an arbitrary open. No proof is supplied in Lean.

Edge cases checked before writing:

- n = 0 gives scalar 1 and the identity, and is included by `n : ℕ`.
- A unit Cartier equation gives an empty divisor on that chart and a full basic
  open; no nonunit hypothesis is added.
- Empty schemes and empty affine opens are allowed. Their section modules are
  zero; regularity over the zero ring and injectivity on the zero module cause
  no exception.
- The zero sheaf is allowed and satisfies each conclusion.
- If the image of g lies in the divisor, the complement is empty and the statement
  forces all sections of M to vanish, as relative flatness and regularity require.
- H can be non-affine and non-quasi-compact: the sheaf-uniqueness argument uses an
  arbitrary affine cover and never chooses a single exponent for all of H.
- No restriction on characteristic is present. Non-zero-divisor regularity, not
  nonzero-in-a-domain, is used, so bases with zero divisors are included.
- Flatness and regularity are essential: M=A/(a) on Spec A can have nonzero
  a-torsion without flatness; choosing a zero-divisor in A makes multiplication
  noninjective even on the flat module A. Neither hypothesis was weakened.

Searches for an existing statement:

1. `msearch.py ... leansearch "A quasi coherent module flat over the base has no
   sections supported on an effective Cartier divisor"`: eight hits, mainly
   `SheafOfModules.IsQuasicoherent` constructors and generic flatness criteria;
   none states either this global restriction assertion or the full item.
2. `msearch.py ... leanfinder "A relatively flat quasi coherent sheaf has injective
   restriction away from the inverse image of an effective Cartier divisor"`:
   eight hits, including `StructureSheaf.toBasicOpen_injective`, image and stalk
   injectivity, and `Flat.flat_appLE`. These concern structure-sheaf localization,
   integral schemes, images, or flat scheme morphisms; none is the item.
3. `msearch.py ... loogle "Module.Flat, IsSMulRegular"`: six hits, including
   `Module.Flat.isSMulRegular_of_nonZeroDivisors` and tensor regularity. These
   supply algebraic ingredients, not the sheaf restriction theorem.
4. `msearch.py ... grep
   "(Cartier|cartier).*(torsion|support|[Ff]lat)|(torsion|support|[Ff]lat).*(Cartier|cartier)"`:
   zero Mathlib hits.
5. Direct `rg -n` in `lean/WeilConjectures` and `lean/Sheaf` for `IsFlatOver`,
   Cartier support, torsion, and injective multiplication found the definitions
   used above, divisor-complement density, and
   `Scheme.Modules.injective_smul_sections_of_flat` in
   `WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree`.
   Its full signature was opened: it assumes a domain base, flat g and an
   invertible sheaf, and only asserts injectivity of one base scalar on global
   sections. It does not state the item for arbitrary relatively flat modules.
6. `grep -rn "lem-trf-relative-flat-cartier-support" lean/WeilConjectures`:
   no result. Direct `rg` of `dag/lean_names_upstream.json` and both source roots
   for the proposed declaration `relative_flat_cartier_support` found no match.
   The raw msearch results are retained in the sandbox's `searches.jsonl`.

No statement fault or dispute was found. The initial compile needed the explicit
`R := Y.ringCatSheaf` parameter for quasi-coherence; that elaboration repair is in
its final signature. `scompile.py Q32 lem-trf-relative-flat-cartier-support` then
compiled the delivered file in both sandbox and library module modes cleanly,
with no errors or warnings. Every variable and universe is explicitly bound and
`autoImplicit` is disabled.

## Second reading by Q32

I reopened the node and final module for a second pass. This is the worker's own
second reading; the dispatcher expressly prohibits starting other agents, and
the maintainer performs the independent delivery review.

I checked the arbitrary g and the absence of a `[Flat g]` hypothesis; the ideal
D with its exact affine-local regular-generator predicate; M with quasi-coherence
only (not the finite-type conjunction); and the exact existing `IsFlatOver`.
I matched the first conjunct's arbitrary open and canonical restriction to
H intersected with the inverse-image complement. In the second conjunct I
checked both affine opens, their inclusion e, the regularity and ideal-generator
conditions on a, the canonical `appLE` image, every power including zero, and
restriction to precisely its basic open followed by the zero implication.
The two conjuncts retain every conclusion of the node. The ideal representation
uses the canonical closed subscheme and its closed immersion; it does not omit
closedness or impose an additional geometric condition. All four proof steps
and the proof imports are retained. The only signature repair was the explicit
ring sheaf in the quasi-coherence instance, as already recorded above. No node
correction, extra notion or dependency replacement was needed.
