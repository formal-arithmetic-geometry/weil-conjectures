## Worker report

The module `Sheaf.AlgebraicGeometry.FlatCoverNormalizationLocalSections` states
`AlgebraicGeometry.exists_flat_cover_normalization_local_sections`, with its sole
proof `sorry`. No definition, new node, dependency repair or statement correction
is needed. The copied node changes only its `lean` record.

Hypotheses and conclusions, checked against the complete node statement:

- A commutative Noetherian integrally closed domain is rendered by `(R : Type u)`
  with `[CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]`.
- Dimension exactly one is `hdim : ringKrullDim R = 1`, not dimension at most one.
- Finitely many maximal ideals is `hmax : Set.Finite {m : Ideal R | m.IsMaximal}`.
- The prescribed fraction field is the canonical `FractionRing R`; the base is
  exactly `Spec (CommRingCat.of R)`, so no arbitrary replacement base or map occurs.
- The affine source is `(T : Scheme.{u}) [IsAffine T]`. The spectrum base is affine
  by Mathlib's existing instance.
- The given morphism is `f : T ⟶ Spec (CommRingCat.of R)`. Its flatness and
  surjectivity are `[Flat f] [Surjective f]`.
- Finite presentation is `[LocallyOfFinitePresentation f]`: this is equivalent to
  finite presentation here because both schemes are affine. In particular every
  morphism between affine schemes is affine, hence quasi-compact and
  quasi-separated. Those automatic properties are not extra hypotheses. The
  dependency node explicitly defines finite presentation as these three properties.
- A finite extension of K is the existential `L : Type u`, `Field L`,
  `Algebra (FractionRing R) L`, `Module.Finite (FractionRing R) L`.
- The existential `Algebra R L` and `IsScalarTower R (FractionRing R) L` specify
  precisely the induced R-algebra structure; they do not allow an unrelated base
  map. The scalar-tower equation says that its algebra map is the composite
  R → FractionRing R → L. This structure always exists for an extension of K.
- The normalization is literally `integralClosure R L`, not an unspecified normal
  ring, and its spectrum is literally `Spec (CommRingCat.of (integralClosure R L))`.
- The finite cover is `(n : ℕ)` with opens `U : Fin n → S_L.Opens` and
  `(⨆ j, U j) = ⊤`. These are Zariski opens with their canonical open subschemes.
- Each map `u_j` is `u j : (U j).toScheme ⟶ T`. Being over S is exactly
  `u j ≫ f = (U j).ι ≫ Spec.map (CommRingCat.ofHom
  (algebraMap R (integralClosure R L)))`.
- The equivalent formulation is the same mathematical assertion, not a second
  hypothesis or an additional conclusion: put a map u_j and the open inclusion
  into `pullback.lift`. Its second projection is the open inclusion, which is
  exactly a section over that open; conversely compose such a section with
  `pullback.fst`. Thus the Lean uses the first of the two equivalent formulations.
- There is no separability, normal-extension, excellence, Nagata or
  module-finiteness hypothesis on L/K or R_L/R. The proof uses a normal envelope,
  but the conclusion does not demand one.

Dependency declarations read and used:

| Node | Module | Declaration / rendering |
|---|---|---|
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |
| def-weil-pbc-normal-ring | Mathlib.RingTheory.IntegralClosure.IntegrallyClosed | IsIntegrallyClosed and IsDomain, normal-domain clause |
| def-weil-pbc-krull-dimension-ring | Mathlib.RingTheory.KrullDimension.Basic | ringKrullDim |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Spec and Spec.map |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | Scheme and Scheme.Hom |
| def-weil-flat-morphism | Mathlib.AlgebraicGeometry.Morphisms.Flat | AlgebraicGeometry.Flat |
| def-weil-surjective-morphism | Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap | AlgebraicGeometry.Surjective |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | LocallyOfFinitePresentation, affine finite-presentation equivalence |
| def-pc-field-extension | Mathlib.Algebra.Algebra.Defs | Algebra, algebraMap |
| def-weil-pbc-integral-closure | Mathlib.RingTheory.IntegralClosure.Algebra.Basic | integralClosure |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion | IsOpenImmersion; canonical Scheme.Opens.ι instance |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | pullback, pullback.lift, pullback.fst, pullback.snd, used for the equivalent formulation |

The statement dependency modules are public imports; the modules of already stated
proof dependencies are ordinary imports. This includes the existing upstream
AffineFibreSectionsTensor, IsLocallyQuasiFiniteResLE and
HasUniversallyBoundedFibersOfIsLocallyQuasiFinite modules and the landed
QuasiFiniteLocusOpen and CommonNormalCompatibleGroups modules. Mathlib matches of
proof dependencies are imported from their recorded files. The two proof nodes
lem-sfb-quasi-section-nearby-open and lem-sfb-normal-coefficient-branch-conjugacy
have no recorded module, so cannot yet be imported; neither is needed to state
this theorem. There are no omitted imports due to a deliberate cycle.

Edge cases: the zero ring is excluded by IsDomain, and fields are excluded by
exact dimension one. A nonzero ring has a maximal ideal, so the finite maximal
set is not being allowed to vacuously bypass any fibre. The empty scheme T
cannot satisfy surjectivity onto this nonempty spectrum. Empty U_j are allowed.
The cover is indexed by Fin n for arbitrary n, including zero; its top-cover
condition rules out n = 0 on this nonempty normalization. Characteristic is
unrestricted, and inseparable extensions are retained. The identity extension
L = K is permitted. No finiteness of the integral closure as an R-module is used.

Universe check: R, T, FractionRing R, and the existential finite extension have
universe u. Every finite extension of a field in Type u has a Type u model by
its finite basis, so this existential universe loses no extension case. The
conclusion quantifies over no test objects in a smaller independent universe.

Searches made with the prescribed wrapper, group Q37 and this item:

- LeanFinder: "A flat surjective affine scheme of finite presentation over a
  semilocal normal one dimensional Noetherian domain has local sections after
  normalization in a finite field extension". Eight hits, all normalization
  constructions and properties; no finite-extension local-sections theorem.
- Loogle: `AlgebraicGeometry.Flat, integralClosure`. Zero hits.
- Mathlib grep: `normaliz.*section|section.*normaliz|quasi.?section` under
  AlgebraicGeometry. Only Normalization.lean:217, the description of sections of
  the relative normalization, which is not the assertion here.
- LeanSearch: "A flat surjective affine scheme of finite presentation over a
  semilocal Dedekind domain admits local sections after normalization in a finite
  extension of the fraction field". Eight hits: normalization maps, flat affine
  faithful-flatness criterion, and smooth finite-presentation properties; no match.
- Project and upstream `rg` searches for the same normalization/section patterns
  produced many unrelated cohomological comparison normalizations. A narrower
  search `quasi.?section|flat.cover.*normaliz|normaliz.*flat.cover` had no match.
  Searches for `flat_cover_normalization_local_sections`,
  `normalization_local_sections`, `flat_cover.*sections`,
  `flat cover.*normalization`, and `semi.?trait` in the project, upstream and
  dag/lean_names_upstream.json found no existing declaration.
- The exact blueprint id was searched with `grep -rn` in lean/WeilConjectures:
  no match.

Source reading: opened local Stacks more-morphisms.tex at
lemma-quasi-finite-quasi-section-meeting-nearby-open-X (05GU), fields.tex at
lemma-normal-closure (09DT), and more-algebra.tex at lemma-one-orbit (0BRI).
The proof docstring reproduces all eight DAG steps, including the localization
calculation and the possibly inseparable branch-conjugacy step. The unavailable
Anantharaman archive is already identified as WANTED by the node; no claim to
have read that unavailable archive is made. No statement dispute was found.

## Second reading by Q37

I reread the node and the file after writing the first draft. This is a separate
self-check in this dispatcher-started solo task; the maintainer supplies the
independent delivery review, as the assignment specifies. No other agent was
started.

The ring hypotheses, exact dimension, finite maximal set, affine source, flatness,
surjectivity and finite presentation each appear as matched above. The canonical
fraction field and scalar tower prevent changing the normalization's R-structure.
The conclusion uses an actual finite collection of Zariski opens covering all of
Spec R_L, and actual maps to the given T commuting with the fixed base morphism.
The explicit commute equation is essential: arbitrary maps would not give local
sections. The equivalent fibre-product wording is accounted for by pullback.lift
and projection, without adding a redundant theorem or a new notion. No additional
separability or finite-normalization hypothesis slipped into the statement.
The recheck added the recorded fibre-product dependency's public import, retaining
the scheme pullbacks implementation as a proof import. No mathematical mismatch
or node correction was needed.

Validation: the final module passed the prescribed scompile.py server checks in
both sandbox and library mode, with no errors or unexpected warnings. The final
source has no diagnostic commands and no lines exceeding 100 characters.
