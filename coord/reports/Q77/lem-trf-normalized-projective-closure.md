## Worker report

Item: `lem-trf-normalized-projective-closure`, group Q77, stage 2, 2026-10-24.

The module `Sheaf.AlgebraicGeometry.NormalizedProjectiveClosure` states
`AlgebraicGeometry.normalized_projective_closure`, with a single postponed proof.
It also names four canonical constructions from the statement, in namespace
`AlgebraicGeometry.NormalizedProjectiveClosure`: `embedding`, `scheme`, `ι`, `toBase`.
All four are transparent abbreviations with real data from the published chart and
Mathlib's scheme-theoretic image. No new mathematical notion or node is needed.
The existing node is changed only in `lean`; no statement correction is made.

Sources read: Stacks `curves.tex`, theorem-curves-rational-maps (0BY1), especially
its final compactify-then-normalize alternative and its generic-stalk description;
lemma-nonsingular-model-smooth (0BY3); `morphisms.tex`,
lemma-scheme-theoretic-image-reduced (056B). The theorem docstring carries the
seven steps of the DAG proof, with its dependency names.

### Hypotheses and specified objects

| Node clause | Lean rendering |
| --- | --- |
| k is a field | `{k : Type u} [Field k]` |
| Every algebraic extension of k is separable | `[PerfectField k]`, the existing equivalent irreducible-polynomial separability criterion |
| U is a scheme over k | `{U : Scheme.{u}} (p : U ⟶ Spec (.of k))` |
| U is affine and integral | `[IsAffine U] [IsIntegral U]` |
| U is finite type over k | `[LocallyOfFiniteType p] [QuasiCompact p]`, the recorded two-part definition |
| dim U = 1 | `hdim : topologicalKrullDim U = 1` |
| n is any nonnegative integer | `(n : ℕ)` |
| The specified closed immersion into affine n-space | `(i : U ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k))) [IsClosedImmersion i]` |
| i is over k | `hi : i ≫ (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) = p` |
| The standard D_+(T_0) chart | `AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin n)) (Spec (.of k))` |
| The composite immersion into projective space | `embedding n i`, definitionally the given i followed by that chart |
| The specified scheme-theoretic closure X | `scheme n i`, definitionally `(embedding n i).image` |
| The factorization j | `ι n i`, definitionally `(embedding n i).toImage` |
| The structure map X → Spec k | `toBase n i`, definitionally `(embedding n i).imageι` followed by the projective projection |
| C = X^ν and ν : C → X | `(scheme n i).normalization` and `(scheme n i).fromNormalization`, precisely the recorded normalization in k(X) |

The homogeneous coordinate type is `Option (ULift.{u} (Fin n))`, with `none`
the distinguished T_0 and `some i` the other n coordinates. This is the base-change
realization `ProjectiveSpace` named by `def-nagata-projective-space-base-change`.
The published `WeilConjectures.Compactification.ProjectiveSpace` constructs this
chart on the integral Proj model by dehomogenization, then base changes it to k;
its source and docstring explicitly identify its image with D_+(T_0) and its
coordinate functions with T_i/T_0. Thus the map is the standard relative-Proj
chart specified in the node, in this realization of projective space, rather
than an arbitrary open immersion. The relative-Proj dependency module is also
imported publicly. No alternate projective completion or affine embedding is chosen.

### Conclusions

| Node clause | Lean rendering |
| --- | --- |
| X is integral | `∃ _hX : IsIntegral (scheme n i), ...` |
| X is projective over k in the blueprint's H-projective convention | `IsHProjective (toBase n i)` |
| dim X = 1 | `topologicalKrullDim (scheme n i) = 1` |
| j is a dense open immersion | `IsOpenImmersion (ι n i) ∧ DenseRange (ι n i)` |
| C is integral | `∃ _hC : IsIntegral (scheme n i).normalization, ...` |
| C is smooth over k | `Smooth ((scheme n i).fromNormalization ≫ toBase n i)` |
| C is proper over k | `IsProper ((scheme n i).fromNormalization ≫ toBase n i)` |
| C is finite type over k | `LocallyOfFiniteType` and `QuasiCompact` of that same structure morphism |
| dim C = 1 | `topologicalKrullDim (scheme n i).normalization = 1` |
| j sends the generic point of U to that of X | existential equality `hj` |
| ν sends the generic point of C to that of X | existential equality `hν` |
| j* : k(X) ≅ k(U) is the actual generic-stalk map | `ej` with `ej.hom = (ι n i).functionFieldMap hj` |
| ν* : k(X) ≅ k(C) is the actual generic-stalk map | `eν` with `eν.hom = (scheme n i).fromNormalization.functionFieldMap hν` |
| Both are k-isomorphisms | the next two equalities of arrows from `CommRingCat.of k`, commuting with the canonical scalar maps |
| j* ∘ (ν*)⁻¹ : k(C) ≅ k(U) is a k-isomorphism for these constructions | the categorical composite `eν.symm ≪≫ ej` and the final scalar commutation equality |

Here an arrow from k to the function field of a scheme T with structure map q
is written explicitly as `(Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫
T.presheaf.germ ⊤ (genericPoint T) trivial`. This is exactly the structural
scalar map on the generic stalk. Consequently an isomorphism in `CommRingCat`
commuting with this arrow is a k-algebra isomorphism, without assuming a second
unrelated algebra structure. The explicit generic-point equalities and equalities
to `functionFieldMap` prevent replacing either induced map by an arbitrary field
isomorphism. The existential integral witnesses are conclusions, not hypotheses;
proof irrelevance ensures that their use to type normalizations and stalks does
not change the specified constructions.

### Dependency declarations read and used

All sixteen statement-dependency records and statements were read, including
the Mathlib-only `def-weil-field` match. Their interfaces are:

- `Mathlib.Algebra.Field.Defs`: `Field` (via `def-weil-field`); also
  `Mathlib.FieldTheory.Perfect`: `PerfectField` for the explicit perfectness condition.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, structure maps and `Scheme.ΓSpecIso`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` (nonempty and integral sections),
  its reducedness and irreducibility instances, and scheme sobriety.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, taking values in `WithBot ℕ∞`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace` and its canonical projection.
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace`: `RelativeProjectiveSpace.scheme`,
  `π`, `standardOpen`, `localStandardOpen`, `localChart`, the symmetric-algebra
  coordinate interface and the degree-zero localization chart definition.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace` and its
  canonical projection; used with Option of a lifted Fin n for the n+1 coordinates.
- `WeilConjectures.Compactification.ProjectiveSpace`:
  `AffineSpace.toRelativeProjectiveSpace`, its integral-model dehomogenization
  definition, `isOpenImmersion_toRelativeProjectiveSpace` and
  `toRelativeProjectiveSpace_over`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.Hom.image`,
  `imageι`, `toImage` (the recorded scheme-theoretic closure interface).
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`,
  as required by `def-kun-projective` (not an unrelated projectivity convention).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalization` and `fromNormalization` (normalization in k(X));
  `normalizationIn` and `fromNormalizationIn` read for the proof's affine description.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the node's
  `Scheme.functionFieldOfComponents` and its integral-scheme specialization to the
  existing `Mathlib.AlgebraicGeometry.FunctionField` `Scheme.functionField`.
  The latter is definitionally the generic stalk, as the dependency record prescribes.
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`:
  `Scheme.Hom.functionFieldMap`, the actual stalk map composed with the identification
  of the image of the generic point with the target generic point.

Proof-only imports retain the plan: `Sheaf.AlgebraicGeometry.NagataAffineOpensProjective`
(`det_nagata_affine_opens_projective`), `Sheaf.TraceFormula.ReducedSchemeImage`
(`schemeTheoreticImage_reduced`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
(`topologicalKrullDim_opens_eq`) and `WeilConjectures.AlgebraicGeometry.Regular`
(`Scheme.smooth_fromNormalization_comp`). Normalization finiteness, surjectivity,
birationality on a nonempty open and dimension equality are the published declarations
of `lem-sc-normalization-exists` in the publicly imported normalization module.
Sobriety and `functionField_isFractionRing_of_isAffineOpen` are in the already
imported Mathlib modules. There is no proof-import cycle.

One proof-interface detail was checked: the current Lean declaration of
`det-nagata-affine-opens-projective` selects `f.affineSpaceImmersion`, whereas its DAG
statement permits a given immersion. It therefore cannot simply be instantiated at
an arbitrary given i. The theorem here retains the required arbitrary i; its docstring
uses the construction underlying that proof (standard chart, image, open factor),
which works for the given closed immersion as well. This statement delivery does not
silently replace i by the selected immersion or modify that proof-dependency node.

### Edge cases

- n = 0 is retained. The homogeneous-coordinate type then has its single distinguished
  coordinate. An integral one-dimensional curve cannot embed closed in A^0_k = Spec k,
  so the input hypotheses are inconsistent in this case; no positive-n hypothesis is added.
- The empty scheme is already excluded by the node's integrality and dimension hypotheses,
  not by an added assumption. Generic points exist from integrality and scheme sobriety.
- Singular affine curves are included: U is not assumed smooth or normal. The theorem
  normalizes the specified closure, not U by an unstated open embedding in C.
- The field may have any characteristic and need not be algebraically closed, finite,
  or geometrically connected. Perfectness is used only for normalized-curve smoothness.
- For a nonsingular closure the normalization may be an isomorphism; the function-field
  clauses still describe its actual stalk map and inverse.
- All schemes and the base field have the explicitly bound universe u; the finite
  coordinate type is lifted into that universe. No auto-bound variable is used.

### Searches for an existing statement

Prescribed `msearch.py Q77 lem-trf-normalized-projective-closure` calls:

- `leanfinder`: "Normalization of the scheme theoretic closure of a specified affine
  integral curve embedding into projective space is a smooth proper curve with canonical
  isomorphic function fields". Eight hits, headed by relative-normalization APIs such as
  `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom`, `Hom.normalization`, and
  `Hom.instIsIntegralNormalization`; no theorem for the specified projective closure.
- `loogle`: `AlgebraicGeometry.Scheme.normalization, AlgebraicGeometry.Smooth`.
  The remote Loogle index did not recognize the upstream `Scheme.normalization` identifier;
  zero hits, recorded as an unavailable identifier query, not evidence of nonexistence.
- `grep`: `normalization|projectiveClosure`, subdirectory `AlgebraicGeometry`.
  Ten hits on Mathlib's relative normalization and Zariski's main theorem; no full match.
- `leansearch`: "The normalization of the scheme theoretic projective closure of an affine
  integral curve over a perfect field is smooth proper and has the same function field".
  Eight hits on relative normalization and its universal morphisms; no full match.

Read-only local `rg` searches of both `lean/WeilConjectures` and `lean/Sheaf` for
`normaliz.*[Pp]rojectiv|[Pp]rojectiv.*[Cc]losure|normalized_projective` and then for
`exists_.*smooth.*[Cc]ompact|normalized_projective_closure|NormalizedProjectiveClosure`.
The upstream `IsCurve.exists_projectiveClosure` and
`exists_smooth_properCompactification_of_perfectField` were read. The first chooses
an unspecified projective embedding; the second additionally assumes smoothness and
geometric connectedness and chooses a Nagata compactification. Neither states this
node for the specified embedding or specifies these generic-stalk identifications.
`Sheaf.AlgebraicGeometry.Curve.NormalSmoothProjectiveCompactification` likewise
assumes a normal geometrically connected input and gives an existential completion.
The exact node-id search in `lean/WeilConjectures` had no hit. No released repair note
for this item was found in `coord/repair-notes`.

### Validation

Every compile uses the prescribed `scompile.py`, on this one module, with the
standard module header and explicit universe/variable binders. The initial elaboration
identified missing `Nonempty ⊤` instances when expressing scalar germs through
`germToFunctionField`; spelling out the identical generic-point germ removed that
unnecessary synthesis step. Two long-line warnings were wrapped. No linter was disabled.
The final compiler and preflight results are recorded below after they complete.

## Second reading by Q77

This is the worker's in-thread final rereading; the dispatcher brief assigns the
independent delivery review to the maintainer and explicitly prohibits starting other
agents. No independent worker reading is claimed here.

Reread the node alongside the module: the input embedding i occurs in the definition of
the image; no existential replacement embedding is introduced. The two integral witnesses
are under existential quantifiers in the conclusion, allowing normalization and generic
stalks to be typed without assuming their claimed properties. The normalization is the
recorded normalization in k(X). The two field isomorphisms have the correct directions,
X to U and X to C, and their hom components are fixed to the actual generic-stalk maps.
Their composite is `eν.symm ≪≫ ej`, so its direction is C to U. Each of the three scalar
commutation diagrams uses the appropriate structure map and the actual generic germ.
Affineness, integrality, both finite-type conditions, perfectness, the one-dimensional
hypothesis, closed immersion and its base commutation are all explicit. All geometric
conclusions in the node occur, including density and both dimension equalities. No
additional normality, smoothness of U, positive-n, algebraic-closure or connectedness
hypothesis was introduced. The only elaboration repair was to use the identical explicit
germ rather than demand synthesis of nonemptiness of the top open.

Final validation: `scompile.py Q77 lem-trf-normalized-projective-closure` passed
for the sandbox and library module with no errors or warnings (2.1 s each).
`deliver2.py Q77 lem-trf-normalized-projective-closure --no-push` reported
`OK (dry run): commit 41730b5b0cc passes the preflight and compiles; nothing pushed`.
A local JSON comparison confirms that `lean` is the only changed node field;
the signature record is exact, the module has one `sorry`, and all Lean lines
are at most 100 characters. The delivery wrapper repeats its checks on the
final report and module before pushing.
