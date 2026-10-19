## Worker report

`Sheaf.AlgebraicGeometry.FiniteGenericCurveModel` states
`AlgebraicGeometry.exists_finite_generic_curve_model`; its entire proof is `sorry`.
No new definitions, dependency replacements, or statement corrections are needed.
The node's statement is unchanged. The docstring contains all eleven repaired DAG
proof steps, including their dependency ids and the source place.

### Hypotheses and clauses

- Ground field: `(k : Type u) [Field k]`. Schemes: `(X S : Scheme.{u})`.
  `[S.Over (Spec (.of k))]` supplies the field structure on S; composition with
  `f : X ⟶ S` supplies the induced field structure on X.
- Integral base: `[IsIntegral S]`, including nonemptiness.
- Finite-type base: `[LocallyOfFiniteType (S ↘ Spec (.of k))]` together with
  `[QuasiCompact (S ↘ Spec (.of k))]`, exactly the recorded finite-type convention.
- Projective f: `[IsProjective f]`, the recorded H-projective plus quasi-compact notion.
- Geometric fibre dimension: `h_dim` quantifies over every `s : S`, with
  `topologicalKrullDim` of `pullback f` along the composite of the spectrum map of
  `κ(s) → AlgebraicClosure κ(s)` and `S.fromSpecResidueField s`, bounded by 1.
  This is precisely the dependency's geometric fibre, with its canonical algebraic
  closure. The dependency states independence up to isomorphism of the closure choice.
  The explicit `Scheme.{u}` ascription fixes elaboration without changing the object.
- Nonempty open restriction: `∃ U : S.Opens, Nonempty U ∧ ...`.
- New integral base and finite surjection:
  `∃ (S' : Scheme.{u}) (p : S' ⟶ U.toScheme),
  IsIntegral S' ∧ IsFinite p ∧ Surjective p ∧ ...`.
  The S of the conclusion's prose is the restricted base `U.toScheme`.
- Comparison target T: `(pullback f (p ≫ U.ι)).nilradical.subscheme` is exactly
  the reduction of X base changed to S'. This agrees by pullback pasting with
  restricting X first. No commutation of reduction with arbitrary base change is assumed.
- Finite disjoint union: `∃ (n : ℕ) (Y : Fin n → Scheme.{u}) ...`; the total
  scheme is the existing coproduct `∐ Y`. Mathlib's coprojections are open immersions,
  have disjoint images, and cover the total scheme. Any finite family can be reindexed
  by `Fin n`, including the empty family.
- Structure maps of the factors: `g : ∀ i : Fin n, Y i ⟶ S'`.
  Each factor satisfies `(SmoothOfRelativeDimension 1 (g i) ∧ IsProjective (g i)) ∨
  (IsFinite (g i) ∧ Etale (g i))`, exactly smooth projective families of pure
  relative dimension one or finite étale families. No connectedness or integrality of
  these factors is added.
- Finite surjective comparison: `ν : (∐ Y) ⟶ T`, `IsFinite ν ∧ Surjective ν`.
- The comparison is over S': `Sigma.desc g = ν ≫ ...subschemeι ≫ pullback.snd ...`.
  This identifies the structural map of the coproduct with the composite through T.
- Closed boundary: `∃ (D : Scheme.{u}) (d : D ⟶ T), IsClosedImmersion d ∧ ...`.
  This is an arbitrary closed subscheme, as in the statement; no reducedness is added.
- Boundary finite over S': `IsFinite (d ≫ ...subschemeι ≫ pullback.snd ...)`.
- Isomorphism outside D: `∃ V : T.Opens, (∀ x, x ∈ V ↔ x ∉ Set.range d) ∧
  IsIso (pullback.snd ν V.ι)`. The first clause says V is precisely the complement
  of the boundary's image. The pullback projection is ν restricted over V, with its
  whole inverse image as domain.

### Dependencies

The following recorded declarations were inspected and reused; the concrete modules
are public imports of the statement module.

- `def-pc-projective-morphism`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `AlgebraicGeometry.IsHProjective`, `AlgebraicGeometry.IsProjective`.
- `def-weil-pbc-scheme-conventions`: convention bundle with no declaration; its concrete notions are the other dependency declarations.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-geometric-fibre`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback`.
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`, `topologicalKrullDim`.
- `def-pc-base-change`: `Sheaf.AlgebraicGeometry.BaseChangeConventions`: `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`, `AlgebraicGeometry.baseChange_morphism_projections`, `AlgebraicGeometry.baseChange_iterated`, `AlgebraicGeometry.baseChange_fiber`, `AlgebraicGeometry.Scheme.Hom.geometricFiberAt`, `AlgebraicGeometry.baseChange_section_characterization`.
- `def-weil-pbc-scheme-reduction`: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `AlgebraicGeometry.Scheme.nilradical`, `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`, `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.IsIntegralHom`.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, `AlgebraicGeometry.SmoothOfRelativeDimension`, `AlgebraicGeometry.Etale`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `lem-weil-pbc-scheme-coproduct-family`: `Mathlib/AlgebraicGeometry/Limits.lean`: `AlgebraicGeometry.instHasColimitsOfShapeDiscreteSchemeOfSmall, AlgebraicGeometry.sigmaOpenCover, AlgebraicGeometry.disjoint_opensRange_sigmaι`; reused through `∐ Y` and `Sigma.desc`.

### Searches

- `grep`, `genericCurve|generic_curve|curve_model|curveModel`: 0 hits; .
- `leanfinder`, `A projective morphism with geometric fibres of dimension at most one has a finite surjective smooth curve model after finite base change and shrinking`: 8 hits; AlgebraicGeometry.Proj.instUniversallyClosedToSpecZeroOfFiniteTypeSubtypeMemOfNatNat, AlgebraicGeometry.IsSmoothOfRelativeDimension, AlgebraicGeometry.AffineSpace.instSurjectiveOverSchemeInferInstanceOverClass, AlgebraicGeometry.isSmoothOfRelativeDimension_isStableUnderBaseChange, AlgebraicGeometry.isSmooth_isStableUnderBaseChange, AlgebraicGeometry.Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat, AlgebraicGeometry.finite_appTop_of_universallyClosed, AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme.
- `loogle`, `AlgebraicGeometry.SmoothOfRelativeDimension, AlgebraicGeometry.IsFinite`: 0 hits; .

Semantic hits concern smoothness, projective spectra, affine-space surjectivity and
base-change permanence. None constructs the required base cover, factor decomposition
and finite boundary isomorphism. Direct `rg` for
`genericCurve|generic_curve|curve_model|curveModel|lem-fin-generic-curve-model` in the
upstream WeilConjectures source and the project's lean/Sheaf returned no matches.
The new declaration name was also searched in the upstream name index, source and
project Lean modules, with no matches. No exact existing statement was found.

The full signatures and docstrings of the statement dependencies were read, including
nilradical/reduction, smooth relative dimension, and scheme coproducts. The updated
canonical projectivity source module is absent from this machine's snapshot. Its
pre-extraction declaration and docstring in Sheaf.AlgebraicGeometry.Morphisms.Projective
were read; a server-only scompile probe confirmed the canonical import and both class
signatures. The delivered module uses that canonical import and compiles successfully.
The nineteen non-public imports are the distinct already-stated proof-dependency
modules, deduplicated against the public imports. No dependency was omitted for an
import cycle. Unstated proof dependencies remain for stage 3; their statements are
not required to formulate this theorem.

### Edge cases

- X may be empty; dimension bottom satisfies the bound, n may be zero, and the empty
  coproduct, empty comparison target and empty D are all permitted.
- Zero-dimensional and mixed-dimensional X are allowed by the disjunction on factors.
  No pure-dimensional hypothesis on X or nonempty-fibre condition is added.
- S is nonempty by integrality, and `Nonempty U` rules out a vacuous shrinking.
- Every universe is explicit. The field and schemes use u as in the project's scheme
  over field convention, residue fields and algebraic closures stay in u, and `Fin n`
  is small in every universe. All points of S are quantified over.
- No restriction on characteristic, perfectness, separability, connectedness of factors,
  surjectivity of f, or generic smoothness is assumed. The base cover can be inseparable.
- D can be empty, in which case the restriction clause requires ν to be an isomorphism
  over all of T, as it should. Its scheme structure is otherwise unrestricted.

No statement dispute or node fault was found.

### Validation

The delivered module compiled cleanly using scompile.py on the server in 1.8 seconds,
nice 19, two threads, within the 60-second file limit. No local compiler or library
build was run. The initial compile required a scheme type ascription in the dimension
expression; after that fix the compiler emitted no diagnostics. The module has no
unbound variables, local notation, local instances, lets, or hidden `show ... from`
terms. The only new declaration is the theorem, whose entire proof is `sorry`.

## Second reading by NA

I read the node's statement and all eleven proof steps independently against the
blueprint source `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-generic-curve-model.md`
(statement and seven proof paragraphs), then read the delivered Lean. This source
is a blueprint lemma, not a Stacks lemma with ambient hypotheses. I also read the
Stacks source `morphisms.tex`, definition-projective (01W8), and
lemma-smooth-omega-finite-locally-free / definition-smooth-relative-dimension
(02G1 / 02G2). The project's explicitly recorded H-projective convention is the
one required here. There is no hidden perfectness or characteristic assumption.

Here is my object/hypothesis/conclusion checklist, in the source's order. Every
entry passes; the signature requires no repair.

1. A ground field: `(k : Type u) [Field k]`, with arbitrary characteristic.
2. Schemes X and S over that field: `(X S : Scheme.{u})` and
   `[S.Over (Spec (.of k))]`. The named map `f : X ⟶ S` induces the structure
   map on X by composition. No unrelated structure map on X is assumed.
3. S integral: `[IsIntegral S]`, which includes nonemptiness and reducedness
   and irreducibility, rather than merely an affine domain hypothesis.
4. S finite type over k: the two instances
   `[LocallyOfFiniteType (S ↘ Spec (.of k))]` and
   `[QuasiCompact (S ↘ Spec (.of k))]`. No separatedness of S is added.
5. f projective: `[IsProjective f]`, the dependency's H-projective plus
   quasi-compact predicate, on the actual map f.
6. Every geometric fibre has dimension at most one: `h_dim : ∀ s : S, ... ≤ 1`.
   Its pullback uses `Spec.map` of the canonical inclusion of `S.residueField s`
   into its `AlgebraicClosure`, followed by `S.fromSpecResidueField s`.
   This is exactly def-weil-geometric-fibre's recorded pullback, over every
   point, not only closed points. `topologicalKrullDim` is global dimension
   of that fibre, not dimension of its local rings or dimension at a point.
7. First shrink S to a nonempty open: `∃ U : S.Opens, Nonempty U ∧ ...`.
   This quantifier precedes the choice of S' and its map.
8. Integral finite surjective new base: `∃ (S' : Scheme.{u})
   (p : S' ⟶ U.toScheme), IsIntegral S' ∧ IsFinite p ∧ Surjective p ∧ ...`.
   No etaleness, separability or normality of p is required.
9. The comparison target is exactly the reduction after base change:
   `(pullback f (p ≫ U.ι)).nilradical.subscheme`. Restricting X before the
   base change gives the same scheme up to the canonical pullback-pasting
   isomorphism. Reduction has not been moved before base change.
10. Y is a finite disjoint union: `∃ (n : ℕ) (Y : Fin n → Scheme.{u}) ...`,
    with total scheme `∐ Y`. Arbitrary finite families admit this indexing.
    `g : ∀ i, Y i ⟶ S'` gives the factors' structure maps.
11. Each factor has precisely one of the allowed types:
    `∀ i, (SmoothOfRelativeDimension 1 (g i) ∧ IsProjective (g i)) ∨
    (IsFinite (g i) ∧ Etale (g i))`.
    The smooth predicate specifies pure relative dimension, with no requirement
    that fibres be connected, integral or nonempty. The second alternative is
    finite etale, not merely smooth of dimension zero.
12. The comparison is a finite surjection: the quantified map
    `ν : (∐ Y) ⟶ ...nilradical.subscheme` satisfies
    `IsFinite ν ∧ Surjective ν`.
13. This is a comparison over S':
    `Sigma.desc g = ν ≫ ...nilradical.subschemeι ≫ pullback.snd f (p ≫ U.ι)`.
    This equality connects the same g, ν, p, U and f already quantified.
    It makes explicit the structural compatibility implicit in the source.
14. A closed boundary D in T: `∃ (D : Scheme.{u}) (d : D ⟶ T),
    IsClosedImmersion d ∧ ...`. This allows every closed subscheme and does
    not strengthen the conclusion by demanding the reduced structure.
15. D finite over S': `IsFinite (d ≫ ...nilradical.subschemeι ≫
    pullback.snd f (p ≫ U.ι))`, on the composite structural map.
16. ν is an isomorphism outside D: `∃ V : T.Opens,
    (∀ x, x ∈ V ↔ x ∉ Set.range d) ∧ IsIso (pullback.snd ν V.ι)`.
    V is exactly the open complement of the image of D, and the displayed
    second projection has source the full inverse image of V. This is an
    isomorphism of schemes, not merely a bijection on points.

I opened every statement dependency node and its recorded signatures. For the
convention bundle there is deliberately no declaration. I read IsIntegral in
Properties, LocallyOfFiniteType and QuasiCompact in their morphism modules,
IsFinite, Surjective, Smooth, SmoothOfRelativeDimension, Etale, and
IsClosedImmersion in Mathlib. The standard-smooth-chart definition of relative
dimension agrees with the Stacks dimension condition by 02G1/02G2.
I read `Scheme.nilradical = .radical ⊥` and the actual `subscheme` / `subschemeι`
constructions, the coproduct instance, `sigmaOpenCover` and
`disjoint_opensRange_sigmaι`, and the definition of `topologicalKrullDim`.
I read BaseChangeConventions in full: its node explicitly permits the chosen
`pullback`, `fst`, `snd` form; moduleBaseChange is a separate module-level
notion and is not substituted for scheme base change here. For projectivity I
read the pre-extraction Projective module, including its projective-space
embedding field and the IsProjective superclass fields, and the worker's
server probe of the canonical extracted class signatures. The delivered file
uses the canonical import. There are no new definition nodes or dependency
replacement modules to audit under H12/H13, and no statement_change record.

Edge cases checked independently: X and its geometric fibres may be empty;
`n = 0` allows the empty coproduct, with empty T and D. Zero-dimensional and
mixed-dimensional fibres are allowed, and f need not be surjective. Empty S
is excluded exactly by the source's integrality; empty U is explicitly
excluded. Empty D forces an isomorphism everywhere. In positive imperfect
characteristic the finite base change is allowed to be inseparable; no
perfectness or generic smoothness hypothesis has slipped in. The common
universe u is arbitrary, following the scheme-over-field convention; residues,
algebraic closures and finite indexing fit it. There is no lower-universe
quantification over test objects or limit diagrams and no hidden smallness
hypothesis on arbitrary index families.

Independent searches (recorded also by msearch.py):

- LeanFinder: `finite surjective morphism from disjoint union of smooth
  projective curves after shrinking integral base`. Eight hits, including
  `IsFinite.instDescScheme` (finiteness of a coproduct of two already finite
  maps), `Surjective.sigmaDesc_of_union_range_eq_univ`, affine-space facts,
  and `finite_appTop_of_universallyClosed`. I inspected the returned
  signatures: none produces the base cover, smooth factors and boundary.
- Loogle: `AlgebraicGeometry.SmoothOfRelativeDimension,
  AlgebraicGeometry.Surjective` returned zero hits. A separate query using
  IsProjective could not resolve that project-specific name in Loogle;
  it is not counted as a successful absence check.
- Direct rg of Mathlib, upstream WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json with the independently chosen patterns
  `generic.{0,20}curve.{0,20}model`,
  `curve.{0,20}finite.{0,20}surject`, and the full declaration name gave
  no matching existing theorem. No duplicate statement or definition found.

The only mismatch found was explanatory prose: the declaration docstring
called Y the coproduct, although Y is the family and the coproduct is `∐ Y`.
I corrected that sentence to identify `Y i`, `g i` and `∐ Y` precisely.
No Lean signature, hypothesis, conclusion, node statement or proof plan was
changed. The docstring's eleven proof steps match the node's eleven steps,
including the correction of the blueprint's nilpotent exponent and the final
shrinking downstairs. The theorem has `sorry` as its entire proof; no hollow
data definitions, helper proofs, local instances, local notation, lets or
unbound variables are introduced. The node's lean.statement was checked
verbatim against the source signature; every Lean line is at most 100 columns.
