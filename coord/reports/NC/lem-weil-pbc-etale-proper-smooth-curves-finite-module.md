## Worker report

The module `Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule` states
`AlgebraicGeometry.Etale.properSmoothCurves_finiteModule_higherDirectImage_constructible`.
It contains one theorem with proof `sorry`, no new definitions, and no statement correction.

Clause-by-clause correspondence:

- Schemes and morphism: `{C S : Scheme.{u}}` and `(f : C ⟶ S)`.
- Noetherian base: `[IsLocallyNoetherian S] [CompactSpace S]`, exactly locally Noetherian
  and quasi-compact, as the node explicitly specifies. No quasi-separatedness hypothesis added.
- Proper and smooth: `[IsProper f] [Smooth f]`.
- Nonempty geometrically connected fibres: `[GeometricallyConnected f]`. Mathlib defines
  this using `ConnectedSpace` of every field-valued base change. `ConnectedSpace` includes
  nonemptiness; the existing fibre instance and the surjectivity instance confirm this.
- Dimension at most one: `h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1`.
  These are the residue-field fibres. Krull dimension is invariant under extension of
  the base field, so this is precisely the geometric-fibre dimension bound, without
  restricting the family to constant relative dimension or excluding dimension zero.
- Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- Finite Λ-module: `(M : ModuleCat.{u + 1} Λ) [Finite M]`; finiteness means finite as a set.
- Every integer degree: `(q : ℤ)`, including negative degrees.
- Constant input: `(constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M`.
- Input in degree zero: `DerivedCategory.Plus.singleFunctor ... 0`.
- Derived direct image: `rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f`.
- The q-th higher direct image: `DerivedCategory.Plus.homologyFunctor ... q` applied to
  that derived direct image.
- Constructibility as a Λ-module sheaf on the small etale site of S:
  `Scheme.IsConstructibleEtaleModuleSheaf` applied to the resulting cohomology sheaf.
- No invertibility or characteristic assumption appears in the signature.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-scheme-conventions`: a convention-only record; quasi-compactness of the
  base is `CompactSpace S`, not the tautological quasi-compactness of its identity map.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (universal closedness supplies quasi-compactness).
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- `def-pc-geometrically-irreducible`: the `mathlib_match` explicitly records its connected
  clause as `AlgebraicGeometry.GeometricallyConnected`, in
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`; no replacement notion needed.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, valued in `WithBot ℕ∞`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf` (sheafification of the constant presheaf).
- `def-weil-pbc-direct-image`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`; its recorded derived declaration is actually in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, which is also imported:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` is the right derived functor of
  this exact lowerStar, not a duplicate construction.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, using
  the recorded ModuleCat-valued encoding; `DerivedCategory.Plus.singleFunctor` and
  `DerivedCategory.Plus.homologyFunctor` from Mathlib's DerivedCategory.Plus render
  the sheaf-in-degree-zero and cohomology operations in its bounded below subcategory.
- `def-weil-pbc-etale-constructible-sheaf`:
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, the exact global finite
  stratification definition with finite constant module values.

The module imports every stated proof-dependency module (including the matching Mathlib
leaves). The dimension-loci lemma, quasi-finite shriek constructibility and prime-coefficient
curve theorem have no Lean records yet and therefore cannot be imported; their node ids
remain in the detailed proof-plan docstring. Nothing is proved in stage 2.

Edge cases checked before writing: empty base and source are allowed (the fibre hypotheses
are vacuous over an empty base); an empty fibre over an existing base point is excluded by
ConnectedSpace, exactly as required; dimension-zero and dimension-one components may coexist;
zero module and the zero coefficient ring are allowed; negative q is included and its
cohomology vanishes; characteristic-p coefficients are allowed. The shared universe u for
schemes and u+1 for coefficient rings/modules follows the recorded constructibility and
six-functor declarations. The finite coefficients impose no size restriction up to lifting.

Source checked directly: `literature/stacks-project/more-etale.tex`,
`lemma-proper-smooth-family-curves-modules` (0GKW), statement and proof. The source proves
its stronger finite-torsion Noetherian-coefficient form. This node deliberately uses the
finite-ring/finite-underlying-module specialization, extends to dimension zero by 0GK3,
and its existing proof splits the smooth dimension loci using 02G1. No correction needed.

Searches for existing statements:

- `msearch.py ... leanfinder "proper smooth families of geometrically connected curves finite
  module higher etale direct image constructible"`: eight unrelated etale, finite and
  smooth morphism declarations; no matching constructibility theorem.
- `msearch.py ... loogle '"constructible", "sheaf"'`: zero hits.
- `msearch.py ... grep 'proper.*smooth.*constructible|constructible.*smooth.*proper'`:
  zero Mathlib hits.
- `msearch.py ... leansearch "finite constant module proper smooth curve higher etale direct
  images constructible"`: service unavailable (Internal Server Error), recorded as unavailable.
- `rg` of `WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for the
  item id, proposed declaration name, and the proper/smooth/constructible combinations:
  no existing statement or declaration-name collision.
- Additional source searches located `rightDerivedLowerStarPlus` in its actual module
  and verified the exact full signature, ambient category parameters and docstring.

No STATEMENT-DISPUTED issue identified. Server compilation and dry-run results are recorded below.

Validation: scompile.py compiled the delivered module cleanly (1.9 seconds), with
nice 19, two threads and the 60-second per-file limit. deliver2.py --no-push printed
OK: compilation and preflight pass, except the independent second-reading section
which the second reader supplies. Nothing pushed.


## Second reading by NC

I independently read the sandbox node and Lean file, all ten statement-dependency
nodes and their recorded declarations, and the source statements and proofs in
more-etale.tex (0GKW, 0GK3) and morphisms.tex (02G1). The section containing 0GKW
introduces no additional standing base hypothesis. Its Noetherian coefficient ring
and finitely generated torsion module hypotheses hold here because both underlying
sets are finite. The node deliberately specializes the coefficients, assumes a
Noetherian base, and includes dimension zero. Its six-step proof justifies this
extension; the Lean follows that node rather than silently replacing it by the
one-dimensional source statement.

Object, hypothesis and conclusion checklist (each verdict: exact):

- Arbitrary schemes C and S and their map: `{C S : Scheme.{u}} (f : C ⟶ S)`.
  Both live in the same arbitrary universe as the recorded scheme category.
- Noetherian S: `[IsLocallyNoetherian S] [CompactSpace S]`. I opened the
  Mathlib class in Noetherian.lean: the first condition is Noetherian rings on
  affine opens, the second is quasi-compactness of S. No separatedness,
  finite-dimensionality or finite-type-over-a-field assumption is imposed.
- Proper f: `[IsProper f]`, whose class extends separatedness, universal
  closedness and local finite type. Universal closedness supplies the missing
  quasi-compactness in the equivalent finite-type formulation.
- Smooth f: `[Smooth f]`, the Mathlib affine-local smooth-ring-map condition;
  this is the recorded notion, not formal smoothness alone.
- Nonempty geometrically connected fibres: `[GeometricallyConnected f]`.
  Connected.lean defines this using `ConnectedSpace` after every field-valued
  base change. Its `iff_geometricallyConnected_fiber` identifies this with
  geometric connectedness of all residue-field fibres. Its fibre ConnectedSpace
  instance and Surjective instance confirm nonemptiness. Thus the field-relative
  connected clause of `def-pc-geometrically-irreducible` is used correctly.
- Fibre dimension at most one: `h_dim : ∀ s : S,
  topologicalKrullDim (f.fiber s) ≤ 1`. KrullDimension.lean defines precisely
  the supremum of irreducible closed chain lengths. Dimension of a finite-type
  scheme over a field is unchanged by field extension; thus residue-field fibres
  encode the same bound as geometric fibres. This permits dimension zero as well
  as one and does not demand constant relative dimension.
- Finite commutative ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  No domain, nontriviality, field, characteristic, or invertibility condition.
- Finite module over that same ring: `(M : ModuleCat.{u + 1} Λ) [Finite M]`.
  Finite is the underlying-set condition; over a finite ring it is equivalent to
  finite generation, so both readings of finite module agree.
- All integer degrees: `(q : ℤ)`, quantified after the coefficients, with no
  nonnegativity restriction.
- Constant input sheaf: `(constantSheaf C.smallEtaleTopology
  (ModuleCat.{u + 1} Λ)).obj M`. I opened ConstantSheaf.lean: this is exactly
  constant presheaf followed by sheafification, the dependency's construction.
- Place that sheaf in degree zero: `DerivedCategory.Plus.singleFunctor ... 0`.
  Plus.lean identifies this with the usual single cochain complex in degree zero.
- Apply Rf_*: `rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f`.
  In UpperLowerStarCoherence.lean it is the rightDerivedFunctorPlus of the
  recorded lowerStar; Defs.lean defines lowerStar by precomposition with the
  small-etale base-change functor, with the required sectionwise formula.
  Both the underived and actual derived-definition modules are imported.
- Take R^q: `DerivedCategory.Plus.homologyFunctor ... q`. Plus.lean defines
  this by inclusion followed by the ordinary derived cohomology functor.
  The category is exactly the dependency's ModuleCat-valued etale encoding.
- Constructible as a module sheaf on S: `Scheme.IsConstructibleEtaleModuleSheaf`
  of the resulting sheaf. I opened its full definition and
  LocallyClosedStratification.lean: finite locally closed partition realized by
  immersions, constructible parts, and etale-local constant finite module values.
  This is the recorded global notion, not merely constructibility of an
  underlying abelian sheaf or a separate stalk-finiteness condition.
- No exponent invertibility assumption: absent throughout the signature.

Edge cases: empty base and hence empty source are covered, with no Nonempty
binder on either scheme; an empty fibre over an existing base point is excluded
by ConnectedSpace as required. Either of the dimension-zero and dimension-one
loci may be empty. The dimension bound uses WithBot natural extended dimension,
so it does not accidentally exclude empty schemes. The zero module, zero ring,
and empty basis in the proof plan are allowed. q = 0 and negative q are included;
the latter have zero higher direct image. A killing exponent need not be supplied:
a finite additive group has a positive annihilator, including the trivial group.
Characteristic-p coefficients are allowed on characteristic-p bases. The sole
universe u is explicitly declared; coefficient and module universe u+1 matches
both recorded sheaf and six-functor APIs and admits all finite coefficients by
lifting. All identifiers and universes in the signature are bound.

Independent searches, with different wording from the first reader:

- `msearch.py ... leanfinder "constructible cohomology of constant torsion
  coefficients for a smooth proper curve"`: eight hits, involving cotangent,
  group or ordinary sheaf cohomology; none is the required theorem.
- `msearch.py ... loogle '"higherDirectImage", "constructible"'`: zero hits.
- `msearch.py ... leansearch "constructibility of the higher pushforwards of a
  finite constant sheaf under a proper smooth relative curve"`: unavailable,
  Internal Server Error; not counted as evidence of absence.
- Direct rg on Mathlib/AlgebraicGeometry, source WeilConjectures, and the
  project's lean/Sheaf for proper/smooth curve terms and the constructible
  higher-direct-image/name combinations: no matching existing statement or
  name collision. Nearby upstream constructible-sheaf declarations concern
  definitions, generic constancy or generation, not this curve-family theorem.

No new definition nodes or dependency modules are present or needed. All existing
statement dependencies are used through their recorded notions. I checked the
proof-dependency import list against the node: every dependency having a recorded
module is imported; the three not-yet-stated proof inputs are retained by id in
the proof plan and do not obstruct stating this result. The declaration docstring
faithfully records all six node proof steps, including the scalar-action upgrade,
fibre-dimension decomposition, dimension-zero case, prime case, exponent induction,
and final coefficient comparison and gluing. The source typo M[n] in the exact
sequence is correctly rendered as the prime kernel in the proof plan.

No mathematical or Lean mismatch found; I preserved the module and node unchanged.
Only this independent review was appended. The module has one named theorem with
proof sorry, no definitions or auxiliary proofs, correct source/blueprint docstrings,
no local notation or instances, and lines within 100 characters. A direct textual
check confirms lean.statement is verbatim the file signature.
