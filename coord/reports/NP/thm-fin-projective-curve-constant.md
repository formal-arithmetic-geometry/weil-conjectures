## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveCurveConstant` states
`AlgebraicGeometry.isConstructibleEtaleModuleSheaf_higherDirectImage_prime_of_projective_curve`
with the sole proof `sorry`. It introduces no definitions, helper statements, or new nodes.
The node's statement is unchanged. The theorem docstring follows all nine proof steps.

Clause-by-clause correspondence:

- “over a field”: `(k : Type u) [Field k]` and
  `(X S : Over (Spec (.of k)))`; the morphism `(f : X ⟶ S)` is over this same field.
- “between schemes of finite type”: `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`
  and `[LocallyOfFiniteType S.hom] [QuasiCompact S.hom]`, precisely the recorded conjunction.
- “f projective”: `[IsProjective f.left]` uses the canonical upstream class.
- “geometric fibres have dimension at most one”: `hdim` quantifies over **all**
  `s : S.left`, uses `pullback f.left` along the composite from the spectrum of
  `AlgebraicClosure (S.left.residueField s)` to `S.left`, and requires
  `topologicalKrullDim ... ≤ 1`. It does not replace geometric fibres by ordinary fibres.
- “ell prime”: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- “invertible on S”: `hinv : IsUnit (ℓ : Γ(S.left, ⊤))`. A section is a unit iff it
  is stalkwise a unit, so this expresses invertibility on the whole base, including empty S.
- “every higher direct image”: arbitrary `(q : ℤ)`, the degree-q homology of
  `Etale.rightDerivedLowerStarPlus` applied to the degree-zero single complex.
  This includes the ordinary direct image in degree zero and zero negative images.
- “F_ell”: the constant sheaf from `constantSheaf` with regular module
  `ModuleCat.of (ULift (ZMod ℓ)) (ULift (ZMod ℓ))`. `ZMod ℓ` is the prime field;
  `ULift.{u+1}` changes only size to the coefficient universe required by the small etale site.
- “is constructible”: `Scheme.IsConstructibleEtaleModuleSheaf`, the exact finite
  locally closed constructible stratification predicate used by the recorded
  bounded-constructible-complex dependency, with finite constant module local models.

Dependencies read and used:

- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsProjective`. Read using `scompile.py --source` since the local
  checkout lacks this split module; the server source extends `IsHProjective` and
  `QuasiCompact`, and defines projectivity by finite projective-space embeddings.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; its section formula is evaluation on fibre products.
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `Etale.rightDerivedLowerStarPlus`, the bounded-below right derived pushforward.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  sheafification of the constant presheaf.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, whose cohomology-sheaf clause uses
  `Scheme.IsConstructibleEtaleModuleSheaf` from
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`. Read both definitions.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, with the geometric-point composite in the dependency record.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, supremum of lengths of
  irreducible closed chains, valued in `WithBot ℕ∞`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `def-weil-pbc-scheme-conventions` is a convention record with no declaration/module;
  its properties are rendered through the concrete recorded dependencies above.

Recorded proof-dependency modules are imported non-publicly unless already a public
statement import, with two incompatible legacy modules omitted: ProjectiveImpliesProper
and ProjectiveBaseChange both import the retired Sheaf.AlgebraicGeometry.Morphisms.Projective,
which redeclares the canonical upstream IsHProjective and prevents any common import.
The server compiler confirmed the duplicate IsHProjective.mk error. These legacy proof-only
imports require a maintainer upstream-import sync before stage 3; the statement uses the
canonical recorded upstream definition throughout. Unrecorded proof lemmas are named in the natural-language proof but have
no module import yet. In particular the smooth-curve finiteness proof dependency has no
recorded Lean declaration; it is not required to type this theorem's statement.

Edge cases checked: no nonemptiness, smoothness, connectedness, irreducibility, reducedness,
Noetherianity, flatness, or separateness assumption is imposed on X or S beyond the node.
Empty X, empty S and empty geometric fibres are allowed (dimension bottom ≤ 1).
Zero-dimensional and mixed zero/one-dimensional fibres are allowed. The field is arbitrary,
including imperfect and positive-characteristic fields; invertibility excludes exactly
residue characteristic ell. The prime condition excludes ell = 0 and ell = 1. All integer
degrees are allowed. No finite-type hypotheses on the morphism are imposed beyond projectivity.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “Higher direct images of constant finite field sheaves
  under projective morphisms with geometric fibres dimension at most one are constructible”.
  Eight hits: topological constructible images, finite scheme fibres, and unrelated results;
  no etale cohomological constructibility theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsProjective, CategoryTheory.Sheaf`.
  Zero hits (public Loogle does not know the project's IsProjective).
- `msearch.py ... grep`: `constructible.*(direct|push)|higher.*direct.*image` in
  Mathlib/AlgebraicGeometry: zero hits.
- `rg` in upstream WeilConjectures, current lean/Sheaf, and dag/lean_names_upstream.json:
  `thm-fin-projective-curve-constant|constructible.*projective|projective.*constructible`.
  No matching theorem; current ProjectiveCurveFiniteGroup cites this unformalized theorem
  and states the subsequent general-finite-group consequence, so is not a duplicate.
  ProjectiveFlatCoherentRanks concerns coherent cohomology; the pro-etale Perfect result
  concerns flat modules, neither is the statement here.

- `msearch.py ... leansearch`: “Constructible higher direct images of constant prime field
  sheaves under projective morphisms with geometric fibres of dimension at most one”.
  Service unavailable (Internal Server Error); no verdict from this unavailable search.

No statement fault or disputed assertion found. No statement correction, dependency repair,
or new definition was necessary.

Validation: after omitting the two incompatible legacy proof imports, the single-file
compile completed cleanly. `deliver2.py NP thm-fin-projective-curve-constant --no-push`
printed OK: the module compiles and passes preflight except for the independent second
reading, which the designated second reader supplies. Nothing was pushed.


## Second reading by NP

I independently read the complete node, its eight statement dependencies and their
recorded interfaces, the sandbox module, and the source blueprint statement and proof
at sec-smooth-purity/sk-prop-sf-cbc/thm-fin-projective-curve-constant.md. The item's
source is this blueprint, rather than a Stacks theorem with an additional standing
hypothesis. The source assumes finite type over an arbitrary field, projectivity,
geometric fibre dimension at most one, and a prime invertible on the base. It does
not assume smoothness, connectedness, reducedness or a perfect field.

Object, hypothesis and conclusion checklist (H3):

1. A field: `(k : Type u) [Field k]`. Exact; no characteristic or perfection constraint.
2. Two schemes over that same field: `(X S : Over (Spec (.of k)))`.
   The object hom fields are their structure maps. Exact.
3. Both schemes are finite type over k: `[LocallyOfFiniteType X.hom]`
   and `[QuasiCompact X.hom]`, and the corresponding two instances for S.
   I opened the Mathlib classes: this is precisely the conjunction recorded by
   def-weil-finite-type-morphism, not finite presentation or separatedness. Exact.
4. A morphism over k: `(f : X ⟶ S)`, with underlying map `f.left`.
   The Over category supplies its structural-map compatibility. Exact.
5. Projectivity: `[IsProjective f.left]`. I fetched the current upstream
   WeilConjectures.AlgebraicGeometry.Morphisms.Projective source using
   `scompile.py --source`. Its class extends H-projectivity and quasi-compactness;
   H-projectivity is a closed immersion into relative projective space with a
   finite homogeneous-coordinate type. This is the dependency's embedding convention.
   Exact, with no extra Proper or Noetherian binder.
6. All geometric fibres have dimension at most one: `hdim : ∀ s : S.left, ... ≤ 1`.
   Its pullback is along `Spec.map` of the residue-field inclusion into
   `AlgebraicClosure (S.left.residueField s)`, followed by `fromSpecResidueField s`.
   This is verbatim the geometric-fibre dependency's construction, for all points,
   not just closed points. Mathlib `topologicalKrullDim` is the dimension of the
   poset of irreducible closed subsets. Exact.
7. A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`. Exact, excluding precisely 0 and 1.
8. Ell invertible on S: `hinv : IsUnit (ℓ : Γ(S.left, ⊤))`.
   Being a unit in global sections is equivalent to being a unit in every stalk:
   local inverses are unique and glue. Thus this neither imposes invertibility
   on an unoccupied ambient field nor excludes the empty base. Exact.
9. The constant prime field sheaf: `constantSheaf` applied to the regular module
   `ModuleCat.of (ULift (ZMod ℓ)) (ULift (ZMod ℓ))`.
   I opened Mathlib's definition: it is constant-presheaf sheafification.
   ZMod at a prime is F_ell; ULift changes its size only. Exact.
10. Every higher direct image: arbitrary `(q : ℤ)`; `singleFunctor ... 0` places
    that sheaf in degree zero, `Etale.rightDerivedLowerStarPlus ... f.left`
    applies its bounded-below derived direct image, and
    `DerivedCategory.Plus.homologyFunctor ... q` takes its degree-q sheaf.
    I opened both upstream lowerStar (evaluation on the base change) and
    rightDerivedLowerStarPlus (the rightDerivedFunctorPlus of that same functor).
    These are the module-sheaf clause of def-weil-pbc-direct-image, not coherent
    or pro-etale cohomology. Exact; no simultaneous vanishing assertion is added.
11. Constructible: `Scheme.IsConstructibleEtaleModuleSheaf`.
    I opened BoundedConstructibleComplexes and its imported defining module, and
    LocallyClosedStratification. The predicate is a finite partition realized by
    scheme immersions, with constructible locally closed parts, and on each part
    an etale cover with finite constant module models. This is precisely the
    sheaf clause of def-weil-pbc-constructible-complexes. Exact.

Edge cases: empty X and empty S are permitted; empty geometric fibres have bottom
Krull dimension and meet the bound. Zero-dimensional and mixed zero/one-dimensional
fibres are permitted. No exact-dimension, nonempty, smooth, connected, normal,
integral or reduced assumption is present. Degree zero is included, and negative
degrees give zero sheaves. Positive and zero characteristic are permitted subject
only to invertibility on S. The coefficient module is finite, with its canonical
regular action, not an arbitrary chosen module or map. Universe u is arbitrary;
small etale coefficient modules live in u+1 as required by the recorded interfaces.
All schemes and the field can be resized to one common ambient universe. There is
no independently quantified test universe or hidden equality of universes.

Independent H4 searches, with different queries from the first reader:

- LeanFinder via msearch: "Finiteness constructibility of etale cohomology with
  constant ZMod coefficients for projective relative curves". Eight unrelated hits
  (cotangent modules, finite scheme fibres, affine-space finite presentation,
  etale algebra descent, and class groups); no matching theorem.
- Loogle via msearch: `ZMod, CategoryTheory.Sheaf`. Zero hits.
- rg in Mathlib/AlgebraicGeometry, upstream WeilConjectures and lean/Sheaf:
  case-insensitive `((constructib|finite).*higher.*(image|push))` and
  `((projective|proper).*curve.*constant)`. I opened the substantive nearby hits.
  ProjectiveCurveFiniteGroup is the subsequent finite-abelian-group consequence,
  with an abelian constructibility predicate, not this theorem.
  EtaleProperDirectImageFiniteness is the general proper theorem with Noetherian,
  dimension and general coefficient hypotheses. ProperSmoothCurvesFiniteModule
  imposes smoothness and geometrically connected nonempty fibres. Upstream
  Etale/Derived/Finiteness/DirectImage states general finite-type bounded
  constructibility using the other IsConstructibleSheaf predicate. None has this
  node's statement or replaces this declaration exactly.

No new node or dependency module occurs in this delivery. No statement_change
occurs, so no corrected-statement citer audit is needed. No hollow definition,
private notion, local notation or proof beyond the sole `sorry` occurs. The
source/blueprint docstrings are present and the theorem's proof docstring follows
all nine node proof steps, including coefficient comparison, the stalk diagonal,
Noetherian induction, reducible bases and reduction.

I also independently fetched the current ProjectiveBaseChange server source and
opened ProjectiveImpliesProper locally. Their legacy imports still refer to
Sheaf.AlgebraicGeometry.Morphisms.Projective, conflicting with the canonical upstream
classes. The worker report already identifies these two proof-only import omissions;
the canonical projectivity module supplies properness, and neither missing proof
import affects the statement interface. I retain that explicit stage-3 integration
note and do not substitute a second projectivity definition.

Mismatches found: none in the statement, dependency objects, hypotheses,
quantifier order, or conclusion. Changes: this independent reading and validation
record only; the correct Lean and node were left unchanged. I mechanically compared
lean.statement to the theorem signature through the colon before its proof: exact
verbatim equality. I compiled the delivered module via scompile.py on the server;
both sandbox and library checks passed cleanly (3.7 s and 3.9 s), with no warnings.
