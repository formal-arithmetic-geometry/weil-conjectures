## Worker report

Record existing: `AlgebraicGeometry.SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension`
in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, source lines 136–138.
No module, new definition, dependency module, or proof is written.

Hypothesis and conclusion comparison:

- Schemes X and S and morphism f are the ambient `{X Y : Scheme.{u}} {f : X ⟶ Y}`,
  with Y naming S. The arbitrary universe u imposes no size restriction beyond the library's
  scheme convention.
- Smoothness of pure relative dimension d is `[SmoothOfRelativeDimension n f]`, with n = d.
  This is the exact recorded declaration of dependency `def-sbc-smooth-morphisms`, whose
  K1 record and R-dsm1444 review explicitly accept this notion via Stacks 02G1/02G2.
  Smoothness follows from `SmoothOfRelativeDimension.smooth`; no additional smoothness
  assumption is needed.
- Every point x is `∀ (x : X)`.
- T = Spec R is `(U : Y.Opens) (_ : IsAffineOpen U)` with R = Γ(Y,U).
  V = Spec A is `(V : X.Opens) (_ : IsAffineOpen V)` with A = Γ(X,V).
  `IsAffineOpen.isoSpec` supplies the actual isomorphisms to those spectra, not an
  assumption that the opens literally equal a chosen syntactic spectrum.
- V is a neighbourhood of x by `(_ : x ∈ V)`.
- f(V) is contained in T by `(e : V ≤ f ⁻¹ᵁ U)`; together with x ∈ V this also gives
  f(x) ∈ U. Thus the base-neighbourhood clause is present even though not separately bound.
- The ring map of the restriction is `(f.appLE U V e).hom`, namely pullback on
  sections followed by restriction to V, as its definition and docstring specify.
- Standard smooth of relative dimension d is
  `IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom`.
  The ring-hom predicate uses the algebra induced by this very map. Its algebra version
  asserts a finite `SubmersivePresentation` P with `P.dimension = n`. The injective map
  from relations to variables gives c ≤ the number of variables; `dimension` is their
  cardinality difference. Renumbering the finite sets puts the distinguished variables
  first, exactly the polynomials, quotient presentation, and unit Jacobian determinant
  of `def-weil-pbc-standard-smooth-algebra`. This expresses existence of a presentation
  of dimension d, not the dimension of an arbitrarily chosen presentation.

Dependency declarations read and used:

- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` and
  `AlgebraicGeometry.SmoothOfRelativeDimension`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
  Read both class signatures, their docstrings, the chart field, and the smoothness lemma.
- `def-weil-affine-spectrum` (Mathlib leaf): `AlgebraicGeometry.Spec`,
  Mathlib.AlgebraicGeometry.Scheme, with `IsAffineOpen.isoSpec` in
  Mathlib.AlgebraicGeometry.AffineScheme explaining the chart identification.
- `def-weil-pbc-standard-smooth-algebra` (Mathlib leaf): `Algebra.IsStandardSmooth`,
  Mathlib.RingTheory.Smooth.StandardSmooth. Read also `Algebra.IsStandardSmoothOfRelativeDimension`,
  `RingHom.IsStandardSmoothOfRelativeDimension` (Mathlib.RingTheory.RingHom.StandardSmooth),
  `Algebra.SubmersivePresentation` and `PreSubmersivePresentation`
  (Mathlib.RingTheory.Extension.Presentation.Submersive), and `Presentation.dimension`
  (Mathlib.RingTheory.Extension.Presentation.Basic).

Edge cases checked: empty X makes the assertion vacuous for every n; n = 0 is included;
no nonempty, nontrivial-ring, Noetherian, separated, field, characteristic, or properness
hypothesis is added. At an actual point the source affine chart cannot be empty; the
base affine chart contains its image. Finite relation/variable sets include empty sets.
An empty scheme can have every relative dimension, consistently on both sides.

Searches:

- `msearch.py ... leanfinder "smooth morphism of relative dimension d has affine open
  neighborhoods with standard smooth coordinate ring map of relative dimension d"`:
  eight hits, led by the old-name alias
  `IsSmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension`.
- `msearch.py ... loogle "AlgebraicGeometry.SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension"`:
  one exact hit, with the affine-open and prescribed-dimension conclusion.
- `msearch.py ... grep "exists_isStandardSmoothOfRelativeDimension|class SmoothOfRelativeDimension"
  AlgebraicGeometry/Morphisms`: five hits, including Smooth.lean lines 135–138.
- `rg -n "exists_isStandardSmoothOfRelativeDimension|lem-sc-standard-smooth-local-relative-dimension"`
  in WeilConjectures and lean/Sheaf: upstream uses of the Mathlib field in Differentials,
  RegularImmersion, and the upstream Mathlib extension; no private replacement in Sheaf.
  No upstream occurrence of the node id was found.
- Direct source searches/readings of the standard-smooth presentation and ring-hom
  predicates confirm the dimension clause and unit-Jacobian condition.

Source verification: the local Stacks files named by the node are not installed here,
so opened [Tag 02G2](https://stacks.math.columbia.edu/tag/02G2) and
[Tag 054L](https://stacks.math.columbia.edu/tag/054L) online. The former defines constant
relative dimension via the differential rank, and the latter's proof chooses affine
standard-smooth charts and sets the dimension to the number of variables minus relations.

The item's older search verdicts deliberately rejected this field when treating fibre
dimension as a separately formalized premise. Since then the dependency has landed an
explicit existing Mathlib record accepting `SmoothOfRelativeDimension`, with its
mathematical equivalence reviewed. This delivery uses that recorded notion, as required
by the one-definition rule. It does not redefine fibre dimension or change the item.
There is no disputed statement or node correction.

## Second reading by J1

I independently opened the item JSON, each of its three statement-dependency nodes,
and the declaration in Mathlib.AlgebraicGeometry.Morphisms.Smooth, lines 135–138,
including its ambient variables and class docstring. The recorded lean.statement is
verbatim equal to the field signature in that file (checked by string comparison).
No mathematical or signature mismatch was found; only this second-reading report
was added. There is no delivered module, new node, dependency module, or statement
correction to review or compile.

Objects, hypotheses, and conclusion clauses, matched separately:

- Schemes X and S: ambient `{X Y : Scheme.{u}}`, with Y = S. Verdict: exact,
  arbitrary universe u, no assumptions on either scheme.
- Morphism f: ambient `(f : X ⟶ Y)` of the class, implicit `{f : X ⟶ Y}`
  in its projection. Verdict: the same scheme morphism, no structural map substituted.
- Nonnegative pure relative dimension d and smoothness: ambient `{n : ℕ}` and
  `[SmoothOfRelativeDimension n f]`, n = d. Verdict: exact using the dependency
  def-sbc-smooth-morphisms's recorded SmoothOfRelativeDimension, not an extra premise.
  I read that dependency's full statement, Mathlib record, and reviewed_lean verdict.
  I also independently checked its mathematical interpretation rather than relying
  on its name: Stacks 02G1 identifies differential rank and dimension at x of the
  smooth fibre; 02G2 says smooth with differentials locally free of constant rank d.
  Standard-smooth charts have rank equal to presentation dimension. Conversely,
  local standard-smooth charts for a smooth morphism must have dimension d by
  comparison at the residue field of x. Thus the chart-based class and the node's
  fibre-dimension premise have the same meaning; the older no-match searches assumed
  a separate fibre-dimension predicate which the dependency does not now record.
- Each point x: `∀ (x : X)` precedes the chart existential. Verdict: exact;
  neighbourhoods may depend on x, and no point is required globally.
- Affine neighbourhood T = Spec R of f(x): `(U : Y.Opens) (_ : IsAffineOpen U)`.
  Verdict: exact with R = Γ(Y,U); `IsAffineOpen.isoSpec` identifies the open scheme
  with that spectrum. The membership clause follows from x ∈ V and e below.
- Affine neighbourhood V = Spec A of x: `(V : X.Opens) (_ : IsAffineOpen V)
  (_ : x ∈ V)`. Verdict: exact with A = Γ(X,V), again by isoSpec. Existential
  order T then V is equivalent to the node's V then T; neither has been universally
  quantified or fixed in advance.
- Image containment: `(e : V ≤ f ⁻¹ᵁ U)`. Verdict: exactly f(V) ⊆ T;
  applying e to the membership proof also gives f(x) ∈ T.
- Ring map R → A induced by the restriction: `(f.appLE U V e).hom`.
  Verdict: exact. I opened Scheme.Hom.appLE: it is f.app U composed with the
  presheaf restriction along e, not an arbitrary algebra structure on A.
- Standard smooth with a presentation of relative dimension d:
  `RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom`.
  Verdict: exact. I opened this ring-map predicate, which uses the algebra
  induced by that same ring map, and Algebra.IsStandardSmoothOfRelativeDimension.out:
  it asserts finite variable/relation types and a SubmersivePresentation P with
  P.dimension = n. PreSubmersivePresentation.map_inj gives c ≤ number of variables;
  Presentation.dimension is Nat.card variables minus Nat.card relations, so there
  is no truncated-subtraction weakening. SubmersivePresentation.jacobian_isUnit,
  jacobian_eq_jacobiMatrix_det, and jacobiMatrix_apply give precisely the unit
  determinant of partial derivatives from the dependency's standard-smooth
  presentation. Finite reindexing puts the selected variables first. This is an
  existential prescribed-dimension presentation, not the unrelated chosen
  IsStandardSmooth.relativeDimension value.

Source reading: literature/stacks-project is absent on this machine. I read the
actual morphisms.tex from the official Stacks repository, including the start of
section-smooth and the full statements/proofs at
`definition-smooth-relative-dimension` (02G2),
`lemma-smooth-omega-finite-locally-free` (02G1),
`lemma-smooth-locally-standard-smooth` (01V7), and
`lemma-smooth-etale-over-affine-space` (054L). There are no ambient Noetherian,
separated, field, or characteristic assumptions. 054L's proof chooses a standard
smooth presentation and uses the number of variables minus relations; 02G1/02G2
force that number to be d as in the node's two proof steps. Sources:
[Stacks morphisms.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex),
[02G2](https://stacks.math.columbia.edu/tag/02G2),
[054L](https://stacks.math.columbia.edu/tag/054L).

Dependency reading: def-weil-affine-spectrum's Mathlib leaf records Spec, whose
signature and affine-open isoSpec I opened in Scheme.lean/AffineScheme.lean.
Def-weil-pbc-standard-smooth-algebra's leaf records Algebra.IsStandardSmooth;
I opened its class and the finite submersive presentations in StandardSmooth.lean,
Submersive.lean and Basic.lean, as well as the prescribed-dimension algebra and
ring-map predicates used above. Neither dependency needs a replacement module.

Edge cases: n = 0 is permitted. Empty variable/relation types are permitted (the
empty determinant is 1). Empty X makes the universal conclusion vacuous for every
n, just as the smooth constant-rank condition is vacuous there. A point of V makes
V nonempty and e makes T contain its image; no Nontrivial ring assumption is added.
If the base is empty, any scheme morphism into it has empty source. All commutative
rings, including zero rings, and every characteristic are allowed. Finite index
sets can always be renumbered in Type 0, so the presentation class's Type binders
lose no finite presentation, even for schemes in arbitrary universe u. There are
no unbound variables: n, X, Y, f and u come from the surrounding class declarations.

Independent searches, with different wording from the first worker:

- LeanFinder via msearch: `constant fibre dimension smooth map affine charts
  prescribed Jacobian rank` returned unrelated differential-geometric hits;
  no match was inferred from them.
- LeanFinder via msearch: `For a morphism of schemes smooth of dimension n, each
  point lies in affine opens whose induced algebra admits a finite submersive
  presentation of dimension n` returned the exact projection under its deprecated
  IsSmoothOfRelativeDimension alias, plus the smoothness and iff declarations.
  I verified the current name and full signature directly in this checkout.
- Loogle via msearch: `"SmoothOfRelativeDimension"` returned twelve algebra
  declarations, notably Algebra.IsStandardSmoothOfRelativeDimension and its out
  projection; these confirm the algebra notion, not a new scheme theorem.
- Mathlib grep via msearch: `submersive|smoothOfRelativeDimension_iff|
  exists_isStandardSmooth` in AlgebraicGeometry/Morphisms found the Smooth.lean
  projection at line 136 and the general standard-smooth chart results.
- Independent rg of `standard.smooth|SmoothOfRelativeDimension|relative.dimension`
  in WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry found uses
  and related diagonal/relative-dimension definitions, no required private copy.
  Exact-name/node-id rg over all WeilConjectures and lean/Sheaf found four uses
  of the Mathlib projection (Differentials, RegularImmersion, and the upstream
  Smooth extension), no competing declaration and no node-id occurrence.

H5/H6/H8/H9: no new definition, proof, or module is delivered; hence no hollow
body, new proved theorem, docstring, import, or line-width defect arises. The
existing Mathlib class docstring describes precisely its charts. The node's proof
and source remain intact; duplicating the projection just to add a docstring would
violate the one-definition rule. Retain existing: true. No changes to correct.
