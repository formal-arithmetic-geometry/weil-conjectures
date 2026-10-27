## Worker report

The module `Sheaf.CategoryTheory.FibredRelativeCech` states
`CategoryTheory.FibredRelativeCech.relativeCech_baseChange`. All its definitions
contain actual data. The final theorem and the five construction-validity lemmas
have `sorry` proofs and source/proof docstrings. The natural-language statement and
its accepted stage-1 split are unchanged. This is the stage-2 handoff explicitly
allowed by coord/brief-stage2.md section 0; the inherited Q122 rejection concerned
repeating stage 1, not writing this missing Lean statement.

Hypothesis and clause correspondence:

- The scheme S is `{S : AlgebraicGeometry.Scheme.{u}}`. The explicit levels `u v`
  implement the size convention; total categories are `BasedCategory.{v, v}
  (Over S)`, small in the sheaf universe v. Coefficients are `AddCommGrpCat.{v}`;
  derived localization uses the standard universe v+1. There is no equality
  imposed between the scheme universe u and site universe v. A common larger
  bound for different total categories is precisely the small-skeleton convention.
- U, X, Y are based categories over Sch/S. The arguments `hU`, `hX`, `hY` use
  the dependency's `CategoryTheory.IsFibredInGroupoids`. The morphisms f and e
  are the existing `BasedFunctor`, with its equality over the base. There is no
  stack, atlas, algebraicity, representability, nonemptiness, or covering hypothesis.
- The big etale site is `topology`: comap of
  `Scheme.etalePrecoverage` along `X.p ⋙ Over.forget S`, followed by
  `Precoverage.toGrothendieck`. Thus covering presieves are exactly those whose
  scheme images are jointly surjective etale families. `Ab X` is the existing
  category `Sheaf (topology X) AddCommGrpCat`, with the usual equalizer meaning.
- Pullback is literally `pull f`, precomposition with f.op. `sheafPull` lifts the
  same data through the full subcategory of sheaves. Its sheaf proof is named
  `sheaf_functoriality`; the instance `sheafPull_additive` records sectionwise
  additivity. Neither definition chooses an unspecified functor.
- Pushforward is `push f = f.op.ran`. Mathlib's
  `Functor.ranObjObjIsoLimit` identifies its value at x with the compatible-family
  limit indexed by arrows f(a) -> x (the structured-arrow category of f.op).
  Factorization through cartesian lifts identifies that category with the test
  fibre over Sch/T. This is precisely 06W6, including restrictions and coefficient
  maps. Right Kan extension is determined by its universal property; its use is
  not a choice from an undetermined existence assertion.
- `Nerve f n` is the full comma subcategory of n-tuples u_i, a shared target x,
  and vertical isomorphisms f(u_i) -> x. Arrows satisfy the comma equation.
  `projection f (p+1)` is f_p. These are the full 2-fibre products, retaining
  automorphisms, rather than products of isomorphism classes. The vertical
  condition uses the existing `IsHomLift` predicate.
- `sheafTerm hU hX f F p` is exactly `(f_p)_* f_p^{-1} F`.
  `degree ... (-1)` is F, nonnegative degree p is `sheafTerm ... p`, and every
  degree below -1 is the zero sheaf. `term_isSheaf` is its named validity lemma.
- `select f a` selects coordinates. `face ... p j` is restriction along
  `select f j.succAbove`, deleting the j-th factor. `restrict` is the right-Kan
  counit transpose, as in remark-cech-complex-presheaves. The augmentation is
  the corresponding adjunction unit. `differential` is exactly
  `sum j : Fin (p+2), (-1 : Int)^j.val` times these face maps, uses the
  augmentation in degree -1, and is zero below that. `differential_squared`
  states the construction's square-zero condition, with the alternating
  cancellation proof in its docstring. `complex` uses `CochainComplex.of`.
- The statement explicitly requests the base-changed nerve. `BaseNerve f e n`
  is the dependency's `moduliTwoFiberProduct e (nerveBasedProjection f n)`;
  `baseProjection` is its first projection to Y. Hence its n=p+1 level is
  Y times_X U_p. By the source's shared-target equivalence it is the nerve of
  V=Y times_X U with projection g, using a common Y-coordinate. No comparison
  equivalence is assumed as an extra hypothesis. Faces are `baseSelect`, which
  leave Y fixed and delete the indicated U-coordinate. `baseTerm`,
  `baseAugmentation`, `baseDegree`, `baseDifferential`, and `baseComplex` repeat
  exactly the prescribed construction with coefficient e^{-1}F. Their named
  validity lemmas are `baseTerm_isSheaf` and `baseDifferential_squared`.
- `baseCoefficientIso` is the explicit coefficient identification induced by
  the vertical isomorphism e(y) -> f_p(z). It uses `F.mapIso`, not an arbitrary
  chosen isomorphism. `baseChange` is the transpose of the counit after this
  transport, thus restriction of compatible families along the test-fibre
  comparison. `comparisonDegree` is this map in nonnegative degrees, identity
  on e^{-1}F in degree -1, and the unique zero map in lower degrees.
- The theorem produces `beta F` as an isomorphism from the actual pulled-back
  integer-indexed complex to `baseComplex`. Its first clause identifies EVERY
  component with `comparisonDegree`, fixing the canonical map and degree -1
  identity. Being a complex morphism also imposes the augmentation equality,
  not merely termwise isomorphisms. Its second clause explicitly imposes
  compatibility with EVERY individual face, before taking the alternating sum.
- `degreeMap` and `baseDegreeMap` apply each original term functor to a morphism
  of coefficients. The third theorem clause states the naturality square in
  EVERY integer degree, including -1 and the zero terms; these are exactly
  the components of naturality of the complex comparison in F.
- The last clause gives the derived isomorphism delta and the equality
  `delta.hom = DerivedCategory.Q.map (beta F).hom`. Thus the derived consequence
  is the canonical localization of the specified comparison, with no arbitrary
  derived isomorphism substituted. `derivedCategory` uses
  `HasDerivedCategory.standard`; no existence hypothesis was added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms,
  and `Over S` from Mathlib's comma-category interface.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`; its definitions were read in full. The stable-curve
  specialization is not imposed on the arbitrary fibred categories here.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` supplies the node's site
  convention; the actual sheaf category uses Mathlib's `Sheaf` and
  `Presheaf.IsSheaf`, as that dependency explicitly specifies.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale` via the public import
  `Mathlib.AlgebraicGeometry.Sites.Etale`: `AlgebraicGeometry.Etale` and
  `Scheme.etalePrecoverage`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- `def-weil-size-convention` is a recorded metatheoretic convention rather
  than a Lean declaration; it is rendered by the explicit universes above.
- `Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings`:
  its full theorem signature and docstring were read. It is a proof dependency,
  imported without `public`; its precomposition/right-adjoint construction is
  used in the documented proof of sheaf_functoriality.
- The proof dependencies `lem-sfb-fibred-site-functor-continuity` and
  `lem-sfb-fibred-presheaf-pushforward-base-change` have no recorded declaration
  or Mathlib match on the read base. Their statements are referenced in proof
  docstrings; no fictitious import or theorem assumption was introduced. The
  item directly constructs the maps to which these eventual proofs apply.

The additional declarations in this module construct E, its base-changed nerve,
and its canonical comparison, which the item itself explicitly introduces.
They are recorded in `lean.declarations`, with this item's blueprint tags, as
per the authorization for helpers of the owning node. There is no independent
new definition node and no dependency-record replacement. Five postponed lemmas
are the stated sheaf and square-zero obligations of these same constructions;
each has its complete natural-language proof route in its docstring.

Edge cases checked before finalizing the statement: an empty total category
or empty test fibre (compatible families give the terminal/zero group), zero
coefficients, p=0 (one factor and two subsequent faces), degree -1 (identity
component and augmentation), every degree below -1 (zero sheaves and zero
maps), arbitrary automorphism groups, and e or f an identity. No Fintype,
Finite, Nonempty, algebraic-stack, or representability requirement excludes any
of these cases. Both inverse-image data and coefficient transport remain the
same for an identity base change. No assertion of exactness of E is made.

Searches performed (no exact existing comparison found):

- `msearch.py`, LeanFinder: "The relative Cech complex of abelian sheaves on
  categories fibred in groupoids commutes with base change". Eight hits,
  including Plus.res_mk_eq_mk_pullback, diagramCompIso_hom_iota, and the
  MayerVietorisSquare sheaf condition; none gives this fibred-groupoid comparison.
- `msearch.py`, Loogle: `"cechNerve", "iso"`. Twelve hits for the ordinary
  categorical nerve, terminal-object product comparisons, and formal
  coproducts. These do not implement the 2-fibre-product sheaf-valued nerve.
- `msearch.py`, Mathlib grep:
  `relativeCech|relative_cech|[Cc]ech.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*[Cc]ech`.
  Zero hits.
- `msearch.py`, LeanSearch: "The augmented relative Cech complex of abelian
  sheaves on categories fibred in groupoids is unchanged by two cartesian
  base change". Eight ordinary augmented-nerve and ChainComplex.augment hits;
  no match for fibred-groupoid sheaf complexes.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, for relativeCech,
  relative_cech, Cech/base-change combinations, and fibred pushforward.
  Read the near hit `WeilConjectures.CategoryTheory.Sites.CechBaseChange`:
  it contracts a finite cover's sections complex in an ordinary category;
  it is not this arbitrary fibred-groupoid base-change statement. Other hits
  concern affine tensor/cohomology base change. No exact match.
- `grep -rn` of this item's id in `lean/WeilConjectures`: no hit.
- DAG/project searches for the proposed helper name and fibred relative Cech
  notions found no existing standalone definition. `blueprint_refs.py search
  'relative Cech'` found no blueprint nodes. The ancestor resolver reports the
  inherited null ancestor; no node metadata was changed to conceal this. No
  new node requiring an invented ancestor was created.

Sources read: stacks-sheaves.tex, extended relative Cech construction,
remark-cech-complex-presheaves, lemma-generalities-sheafified,
remark-cech-complex-sections, and lemma-base-change-cech-complex (Tag 06XC).
The base-changed nerve and sectionwise/right-Kan presentation are the source's
canonical presentation, not a replacement mathematical statement.

Validation: the required scompile wrapper compiles the module separately under
the standard 60-second limit; no errors or non-sorry warnings. The required
deliver2 dry run passed preflight and compilation (7c16bd3a246). Source-tag
spellings in docstrings were then checked against the Stacks tag table; a final
dry run and delivery repeat all mandatory validation.

No STATEMENT-DISPUTED issue, statement correction, or dependency change.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
