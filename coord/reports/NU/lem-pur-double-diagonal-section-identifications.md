## Worker report

The module `Sheaf.Paper.DoubleDiagonalSectionIdentifications` states
`lem-pur-double-diagonal-section-identifications` in three named theorems,
all with whole proofs `sorry`. The namespace is
`WeilConjectures.PurityFiniteSetting.DiagonalPasting`.
`doubleDiagonalGeometry` gives the four Cartesian squares and section identities;
`doubleDiagonalProperties` gives the smooth separated finite-type assertions;
`doubleDiagonalSectionIdentifications` gives the three specified restriction equations.
The only new definition, `doubleDiagonalRestrictionEquations`, is the fully explicit
proposition containing those equations, with the source-implied compactifications and
dimensions installed internally. Its data are concrete expressions, not a choice of maps.
There are no new DAG nodes, dependency repairs, or statement corrections.

I read the whole standing stage-2 brief, stage document, delivery-errors H, worker role,
SETUP, GOAL, STATE and tools documentation. The specified CompactObject example is now
withdrawn (its module has no declarations); I used the current module-mode conventions
and the existing purity modules for the header and public interfaces.
No repair note exists for this item. I read each statement dependency's node statement,
recorded declaration signature and surrounding source docstring. Convention-only
scheme-morphism-properties has no declaration to import. Mathlib matches were read as
the dependency declarations, without requiring a lean record.

Source read: `literature/blueprint/latest/blueprint/sec-smooth-purity/` followed by
`sk-prop-sp-composition/thm-pur-composition-coherence.proof.md`, Step 1. Its final
paragraph says that the remaining smooth base-change constituents are compatible with
composition by the canonical maps and base-change squares of the composite. The DAG's
six-step refinement specifies these three exact equations. Its source path names an old
snapshot; I read the current latest file, not that old snapshot. The six proof steps are
rendered in the three theorem docstrings.

Hypotheses, individually matched:

- The complete finite-field, coefficient-extension and positive-level datum is
  `(P : PurityFiniteSetting.{u})`. Its fields give the algebraic closure of the finite
  field, the coefficient prime different from the characteristic, the finite
  subextension E, and the positive n. `P.Coefficient` is the published standard ULift
  of O_E/(varpi_E^n); there is no ramification-index divisibility restriction.
- `{X Y Z : Scheme.{u}}` and `(f : X ⟶ Y) (g : Y ⟶ Z)` give the tower. The structure
  map `(aZ : Z ⟶ Spec (.of P.field.k))` has `LocallyOfFiniteType` and `QuasiCompact`
  instances. The structure maps of Y and X are respectively `g ≫ aZ` and
  `f ≫ g ≫ aZ`. This explicitly encodes the same k-schemes and k-morphisms without
  requiring compatibility equations for redundant independent structure maps.
- Separated finite type for f and g is exactly `IsSeparated`, `LocallyOfFiniteType`
  and `QuasiCompact` on each. No absolute separatedness of X, Y or Z is assumed.
- `(d e : ℕ)` and the two `SmoothOfRelativeDimension` instances say pure smooth
  dimensions d,e, including zero. Smoothness and dimension of the composite and base
  changes are conclusions, not extra hypotheses.
- The finite-Tor constructible domain is the one fixed by the dependencies. The
  displayed objects are their specified dualizing and section objects; there is no
  free input K on which to add a new finite-Tor hypothesis. Their finite constructible
  etale origins compute the transported pro-etale operations. The equations compare
  actual pro-etale arrows via the published `SameProEtaleMap`.
- All HasCompactification, Noetherian, compact-space and coefficient-exponent instances
  needed by the published finite-coordinate API are derived inside the proposition,
  from finite type over the field and the existing Nagata/coefficient theorems. They
  are not additional assumptions of the main theorem. Local lets occur only in this
  definition's body; the theorem signature contains no let or hidden have.

Constructions and conclusions, clause by clause:

- Q is `pullback (f ≫ g) g`, W is `pullback (f ≫ g) (f ≫ g)`; W_f and W_g are
  `pullback f f` and `pullback g g`. The published `a f g`, `s f g`, `i f g`, and
  `j f g` are reused unchanged. Their definitions are universal-property morphisms,
  not formulas merely on geometric points. They send (x,x') to (x,fx'), x to (x,fx),
  the same pair to W, and (x,y) to (fx,y), respectively.
- b is `pullback.fst (f ≫ g) g`, l is `pullback.snd (f ≫ g) (f ≫ g)`, r is
  `pullback.snd (f ≫ g) g`, and t is `pullback.diagonal (f ≫ g)`.
- The first conjunct of `doubleDiagonalGeometry` is the square (l,a;f,r), and the
  second is (r,b;g,gf). Its third and fourth conjuncts are (i,p_f;a,s) and
  (j,b;p_g,f). These are all `IsPullback`, hence scheme-theoretic universal properties.
- The next six conjuncts explicitly give at=s, lt=1, rs=f, ba=p_gf,
  i Delta_f=t and js=Delta_g f (written in Lean's left-to-right composition order).
  The final equality li=p_2,f is the projection identity used by the node's proof.
- `doubleDiagonalProperties` explicitly asserts smooth dimensions d,e,d+e for a,b,ba,
  with `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` for each. Its last
  conjunct gives the source-implied dimension d+e of gf. The geometric theorems are
  stated generally on schemes, so their specializations give exactly the geometric
  clauses in the fixed coefficient setting.
- For each h, the existing `diagonalSection P.Coefficient P h` is the recorded
  `Etale.sectionInvariant` presentation of C_h. `alpha` calls the dependency's
  `finiteDiagonalRestriction`, using the canonical self-base-change counit mate.
  `comparedSectionPresentation` identifies the comparison image with the actual
  pro-etale section object; `finiteComparedDualizing` identifies the output.
- A is the existing `beta P.Coefficient P d (doubleDiagonalGeometry f g).1 ...`.
  The square has upper arrow l, lower arrow r, original map f and base-changed map a;
  this is precisely beta_(f,r), not an arbitrary isomorphism with the same endpoints.
- B is `beta ... e (IsPullback.of_hasPullback (f ≫ g) g).flip ...`. Its square has
  upper arrow r, lower arrow gf, original map g and base-changed map b. Thus it is
  beta_(g,gf). D is `beta ... (d+e) (IsPullback.of_hasPullback (f ≫ g) (f ≫ g)).flip ...`,
  exactly beta_(gf,gf), with upper arrow l and first projection p_gf.
- T_f and T_g are already inside the reused `gammaF` and `gammaG`: the former pulls
  inverse beta_(a,s) along Delta_f and uses i Delta_f=t; the latter pulls
  beta_(p_g,f) along s and uses js=Delta_g f. Their signatures and bodies were read.
  These are the node's specified gamma maps, not new or existential comparisons.
- The first conjunct of `doubleDiagonalRestrictionEquations` says that alpha_f.hom
  equals the hom of `gammaF ≪≫ t^*(A.symm) ≪≫ section(t,l)`. The final section
  comparison explicitly removes t^*l^* using lt=1. This is alpha_f=(t^*A)^(-1) gamma_f.
- Its second conjunct compares `f^*(alpha_g)` with
  `gammaG ≪≫ s^*(B.symm) ≪≫ comp(s,r,f).symm`. The last comparison is explicitly
  instantiated with rs=f. This is f^*alpha_g=(s^*B)^(-1) gamma_g.
- Its third conjunct compares alpha_gf with `t^*(D.symm) ≪≫ section(t,l)`, exactly
  the specified inverse diagonal restriction alpha_gf=(t^*D)^(-1).
- Every equality is wrapped in `SameProEtaleMap P.Coefficient P`: it is equality
  after the actual comparison inverse image to the small pro-etale derived category.
  Because these are the canonical etale-origin coordinates of the constructible
  operations, their canonical source and target comparisons give the node's arrows.
  Equality of isomorphisms is expressed by equality of their homs, which is equivalent
  since inverses are unique. No per-degree substitute is used.
- c, theta and sigma in the opening paragraph fix conventions; they do not occur in
  the three claimed equations. Their existing definitions are imported, and no new
  compositor or symmetry convention is introduced. No orientation or Tate twist is
  supplied anywhere in the delivery.

Dependency declarations used or retained in the plan:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `PurityFiniteSetting`,
  `Ring`, `Coefficient`, with their canonical coefficient ring structures.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`,
  `finiteTorConstructibleEtale`, with the reexported pro-etale finite-Tor predicate.
- `def-weil-pbc-proetale-site`: Mathlib `Scheme.ProEt` and `ProEt.topology`.
- `def-weil-scheme-morphism-properties`: convention only; Mathlib's `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` are the applicable recorded notions.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `Smooth` and `SmoothOfRelativeDimension`.
- `def-pc-fibre-product`: Mathlib `CategoryTheory.Limits.pullback`, its fst/snd,
  diagonal and universal maps, and `CategoryTheory.IsPullback`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`,
  the existing finite-coordinate derived operations reexported by its dependencies.
  Higher-coefficient internal Hom is not used in this finite statement.
- `def-weil-exceptional-inverse-image`:
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`,
  `ConstructibleExceptionalCoefficients.System`; its finite operation is the recorded
  etale-origin exceptional operation, represented here by `Etale.dualizingComplex`.
- `def-pur-finite-exceptional-composition`: `Sheaf.Paper.PurityFiniteExceptionalComposition`,
  `finiteExceptionalComposition`, the specified adjunction conjugate; contextual here.
- `def-pur-co-smoothness`: `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`,
  `IsCohomologicallySmoothFiniteCompared`, `finiteComparedDualizing`,
  `finiteComparedInvertibleExponent`; underlying specified mate
  `Etale.dualizingComplexBaseChangeMap` in upstream UpperShriekCanonicalMaps.
- `def-pur-section-invariant`: `Sheaf.Paper.PuritySectionInvariantIntrinsic`,
  `sectionInvariantFinite` (retained public import), with the already published
  `Etale.sectionInvariant`/`comparedSectionInvariant` presentation used by alpha.
- `lem-pur-diagonal-base-change`: `Sheaf.Paper.PurityDiagonalBaseChangeCompared`,
  `finiteDiagonalRestriction`, `diagonalComparedProEtale`, `comparedDiagonalBaseChange`.
- Pullback composition and tensor dependencies:
  `Sheaf.Paper.IntegralFinitePullbackComposition`,
  `integralTowerGeneralPullbackComposition`, and
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
  `ringedTopoiCanonicalDerivedTensorPullback`. The finite-coordinate compositors are
  the already used upstream `Etale.leftDerivedUpperStarComp` and
  `Etale.leftDerivedUpperStarCompSectionIso`, with the same canonical normalization.
- `Sheaf.Paper.PurityDiagonalSectionPasting` provides the already defined a,s,i,j,
  alpha,beta,gammaF,gammaG,diagonalSection,SameProEtaleMap. These are reused to obey
  one definition per notion. The new equations are not asserted by its geometry or
  geometryProperties theorems; its final diagonalSectionPasting theorem is not used.
  Our setup uses our own `doubleDiagonalProperties` for the needed dimensions.
- Proof dependency `lem-pur-smooth-exceptional-tensor-pasting` is retained as the
  plain import `Sheaf.Paper.SmoothExceptionalTensorPasting`, including its
  `smoothExceptionalBasePasting` and unit-normalization results.
- The proof's smooth-dimension permanence and separated finite-type base-change
  declarations are in the imported Mathlib/WeilConjectures smooth, separated,
  finite-type and quasi-compact modules. `IsClosedImmersion.of_comp` and stability
  under base change support the closed-section arguments. The plain Mathlib
  ZariskisMainTheorem import supplies `IsClosedImmersion.iff_isProper_and_mono`.
  The recorded cohomological-smoothness theorem is reexported by the existing
  purity construction module; no second declaration is supplied.

Searches (actual tool outputs were inspected):

- msearch LeanFinder: `diagonal restriction exceptional inverse image smooth base
  change two Cartesian squares`; eight hits about scheme diagonal restrictions,
  affine morphism properties and ordinary pullback restriction. None gives the
  specified exceptional counit-mate equations.
- msearch Loogle: `CategoryTheory.Limits.pullback, Functor.mapIso`; zero hits, with
  service message `unknown identifier 'Functor.mapIso'`. This does not mean the
  existing local Functor.mapIso API is absent; it is used and compiles.
- msearch grep: `doubleDiagonal|diagonal.*[Pp]asting|finiteDiagonalRestriction`;
  zero Mathlib hits.
- msearch LeanSearch: `smooth exceptional inverse image diagonal base change
  restriction composition identities`; eight hits, including smooth base-change
  stability, smooth composition and pullback.diagonal_comp. No full statement.
- Local rg over WeilConjectures and Sheaf for the item id and
  `doubleDiagonal|double_diagonal|finiteDiagonalRestriction` found the existing
  diagonal-restriction construction and its use in PurityDiagonalSectionPasting.
  I opened and reused those definitions. The broader graph and diagonal search
  found no existing theorem asserting these three equalities.
- Exact grep for the item id under WeilConjectures returned no hits. Exact rg for
  `doubleDiagonalSectionIdentifications|doubleDiagonalRestrictionEquations` in
  the upstream-name inventory and both library roots returned no hits.

Edge cases checked: d=0, e=0, both zero; f or g identity; empty X, Y or Z; arbitrary
positive coefficient level; nonseparated finite-type base schemes. No point is selected
in the geometry proof, and `SmoothOfRelativeDimension` on empty sources is allowed.
The graph maps and their section equations use categorical universal properties, so
nilpotent test schemes are retained. Positive coefficient level is inherited from P,
with no n/e integrality assumption. All universes are explicitly bound; the existing
small-site and coefficient-size lifts are retained without equating object and
morphism universes. No STATEMENT-DISPUTED issue was found.

Import-cycle note for the maintainer: as with the delivered affine-difference tower,
this module imports `PurityDiagonalSectionPasting` to reuse its canonical helper data.
That node lists this item as a proof dependency. Do not add its reverse proof import
of this module: it would close a module cycle, and stage-2 rule 7 explicitly permits
omitting and reporting that import. No cyclic DAG edge is added, and no downstream
`diagonalSectionPasting` theorem is used. Shared-helper extraction is outside this
read-only worker's scope; duplicating those data is forbidden.

Validation: scompile.py compiled both sandbox and actual library module names cleanly
on the server, within 60 seconds each, including after replacing the setup's existing
partial geometry theorem with this node's own full property theorem. There are three
postponed theorems, all matching parts of this node and carrying source/proof docstrings.

## Second reading by NU

No independent worker was started: the dispatcher brief explicitly prohibits starting
other agents and assigns the independent reading to the maintainer. This report does
not claim an independent reading that did not occur. I checked the finalized file
against every hypothesis and clause above, including the directions of A,B,D and both
gamma maps, the rs=f compositor and lt=1 section unitor. The maintainer's independent
review remains the delivery review.
