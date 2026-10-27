## Worker report

The module `Sheaf.Paper.DifferenceCoordinateSectionIdentifications` states
`AlgebraicGeometry.ProEtale.DifferenceCoordinateSection.difference_coordinate_section_identifications`.
Its only postponed proof is this theorem, with the seven DAG proof steps in its docstring.
`normalizedE` inserts the equality of structure maps into the dependency's specified
counit-normalized `sourceEtale`; it constructs its isomorphism from real data.
`Statement` constructs the three precise equations. Its local typeclass installations
are consequences of the already recorded factorization theorem, not new hypotheses.
No node statement or dependency record has been changed and there are no new nodes.

Hypothesis and clause correspondence:

- The entire finite-field, prime, finite-extension, quotient-coefficient and positive-level
  datum is `P : PurityFiniteSetting.{u}`. In particular `P.level_pos` includes n >= 1,
  `P.field.k` is the fixed algebraic closure, and `P.Coefficient` is the canonical size
  lift of the actual quotient `P.Ring`. `P.comparedExponent` supplies the implied
  invertible-exponent condition; it is not an assumption on the caller.
- Finite-type k-schemes U,V,T are the `Over (Spec (.of P.field.k))` instances together
  with `LocallyOfFiniteType` and `QuasiCompact` on their structure maps. The three
  `IsAffine` hypotheses are precisely the affine-chart setting of this node.
- f and g are k-morphisms through their `IsOver` instances; their separatedness and
  finite type are the three listed morphism classes. Smoothness of pure dimensions
  d,e is `SmoothOfRelativeDimension d f` and `SmoothOfRelativeDimension e g`, with
  `d e : ℕ`. Auxiliary dimensions, morphism properties and compactifiability are
  supplied internally; no absolute separatedness assumption is added.
- The specified charts are `x : U ⟶ A d V`, `y : V ⟶ A e T`, their `Etale`
  instances, and `hx`, `hy`, saying their projections are f,g. The coordinate index
  type is the established `ULift (Fin r)`, retaining both empty blocks.
- B is U. Q,W,R are the actual `AffineDifferenceTower.Q`, `.W`, `.R`. The latter
  is the explicit affine d-space over Q with the Cartesian universal property
  supplied by `factorization`; it is not an arbitrary Cartesian object.
- a,s,i,j and t are `DiagonalPasting.a`, `.s`, `.i`, `.j` and
  `pullback.diagonal (f ≫ g)`. b is `pullback.fst (f ≫ g) g`; P_r,z_r,q are
  `pr r U`, `zero r U`, `q d e U`.
- G,H,J,F are `differenceSecond e f g y`, `AffineDifferenceTower.H f g x`,
  `AffineDifferenceTower.J d f g y`, `differenceTotal d e f g x y`. The extracted
  equation `hHJ` identifies F with H followed by J as scheme maps. The actual
  difference functions are those of the existing definitions, not supplied maps.
- The source C_f of `chiF` is literally Delta_f-pullback of omega_(p_f), the
  existing `Etale.sectionInvariant`/`DiagonalPasting.diagonalSection` formula.
  `chiG0` similarly starts at C_g. All these are the canonical etale presentations
  of the recorded section invariant `P.sectionInvariantFinite`, using the same
  actual pullback-of-exceptional-unit construction; no section notion is copied.
- The specified rho,c,E and omega are the recorded `FiniteEtaleNormalization`
  constructions. In particular `.comp` is the conjugate of the same
  `unboundedEtaleLowerShriekCompIso` used by `P.finiteExceptionalComposition`;
  `.sourceEtale` is its unit component followed by `.rho`. `normalizedE` only
  adds the required equality-of-composites isomorphism.
- `chiF` is pullback of E_(H_f,P_d), followed by the inverse pullback compositor
  for H_f Delta_f = z_d. H_f is `differenceFirst d f x`.
- `chiG0` is pullback of E_(G_g,P_e^V), with G_g = `differenceFirst e g y`.
  `tau` is exactly beta_(P_e^V,f) restricted along z_e, with the canonical
  pullback-composition maps for v z_e = z_e^V f. `chiG` is f-pullback of
  `chiG0` followed by this `tau`, so its target is D_e over U.
- `delta` is z_(d+e)-pullback of beta_(P_d,P_e) inverse followed by the
  compositor for first z_(d+e) = z_d. Thus it has exactly the inverse
  base-change direction and target D_d required by delta_d.
- `gammaF` is the dependency's pulled-back beta_(a,s) inverse; `gammaG` is its
  pulled-back beta_(p_g,f). Their canonical compositors are retained by reusing
  the existing declarations.
- `firstRoute` is gammaF, followed by t-pullback of E_(H,q_Q), H-pullback of
  beta_(q,G) inverse, then the canonical pullback constraints and `delta`.
  The first conjunct states `chiF = firstRoute` on the original pro-etale site.
- `secondRoute` is gammaG, s-pullback of E_(G,P_e), then the compositor for
  G s = z_e. The second conjunct states `chiG = secondRoute` on that site.
- `outputDirect` is t-pullback of E_(F,P_(d+e)); q followed by P_e equals
  P_(d+e) canonically by `affineGeometry`. `outputComposite` is t-pullback of
  E_(H,P_(d+e) J), then H-pullback of E_(J,P_(d+e)), then the canonical
  pullback compositor for H J = F. The third conjunct is their equality.
  Composing `outputDirect` with the inverse compositor for F t = z_(d+e)
  is exactly chi_(gf): C_(gf) -> D_(d+e), not a chosen trivialization.
- The three equalities use the existing `SameProEtaleMap` definition: apply
  canonical comparison inverse image to the actual etale-origin arrows and
  compare their images. Thus the conclusion is about small pro-etale derived
  morphisms, with the specified finite constructible coefficient realization.
  There is no arbitrary endpoint isomorphism, orientation, or Tate twist.

Dependency declarations used/read:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient` and their finite-field/coefficient structures.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `WeilConjectures.finiteTorConstructibleEtale`
  and the published native `ProEtale.DerivedCategory.constructibleFiniteTor`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback` and the finite
  intrinsic derived tensor/Hom API; the etale-origin pullback coordinates here
  are the recorded `FiniteEtaleNormalization.pull` and the canonical comparison.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded
  `ConstructibleExceptionalCoefficients.System` and finite exceptional interface;
  the used finite-coordinate functor is `FiniteEtaleNormalization.exceptional`.
- `Sheaf.Paper.PurityFiniteExceptionalComposition`: `P.finiteExceptionalComposition`.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`: specified dualizing,
  theta and beta finite-coordinate interfaces, exposed through the normalization
  and `DiagonalPasting.beta` constructions.
- `Sheaf.Paper.IntegralFinitePullbackComposition` and
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: canonical pullback
  composition and tensor comparison, whose finite-coordinate constraints are
  `Etale.leftDerivedUpperStarComp` and the published tensor/pullback comparisons.
- Mathlib `SmoothOfRelativeDimension`, `Etale`, `Limits.pullback`; Mathlib
  `AffineSpace`, with `ULift (Fin r)`, exactly the affine-space mathlib_match.
- `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`: `.sourceEtale`,
  `.congr`, `.comp`, `.rho`, `.pull`, `.coefficientUnit`, and `.beta`.
- `Sheaf.Paper.PuritySectionInvariantIntrinsic`: `.sectionInvariantFinite`,
  `.sectionInvariantIntrinsic` and `.intrinsicDualizing`, read to check the
  actual pullback-of-unit definition against its etale coordinate expression.
- The proof dependencies are imported: affine difference factorization,
  cohomological smoothness, dualizing sigma locality, exchange functoriality,
  etale Cartesian tower comparison, and Mathlib adjunction mates. The existing
  diagonal-pasting module already enters through the factorization module;
  adding this module as a proof import to that parent would close an import
  cycle and must be omitted there under stages/2-statements.md rule 7.

Edge cases checked: d=0, e=0, both zero, empty U/V/T and empty fibred products,
positive coefficient level including level 1, arbitrary coefficient extension
and scheme universe u. No positivity or point is requested for either coordinate
block. Polynomial coordinate definitions work for zero rings. The inverse beta
uses P_e z_e = id, not the generally false reversed equation. Relative smooth
projections and all specified etale comparisons remain present at dimension zero.
No node faults or STATEMENT-DISPUTED issues were found.

Searches (all through the prescribed tools, 2026-10-24):

- msearch leanfinder, query "The diagonal section invariant comparison in difference
  coordinates agrees with canonical smooth base change and etale exceptional pullback":
  eight hits, including Scheme.Pullback.diagonalRestrictIsoDiagonal,
  diagonal_SpecMap, diagonal_Spec_map and Kahler-differential base change; none
  states these derived morphism equations.
- msearch loogle, query "AlgebraicGeometry.Etale.leftDerivedUpperStarComp,
  AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap": zero hits; upstream
  identifiers are not in the Mathlib index. Their source signatures were opened.
- msearch grep, query "difference.*coordinate|sourceEtale|sectionInvariant",
  Mathlib subdirectory AlgebraicGeometry: zero hits.
- msearch leansearch, query "The canonical comparison between a diagonal section
  invariant and affine space difference coordinates is compatible with smooth
  base change": eight hits, including AffineSpace.map_appTop_coord and smooth
  base-change stability, plus manifold bundle results; no statement match.
- rg of lean/WeilConjectures and lean/Sheaf for difference coordinates, sourceEtale,
  sectionInvariant and the item id found the existing definitions and the
  diagonal-pasting parent, but no declaration of these three equations. The
  prescribed grep for the item id in WeilConjectures returned no hits.
- Mathlib source signatures of ProEt, SmoothOfRelativeDimension, Etale, AffineSpace,
  its homOfVector and map/reindex/zero-section identities were opened. Existing
  project signatures and docstrings for the difference maps and normalization
  were opened and reused. The latest blueprint composition-coherence proof was
  read at literature/blueprint/latest; this item is its agent-written refinement.

## Second reading by Q58

A second pass by the same dispatcher worker (the brief forbids starting other
agents) read the node and final Lean together. The first equation was checked
from its sources: inverse beta_(q,G) changes omega_qQ into J*omega_q; the inverse
H,J compositor and F t = z_(d+e) lead to delta with target D_d. The second equation
retains the f-pullback source and the actual zero-section restriction of
beta_(P_e^V,f); its `tau` was checked separately rather than replaced by an
arbitrary endpoint isomorphism. The output equation keeps the exceptional
congruence for both H J and P_e q and uses normalized E for the composite F.
The final formulation uses `SameProEtaleMap` for all three clauses so that the
stated arrows inhabit the requested pro-etale realization. No mathematical
mismatch or statement correction was found. One long theorem header was wrapped
following the first final compile; no proof was attempted.

Validation: every compilation used the prescribed `scompile.py` wrapper. The final
module compiled both under its sandbox name and its library module name. After
wrapping the theorem header, `deliver2.py --no-push` returned
`OK (dry run): commit 90eda5c32b8 passes the preflight and compiles; nothing pushed`.
No errors or non-sorry warnings remain. There was no global build or direct Git command.
