## Worker report

The module `Sheaf.AlgebraicGeometry.IsomorphismScalarKFlatDescent` states
`AlgebraicGeometry.Scheme.IsomorphismScalarKFlatDescent.scalar_kflat_descent`.
It has one postponed theorem, with exactly `sorry` as its proof. All thirteen helpers
are real definitions or transparent abbreviations; none chooses module data or an
unconstrained comparison. The natural-language statement and accepted proof are unchanged.
The existing, landed `def-weil-pbc-proetale-operations` is added to `stmt_deps` to cite
the canonical identified-coefficient operation already used in the statement.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-derived-tor-quasi-isomorphism-other-side` (06YT), its following derived-tensor
construction and `definition-derived-tor` (06YU), and `lemma-factor-through-K-flat`
(0G7D). The item is the accepted preservation/localization assembly of those tools,
not a claim that 0G7D alone states this theorem. The theorem docstring reproduces
all six accepted proof steps and names their dependencies.

Hypotheses and clauses, in the namespace above:

- Schemes and scheme isomorphism: `{X Y : Scheme.{u}}`, `g : X ⟶ Y`, `[IsIso g]`.
  All section variables and the universe `u` are explicitly declared and
  `autoImplicit` is false.
- Small pro-etale sites: `ProEt.topology X` and `ProEt.topology Y`, on `X.ProEt`
  and `Y.ProEt`. Their object universe is `u+1`, Hom universe `u`, coefficients
  and module sections are in `u+1`, and the standard ordinary derived localization
  has Hom universe `u+2`. No site object/Hom universe equality is assumed.
  The recorded inverse image internally transports through its `AsSmall` model.
- The four arbitrary commutative ring sheaves are `RY,SY,RX,SX`. Their maps are
  `jY : RY ⟶ SY`, `jX : RX ⟶ SX`. The specified ring isomorphisms are `cR,cS`
  from the actual `proEtaleSheafInverseImage g CommRingCat` objects. `comm` is
  exactly `F(jY) ≫ cS.hom = cR.hom ≫ jX`, the source square in diagrammatic order.
- Module categories are the existing `proEtaleRingModules`, definitionally the
  recorded `ringedSiteModules` / Mathlib `SheafOfModules` over the underlying ring.
  `inverseR,inverseS` abbreviate the existing `proEtaleRingModulePullback` for
  the supplied coefficient isomorphisms. This is actual inverse image followed
  by extension along the isomorphism, canonically the specified action transport;
  no arbitrary exact functors are quantified over.
- `CY,CX : DerivedChangeOfRingsCochainModel jY/jX` fix presentations of the ordinary
  scalar-extension universal pairs. These are the source's chosen `C_Y,C_X`,
  including their canonical counits, not extra flatness or existence hypotheses:
  `nonempty_derivedChangeOfRingsCochainModel` supplies them for every coefficient map.
  Their ordinary functors have prescribed `changeOfRings` objects and
  `changeOfRingsHom` maps, their derived functors have the universal left-derived
  property, and their `computes` fields make the canonical counits invertible on
  every K-flat complex. The result is stated for any such presentations.
- `good R` is precisely the conjunction of the recorded
  `IsKFlatIndependentCoefficients` and `∀ n, IsFlatOnSite (P.X n)`;
  both carry the full small-site universes explicitly. No flatness is redefined.
- `U` is `G_R` applied termwise followed by ordinary scalar extension over `jX`;
  `V` is ordinary scalar extension over `jY` followed by termwise `G_S`.
  Scalar extension of a complex by a ring in degree zero is termwise extension,
  equivalently the stated direct-sum total tensor with that degree-zero ring.
- `b` is a natural isomorphism on `(good RY).FullSubcategory`; thus it has an
  isomorphism of complexes for every good complex and is natural for every chain map.
  `hb : HomotopyCompatible ... b` spells out its homotopy compatibility:
  `E_X(G_R(h_ij)) ≫ b_j = b_i ≫ G_S(E_Y(h_ij))` for every chain homotopy,
  with the two functors applied to the actual degree-minus-one homotopy maps.
- The existential witness `hGR` is the asserted goodness of `G_R P` for every good P.
  The first following conjunct gives goodness of `Q=E_Y P` and `Z=U P`.
  `hGR` is a conclusion, never an assumed preservation result.
- The next conjunct gives `QuasiIso (U.map f)` and `QuasiIso (V.map f)` for every
  quasi-isomorphism between good complexes, including arbitrary unbounded ones.
- The following existential supplies `UH,VH` on the quotient of the full good
  cochain category by actual chain homotopies (`goodHomotopy`). Its two natural
  isomorphisms identify restriction of these functors with `U,V` followed by the
  target homotopy quotient. This is the assertion that they induce homotopy functors.
- The next conjunct explicitly records the quasi-isomorphism `G_R s` for every
  quasi-isomorphism `s`, hence in particular for every good resolution in the node.
  This is also part of the exactness of the identified inverse-image operation.
- `A=G_R.mapDerivedCategory ⋙ CX.T` and `B=CY.T ⋙ G_S.mapDerivedCategory` are
  precisely `C_X G_R` and `G_S C_Y` in categorical composition order.
  `∃! β : A ≅ B, Normalized ... β` asserts the requested unique natural isomorphism,
  with equality of natural isomorphisms, not just isomorphism existence.
- `sourceIso` first inverts `A([s])`, then applies `C_X` to the exact `G_R`
  representative isomorphism, then uses the K-flat scalar counit at `G_R P`.
  `targetIso` first inverts `B([s])`, then applies derived `G_S` to the scalar
  counit at P, then uses the exact `G_S` representative isomorphism at Q.
  Both are actual canonical isomorphisms; their invertibility uses the recorded
  universal-pair `computes` field and the proved conclusion `hGR`.
  The exact-functor representative square identifies the first source factor
  with localization of the quasi-isomorphism `G_R s`.
- `Normalized` quantifies over every complex K and every good quasi-isomorphism
  `s:P→K`, and says `β_[K] ≪≫ d_s = a_s ≪≫ [b_P]`. Equivalently,
  `d_s β_[K] a_s^-1 = [b_P]` in the node's usual composition order.
  Thus normalization applies to every resolution, not only the identity resolution.
- `ResolutionCoherent` gives the square for two resolutions using the canonical
  transitions `a_s^-1 ≪≫ a_s'` and `d_s^-1 ≪≫ d_s'`, and the two source and target
  cocycle equalities for three resolutions. Its quantification over triples covers
  pairs by repeating the second resolution. There is no chosen roof or chain lift.
- No flatness of `jY,jX`, boundedness, derived completeness or constructibility
  appears. No chain comparison or quotient-tower comparison is constructed.

Recorded dependencies used (full declarations and docstrings inspected):

- `def-weil-scheme-morphism-properties` and `def-weil-size-convention` are recorded
  conventions; `Scheme`, `IsIso`, and the explicit universes implement their uses here.
- `def-weil-pbc-proetale-site`: Mathlib `AlgebraicGeometry.Scheme.ProEt`,
  `AlgebraicGeometry.Scheme.ProEt.topology` in
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `def-weil-proetale-inverse-image`:
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage` and
  `proEtaleModuleInverseImage`; `proEtaleBaseChange` and the small-model transport
  are used by these published constructions.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `SheafOfModules.cochainModulesMonoidal`; extension uses the published
  sheafification of balanced sectionwise tensor.
- `def-pc-tensor-complex-sheaves`: Mathlib `CochainComplex.mapBifunctor`
  (publicly imported through the tensor/K-flat interfaces), with scalar ring in
  degree zero; `U,V` are the corresponding termwise scalar-extension functors.
- `def-weil-abstract-derived-category`: Mathlib `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and the standard localization.
- `def-pc-kflat-complex`:
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `def-pc-flat-sheaf-modules`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
- `lem-pur-derived-change-of-rings`: the recorded
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly retains
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel` from
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`. This sheaf interface,
  not the additional `ModuleCat` specialization in the primary record, is used.
- Added landed dependency `def-weil-pbc-proetale-operations`: its recorded public
  module `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` reexports
  `proEtaleRingModules`, `proEtaleRingModulePullback` and its additive/exact instances
  from `ProEtaleOperations`; these operate on arbitrary ring sheaves.

All proof dependencies are imported: `Sheaf.Paper.KFlatRingedToposPullback`
(`SheafOfModules.isKFlat_ringedToposPullback`), Mathlib
`CategoryTheory.Functor.mapDerivedCategoryFactors`, the recorded change-of-rings
module, `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
(`SheafOfModules.site_derived_tensor_descent_independentCoefficients`) and Mathlib
`CategoryTheory.Localization.liftNatIso`, `natTrans_ext` in
`Mathlib.CategoryTheory.Localization.Predicate`. No proof import is omitted for a cycle.

Edge cases checked before and during writing: identity scheme isomorphism with
identity coefficient identifications; zero rings and the empty scheme; the nonflat
map Z→Z/2 as a constant sheaf map; complexes unbounded in both directions; the zero
complex; identity resolutions and repetition of one resolution in the cocycle.
The formulas retain all of these cases. The normalization of an arbitrary supplied
b is retained rather than replaced by the canonical tensor comparison.

Searches for an existing complete statement (all msearch.py calls use Q73 and this item):

1. LeanFinder: “An arbitrary natural scalar extension chain isomorphism under a
   scheme isomorphism descends uniquely to derived change of rings using flat term
   K flat resolutions”. Eight results about flat ring maps, faithfully flat scalar
   extension and representably flat functors; none states this supplied-b descent.
2. Loogle: `"DerivedCategory", "NatIso"`. Zero results.
3. Mathlib grep: `mapDerivedCategory.*[iI]so|[kK].?[fF]lat` in
   `Algebra/Homology/DerivedCategory`. Two hits, exact-functor and Ext map code;
   neither is the complete statement.
4. LeanSearch: “A natural isomorphism on K flat complexes descends uniquely through
   localization to the derived category”. Eight hits including `leftDerivedNatIso`,
   exact-functor factorization and `HasDerivedCategory.standard`. They provide
   ingredients, not preservation with the required all-resolution normalization.
5. `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
   for the item id and `IsomorphismScalarKFlatDescent|scalar_kflat_descent`: no hits.
   Broader scalar/K-flat searches found the imported generic interfaces and the
   projection-mate/coefficient-comparison specializations, not this arbitrary-b lemma.

No STATEMENT-DISPUTED finding, source error or statement correction. No new nodes
or dependency modules. The selected scalar universal-pair presentations are explicit
parameters so the statement does not choose unrelated functors from bare existence.

Validation: the file compiled on the server with scompile.py. Compiler-guided repairs
made the coefficient/site universes explicit and included all section parameters in
helper applications. Only the theorem proof is postponed. The final delivery dry run
will check the exact node record, shape, docstrings, line widths and per-file compilation.


Resumption verification (2026-10-22): inspected the existing draft rather than replacing
it. Repeated the following searches through the prescribed wrapper: LeanFinder for
“K flat complexes with flat terms preserved by inverse image of a ringed topos and
natural scalar extension isomorphism descends uniquely to derived categories” found
exact-functor factors and unrelated flatness declarations; Loogle for
`CategoryTheory.Localization.liftNatIso` found the generic localization construction
and its hom/inv equations; Mathlib grep `KFlat|kflat|mapDerivedCategory` in
`Algebra/Homology/DerivedCategory` found exact-functor and Ext-map code. None is this
arbitrary supplied-comparison statement. Read the actual arbitrary-ring definitions
and exactness instances in `ProEtaleOperations`, confirming that the added dependency
exports precisely the operations used, and rechecked the source passages for 0G7D,
0G7E and 06YT. The module compiled successfully through the prescribed `scompile.py`
against the live server build, with no diagnostics. A local textual check confirmed
that only `lean` and the added `stmt_deps` entry differ from the current node, that
`lean.statement` is the exact theorem signature, that every line has at most 100
characters, and that the sole postponed proof is the main named theorem.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
