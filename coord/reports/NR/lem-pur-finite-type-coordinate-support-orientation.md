## Worker report

Item: `lem-pur-finite-type-coordinate-support-orientation`, group NR, 2026-10-21.
Module: `Sheaf.Paper.FiniteTypeCoordinateSupportOrientation`.
Namespace: `WeilConjectures.PurityFiniteSetting`.

This is a statement delivery. Every definition has actual data. The three postponed
theorems have source and complete proof docstrings: the ordinary closed-support
comparison, the unique global kernel comparison needed to construct the canonical
field map, and the normalized coordinate-orientation theorem. All 25 declarations
are listed in the node record. The global-kernel comparison is a helper of the
already recorded support functor, not a new independent support notion. Its unique
kernel-inclusion characterization justifies the choice used by the derived comparison.
No statement correction is needed. The H2 repair adds definition-node ownership of
the existing supported Hom comparison, as detailed under "New nodes" below.

### Hypotheses and clauses

* The fixed datum is `(P : PurityFiniteSetting.{u})`. This retains the recorded
  algebraic closure, ell, finite coefficient ring and arbitrary positive coefficient
  index, without a divisibility condition on the ramification index. Coefficients
  throughout are the actual `ModuleCat.{u + 1} P.Coefficient`.
* Rank is `(b : ℕ)`, including zero. The affine space and closed immersion are
  `AffineSpace (ULift.{u} (Fin b)) B` and its existing `AffineSpace.zeroSection`.
  The lift puts the coordinate set in the scheme universe without changing rank.
* Every family and compatibility predicate binds `(B : Scheme.{u}) [IsAffine B]`
  and `(a : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType a] [QuasiCompact a]`.
  This is precisely an affine finite-type k-scheme, including nonreduced and
  disconnected schemes. The explicit structural map is needed by twist pullback
  and by the displayed base-change equations.
* `coordinateTwist P X r` is an abbreviation for the existing ordinary finite
  twist `P.functorialCupTwist false X r`, not a replacement coefficient object.
  It uses ell to the coefficient index, which kills the coefficient ring for
  every positive index. The referenced signed finite-twist API supplies the
  root normalization, tensor powers, negative dual powers and exponent transitions.
* `CoordinateOrientationFamily` binds every `(r : ℤ)` and gives
  `single (z_* A_B(r-b)) ≅ (RQ_z (single A_X(r)))⟦2*b⟧`. This is the isomorphism
  in the node written in its equivalent inverse shifted direction. `RQ_z` is
  exactly `Etale.coordinateSupportSheaf ... z |>.rightDerivedFunctorPlus`.
* `coordinateDerivedInclusion` derives the existing kernel inclusion, using the
  canonical derived identity comparison. `coordinateOrientationCounit` composes
  the family with this inclusion; it does not introduce an unspecified map.
  `coordinateOrientationClass` is that counit representative at r=b, with b-b=0.
* `CoordinateOrientationNormalization` identifies the simultaneous coordinate
  zero locus scheme-theoretically with B over X. Such an isomorphism is unique
  because the closed immersion is monic. It equates the image of this exact
  counit class under `functorialCupCompare` with `frameBoundaryProduct` in the
  order `Fin b`. The support map is included in the equation, so this is equality
  in supported Hom, not equality after erasing support. The empty product in the
  existing declaration is the unit. The comparison is faithful on these supported
  classes by the recorded finite-site comparison.
* This normalization is equivalently the ordinary ordered Cartier-Kummer product:
  `cartier_kummer_map` identifies each ordinary witness with the same pro-etale
  principal boundary used by `frameBoundaryProduct`; `supportedCupFunctoriality`
  identifies the two products. In particular this equation fixes the class at
  EVERY positive annihilating ell-power N, rather than just choosing an N-specific
  witness. The exponent-transition and Cartier normalization results in those
  dependency declarations make the equation independent of N. An additional
  arbitrary choice of boundary or coefficient identification is absent.
* `CoordinateOrientationTensor` asserts that every field twist admits a basis,
  and quantifies over EVERY such basis. Its equation says that the r orientation
  after the basis identification is the b orientation tensored with that basis
  using `functorialCupTwistProduct false`; thus the actual family does not depend
  on a selected basis. `coordinateBasis` pulls the field basis to X by the
  canonical constant-sheaf and root-normalized twist comparisons.
  `coordinateBasisTwist` uses the existing signed multiplication, including its
  dual/evaluation convention for r-b<0. This renders the constant-line tensor,
  signed tensor and negative-twist clauses together.
* `CoordinateOrientationBaseChange` quantifies over every affine finite-type B
  and B', structural map a and morphism g with g≫a finite type. There is no
  flatness, smoothness, etaleness or separatedness restriction on g. The required
  square `sq` is cartesian for the actual affine-space map. `coordinateTwistedExchange`
  is the canonical `Etale.baseChangeMap` followed by the recorded twist pullback.
  The displayed equation is the square for the actual counit representatives,
  with the canonical derived inverse-image single/shift identifications. By the
  closed adjunction it is equivalent to commutation with the canonical supported
  pullback maps. Both orientations are invertible, so this asserts compatibility
  for those maps, not existence of an unrelated comparison isomorphism.
* `coordinateSupport_closedComparison` states the remaining ordinary-support
  clauses separately in the same node: Q is isomorphic to `closedUpperShriek ⋙
  lowerStar`, RQ to its bounded-below derived version, and both isomorphisms take
  the inclusion to the actual closed adjunction counit. The existing
  `closedUpperShriek` is exactly `z^{-1} Q` via the canonical sectionwise kernel
  identification. Its third conjunct compares the prescribed ABELIAN derived
  support functor `Etale.derivedSupportSections` after forgetting modules with
  derived closed inverse image followed by derived abelian global sections on B.
  The proof docstring explicitly uses the module-to-abelian acyclicity bridge;
  it does not assume that forgetting an injective module sheaf is injective.
* `coordinateFieldLine P s` evaluates the actual signed twist at the terminal
  etale object of Spec k, retaining its A-module structure: it is exactly L_s.
  `coordinateGlobalSupport_existsUnique` characterizes the global kernel
  comparison by its kernel-inclusion equation. `coordinateDerivedGlobalSupportIso`
  derives that unique comparison and uses the canonical composition isomorphism.
  `coordinateFieldSourceIso` is closed pushforward/global sections followed by
  terminal evaluation. `coordinateFieldOrientation` applies derived global
  sections to THIS SAME family, with the canonical single unit and shift maps,
  and then the derived global-support comparison. The final conjunct of
  `finiteTypeCoordinateSupportOrientation` says this specified map is `IsIso`
  for every integer r. It is the field isomorphism in the equivalent forward
  shifted direction, with the same orientation, not a new arbitrary isomorphism.

### Dependency declarations used

The following recorded interfaces are reused (module: declaration):

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the intrinsic finite
  coefficient twists recorded by `def-coefficient-twists-detailed`; their ordinary
  signed witness is the existing finite-etale Tate sheaf used below.
* Mathlib: `AlgebraicGeometry.Scheme`, `IsAffine`, `LocallyOfFiniteType`,
  `QuasiCompact`, `AffineSpace` and the small etale topology.
* `Sheaf.AlgebraicGeometry.EtaleCoordinateSupport`:
  `AlgebraicGeometry.Etale.coordinateSupportSheaf`,
  `coordinateSupportInclusion`, `coordinateGlobalSupport`, and its injective
  preservation instance.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded bounded-below
  derived categories; the shared `DerivedCategory.Plus` API is used directly.
* `Sheaf.AlgebraicGeometry.CartierKummerMap`:
  `AlgebraicGeometry.cartier_kummer_map` and its normalized witnesses.
* `Sheaf.Paper.SupportedCup`: the supported tensor-morphism cup operation.
* `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `AlgebraicGeometry.Etale.FiniteEtaleTwistPullbackData` and
  `finiteEtaleTwistPullbackData`, including exponent, tensor and evaluation clauses.
* `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `AlgebraicGeometry.Etale.derivedSupportSections` and supported-sections kernel.
* `Sheaf.Paper.PurityFrameClass`: `frameBoundaryProduct`.
* `Sheaf.Paper.SupportedCupFunctoriality`: `functorialCupCompare`,
  `functorialCupSupportMap`, `functorialCupTwist`, `functorialCupTwistProduct`,
  `functorialCupEtaleTwistPullback` and their recorded normalization.

The landed definition nodes `def-pur-frame-class` and
`def-pur-supported-class-operations` are added to `stmt_deps`; the latter owns all
listed plain cup operations except `functorialCupCompare`. The new definition node
`def-pur-supported-hom-site-comparison` owns that existing declaration.
`lem-pur-supported-cup-functoriality` is retained only in `proof_deps`.
The Lean statement itself is unchanged.

Proof dependency modules are imported explicitly when recorded: finite type,
`EtaleInjectiveSupportSequence`, `EtaleSupportedKernelAdjunction`,
`ModuleCohomologyConventions`, `SupportLongExact`, `FiniteTateSiteDescent`,
`CompactSupportComparisonUnit`, `SupportedKummerSupportHomNaturality` and
`AbelianSheavesGModules`, in addition to the public statement imports. The two
proof-only nodes `lem-pur-closed-finite-adjoint-counit-transport` and
`cor-pur-affine-space-zero-section-purity` currently have no recorded module;
there is consequently no module to import for them. They remain named in the
seven-step proof plan; they are not missing notions needed to type this statement.

### Edge cases

Checked b=0 (empty coordinate set, full support, unit normalization, zero shift),
b=1 (single Cartier boundary), r=b (zero field-line twist), r<b and r<0
(signed dual powers), empty B (zero sheaf category), disconnected/nonreduced B
(polynomial coordinates still regular), identity base change, and arbitrary
nonflat base change. No smoothness of B is assumed. Arbitrary n>=1, including
indices not divisible by the ramification index, use the fixed annihilator ell^n
and the existing unrestricted intrinsic twist comparison. No independent universe
is introduced for tests below the scheme universe. No disputed statement or
node fault was found.

### Searches and sources

Read Stacks etale-cohomology.tex, Tags 09XP and 09XQ (ordinary support and
injective preservation), and blueprint main-20261015
`sec-smooth-purity/sk-prop-an/cor-pur-affine-space-zero-section-purity.proof.md`.
Read the item and every statement dependency's recorded signature and docstring.

Searches used the prescribed msearch.py wrapper:

* leanfinder: “Etale cohomology with support zero section affine space normalized
  Tate twist shifted twice dimension” returned affine-coordinate algebra results;
  none states the supported orientation.
* loogle: “AlgebraicGeometry.Etale.coordinateSupportSheaf, AffineSpace” had no
  match (the first project identifier is not in Mathlib's index).
* grep: “coordinateSupport|Kummer|TateTwist” under Mathlib/AlgebraicGeometry
  returned no match.
* leansearch: “cohomology with support in zero section affine space Tate orientation”
  returned unrelated manifold/ideal-support results, not this assertion.
* rg in the project's Sheaf and WeilConjectures sources for coordinate support,
  orientations and Kummer products found the interfaces cited above, but no
  theorem with the complete ordinary support-kernel statement. The required
  item-id grep in WeilConjectures found no declaration for this node.

The three proof placeholders are deliberately `sorry`; no mathematical proof is
claimed. Every definition is concrete, and the sole theorem-based definition uses
an existence-AND-uniqueness characterization fixing the comparison and its inclusion.

### Validation

All compiles used scompile.py against the published server library, never a local
lake build. The final module passed both sandbox and proper-library compilation
with no errors or warnings (37.7 s / 32.8 s). The timeout remains 60 s.

## Second reading by NR

The dispatcher explicitly prohibits starting other agents and assigns no lead.
This section records a separate self-check, not a claim of independent review;
the maintainer performs the independent reading of the delivery.

Reopened the full node and the final module, expanded every predicate, and checked
all hypotheses and clauses listed above. The checks specifically retained the
abelian-cohomology bridge, the actual derived kernel inclusion, the supported-Hom
normalization, the all-bases/all-twists quantifiers, signed tensor evaluation,
canonical base-change exchange, and the field map induced by the same family.
The preliminary field construction needed the small derived localization universe
and a transparent abbreviation for the existing derived global-sections functor;
these were repaired without adding a universe equality or restricting any scheme.
The only final compiler warning was a long line; it was shortened and both final
compiles are clean. No statement mismatch remains identified by this self-check.

## New nodes

`def-pur-supported-hom-site-comparison` records the existing definition
`WeilConjectures.PurityFiniteSetting.functorialCupCompare` in
`Sheaf.Paper.SupportedCupFunctoriality`, with `existing: true`. It owns the canonical
map from ordinary-etale supported signed-twist Hom to pro-etale supported Hom.
The closed source is transported by the inverse of the unique coefficient-unit
normalized comparison, the representative by exact derived inverse image with the
canonical single and shift identifications, and its target by the defining twist
identification. This is the existing declaration verbatim; no new Lean module,
comparison choice or theorem is introduced. Its source is Stacks proetale.tex,
Tags 099V/099W/09B1 and the blueprint zero-section proof's finite-site comparison.

The recorded LeanSearch query returned eight algebra-etale/Ext results; LeanFinder
returned eight etale-algebra and scheme results; Mathlib grep returned zero hits.
None defines this map. Project rg finds the definition at line 980 of
SupportedCupFunctoriality. The DAG search finds theorem ownership and consumers,
but no definition-node owner: supported-class-operations owns the Hom and other
operations, and supported-class-site-comparison owns a tensor-source transport.
Blueprint searches for "supported comparison" and "etale pro-etale" both return
zero nodes. All wrapper results are preserved verbatim in the new node.

## Repair of independent return H2

Compared the saved packet with current main through file reads: only `lean` and
`stmt_deps` differed in the item. The saved module is retained from the returned
packet c8a0677a3490. The initial saved-packet dry run passed at 00cf6603c24, but
still contained the returned dependency mistake, so it was not pushed.

Removed `lem-pur-supported-cup-functoriality` from `stmt_deps`, retaining it in
`proof_deps`. Added the already-landed `def-pur-supported-class-operations`
(`existing: true`) for `functorialCupTwist`, `functorialCupSingle`, `FunctorialCupH`,
`functorialCupSupportMap`, `functorialCupTwistProduct` and
`functorialCupEtaleTwistPullback`. Added the new definition node above for
`functorialCupCompare`. Retained the allowed landed `def-pur-frame-class`.

Reopened the supported comparison implementation and its local existsUnique helper:
the chosen closed-source comparison is characterized by its coefficient-unit
restriction equation. No data is chosen from the functoriality theorem. The
comparison node asserts only the concrete map; identities, bijectivity, products
and pullback laws remain theorem/proof material. Edge cases a=0, negative a and r,
empty C, C=X and empty X use the same exact transport and introduce no additional
assumption. The new record's signature is extracted verbatim from the landed source.
The H2 repair changes no Lean declaration and no mathematical statement.

### Second reading by NR of the H2 repair

Read the new definition node against the full signature and body of
`functorialCupCompare`: P, arbitrary schemes C and X, closed immersion i, integer
degree a, integer twist r, input ordinary-etale supported Hom, and output
pro-etale supported Hom agree individually. The formula uses the inverse normalized
closed-source comparison, `functorialCupExactHom`, and the shifted twist equality,
in that order. Read the source comparisons in proetale.tex at labels
lemma-relative-comparison, lemma-compare-cohomology and lemma-compare-derived, and
the blueprint zero-section proof. The definition node carries no theorem laws,
new hypotheses or new definition data. Reviewed the ownership records of
`def-pur-supported-class-operations` and `def-pur-supported-class-site-comparison`
to check this is missing ownership of the existing map rather than a duplicate
notion. All hypotheses and clauses of the orientation module remain as reviewed
above. No mismatch remains in the repair.

After this repair, scompile.py compiled the preserved module in its sandbox
(37.7 s) and proper library module path (36.7 s), with no errors or warnings.
