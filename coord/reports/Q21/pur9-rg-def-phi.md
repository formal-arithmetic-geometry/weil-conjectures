## Worker report

The delivery defines `AlgebraicGeometry.ProEtale.RegularImmersionPurity.comparison`
in `Sheaf.Paper.RegularImmersionPurityComparison`. This is the canonical smooth-purity
comparison for the entire scheme, including the connected, disconnected, and empty cases.
There is no change to the mathematical statement and no new definition node.

The source read in full is main-20261015
`sec-smooth-purity/sk-thm-regular/pur9-rg-def-phi.md`, together with the current DAG
statement, which specifies the empty case and the exact component comparison beta.

Hypotheses and clauses, with their Lean renderings:

- The global finite-field and finite-coefficient datum is `P : PurityFiniteSetting.{u}`.
  Its fields include the fixed algebraic closure, the different coefficient prime, finite
  coefficient extension and positive quotient level. The coefficient ring in the actual
  sheaf category is `P.Coefficient = ULift P.Ring`, as in the recorded dependencies.
- The schemes have arbitrary common scheme universe `u`; the small pro-etale category
  is `D P T = PurityCancellationCategory P T`, namely the unbounded derived category of
  `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u+1} P.Coefficient)`. The small site retains
  object universe `u+1` and morphism universe `u`.
- Structure morphisms and compatibility over k are the explicit section binders
  `[X.Over ...]`, `[Z.Over ...]`, and `[i.IsOver ...]`. Separated finite type is expressed
  by `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on both structure maps.
- The closed immersion is `[IsClosedImmersion i]`. Its positive pure codimension and
  both stalkwise clauses are exactly `hreg : IsRegularImmersionOfPureCodimension
  (X ↘ Spec (.of P.field.k)) i c`, the recorded dependency definition. No replacement
  affine-local regular-immersion predicate is used.
- Smoothness of X and regularity of Z are `[Smooth (X ↘ ...)]` and `[IsRegular Z]`.
  Smoothness of Z and the component dimension relation are conclusions used in the
  existence theorem, not extra hypotheses on `comparison`.
- The coefficient object Lambda_T is `unit P T = P.diagonalTwist T 0`.
  `unitPresentation` identifies this object with exact comparison inverse image of
  the ordinary degree-zero coefficient unit, using the published power-zero equation.
- `exceptional` is the existing `P.smoothPurityExceptionalOver`, i.e. the existing
  transported etale exceptional inverse image, with its Nagata compactification supplied
  internally from the finite-type field domain. The output is literally
  `unit P Z ⟶ (exceptional P i).obj (P.diagonalTwist X c)`.
- `omega P T` is `Ra_T! Lambda_S`; `orientation` composes its canonical unit transport
  with `P.diagonalDualizingObject`. The latter is precisely the Pi specified in
  def-pur-smooth-purity-map, not a variable orientation or an arbitrary endpoint iso.
- `comp` is literally `standingExceptionalComposition` on the recorded bounded
  constructible object. `comp_isIso` states invertibility by conjugacy of the given
  compact-support composition iso; `compIso` retains exactly this hom.
  `omegaComp` inserts only `comp_over` to identify `a_Z` with `i ≫ a_X`.
- For N=m+c, `ConnectedEquation` fixes the connected composite by tensoring Phi
  with T_Z(m)=Lambda_Z(m)[2m]. Its left side is Phi tensor identity, the inverse of
  the canonical root-normalized pullback identification, inverse canonical co-projection,
  and `Ri!` of the inverse positive product `T_X(N) ≅ T_X(c) tensor T_X(m)`.
  Its right side is the unit contraction, Pi_Z inverse, c, and Ri!Pi_X. Thus cancelling
  T_Z(m) gives exactly the source's negative-twist four-arrow formula. The Tate shifts
  are even, so the published derived symmetry introduces no odd-shift sign.
- `positiveCoprojectionWitnessIso` extracts the existing projection/counit
  characterization `purityCoprojectionProperty`. `positiveCoprojectionIso` names that
  exact map in the fixed functor interface via a unique HEq requirement. HEq here
  compares definitionally equal presentations on the same site with the same
  left-derived pullback; it does not identify merely isomorphic objects. The actual
  exact/left-derived pullback coordinate change is an explicit factor of the pull
  isomorphism passed to `positiveEquation`. No co-projection map is left free.
- `existsUnique_connected` is a named theorem with postponed proof and the full
  natural-language argument. `connected` extracts only the unique morphism satisfying
  the equation. No data is selected from mere unnormalized existence.
- `Component P i` records a connected clopen component Xs, its clopen inverse image Zs,
  the induced closed immersion and their Cartesian square. It contains no purity map,
  orientation, scalar, or categorical equivalence. Quantification over every such
  coordinate system is equivalent to the source's finite enumeration of components.
- `rho` applies `FiniteEtaleNormalization.rho` at Rnu_*K, then the exact/derived and
  site-square pullback comparisons, then pullback of the comparison counit. Thus it
  is the specified counit-normalized etale comparison on the original pro-etale K.
  `rho_isIso` uses bounded constructible etale origin, not an ambient exceptional
  adjunction.
- `componentBeta` is the exact displayed paste: pullback of the Tate coefficient
  identification, Ri_s!(rho_j inverse), c_{j,i_s} inverse, equality transport along
  the Cartesian square, c_{i,jZ}, then rho_jZ. The first factor only expresses the
  source's identification `Lj*L = Lambda_Xs(c)[2c]` in published coordinates.
- `ComponentEquations` requires `LjZ*Phi = unitPull.hom ≫ connected ≫ componentBeta`
  for every component and every pair N,m satisfying the source's dimension conditions.
  Empty inverse images require zero; `IsEmpty Z → Phi=0` includes the globally empty
  source explicitly. Empty X is permitted; there are then no nonempty components.
- `existsUnique_comparison` states the existence and uniqueness furnished by the
  finite-clopen derived restriction equivalence. `comparison` extracts this uniquely
  determined global morphism. The identity component and identity normalizations of
  c and rho recover the connected construction. Its docstring explains the gluing
  and empty cases as well as invariance under component coordinates.

Dependency declarations inspected and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its
  coefficient ring; `Sheaf.AlgebraicGeometry.RegularImmersionPureCodimension`:
  `AlgebraicGeometry.IsRegularImmersionOfPureCodimension`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
- The recorded exceptional coefficient system module was inspected. Its finite
  functor is the existing `sfFiniteExceptionalAt` / `sfFiniteExceptionalFixed` formula,
  used through `smoothPurityExceptionalOver`, not redefined as an arbitrary adjoint.
- `WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion`:
  `IsRegularImmersion.smooth_comp` and `ringKrullDim_stalk_add` were inspected.
  The chapter's stronger stalkwise predicate is retained; no unusable affine-local
  regularity instance is demanded from the user.
- `Sheaf.Paper.StandingExceptionalComposition`: `standingExceptionalComposition`;
  `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: `originComposition`;
  Mathlib `CategoryTheory.conjugateEquiv` and `conjugateIsoEquiv` describe why the
  specified mate is invertible.
- `Sheaf.Paper.SmoothPurityMap` and `Sheaf.Paper.PurityDiagonalDualizingObject`:
  `diagonalDualizingObject`, the exact Pi named by the dependency statement.
- `Sheaf.Paper.PurityTwistCancellation`: `PurityCancellationCategory` and the
  specified `purityTwistCancellationComposite`; the connected determining equation
  is its positive-power presentation. `Sheaf.Paper.PurityCoprojection`:
  `purityCoprojectionProperty` and its counit-normalized isomorphism.
- `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`:
  `FiniteEtaleNormalization.rho` and `.compactification`.
- `Sheaf.Paper.FiniteClopenDerivedDecomposition`:
  `finiteClopen_unbounded_decomposition` is the gluing/uniqueness justification.
- Added the existing:true definition node `def-pur-composition-comparisons` to
  stmt_deps. Its recorded module `Sheaf.Paper.PurityCompositionCoherence` owns
  `compositionEtalePowerZero`, `compositionPowerAdd`, and `compositionTwistPullback`
  as factors of `compositionSourceIdentification`. These are the unfolding lemma
  and plain canonical tensor-power/root-restriction definitions, respectively;
  none chooses data from `smoothPurityCompositionCoherence`. The coherence theorem
  is not a statement dependency. A graph traversal confirms the replacement is acyclic.

Searches (2026-10-18):

- `msearch.py ... leanfinder "smooth purity comparison for regular closed immersion
  assembled from dualizing orientations and exceptional composition"`: eight hits
  about ordinary scheme smoothness/immersion, none the comparison being defined.
- `msearch.py ... loogle "CategoryTheory.conjugateEquiv"`: twelve mate-calculus hits;
  source read in full for the relevant conjugate and isomorphism signatures. No Phi.
- `msearch.py ... leansearch "smooth purity comparison regular immersion exceptional
  inverse image"`: eight ordinary smoothness/immersion hits, no purity comparison.
- `msearch.py ... grep "smoothPurity|regularImmersionPurity|TateTwist"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of upstream WeilConjectures and the project's `lean/Sheaf` for the item id,
  smoothPurityComparison, regularImmersionPurity, standingExceptionalComposition,
  and diagonalTwist/purityCancellation found only component ingredients and the
  generic cancellation composite. None defines the canonical global regular-immersion
  comparison. All helpers are reused rather than recreated.

Edge cases checked: empty X; empty Z; components of X missed by Z (including those
with dimension smaller than c); disconnected X with different component dimensions;
possibly disconnected but pure-dimensional nonempty Zs; m=0 and N=c; arbitrary
positive coefficient level with no ramification divisibility assumption. The input
predicate retains the chapter's c>=1 restriction. The construction's generic
connected helper also makes sense at c=0, without expanding the final input domain.
No false-statement dispute, statement correction, new node, or dependency rebinding.

## Second reading by Q21

This is the writing worker's second reading, not an independent reviewer claim;
the dispatcher's maintainer provides the independent delivery review. I reopened
the node and the Lean module and checked each clause against the list above.
The principal risks checked were choosing an unnormalized orientation, forgetting
the beta paste, excluding empty components, or assuming uniform dimension on all
of X. The implementation fixes Pi to the recorded diagonal orientation, fixes
co-projection by its counit equation, writes every beta factor, and quantifies over
connected clopen coordinates with their own N,m. Only a unique morphism is chosen.
The positive-power equation is essential: it avoids asserting that the published
positive-power and signed-line presentations are definitionally equal. The actual
left-derived/exact pullback comparison is inserted explicitly in ConnectedEquation.
The auxiliary positiveEquation constructs the equation before specializing sheaf
categories, avoiding expensive repeated kernel conversions without changing any map.

Validation: the complete delivered module passed the prescribed scompile.py in both
sandbox and final library module contexts with no errors or warnings: 15.5 seconds
and 26.1 seconds respectively, both within the unchanged 60-second limit. A temporary
diagnostic copy with a lower heartbeat budget also passed, then was removed. The
final module has no heartbeat override and every theorem proof is exactly `sorry`.

## Return repair (2026-10-18)

H2 at immutable reviewed head b022a6c38dc3: replaced the added theorem statement
dependency `thm-pur-composition-coherence` with the already recorded existing:true
`def-pur-composition-comparisons`, and updated lean.note. Read the definition node
and the three factor declarations in its recorded module; all used factors belong
to that definition node and do not extract data from the coherence theorem.
The Lean module, its signatures, hypotheses, and mathematical statement are unchanged.
The saved packet first passed the required dry run (d883c51831); this repair addresses
the independent review's semantic dependency objection beyond that mechanical check.

Repair validation: prescribed scompile.py passed in sandbox and final module contexts
(11.5 s and 14.7 s) with no errors or warnings. The comparison signature remains
verbatim in lean.statement. Against current main, only lean and stmt_deps differ;
stmt_deps adds exactly def-pur-composition-comparisons. Traversing both statement
and proof dependencies from that node found no path back to pur9-rg-def-phi.
The unchanged Lean module SHA256 is
bed0ae00c87fbfdfcde2692de754e0f9097af762e9e863e69ac4b782f7710ee5.

## Returned compile validation (2026-10-18)

For the return at immutable head fd647cbc3184, I first inspected the saved report
and ran the required deliver2.py --no-push without changing the saved Lean packet.
The prescribed dry run passed preflight and both file-only compilation contexts
against the current published dependency environment: commit 4ebae25efa. The
returned RingedSiteDualityMaps overlay errors did not recur. As instructed for a
saved packet that passes, I retained the existing Lean and node records rather
than introduce an unnecessary dependency replacement.

Self-check: reopened the source node, its blueprint text, the component assembly
and the comparison signature. The signature is verbatim in lean.statement;
set_option autoImplicit false remains enabled; no Lean line exceeds 100 columns.
The only node differences from the current shared copy are lean and stmt_deps,
whose addition is the already recorded def-pur-composition-comparisons. The Lean
SHA256 remains bed0ae00c87fbfdfcde2692de754e0f9097af762e9e863e69ac4b782f7710ee5.
The connected equation, beta paste and empty-component clauses are unchanged.
