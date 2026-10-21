## Worker report

Item: `lem-sfb-partial-kummer-boundary-unit-model` (O3, stage 2).
Module: `Sheaf.Paper.PartialKummerBoundaryUnitModel`.
Main declaration: `AlgebraicGeometry.ProEtale.PartialKummer.partial_kummer_boundary_unit_model`.

The module states the local derived-arrow model of the actual closed adjunction unit,
simultaneously for the all-continuous E and Omega coefficient rings. The only theorem
has proof `sorry`. All definitions and instances have explicit bodies without `sorry`.
The local helper structures belong to this node's arrow model and are listed in its
`lean.declarations`. There are no new definition nodes or dependency repairs.
Four already landed definitions were added to `stmt_deps`: strict-local Kummer tameness,
the all-continuous scalar map, condensed action modules, and norm-continuous representations.
The node's prose statement, proof, proof dependencies, and other fields are unchanged.
No repair note exists for this item.

Source read: main-20261015, `sec-six-functors-basics/sk-thm-sf-ctf-stability/` followed
by `sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), together with the
node's seven-step expansion. The precise geometric reference is WANTED in the original
node; that inherited source limitation is retained. No counterexample or statement
correction was found.

Hypotheses and objects, in the order of the node:

- Distinct primes: `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)`.
  Characteristic-p base: `(k : Type u) [Field k] [CharP k p]`.
- Omega is the existing `PadicAlgCl ℓ`, with its norm topology, and E is the existing
  `PadicAlgCl.FiniteIntermediateField ℓ`. This is the specified finite intermediate
  field in the fixed algebraic closure of Q_ell.
- Both rings are `Profinite.continuousMapRingObj`, applied to `E.1` or `PadicAlgCl ℓ`.
  At coefficient universe zero these are definitionally the recorded
  `continuousMapRingObjOfUniverse` objects. They use all continuous maps, also for
  incomplete Omega. They are not a filtered union of finite-subfield coefficient rings.
- `SchemeModules R X` is only an abbreviation for the recorded internal
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) (condensedRingObj R X)`.
  In particular `condensedRingObj` is the actual pullback from the condensed point.
- Y has its map to `Spec (.of k)` through `[Y.Over ...]`. Finite type is rendered by
  `[LocallyOfFiniteType (Y ↘ Spec (.of k))]` and `[QuasiCompact ...]`;
  separatedness by `[IsSeparated ...]`; regularity by `(_hY : IsRegularScheme Y)`.
- `(D : Y.IdealSheafData) (hD : IsStrictNormalCrossingsBoundary D)` uses the recorded
  reduced SNC definition, including its finite component witness. `components D hD`
  only abbreviates that witness's component family. `Fin hD.2.2.choose` represents A.
- `out : Finset A` specifies the outer part; its complement is the inner part.
  `J : Finset A`, `_hJi : (J \ out).Nonempty`, and `J ∩ out` are precisely J_i and J_o.
- W, V and their maps are explicit scheme objects, with open immersion instances on
  b and j. `_hW : Set.range (b ≫ j) = D.supportᶜ` identifies W as the complement of D.
  `_hV` specifies the complement of the union of the outer components. Thus these
  are representations of the stated opens, rather than extra arbitrary open subsets.
- h is a closed immersion from reduced Z; `_hZ` says its image is the complement of
  W inside V. This specifies the reduced closed complement, including when it is empty.
- s is an immersion from reduced S. `_hS` says its image is `stratumSet D hD J`, whose
  definition is membership in D_a if and only if a belongs to J. This specifies exactly
  the reduced locally closed stratum, allowing any isomorphic scheme presentation.
- L is a module over the recorded pulled-back E ring. `_hL` is the existing
  `IsLisseCoefficientModule`, hence locally finite free with rank allowed to vary.
- `_htame` is the existing `IsStrictLocalKummerTameModule` for the composite `b ≫ j`.
  It quantifies over geometric points, strict henselizations and every regular boundary
  parameter tuple, and pulls L back to the real algebra with all compatible prime-to-p
  roots and divisibility relations. The empty tuple has no new variables and gives the
  identity cover. No discrete or finite-image monodromy hypothesis was substituted.
- For E the input is L itself, the canonical identification of E tensor_E L with L.
  For Omega it is `(Mod.extendScalars (coefficientMap
  (CondensedRing.tameBoundaryScalarMap ℓ E) W)).obj L`, the ordinary internal extension
  along the actual continuous inclusion. No derived tensor or completion is used.

Conclusion, clause by clause:

- `∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage S` is a covering family of the
  whole stratum, not just selected geometric points. Each chart has structural map
  `U.f a ≫ s` to Y. Its schemes and indexing set have the scheme universe u.
- Each chart has `Nonempty (ChartModel ...)`; `ChartModel.roots` is a single
  `CompatibleRoots p T` datum shared by the two fields. It supplies primitive units
  in global sections for every positive order coprime to p, compatible under taking
  powers for every divisibility relation.
- `Inertia p Jo` and `Inertia p Ji` are products of all the q-adic integer groups for
  primes q different from p, indexed by exactly those branch subsets. Multiplicative
  notation is used for the additive groups of the q-adic integers. The ULift changes
  only the universe, and carries the product topology and group structure.
- `ChartModel.representation` is one `FiniteRepresentation E.1 (Go × Gi)`. This
  helper is a finite-basis presentation of the existing `NormContinuousRepresentations`
  object, rather than a second definition of continuous representations. Its `basis`
  identifies its vector space with `Fin rank → E`. The helper `.action` is exactly
  the existing representation transported through that basis.
- `coordinateModule F rank` constructs the actual internal module of continuous
  functions valued in `Fin rank → F`: take the regular module of that continuous-map
  ring and restrict scalars along the canonical diagonal ring-object map. This has
  the finite product norm topology, the finite-basis form of F tensor_E M.
- `Condensation.coordinates` identifies the action module with that constructed module.
  `Condensation.action_coordinates` pins the action on every profinite family g and
  every section x to the matrix of the E-representation, with entries mapped by E → F.
  Consequently it specifies condensed action, rather than just pointwise G-actions.
  The E and Omega condensations use the same representation and basis.
- `DerivedInvariants` packages the recorded normalized `Invariants` and
  `ProductInvariants` adjunctions, their additivity, and the proof-only abelian,
  Grothendieck and exact-inflation structures. They are existentially supplied in
  the chart models, not new hypotheses on the geometric input. `actionAbelian`
  assembles them with precisely the already defined native sectionwise preadditive
  structure, avoiding a second additive category. Its existence is the content of
  the recorded product-action-inflation dependency.
- All right derivations are `.rightDerivedFunctor` on the ordinary unbounded
  `DerivedCategory`, with the recorded ordinary K-injective normalization. The
  `HasDerivedCategory.{u+2}` presentation of action categories accommodates their
  actual object and morphism universes; it does not identify or restrict universes.
- `theta` is explicitly `conjugateIsoEquiv` of the actual derived adjunction for product
  invariants and the composite derived adjunction for inner then outer invariants.
  Its left comparison is the recorded `Adjunction.derivedCompositionLeftIso`, applied
  to `eqToIso inflation_eq.symm`. Thus `DerivedInvariants.comparison` is its hom at
  the actual degree-zero action module. There is no arbitrary comparison map.
- `unitArrow R b j h L` applies the actual Rj_* to the unit of the derived
  `upperStarLowerStarAdjunction R h`, at the actual Rb_* of `L[0]`.
  Since closed direct image is exact, its right derivation is the canonical derived
  form of h_* in the node. This uses the coefficient inverse/direct images themselves,
  not an assumed arrow and not extension by zero.
- `LocalModel.sourceIso` identifies the restricted Rj_* Rb_* object with the point
  pullback of product derived invariants. `targetIso` identifies the restricted
  Rj_* Rh_* h^* Rb_* object with the point pullback of inner-then-outer invariants.
  `unit_eq` is the commuting derived square sending the restricted actual closed
  unit to the prescribed theta. These are isomorphisms and an equality of arrows
  in the derived category, not only identifications of cohomology sheaves.
- `pointPull R T` is `(upperStarFromPoint T).mapMod R.X`, the recorded p_T^*.
  Its three instances expose the already exact additive inverse image with actual
  instance terms. No extra exactness assumption occurs in the theorem.
- The augmentation normalization of the two partial nerves is rendered by using
  the actual unit and the specified conjugate comparison in `unit_eq`; the
  seven-step docstring records inner-first/outer-second augmented-nerve construction
  of these identifications and the compatible nonnegative resolutions.
- Naturality in L is an additional part of the conclusion, for every other lisse
  tame L' and every actual module morphism f. It gives common pro-etale charts and
  `ChartModelsNatural f C C'`. This specifies one E-linear equivariant matrix a,
  its actual induced condensed maps mE and mOmega (via `HasMatrix` on every profinite
  family), and both commuting source and target derived squares (`ModelNatural`).
  The invariant adjunction data agree, so these equations use the same categories
  and functors. Ordinary scalar extension of f is used for the Omega square.
- Restrictions of a chart pull back the roots, representation, isomorphisms and all
  the displayed squares; the `LocalModel` and `ModelNatural` equations are formulated
  on whole charts, so applying the exact inverse-image functor gives the equations
  on every further restriction. The proof docstring states this refinement argument.
- No global `IsIso u_F`, extension-by-zero formula or scalar/direct-image interchange
  is asserted. The Omega model is calculated separately with the same finite basis.

Dependency declarations used (all recorded signatures and docstrings were read):

- `Sheaf.Topology.ContinuousMapCondensedRing`: `Profinite.continuousMapRingObjOfUniverse`
  and its ring-object structures; at coefficient universe zero use its definitionally
  equal published `Profinite.continuousMapRingObj` specialization.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, `upperStarFromPoint`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`, `Mod.comap`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward`, with its recorded upper/lower-star
  and derived-adjunction interfaces.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the recorded separated finite-type-over-a-field convention. Its geometric
  hypotheses are written explicitly; no bounded-constructible assumption is imposed.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`, `.Morphisms.ClosedImmersion`,
  `.Morphisms.Immersion`: `IsOpenImmersion`, `IsClosedImmersion`, `IsImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.proetalePrecoverage`.
- `Sheaf.CategoryTheory.CondensedProductActionInflation`:
  `Profinite.CondensedAction.product_action_inflation`; the associated
  `CondensedActionModule` declarations `ActionModule`, `Modules`, `sectionModule`,
  `actionPreadditive`, `Invariants`, `ProductInvariants`, `trivial`, `inflate`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  ordinary unbounded `DerivedCategory` and the recorded K-injective convention;
  the Grothendieck categories here use the canonical `.rightDerivedFunctor` interface.
- `Sheaf.Paper.StrictLocalKummerTameModule`: `TameRootOrder`,
  `IsStrictLocalKummerTameModule` and its actual compatible-root algebra.
- `Sheaf.Paper.AllContinuousScalarMate`: `CondensedRing.tameBoundaryScalarMap`.
  Only this existing underived coefficient inclusion is needed here.
- `Sheaf.Paper.NormContinuousMonodromyData`: `NormContinuousRepresentations`.
- `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`:
  `Adjunction.derivedCompositionLeftIso`, `derivedCompositionAdjunctionNormalization`.
  Its public visibility is necessary because the definition of theta uses its interface.
- Plain proof imports also include `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
  (`Scheme.proEtale_ringed_open_closed`),
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
  (`Scheme.ProEt.weaklyEtale_localization`), and the newly landed
  `Sheaf.Paper.RootTowerLisseMorphismExtension`
  (`ProEtale.rootTower_lisse_restriction_bijective`). Proof dependencies still lacking
  Lean records have no fictitious imports; their statements remain in the proof plan.

Edge cases checked before finalizing:

- Empty stratum: the empty covering family makes the chart assertion vacuous;
  it does not demand primitive roots in the zero global-section ring.
- Empty outer part or J_o: `Inertia p ∅` is a function group on an empty type,
  hence the trivial group. The exact inflation and iterated-invariants expressions
  continue to type without a nonempty-outer hypothesis.
- J_i must be nonempty as in the node. With empty inner part or empty D there are
  no permitted J. No claim about an empty inner boundary was added.
- Rank zero is permitted by both the existing representation definition and `rank : ℕ`.
  Empty matrices and the function module `Fin 0 → F` give the zero module.
- The empty scheme, disconnected charts and variable rank are allowed. Each chart
  has its own finite basis; no global constant-rank assumption was added.
- The same common chart and E matrix specify both coefficient cases; nowhere are
  Omega-valued functions required to lie in a single finite intermediate field.
- Geometric points and strict-local data use the already recorded scheme-universe
  convention; action-group ULifts preserve every prime-to-p inertia factor.

Searches actually made:

- `msearch.py ... leanfinder` with query
  `partial Kummer boundary closed adjunction unit product group derived invariants tame lisse sheaf`:
  eight unrelated number-theoretic Kummer/Hilbert-90 hits; no geometric arrow model.
- `msearch.py ... loogle` with query
  `CategoryTheory.conjugateIsoEquiv, CategoryTheory.Adjunction.unit`: zero hits.
- `msearch.py ... grep` with query `Kummer|kummer|ProductInvariants|partial.*boundary`:
  25 unrelated Mathlib Kummer hits; no statement of this geometric comparison.
- Local `rg` over the named Mathlib and project Lean trees for
  `Kummer|kummer|TameRoot|tameRoot|ProductInvariants|PartialKummer`: existing strict-local
  Kummer predicate, tame-root and scalar-comparison files, and condensed-action interfaces
  were found and read. The existing finite-dimensional continuous representation category
  was found in `NormContinuousMonodromyData` and reused.
- Search for this exact node id in `lean/WeilConjectures` found no declaration of the item.
  Searches in `lean/Sheaf` and upstream Lean likewise found no existing partial closed-unit
  theorem. Mathlib representation and primitive-root APIs supply only the component notions.
- Focused `rg` of the basis and linear-equivalence files identified `Module.Basis.equivFun`
  for the actual finite-coordinate presentation. No replacement of that map was axiomatized.

Validation: `scompile.py` compiled both the sandbox module and the intended library module
cleanly after replacing the duplicate representation predicate with a presentation of
`NormContinuousRepresentations`. The final packet adds the newly available proof import
and is checked again by the prescribed delivery dry run. No local or global library build,
read-only source edit, direct git mutation or launcher-script modification was performed.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
