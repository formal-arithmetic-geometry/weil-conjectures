## Worker report

States `AlgebraicGeometry.ProEtale.localFinitePresentation_inverseImage` in
`Sheaf.AlgebraicGeometry.LocalFinitePresentationInverseImage`. Its only postponed
proof is that named theorem. No statement correction, dependency repair, or new
DAG node is needed. The original node changes only in `lean`.

The real-data helper `finitePresentationPullbackComparison` is the inverse of
`upperStarComp` for `pullback.fst ≫ f`, followed by `eqToIso` of
`pullback.condition`, followed by `upperStarComp` for `pullback.snd ≫ u`.
Thus it has direction `v* f* ≅ h* u*` and uses the canonical specified mates.
`FinitePresentationTransportWitness` merely packages the local conclusion of
this item; its abstract ambient categories avoid repeatedly elaborating the
large sheaf constructions. It introduces no replacement definition of modules,
finite freeness, finite presentation, restriction, or inverse image.

Hypothesis and conclusion correspondence:

- Arbitrary schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Commutative ring object on the abelian pro-etale site: the binder
  `R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}` with `[MonObj R]` and
  `[IsCommMonObj R]`. The imported upstream tensor on Ab is tensor over the
  integers, and the sheaf tensor is its localized/sheafified objectwise tensor.
- Internal module: `M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R`.
- The given indexed covering: `𝒰 : Scheme.Cover.{v} Scheme.proetalePrecoverage Y`.
  The index universe `v` is independent of `u`; `𝒰.I₀`, `𝒰.X`, `𝒰.f` give I, U_i,
  and u_i. Covers are not assumed finite or nonempty.
- The specified nonnegative ranks: `m n : 𝒰.I₀ → ℕ`.
- Specified differentials: `d i : Mod.finiteFree (u_i*.obj R) (m i) ⟶
  Mod.finiteFree (u_i*.obj R) (n i)`.
- Specified presentations: `p i : (u_i*.mapMod R).obj M ≅ cokernel (d i)`.
- V_i, v_i and h_i are exactly `pullback f (𝒰.f i)`, `pullback.fst`, and
  `pullback.snd`. The first conjunct says the presieve of the actual pulled-back
  pre-zero-hypercover belongs to `Scheme.proetalePrecoverage X`. This uses the
  original index type, not a refinement or newly chosen cover.
- For each i the next conjunct supplies `FinitePresentationTransportWitness`
  with F=f*, G=v*, J=u*, H=h*, and e the helper comparison above.
- `ringIso` is an isomorphism of bundled monoid/ring objects `Mon.mk (G(F R)) ≅
  Mon.mk (H(J R))`. `ringIso_hom` fixes its underlying map as e_R, so this is
  beta_i from the node, rather than an existentially unrelated ring isomorphism.
- `moduleIso` has precisely the iterated-module source and the target restricted
  along `ringIso.hom.hom` using the existing `Mod.comap`. `moduleIso_hom` fixes
  its underlying map as e_M, with the actual transported actions.
- `freeIso k` has source `Res_beta (mapMod H ((J R)^k))` and target `(G(F R))^k`
  for every `k : ℕ`. `freeIso_projection` specifies each coordinate as H applied
  to the original biproduct projection, followed by beta inverse. These
  coordinates uniquely determine the canonical map and hence its inverse.
- `presentationIso` uses the literal differential
  `(freeIso m).inv ≫ Res_beta.map (mapMod H |>.map d) ≫ (freeIso n).hom`.
  In mathematical right-to-left notation this is a_n H(d) a_m^{-1}, exactly d'.
- `presentationIso_π` fixes the induced cokernel presentation using the original
  `cokernel.π d ≫ p.inv`, its transported/restricted image, the inverse module
  comparison, and the new cokernel projection. This retains dependence on the
  specified p and rules out an arbitrary isomorphism with the same objects.
- The last conjunct is exactly the existing `IsLocallyFinitelyPresented` for
  `(f*.mapMod R).obj M`. The preceding conjuncts retain the specified original
  base-changed cover and its original ranks as explicit witnesses. The existing
  existential predicate uses u-small cover indices; an arbitrary larger cover
  can be reduced for that predicate by choosing finite affine subfamilies over
  affine opens, while all explicit original-cover data remain in the theorem.
- There is no flatness, finite type, Noetherian, nonzero-ring, positive-rank,
  nonempty-index, or weakly-etale-f assumption.

Recorded dependency declarations read and used:

- `sk-def-sfb-sheaf-tensor`: `Sheaf.CategoryTheory.SheafTensor`,
  `CategoryTheory.sfbSheafTensor_properties`, and its recorded canonical
  `sfbSheafTensorStructure`; the upstream pro-etale instances use this same
  localized sheaf tensor.
- `sk-def-sfb-ring-object`:
  `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`,
  `CategoryTheory.Functor.monObjCompForget₂` and the public Ab tensor/ring
  constructions; `MonObj`, `IsCommMonObj`, and `Mon` are the actual ring notions.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `ModObj`, and the regular module.
- `def-sfb-finite-upper-star`:
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.ProEtale.upperStar`; the compatibility module reexports
  `FiniteCoefficient.UpperLowerStar.Defs`, which was read in full at the relevant
  declarations, including `upperStarComp` and the adjunction.
- `def-sfb-finite-upper-star-monoidal`:
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`,
  `AlgebraicGeometry.ProEtale.monoidal_upperStar`; public through the module-object
  monoidal module used by the existing local-finite-presentation module.
- `def-sfb-modobj-transport`:
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Functor.mapMod`, `modObjObj`, `act_mapMod_obj`. The compact lean
  attachment gives `declarations`; the closed audit supplies their module/ranges.
- `def-sfb-locally-finitely-presented`:
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`,
  `AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented`.
- `def-weil-pbc-proetale-covering`:
  `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.proetalePrecoverage` from `mathlib_match`.
- `def-sfb-finitely-presented-module`:
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`,
  `CategoryTheory.Mod.finiteFree` and `Mod.IsFinitelyPresented`.
- `sk-def-sfb-change-of-scalars`:
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`,
  `CategoryTheory.Mod.comap` and the extension/coextension adjunctions. The former
  is the actual Mathlib restriction functor, with unchanged underlying maps.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.

Proof-plan modules are imported through the above public closure and the
additional ordinary imports of `WeaklyEtaleStability`,
`MonoidalFiniteFreeTransport`, and `Adjunction.Mates`. The theorem docstring
carries all eight DAG proof steps, including the mate formula, linearity,
right exactness, coordinate identifications, and universal cokernel argument.

Edge cases checked before drafting: ranks zero (empty biproduct, unique zero
map), m=0, n=0, zero ring/module, empty cover of the empty scheme, identity f,
isomorphisms f, arbitrary non-flat f, large index sets, and both scalar-comparison
directions. For zero rank the coordinate condition is empty but the source and
target are zero objects; for nonzero rank the projections determine the map.
The empty-index case leaves the pointwise witnesses vacuous and retains the
covering membership condition, so it does not assert that an empty family covers
a nonempty scheme. No disputed statement or node fault was found.

Searches (all read-only; launcher msearch wrapper):

- LeanFinder: `Inverse image of internal modules on a pro-etale site preserves
  a specified finite free presentation on the base changed covering`.
  Eight hits, including Scheme.etaleTopology, Scheme.smallEtaleTopology,
  IsEtale.of_comp and KaehlerDifferential.isBaseChange_of_formallyEtale;
  none is the internal-module statement on a specified covering.
- Loogle: `"IsFinitePresentation"`. Twelve hits in the ordinary
  `SheafOfModules` API, including `IsFinitePresentation`, `isFinitePresentation`,
  and local `QuasicoherentData.IsFinitePresentation`; these concern another
  encoding and do not provide the specified internal-module comparisons.
- msearch grep: `IsLocallyFinitelyPresented|finiteFree|mapMod` in
  `CategoryTheory/Monoidal`. One result, Mon.lean:856, the TODO for mapMod;
  the implementation actually used is already in the upstream project.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for
  `IsLocallyFinitelyPresented`, finite-free isomorphisms and base-change
  presentations found the existing notions used here and
  `CondensedConstructibleSerre.lfp_pullback` (private), which states only
  existential preservation, not the specified cover, beta, coordinates, d', or
  induced presentation. It therefore cannot bind this strengthened item.
- rg for the item id in `lean/WeilConjectures` returned no match; searches for
  the new full names in both library roots and `dag/lean_names_upstream.json`
  returned no pre-existing declaration. The node's earlier search/audit also
  explicitly distinguishes the same stronger specified-cover assertion from
  existing existential preservation lemmas.

Validation: every compile uses the prescribed scompile.py. The initial large
sheaf-specialized witness exceeded 60 seconds. A scratch compile isolated the
cost to repeated concrete sheaf elaboration; the actual comparison compiled
cleanly. The final generic witness retains the same specialized fields and
normalizations. Final compile and delivery-check outcomes are recorded below.

## Second reading by Q57

This is a separate rereading by the same dispatcher worker; no second agent was
started, as explicitly instructed. Independent review is performed by the
maintainer after delivery. I reopened the node and module and matched every
binder and clause above. In particular I checked e has direction v*f* to h*u*,
beta is a ring-object isomorphism with that underlying map, restriction uses
beta (not its inverse), the coordinates use beta inverse, and d' has direction
rank m to rank n. I checked the induced-cokernel equation starts at the new
rank-n free module and ends at the chosen new cokernel. The abstract witness
parameters specialize to the four actual inverse-image functors without an
extra hypothesis on any of them. The same index set and both original ranks
are retained. No mathematical statement was changed in resolving compilation
costs, and no independent notion was introduced by the witness packaging.

Final validation: scompile.py passed both the isolated sandbox compile (26.8 s)
and the actual module compile (26.6 s), with no errors or warnings. The required
`deliver2.py Q57 lem-sfb-local-finite-presentation-inverse-image --no-push`
printed `OK (dry run)` for commit `46bfb1b90f7`: the server preflight and per-file
compile both passed. The final delivery reruns these checks after adding this
validation note.
